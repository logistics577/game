"""
Multiplayer Ludo Game Backend
FastAPI + WebSockets + SQLite + asyncio
"""

import asyncio
import json
import random
import sqlite3
import uuid
from datetime import datetime
from typing import Dict, List, Optional, Set
from contextlib import asynccontextmanager

from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel

# ─────────────────────────────────────────────
#  DATABASE SETUP
# ─────────────────────────────────────────────
DB_PATH = "ludo_game.db"

def get_db():
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    conn = get_db()
    cursor = conn.cursor()
    cursor.executescript("""
        CREATE TABLE IF NOT EXISTS users (
            id TEXT PRIMARY KEY,
            username TEXT UNIQUE NOT NULL,
            session_token TEXT UNIQUE,
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS rooms (
            room_id TEXT PRIMARY KEY,
            host_id TEXT NOT NULL,
            created_at TEXT NOT NULL,
            status TEXT DEFAULT 'waiting'
        );

        CREATE TABLE IF NOT EXISTS room_players (
            room_id TEXT NOT NULL,
            user_id TEXT NOT NULL,
            joined_at TEXT NOT NULL,
            PRIMARY KEY (room_id, user_id)
        );

        CREATE TABLE IF NOT EXISTS invitations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            room_id TEXT NOT NULL,
            inviter_id TEXT NOT NULL,
            inviter_username TEXT NOT NULL,
            invited_user_id TEXT NOT NULL,
            timestamp TEXT NOT NULL,
            seen INTEGER DEFAULT 0
        );

        CREATE TABLE IF NOT EXISTS activity_logs (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            room_id TEXT,
            user_id TEXT,
            event_type TEXT NOT NULL,
            event_data TEXT,
            timestamp TEXT NOT NULL
        );
    """)
    conn.commit()
    conn.close()

async def log_event(room_id: Optional[str], user_id: Optional[str], event_type: str, event_data: dict):
    """Async wrapper for DB logging — runs in thread pool to avoid blocking."""
    def _write():
        conn = get_db()
        conn.execute(
            "INSERT INTO activity_logs (room_id, user_id, event_type, event_data, timestamp) VALUES (?,?,?,?,?)",
            (room_id, user_id, event_type, json.dumps(event_data), datetime.utcnow().isoformat())
        )
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _write)


# ─────────────────────────────────────────────
#  IN-MEMORY STORES
# ─────────────────────────────────────────────
sessions: Dict[str, dict] = {}        # token -> {user_id, username, connected}
rooms: Dict[str, dict] = {}           # room_id -> room object
invitations: Dict[str, list] = {}     # user_id -> list of invite objects
user_tokens: Dict[str, str] = {}      # user_id -> session token (reverse lookup)
online_users: Set[str] = set()         # user_ids currently connected via WebSocket


# ─────────────────────────────────────────────
#  LUDO GAME LOGIC
# ─────────────────────────────────────────────
COLORS = ["red", "green", "yellow", "blue"]

# Each color's starting position on the absolute 52-square track
COLOR_START = {"red": 0, "green": 13, "yellow": 26, "blue": 39}

# Safe squares (absolute track positions)
SAFE_SQUARES = {0, 8, 13, 21, 26, 34, 39, 47}

# POSITIONS: -1=yard, 0-51=main track (LOCAL to each color), 52-56=home column
# Local position 0 = color's own start square
# Local position 51 = last square before home column
# Home column = positions 52-56 (5 squares toward center)
# Win = position 56

def initial_token_positions(color: str) -> list:
    """All 4 tokens start in yard (-1)."""
    return [-1, -1, -1, -1]

def can_enter_board(dice: int) -> bool:
    return dice == 6

def move_token(positions: list, token_idx: int, dice: int, color: str) -> dict:
    """
    Local position system: 0-51 = main track, 52-56 = home column.
    Position 0 is always THIS color's starting square.
    """
    pos = positions[token_idx]
    result = {"new_positions": positions[:], "captured": False, "finished_token": False, "valid": True}

    # In yard — need 6 to exit
    if pos == -1:
        if dice == 6:
            result["new_positions"][token_idx] = 0  # start at local pos 0
        else:
            result["valid"] = False
        return result

    new_pos = pos + dice

    # Still on main track
    if new_pos <= 51:
        result["new_positions"][token_idx] = new_pos
        return result

    # Entering home column (pos 52-56)
    home_step = new_pos - 51  # 1-5 steps into home
    if home_step <= 5:
        result["new_positions"][token_idx] = 51 + home_step  # 52-56
        if 51 + home_step == 56:
            result["finished_token"] = True
    else:
        result["valid"] = False  # overshot home

    return result

def create_game_state(players: list) -> dict:
    """Creates fresh game state for a list of players (user dicts)."""
    color_map = {p["user_id"]: COLORS[i] for i, p in enumerate(players)}
    token_positions = {uid: initial_token_positions(color_map[uid]) for uid in color_map}
    return {
        "status": "playing",
        "players": [p["user_id"] for p in players],
        "color_map": color_map,
        "token_positions": token_positions,
        "current_turn": players[0]["user_id"],
        "dice_value": None,
        "dice_rolled": False,
        "finished_players": [],
        "winner": None,
    }

def check_winner(game_state: dict) -> Optional[str]:
    for uid, positions in game_state["token_positions"].items():
        if all(p == 56 for p in positions):  # all tokens at end of home column
            return uid
    return None

def next_turn(game_state: dict, current_uid: str, got_six: bool) -> str:
    if got_six:
        return current_uid  # same player rolls again on 6
    players = [p for p in game_state["players"] if p not in game_state["finished_players"]]
    idx = players.index(current_uid) if current_uid in players else 0
    return players[(idx + 1) % len(players)]


# ─────────────────────────────────────────────
#  WEBSOCKET MANAGER
# ─────────────────────────────────────────────
class WebSocketManager:
    def __init__(self):
        # room_id -> set of (websocket, user_id) tuples
        self.room_connections: Dict[str, Set] = {}
        # user_id -> websocket
        self.user_ws: Dict[str, WebSocket] = {}

    async def connect(self, ws: WebSocket, room_id: str, user_id: str):
        await ws.accept()
        if room_id not in self.room_connections:
            self.room_connections[room_id] = set()
        self.room_connections[room_id].add((ws, user_id))
        self.user_ws[user_id] = ws

    def disconnect(self, ws: WebSocket, room_id: str, user_id: str):
        if room_id in self.room_connections:
            self.room_connections[room_id].discard((ws, user_id))
            if not self.room_connections[room_id]:
                del self.room_connections[room_id]
        self.user_ws.pop(user_id, None)

    async def broadcast(self, room_id: str, message: dict):
        """Broadcast to all connections in a room."""
        if room_id not in self.room_connections:
            return
        dead = set()
        data = json.dumps(message)
        for ws, uid in self.room_connections[room_id]:
            try:
                await ws.send_text(data)
            except Exception:
                dead.add((ws, uid))
        self.room_connections[room_id] -= dead

    async def send_to_user(self, user_id: str, message: dict):
        """Send a private message to a specific user."""
        ws = self.user_ws.get(user_id)
        if ws:
            try:
                await ws.send_text(json.dumps(message))
            except Exception:
                self.user_ws.pop(user_id, None)


ws_manager = WebSocketManager()


# ─────────────────────────────────────────────
#  PYDANTIC MODELS
# ─────────────────────────────────────────────
class LoginRequest(BaseModel):
    username: str

class CreateRoomRequest(BaseModel):
    session_token: str
    max_players: int = 4

class JoinRoomRequest(BaseModel):
    session_token: str
    room_id: str

class InviteRequest(BaseModel):
    session_token: str
    room_id: str
    invited_username: str

class StartGameRequest(BaseModel):
    session_token: str
    room_id: str


# ─────────────────────────────────────────────
#  SESSION HELPERS
# ─────────────────────────────────────────────
def get_session(token: str) -> dict:
    session = sessions.get(token)
    if not session:
        raise HTTPException(status_code=401, detail="Invalid or expired session token")
    return session

def get_user_by_username(username: str) -> Optional[dict]:
    for token, sess in sessions.items():
        if sess["username"].lower() == username.lower():
            return sess
    return None


# ─────────────────────────────────────────────
#  FASTAPI APP
# ─────────────────────────────────────────────
@asynccontextmanager
async def lifespan(app: FastAPI):
    init_db()
    print("✅ Database initialized")
    yield
    print("🛑 Shutting down")

app = FastAPI(title="Multiplayer Ludo API", lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)



# ─────────────────────────────────────────────
#  SERVE FRONTEND
# ─────────────────────────────────────────────
@app.get("/", response_class=HTMLResponse)
async def serve_frontend():
    with open("index.html", "r") as f:
        return HTMLResponse(content=f.read())


# ─────────────────────────────────────────────
#  REST API ROUTES
# ─────────────────────────────────────────────

@app.post("/api/login")
async def login(req: LoginRequest):
    username = req.username.strip()
    if not username or len(username) < 2:
        raise HTTPException(status_code=400, detail="Username must be at least 2 characters")

    # Check if already logged in
    existing = get_user_by_username(username)
    if existing:
        token = user_tokens.get(existing["user_id"])
        return {"session_token": token, "user_id": existing["user_id"], "username": username, "message": "Resumed session"}

    user_id = str(uuid.uuid4())
    token = str(uuid.uuid4())

    sessions[token] = {"user_id": user_id, "username": username, "connected": True}
    user_tokens[user_id] = token
    online_users.add(user_id)  # mark online immediately on login

    # Persist to DB async
    def _persist():
        conn = get_db()
        conn.execute(
            "INSERT OR REPLACE INTO users (id, username, session_token, created_at) VALUES (?,?,?,?)",
            (user_id, username, token, datetime.utcnow().isoformat())
        )
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _persist)
    await log_event(None, user_id, "user_login", {"username": username})

    return {"session_token": token, "user_id": user_id, "username": username, "message": "Login successful"}


@app.post("/api/rooms/create")
async def create_room(req: CreateRoomRequest):
    session = get_session(req.session_token)
    user_id = session["user_id"]

    room_id = str(uuid.uuid4())[:8].upper()
    now = datetime.utcnow().isoformat()

    max_players = max(2, min(4, req.max_players))  # clamp 2-4

    room = {
        "room_id": room_id,
        "host_id": user_id,
        "players": [{"user_id": user_id, "username": session["username"]}],
        "game_state": None,
        "created_at": now,
        "status": "waiting",
        "max_players": max_players,
    }
    rooms[room_id] = room

    def _persist():
        conn = get_db()
        conn.execute("INSERT INTO rooms (room_id, host_id, created_at, status) VALUES (?,?,?,?)",
                     (room_id, user_id, now, "waiting"))
        conn.execute("INSERT INTO room_players (room_id, user_id, joined_at) VALUES (?,?,?)",
                     (room_id, user_id, now))
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _persist)
    await log_event(room_id, user_id, "room_created", {"room_id": room_id})

    return {"room_id": room_id, "message": "Room created", "room": _room_info(room)}


@app.post("/api/rooms/join")
async def join_room(req: JoinRoomRequest):
    session = get_session(req.session_token)
    user_id = session["user_id"]
    room_id = req.room_id.upper()

    room = rooms.get(room_id)
    if not room:
        raise HTTPException(status_code=404, detail="Room not found")
    if room["status"] != "waiting":
        raise HTTPException(status_code=400, detail="Game already started")
    if len(room["players"]) >= room.get("max_players", 4):
        raise HTTPException(status_code=400, detail=f"Room is full (max {room.get('max_players', 4)} players)")
    if any(p["user_id"] == user_id for p in room["players"]):
        return {"message": "Already in room", "room": _room_info(room)}

    room["players"].append({"user_id": user_id, "username": session["username"]})
    now = datetime.utcnow().isoformat()

    def _persist():
        conn = get_db()
        conn.execute("INSERT OR IGNORE INTO room_players (room_id, user_id, joined_at) VALUES (?,?,?)",
                     (room_id, user_id, now))
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _persist)
    await log_event(room_id, user_id, "player_joined", {"username": session["username"]})

    # Broadcast join event to room
    await ws_manager.broadcast(room_id, {
        "event": "player_joined",
        "user_id": user_id,
        "username": session["username"],
        "players": room["players"],
        "room_id": room_id,
    })

    return {"message": "Joined room", "room": _room_info(room)}


@app.post("/api/rooms/invite")
async def invite_player(req: InviteRequest):
    session = get_session(req.session_token)
    room = rooms.get(req.room_id.upper())
    if not room:
        raise HTTPException(status_code=404, detail="Room not found")
    if room["host_id"] != session["user_id"]:
        raise HTTPException(status_code=403, detail="Only the host can invite players")

    target = get_user_by_username(req.invited_username)
    if not target:
        raise HTTPException(status_code=404, detail="User not found or not logged in")

    invite = {
        "room_id": req.room_id.upper(),
        "inviter_id": session["user_id"],
        "inviter_username": session["username"],
        "invited_user_id": target["user_id"],
        "timestamp": datetime.utcnow().isoformat(),
    }
    invitations.setdefault(target["user_id"], []).append(invite)

    # Push real-time invite notification
    await ws_manager.send_to_user(target["user_id"], {
        "event": "invitation_received",
        "invite": invite,
    })

    # Persist invite to DB
    def _save_invite():
        conn = get_db()
        conn.execute(
            "INSERT INTO invitations (room_id,inviter_id,inviter_username,invited_user_id,timestamp) VALUES (?,?,?,?,?)",
            (invite["room_id"], invite["inviter_id"], invite["inviter_username"], invite["invited_user_id"], invite["timestamp"])
        )
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _save_invite)

    return {"message": f"Invitation sent to {req.invited_username}"}


@app.get("/api/rooms/{room_id}")
async def get_room(room_id: str):
    room = rooms.get(room_id.upper())
    if not room:
        raise HTTPException(status_code=404, detail="Room not found")
    return _room_info(room)


@app.get("/api/rooms")
async def list_rooms():
    return [_room_info(r) for r in rooms.values() if r["status"] == "waiting"]


@app.get("/api/invitations/{session_token}")
async def get_invitations(session_token: str):
    session = get_session(session_token)
    uid = session["user_id"]
    # Merge in-memory + DB persisted invitations
    mem = invitations.get(uid, [])
    def _load():
        conn = get_db()
        rows = conn.execute(
            "SELECT * FROM invitations WHERE invited_user_id=? ORDER BY timestamp DESC",
            (uid,)
        ).fetchall()
        conn.close()
        return [dict(r) for r in rows]
    db_invs = await asyncio.get_event_loop().run_in_executor(None, _load)
    # Convert DB rows to same format as memory invites
    merged = []
    seen_keys = set()
    for inv in mem:
        key = f"{inv['room_id']}|{inv['inviter_id']}|{inv['timestamp']}"
        if key not in seen_keys:
            seen_keys.add(key)
            merged.append(inv)
    for row in db_invs:
        key = f"{row['room_id']}|{row['inviter_id']}|{row['timestamp']}"
        if key not in seen_keys:
            seen_keys.add(key)
            merged.append({
                "room_id": row["room_id"],
                "inviter_id": row["inviter_id"],
                "inviter_username": row["inviter_username"],
                "invited_user_id": row["invited_user_id"],
                "timestamp": row["timestamp"],
            })
    return merged


@app.post("/api/game/start")
async def start_game(req: StartGameRequest):
    session = get_session(req.session_token)
    room_id = req.room_id.upper()
    room = rooms.get(room_id)
    if not room:
        raise HTTPException(status_code=404, detail="Room not found")
    if room["host_id"] != session["user_id"]:
        raise HTTPException(status_code=403, detail="Only host can start game")
    if len(room["players"]) < 2:
        raise HTTPException(status_code=400, detail="Need at least 2 players to start")
    if len(room["players"]) > room.get("max_players", 4):
        raise HTTPException(status_code=400, detail="Too many players")
    if room["status"] != "waiting":
        raise HTTPException(status_code=400, detail="Game already started")

    room["game_state"] = create_game_state(room["players"])
    room["status"] = "playing"

    def _persist():
        conn = get_db()
        conn.execute("UPDATE rooms SET status='playing' WHERE room_id=?", (room_id,))
        conn.commit()
        conn.close()
    await asyncio.get_event_loop().run_in_executor(None, _persist)
    await log_event(room_id, session["user_id"], "game_started", {"players": [p["user_id"] for p in room["players"]]})

    await ws_manager.broadcast(room_id, {
        "event": "game_started",
        "game_state": room["game_state"],
        "room_id": room_id,
    })

    return {"message": "Game started", "game_state": room["game_state"]}


@app.get("/api/users")
async def list_users():
    return [
        {"user_id": s["user_id"], "username": s["username"], "online": s["user_id"] in online_users}
        for s in sessions.values()
    ]

@app.post("/api/logout")
async def logout(req: CreateRoomRequest):  # reuse {session_token}
    session = sessions.pop(req.session_token, None)
    if session:
        uid = session["user_id"]
        online_users.discard(uid)
        user_tokens.pop(uid, None)
        await log_event(None, uid, "user_logout", {"username": session["username"]})
    return {"message": "Logged out"}

@app.post("/api/session/restore")
async def restore_session(req: CreateRoomRequest):  # {session_token}
    session = sessions.get(req.session_token)
    if not session:
        # Try to restore from DB
        def _lookup():
            conn = get_db()
            row = conn.execute("SELECT * FROM users WHERE session_token=?", (req.session_token,)).fetchone()
            conn.close()
            return dict(row) if row else None
        row = await asyncio.get_event_loop().run_in_executor(None, _lookup)
        if not row:
            raise HTTPException(status_code=401, detail="Session expired")
        # Re-hydrate session
        sessions[req.session_token] = {"user_id": row["id"], "username": row["username"], "connected": False}
        user_tokens[row["id"]] = req.session_token
        session = sessions[req.session_token]
    online_users.add(session["user_id"])  # mark online on restore
    return {"session_token": req.session_token, "user_id": session["user_id"], "username": session["username"], "message": "Session restored"}


def _room_info(room: dict) -> dict:
    return {
        "room_id": room["room_id"],
        "host_id": room["host_id"],
        "players": room["players"],
        "status": room["status"],
        "created_at": room["created_at"],
        "game_state": room.get("game_state"),
        "player_count": len(room["players"]),
        "max_players": room.get("max_players", 4),
    }


# ─────────────────────────────────────────────
#  WEBSOCKET ENDPOINT
# ─────────────────────────────────────────────
@app.websocket("/ws/{room_id}/{session_token}")
async def websocket_endpoint(ws: WebSocket, room_id: str, session_token: str):
    session = sessions.get(session_token)
    if not session:
        await ws.close(code=4001, reason="Invalid session")
        return

    room_id = room_id.upper()
    room = rooms.get(room_id)
    if not room:
        await ws.close(code=4004, reason="Room not found")
        return

    user_id = session["user_id"]
    username = session["username"]

    await ws_manager.connect(ws, room_id, user_id)
    session["connected"] = True
    online_users.add(user_id)

    await log_event(room_id, user_id, "ws_connected", {"username": username})

    # Send current room state on connect
    await ws.send_text(json.dumps({
        "event": "connected",
        "room": _room_info(room),
        "user_id": user_id,
        "username": username,
    }))

    # Notify others
    await ws_manager.broadcast(room_id, {
        "event": "player_online",
        "user_id": user_id,
        "username": username,
    })

    try:
        while True:
            raw = await ws.receive_text()
            try:
                data = json.loads(raw)
            except json.JSONDecodeError:
                await ws.send_text(json.dumps({"event": "error", "message": "Invalid JSON"}))
                continue

            action = data.get("action")

            # ── ROLL DICE ──────────────────────────────────
            if action == "roll_dice":
                gs = room.get("game_state")
                if not gs or gs["status"] != "playing":
                    await ws.send_text(json.dumps({"event": "error", "message": "Game not active"}))
                    continue
                if gs["current_turn"] != user_id:
                    await ws.send_text(json.dumps({"event": "error", "message": "Not your turn"}))
                    continue
                if gs["dice_rolled"]:
                    await ws.send_text(json.dumps({"event": "error", "message": "Already rolled this turn"}))
                    continue

                dice = random.randint(1, 6)
                gs["dice_value"] = dice
                gs["dice_rolled"] = True

                await log_event(room_id, user_id, "dice_rolled", {"dice": dice})
                await ws_manager.broadcast(room_id, {
                    "event": "dice_rolled",
                    "user_id": user_id,
                    "username": username,
                    "dice": dice,
                    "game_state": gs,
                })

                # Auto-advance turn if no valid moves exist
                color = gs["color_map"][user_id]
                positions = gs["token_positions"][user_id]
                has_move = any(
                    move_token(positions, i, dice, color)["valid"]
                    for i in range(4)
                )
                if not has_move:
                    gs["dice_rolled"] = False
                    gs["current_turn"] = next_turn(gs, user_id, False)
                    await ws_manager.broadcast(room_id, {
                        "event": "turn_skipped",
                        "user_id": user_id,
                        "username": username,
                        "reason": "no_valid_move",
                        "game_state": gs,
                    })

            # ── MOVE TOKEN ─────────────────────────────────
            elif action == "move_token":
                gs = room.get("game_state")
                if not gs or gs["status"] != "playing":
                    await ws.send_text(json.dumps({"event": "error", "message": "Game not active"}))
                    continue
                if gs["current_turn"] != user_id:
                    await ws.send_text(json.dumps({"event": "error", "message": "Not your turn"}))
                    continue
                if not gs["dice_rolled"]:
                    await ws.send_text(json.dumps({"event": "error", "message": "Roll dice first"}))
                    continue

                token_idx = data.get("token_index")
                if token_idx is None or not (0 <= token_idx <= 3):
                    await ws.send_text(json.dumps({"event": "error", "message": "Invalid token index (0-3)"}))
                    continue

                color = gs["color_map"][user_id]
                positions = gs["token_positions"][user_id]
                dice = gs["dice_value"]

                result = move_token(positions, token_idx, dice, color)
                if not result["valid"]:
                    await ws.send_text(json.dumps({"event": "error", "message": "Invalid move for this token"}))
                    continue

                gs["token_positions"][user_id] = result["new_positions"]
                got_six = dice == 6

                if result["finished_token"]:
                    # Check if all tokens finished
                    if all(p == HOME_COLUMN_START[color] + 5 for p in result["new_positions"]):
                        gs["finished_players"].append(user_id)

                winner = check_winner(gs)
                if winner:
                    gs["status"] = "finished"
                    gs["winner"] = winner
                    await log_event(room_id, winner, "game_ended", {"winner": winner})
                    await ws_manager.broadcast(room_id, {
                        "event": "game_over",
                        "winner": winner,
                        "winner_username": next(p["username"] for p in room["players"] if p["user_id"] == winner),
                        "game_state": gs,
                    })
                else:
                    gs["dice_rolled"] = False
                    gs["current_turn"] = next_turn(gs, user_id, got_six)
                    await log_event(room_id, user_id, "token_moved", {"token": token_idx, "pos": result["new_positions"][token_idx]})
                    await ws_manager.broadcast(room_id, {
                        "event": "token_moved",
                        "user_id": user_id,
                        "username": username,
                        "token_index": token_idx,
                        "new_positions": result["new_positions"],
                        "got_six": got_six,
                        "game_state": gs,
                    })

            # ── CHAT MESSAGE ───────────────────────────────
            elif action == "chat":
                msg = str(data.get("message", ""))[:200]
                await ws_manager.broadcast(room_id, {
                    "event": "chat",
                    "user_id": user_id,
                    "username": username,
                    "message": msg,
                    "timestamp": datetime.utcnow().isoformat(),
                })

            # ── PING ───────────────────────────────────────
            elif action == "ping":
                await ws.send_text(json.dumps({"event": "pong", "timestamp": datetime.utcnow().isoformat()}))

            else:
                await ws.send_text(json.dumps({"event": "error", "message": f"Unknown action: {action}"}))

    except WebSocketDisconnect:
        pass
    except Exception as e:
        print(f"WS error [{user_id}]: {e}")
    finally:
        ws_manager.disconnect(ws, room_id, user_id)
        session["connected"] = False
        online_users.discard(user_id)
        await log_event(room_id, user_id, "ws_disconnected", {"username": username})

        # Handle host leaving
        if room and room["host_id"] == user_id and room["status"] == "waiting":
            remaining = [p for p in room["players"] if p["user_id"] != user_id]
            if remaining:
                room["host_id"] = remaining[0]["user_id"]
                room["players"] = remaining
                await ws_manager.broadcast(room_id, {
                    "event": "host_changed",
                    "new_host_id": remaining[0]["user_id"],
                    "new_host_username": remaining[0]["username"],
                })
            else:
                room["status"] = "empty"

        await ws_manager.broadcast(room_id, {
            "event": "player_left",
            "user_id": user_id,
            "username": username,
        })


# ─────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────
if __name__ == "__main__":
    import uvicorn
    uvicorn.run("main:app", host="0.0.0.0", port=8000, reload=True)