"""
Averin Holdings' Sentinel — Discord Moderation Bot v2.0
Production-grade moderation system with full feature parity.

New in v2.0:
  - Automod engine (spam, invites, mass mentions, word filter, anti-raid)
  - Punishment ladder / escalation system
  - Slowmode & channel lockdown
  - Moderator notes
  - Event logging (joins, leaves, edits, deletes, role changes, voice)
  - Temporary bans with auto-expiry background task
  - /whois user lookup
  - Staff report system
  - Tags / custom commands
  - Strike expiry & case expungement
  - Moderation statistics
"""

import discord
from discord.ext import commands, tasks
from discord import app_commands
import sqlite3
import asyncio
import uuid
import datetime
import json
import re
import os
import sys
from collections import defaultdict
from typing import Optional

try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass  # dotenv optional — falls back to real environment variables

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION  (set via environment variables or a .env file)
# Required:  DISCORD_TOKEN=your_bot_token
# Optional:  BOT_NAME, DATABASE_PATH
# ─────────────────────────────────────────────────────────────────────────────
BOT_TOKEN = os.environ.get("DISCORD_TOKEN", "")
if not BOT_TOKEN:
    print("[Sentinel] ERROR: DISCORD_TOKEN environment variable is not set.")
    print("[Sentinel] Create a .env file containing:  DISCORD_TOKEN=your_token_here")
    sys.exit(1)

BOT_NAME      = os.environ.get("BOT_NAME", "Averin Holdings' Sentinel")
BOT_VERSION   = "2.0.0"
DATABASE_PATH = os.environ.get("DATABASE_PATH", "sentinel.db")


DEFAULT_DM_ON_ACTION    = True
DEFAULT_APPEALS_ENABLED = True

# Automod defaults (all per-guild configurable via /automod commands)
AUTOMOD_SPAM_THRESHOLD  = 5    # messages within window
AUTOMOD_SPAM_WINDOW     = 5    # seconds
AUTOMOD_MENTION_LIMIT   = 5    # mentions per message
AUTOMOD_RAID_JOIN_COUNT = 10   # joins within window to trigger raid mode
AUTOMOD_RAID_WINDOW     = 30   # seconds

# Strike expiry default
DEFAULT_STRIKE_EXPIRY_DAYS = 90

# Brand colors
COLOR_SUCCESS = 0x2ECC71
COLOR_ERROR   = 0xE74C3C
COLOR_WARNING = 0xF39C12
COLOR_INFO    = 0x3498DB
COLOR_NEUTRAL = 0x2C2F33
COLOR_MOD     = 0x9B59B6
COLOR_LOG     = 0x5865F2

# ─────────────────────────────────────────────────────────────────────────────
# IN-MEMORY STATE (non-persistent, resets on restart — intentional)
# ─────────────────────────────────────────────────────────────────────────────
# spam tracking:  guild_id -> user_id -> [timestamps]
_spam_tracker: dict[int, dict[int, list]] = defaultdict(lambda: defaultdict(list))
# raid tracking:  guild_id -> [join timestamps]
_raid_tracker: dict[int, list] = defaultdict(list)
# raid mode active: guild_id -> bool
_raid_mode: dict[int, bool] = defaultdict(bool)

# ─────────────────────────────────────────────────────────────────────────────
# DATABASE
# ─────────────────────────────────────────────────────────────────────────────
def get_db():
    conn = sqlite3.connect(DATABASE_PATH)
    conn.row_factory = sqlite3.Row
    return conn

def _safe_migrate(c, table: str, required: set):
    """Add missing columns to an existing table without data loss."""
    c.execute(f"PRAGMA table_info({table})")
    existing = {row[1] for row in c.fetchall()}
    missing = required - existing
    return missing  # caller decides what to do

def init_db():
    conn = get_db()
    c = conn.cursor()

    # ── guild_config ──────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS guild_config (
            guild_id                INTEGER PRIMARY KEY,
            mod_log_channel_id      INTEGER,
            appeals_channel_id      INTEGER,
            moderator_role_id       INTEGER,
            dm_on_action            INTEGER DEFAULT 1,
            appeals_enabled         INTEGER DEFAULT 1,
            setup_complete          INTEGER DEFAULT 0,
            log_joins               INTEGER DEFAULT 1,
            log_leaves              INTEGER DEFAULT 1,
            log_edits               INTEGER DEFAULT 1,
            log_deletes             INTEGER DEFAULT 1,
            log_roles               INTEGER DEFAULT 1,
            log_voice               INTEGER DEFAULT 1,
            event_log_channel_id    INTEGER,
            strike_expiry_days      INTEGER DEFAULT 90,
            admin_role_id           INTEGER
        )
    """)
    # migrate existing rows
    for col, default in [
        ("log_joins", 1), ("log_leaves", 1), ("log_edits", 1),
        ("log_deletes", 1), ("log_roles", 1), ("log_voice", 1),
        ("event_log_channel_id", "NULL"), ("strike_expiry_days", 90), ("admin_role_id", "NULL"),
    ]:
        try:
            c.execute(f"ALTER TABLE guild_config ADD COLUMN {col} INTEGER DEFAULT {default}")
        except Exception:
            pass

    # ── mod_cases ─────────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS mod_cases (
            case_id          TEXT PRIMARY KEY,
            guild_id         INTEGER NOT NULL,
            user_id          INTEGER NOT NULL,
            moderator_id     INTEGER NOT NULL,
            action_type      TEXT NOT NULL,
            reason           TEXT,
            duration_minutes INTEGER,
            timestamp        TEXT NOT NULL,
            expires_at       TEXT,
            active           INTEGER DEFAULT 1
        )
    """)
    try:
        c.execute("ALTER TABLE mod_cases ADD COLUMN expires_at TEXT")
    except Exception:
        pass

    # ── appeals ───────────────────────────────────────────────────────────────
    c.execute("PRAGMA table_info(appeals)")
    existing_cols = {row[1] for row in c.fetchall()}
    required_cols = {"appeal_id","case_id","guild_id","user_id","appeal_message",
                     "status","reviewed_by","reviewed_at","timestamp"}
    if existing_cols and not required_cols.issubset(existing_cols):
        c.execute("ALTER TABLE appeals RENAME TO appeals_backup")
        existing_cols = set()
    if not existing_cols:
        c.execute("""
            CREATE TABLE IF NOT EXISTS appeals (
                appeal_id     TEXT PRIMARY KEY,
                case_id       TEXT NOT NULL,
                guild_id      INTEGER NOT NULL,
                user_id       INTEGER NOT NULL,
                appeal_message TEXT NOT NULL,
                status        TEXT DEFAULT 'pending',
                reviewed_by   INTEGER,
                reviewed_at   TEXT,
                timestamp     TEXT NOT NULL
            )
        """)

    # ── notes ─────────────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS notes (
            note_id      TEXT PRIMARY KEY,
            guild_id     INTEGER NOT NULL,
            user_id      INTEGER NOT NULL,
            moderator_id INTEGER NOT NULL,
            content      TEXT NOT NULL,
            timestamp    TEXT NOT NULL
        )
    """)

    # ── automod_config ────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS automod_config (
            guild_id            INTEGER PRIMARY KEY,
            enabled             INTEGER DEFAULT 1,
            anti_spam           INTEGER DEFAULT 1,
            spam_threshold      INTEGER DEFAULT 5,
            spam_window         INTEGER DEFAULT 5,
            anti_invite         INTEGER DEFAULT 1,
            anti_mass_mention   INTEGER DEFAULT 1,
            mention_limit       INTEGER DEFAULT 5,
            anti_raid           INTEGER DEFAULT 1,
            raid_join_count     INTEGER DEFAULT 10,
            raid_join_window    INTEGER DEFAULT 30,
            word_filter         INTEGER DEFAULT 0,
            blocked_words       TEXT DEFAULT '[]',
            action_spam         TEXT DEFAULT 'timeout',
            action_invite       TEXT DEFAULT 'delete',
            action_mention      TEXT DEFAULT 'timeout',
            spam_timeout_mins   INTEGER DEFAULT 10,
            mention_timeout_mins INTEGER DEFAULT 10
        )
    """)

    # ── punishment_ladder ─────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS punishment_ladder (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            guild_id     INTEGER NOT NULL,
            threshold    INTEGER NOT NULL,
            action       TEXT NOT NULL,
            duration_min INTEGER DEFAULT 0,
            UNIQUE(guild_id, threshold)
        )
    """)

    # ── temp_bans ─────────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS temp_bans (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            guild_id     INTEGER NOT NULL,
            user_id      INTEGER NOT NULL,
            expires_at   TEXT NOT NULL,
            case_id      TEXT NOT NULL,
            processed    INTEGER DEFAULT 0
        )
    """)

    # ── reports ───────────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS reports (
            report_id    TEXT PRIMARY KEY,
            guild_id     INTEGER NOT NULL,
            reporter_id  INTEGER NOT NULL,
            target_id    INTEGER NOT NULL,
            reason       TEXT NOT NULL,
            status       TEXT DEFAULT 'open',
            resolved_by  INTEGER,
            resolved_at  TEXT,
            timestamp    TEXT NOT NULL
        )
    """)

    # ── tags ──────────────────────────────────────────────────────────────────
    c.execute("""
        CREATE TABLE IF NOT EXISTS tags (
            tag_id       TEXT PRIMARY KEY,
            guild_id     INTEGER NOT NULL,
            name         TEXT NOT NULL,
            content      TEXT NOT NULL,
            creator_id   INTEGER NOT NULL,
            uses         INTEGER DEFAULT 0,
            timestamp    TEXT NOT NULL,
            UNIQUE(guild_id, name)
        )
    """)

    conn.commit()
    conn.close()

# ─────────────────────────────────────────────────────────────────────────────
# DB HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def now_iso() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def now_dt() -> datetime.datetime:
    return datetime.datetime.now(datetime.timezone.utc)

def get_guild_config(guild_id: int) -> dict:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM guild_config WHERE guild_id = ?", (guild_id,))
    row = c.fetchone()
    conn.close()
    if row:
        return dict(row)
    return {
        "guild_id": guild_id,
        "mod_log_channel_id": None, "appeals_channel_id": None,
        "moderator_role_id": None, "dm_on_action": DEFAULT_DM_ON_ACTION,
        "appeals_enabled": DEFAULT_APPEALS_ENABLED, "setup_complete": 0,
        "log_joins": 1, "log_leaves": 1, "log_edits": 1, "log_deletes": 1,
        "log_roles": 1, "log_voice": 1, "event_log_channel_id": None,
        "strike_expiry_days": DEFAULT_STRIKE_EXPIRY_DAYS,
        "admin_role_id": None,
    }

def upsert_guild_config(guild_id: int, **kwargs):
    conn = get_db()
    c = conn.cursor()
    c.execute("INSERT OR IGNORE INTO guild_config (guild_id) VALUES (?)", (guild_id,))
    for key, value in kwargs.items():
        c.execute(f"UPDATE guild_config SET {key} = ? WHERE guild_id = ?", (value, guild_id))
    conn.commit()
    conn.close()

def get_automod_config(guild_id: int) -> dict:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM automod_config WHERE guild_id = ?", (guild_id,))
    row = c.fetchone()
    conn.close()
    if row:
        d = dict(row)
        d["blocked_words"] = json.loads(d.get("blocked_words") or "[]")
        return d
    return {
        "guild_id": guild_id, "enabled": 1,
        "anti_spam": 1, "spam_threshold": AUTOMOD_SPAM_THRESHOLD,
        "spam_window": AUTOMOD_SPAM_WINDOW, "anti_invite": 1,
        "anti_mass_mention": 1, "mention_limit": AUTOMOD_MENTION_LIMIT,
        "anti_raid": 1, "raid_join_count": AUTOMOD_RAID_JOIN_COUNT,
        "raid_join_window": AUTOMOD_RAID_WINDOW, "word_filter": 0,
        "blocked_words": [], "action_spam": "timeout",
        "action_invite": "delete", "action_mention": "timeout",
        "spam_timeout_mins": 10, "mention_timeout_mins": 10,
    }

def upsert_automod_config(guild_id: int, **kwargs):
    conn = get_db()
    c = conn.cursor()
    c.execute("INSERT OR IGNORE INTO automod_config (guild_id) VALUES (?)", (guild_id,))
    for key, value in kwargs.items():
        if key == "blocked_words":
            value = json.dumps(value)
        c.execute(f"UPDATE automod_config SET {key} = ? WHERE guild_id = ?", (value, guild_id))
    conn.commit()
    conn.close()

def create_case(guild_id: int, user_id: int, moderator_id: int, action_type: str,
                reason: str = None, duration_minutes: int = None,
                expires_at: str = None) -> str:
    case_id = str(uuid.uuid4())[:8].upper()
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO mod_cases
            (case_id, guild_id, user_id, moderator_id, action_type, reason, duration_minutes, timestamp, expires_at)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (case_id, guild_id, user_id, moderator_id, action_type, reason,
          duration_minutes, now_iso(), expires_at))
    conn.commit()
    conn.close()
    return case_id

def get_case(case_id: str, guild_id: int) -> Optional[dict]:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM mod_cases WHERE case_id = ? AND guild_id = ?", (case_id, guild_id))
    row = c.fetchone()
    conn.close()
    return dict(row) if row else None

def get_user_cases(user_id: int, guild_id: int, active_only: bool = False) -> list:
    conn = get_db()
    c = conn.cursor()
    if active_only:
        cutoff = (now_dt() - datetime.timedelta(days=DEFAULT_STRIKE_EXPIRY_DAYS)).isoformat()
        c.execute("""
            SELECT * FROM mod_cases
            WHERE user_id=? AND guild_id=? AND timestamp > ?
            ORDER BY timestamp DESC
        """, (user_id, guild_id, cutoff))
    else:
        c.execute("SELECT * FROM mod_cases WHERE user_id=? AND guild_id=? ORDER BY timestamp DESC",
                  (user_id, guild_id))
    rows = c.fetchall()
    conn.close()
    return [dict(r) for r in rows]

def expunge_case(case_id: str, guild_id: int):
    conn = get_db()
    c = conn.cursor()
    c.execute("DELETE FROM mod_cases WHERE case_id=? AND guild_id=?", (case_id, guild_id))
    conn.commit()
    conn.close()

def count_active_strikes(user_id: int, guild_id: int) -> int:
    config = get_guild_config(guild_id)
    expiry_days = config.get("strike_expiry_days", DEFAULT_STRIKE_EXPIRY_DAYS)
    cutoff = (now_dt() - datetime.timedelta(days=expiry_days)).isoformat()
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        SELECT COUNT(*) FROM mod_cases
        WHERE user_id=? AND guild_id=? AND action_type='warn' AND timestamp > ?
    """, (user_id, guild_id, cutoff))
    count = c.fetchone()[0]
    conn.close()
    return count

def get_ladder(guild_id: int) -> list:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM punishment_ladder WHERE guild_id=? ORDER BY threshold ASC", (guild_id,))
    rows = c.fetchall()
    conn.close()
    return [dict(r) for r in rows]

def save_appeal(appeal_id, case_id, guild_id, user_id, appeal_message):
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO appeals (appeal_id, case_id, guild_id, user_id, appeal_message, timestamp)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (appeal_id, case_id, guild_id, user_id, appeal_message, now_iso()))
    conn.commit()
    conn.close()

def update_appeal_status(appeal_id, status, reviewed_by):
    conn = get_db()
    c = conn.cursor()
    c.execute("UPDATE appeals SET status=?, reviewed_by=?, reviewed_at=? WHERE appeal_id=?",
              (status, reviewed_by, now_iso(), appeal_id))
    conn.commit()
    conn.close()

def get_appeal(appeal_id):
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM appeals WHERE appeal_id=?", (appeal_id,))
    row = c.fetchone()
    conn.close()
    return dict(row) if row else None

def add_note(guild_id, user_id, moderator_id, content) -> str:
    note_id = str(uuid.uuid4())[:8].upper()
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO notes (note_id, guild_id, user_id, moderator_id, content, timestamp)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (note_id, guild_id, user_id, moderator_id, content, now_iso()))
    conn.commit()
    conn.close()
    return note_id

def get_notes(user_id, guild_id) -> list:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM notes WHERE user_id=? AND guild_id=? ORDER BY timestamp DESC",
              (user_id, guild_id))
    rows = c.fetchall()
    conn.close()
    return [dict(r) for r in rows]

def delete_note(note_id, guild_id):
    conn = get_db()
    c = conn.cursor()
    c.execute("DELETE FROM notes WHERE note_id=? AND guild_id=?", (note_id, guild_id))
    conn.commit()
    conn.close()

def add_temp_ban(guild_id, user_id, expires_at_str, case_id):
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO temp_bans (guild_id, user_id, expires_at, case_id)
        VALUES (?, ?, ?, ?)
    """, (guild_id, user_id, expires_at_str, case_id))
    conn.commit()
    conn.close()

def get_pending_temp_bans() -> list:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM temp_bans WHERE processed=0")
    rows = c.fetchall()
    conn.close()
    return [dict(r) for r in rows]

def mark_temp_ban_processed(ban_id):
    conn = get_db()
    c = conn.cursor()
    c.execute("UPDATE temp_bans SET processed=1 WHERE id=?", (ban_id,))
    conn.commit()
    conn.close()

def create_report(guild_id, reporter_id, target_id, reason) -> str:
    report_id = str(uuid.uuid4())[:8].upper()
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO reports (report_id, guild_id, reporter_id, target_id, reason, timestamp)
        VALUES (?, ?, ?, ?, ?, ?)
    """, (report_id, guild_id, reporter_id, target_id, reason, now_iso()))
    conn.commit()
    conn.close()
    return report_id

def resolve_report(report_id, resolved_by):
    conn = get_db()
    c = conn.cursor()
    c.execute("UPDATE reports SET status='resolved', resolved_by=?, resolved_at=? WHERE report_id=?",
              (resolved_by, now_iso(), report_id))
    conn.commit()
    conn.close()

def get_tag(guild_id, name) -> Optional[dict]:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM tags WHERE guild_id=? AND name=?", (guild_id, name.lower()))
    row = c.fetchone()
    conn.close()
    return dict(row) if row else None

def create_tag(guild_id, name, content, creator_id) -> bool:
    tag_id = str(uuid.uuid4())[:8].upper()
    conn = get_db()
    c = conn.cursor()
    try:
        c.execute("""
            INSERT INTO tags (tag_id, guild_id, name, content, creator_id, timestamp)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (tag_id, guild_id, name.lower(), content, creator_id, now_iso()))
        conn.commit()
        return True
    except sqlite3.IntegrityError:
        return False
    finally:
        conn.close()

def delete_tag(guild_id, name):
    conn = get_db()
    c = conn.cursor()
    c.execute("DELETE FROM tags WHERE guild_id=? AND name=?", (guild_id, name.lower()))
    affected = c.rowcount
    conn.commit()
    conn.close()
    return affected > 0

def increment_tag_uses(guild_id, name):
    conn = get_db()
    c = conn.cursor()
    c.execute("UPDATE tags SET uses=uses+1 WHERE guild_id=? AND name=?", (guild_id, name.lower()))
    conn.commit()
    conn.close()

def list_tags(guild_id) -> list:
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT * FROM tags WHERE guild_id=? ORDER BY name ASC", (guild_id,))
    rows = c.fetchall()
    conn.close()
    return [dict(r) for r in rows]

# ─────────────────────────────────────────────────────────────────────────────
# BOT INSTANCE
# ─────────────────────────────────────────────────────────────────────────────
intents = discord.Intents.all()
bot = commands.Bot(command_prefix=".", intents=intents)

# ─────────────────────────────────────────────────────────────────────────────
# PERMISSION HELPERS
# ─────────────────────────────────────────────────────────────────────────────
# Bot owner ID — bypasses all permission checks in every server
BOT_OWNER_ID = 1085959607484153966

def is_bot_owner(interaction: discord.Interaction) -> bool:
    return interaction.user.id == BOT_OWNER_ID

def is_moderator(interaction: discord.Interaction) -> bool:
    if interaction.user.guild_permissions.administrator:
        return True
    config = get_guild_config(interaction.guild_id)
    mod_role_id = config.get("moderator_role_id")
    if mod_role_id:
        role = interaction.guild.get_role(int(mod_role_id))
        if role and role in interaction.user.roles:
            return True
    return any([
        interaction.user.guild_permissions.ban_members,
        interaction.user.guild_permissions.kick_members,
        interaction.user.guild_permissions.moderate_members,
        interaction.user.guild_permissions.manage_messages,
    ])

def is_admin(interaction: discord.Interaction) -> bool:
    """True if the user holds the configured Admin Role or has Discord Administrator permission."""
    if interaction.user.guild_permissions.administrator:
        return True
    config = get_guild_config(interaction.guild_id)
    admin_role_id = config.get("admin_role_id")
    if admin_role_id:
        role = interaction.guild.get_role(int(admin_role_id))
        if role and role in interaction.user.roles:
            return True
    return False


def setup_required(interaction: discord.Interaction) -> bool:
    """Returns True if setup has been completed for this guild, False otherwise."""
    config = get_guild_config(interaction.guild_id)
    return bool(config.get("setup_complete", 0))

async def enforce_setup(interaction: discord.Interaction) -> bool:
    """
    Call at the top of every operational command.
    Sends an ephemeral error and returns False if setup is not complete.
    Returns True if the command should proceed.
    """
    if not setup_required(interaction):
        embed = discord.Embed(
            title="Sentinel Is Not Configured",
            description=(
                "Sentinel has not been set up for this server yet.\n\n"
                "A server administrator must run **/setup** and complete the configuration "
                "wizard before any commands can be used.\n\n"
                "This restriction exists to ensure moderation channels, roles, and settings "
                "are properly established before any actions are taken."
            ),
            color=COLOR_ERROR
        )
        embed.set_footer(text=f"{BOT_NAME} • Run /setup to get started")
        await interaction.response.send_message(embed=embed, ephemeral=True)
        return False
    return True

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING HELPERS
# ─────────────────────────────────────────────────────────────────────────────
async def send_mod_log(guild: discord.Guild, embed: discord.Embed):
    config = get_guild_config(guild.id)
    ch_id = config.get("mod_log_channel_id")
    if ch_id:
        ch = guild.get_channel(int(ch_id))
        if ch:
            try:
                await ch.send(embed=embed)
            except discord.Forbidden:
                pass

async def send_event_log(guild: discord.Guild, embed: discord.Embed):
    config = get_guild_config(guild.id)
    ch_id = config.get("event_log_channel_id") or config.get("mod_log_channel_id")
    if ch_id:
        ch = guild.get_channel(int(ch_id))
        if ch:
            try:
                await ch.send(embed=embed)
            except discord.Forbidden:
                pass

async def dm_user_action(user: discord.User, action_type: str, guild_name: str,
                          reason: str, case_id: str, appeals_enabled: bool,
                          guild_id: int, guild: discord.Guild):
    embed = discord.Embed(
        title=f"Moderation Action — {action_type.upper()}",
        color=COLOR_WARNING,
        timestamp=now_dt()
    )
    embed.add_field(name="Server", value=guild_name, inline=True)
    embed.add_field(name="Action", value=action_type.title(), inline=True)
    embed.add_field(name="Case ID", value=f"`{case_id}`", inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    view = None
    if appeals_enabled and action_type.lower() in ("ban","tempban","softban","kick","timeout","warn"):
        view = AppealButton(case_id=case_id, guild_id=guild_id, guild=guild)
    try:
        await user.send(embed=embed, view=view)
    except discord.Forbidden:
        pass

def build_case_embed(case: dict, guild: discord.Guild) -> discord.Embed:
    colors = {"ban": COLOR_ERROR, "tempban": COLOR_ERROR, "softban": COLOR_ERROR,
               "kick": COLOR_WARNING, "timeout": COLOR_WARNING, "untimeout": COLOR_SUCCESS,
               "warn": COLOR_MOD, "unban": COLOR_SUCCESS, "note": COLOR_INFO}
    color = colors.get(case["action_type"].lower(), COLOR_NEUTRAL)
    embed = discord.Embed(
        title=f"Case #{case['case_id']} — {case['action_type'].upper()}",
        color=color,
        timestamp=datetime.datetime.fromisoformat(case["timestamp"])
    )
    embed.add_field(name="User", value=f"<@{case['user_id']}> ({case['user_id']})", inline=True)
    embed.add_field(name="Moderator", value=f"<@{case['moderator_id']}>", inline=True)
    embed.add_field(name="Action", value=case["action_type"].title(), inline=True)
    embed.add_field(name="Reason", value=case["reason"] or "No reason provided.", inline=False)
    if case.get("duration_minutes"):
        embed.add_field(name="Duration", value=f"{case['duration_minutes']} minutes", inline=True)
    if case.get("expires_at"):
        embed.add_field(name="Expires", value=case["expires_at"][:19].replace("T", " ") + " UTC", inline=True)
    embed.set_footer(text=f"{BOT_NAME} • Case ID: {case['case_id']}")
    return embed

# ─────────────────────────────────────────────────────────────────────────────
# PUNISHMENT LADDER EXECUTOR
# ─────────────────────────────────────────────────────────────────────────────
async def run_ladder(guild: discord.Guild, member: discord.Member, strike_count: int):
    ladder = get_ladder(guild.id)
    if not ladder:
        return
    action_row = None
    for row in ladder:
        if strike_count >= row["threshold"]:
            action_row = row
    if not action_row:
        return
    action = action_row["action"]
    dur = action_row.get("duration_min", 0) or 0
    reason = f"[Auto-Escalation] {strike_count} active strikes triggered threshold {action_row['threshold']}"
    case_id = create_case(guild.id, member.id, bot.user.id, f"auto-{action}", reason, dur or None)
    try:
        if action == "kick":
            await member.kick(reason=reason)
        elif action == "ban":
            await guild.ban(member, reason=reason, delete_message_days=0)
        elif action == "timeout" and dur:
            await member.timeout(datetime.timedelta(minutes=dur), reason=reason)
    except Exception:
        pass
    embed = discord.Embed(
        title=f"Case #{case_id} — AUTO-ESCALATION ({action.upper()})",
        color=COLOR_ERROR,
        timestamp=now_dt()
    )
    embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
    embed.add_field(name="Active Strikes", value=str(strike_count), inline=True)
    embed.add_field(name="Action", value=action.title(), inline=True)
    embed.add_field(name="Reason", value=reason, inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(guild, embed)

# ─────────────────────────────────────────────────────────────────────────────
# AUTOMOD ENGINE
# ─────────────────────────────────────────────────────────────────────────────
INVITE_RE = re.compile(r"(discord\.gg/|discord\.com/invite/|discordapp\.com/invite/)\S+", re.IGNORECASE)

async def automod_process(message: discord.Message):
    if not message.guild or message.author.bot:
        return
    if message.author.guild_permissions.administrator or message.author.guild_permissions.manage_messages:
        return
    # Do not run automod until the server has completed setup
    guild_cfg = get_guild_config(message.guild.id)
    if not guild_cfg.get("setup_complete", 0):
        return

    cfg = get_automod_config(message.guild.id)
    if not cfg.get("enabled"):
        return

    guild = message.guild
    member = message.author

    # ── Word filter ───────────────────────────────────────────────────────────
    if cfg.get("word_filter"):
        blocked = cfg.get("blocked_words", [])
        content_lower = message.content.lower()
        for word in blocked:
            if word.lower() in content_lower:
                try:
                    await message.delete()
                except Exception:
                    pass
                case_id = create_case(guild.id, member.id, bot.user.id, "automod-wordfilter",
                                      f"Blocked word detected: {word}")
                embed = discord.Embed(title=f"Case #{case_id} — AUTOMOD: WORD FILTER",
                                      color=COLOR_MOD, timestamp=now_dt())
                embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
                embed.add_field(name="Trigger", value=f"Blocked word: `{word}`", inline=True)
                embed.add_field(name="Channel", value=message.channel.mention, inline=True)
                embed.set_footer(text=BOT_NAME)
                await send_mod_log(guild, embed)
                return

    # ── Invite filter ─────────────────────────────────────────────────────────
    if cfg.get("anti_invite") and INVITE_RE.search(message.content):
        try:
            await message.delete()
        except Exception:
            pass
        action = cfg.get("action_invite", "delete")
        case_id = create_case(guild.id, member.id, bot.user.id, "automod-invite",
                              "Unauthorized invite link posted")
        if action == "timeout":
            try:
                await member.timeout(datetime.timedelta(minutes=10), reason="[Automod] Invite link")
            except Exception:
                pass
        elif action == "warn":
            pass  # case already logged
        embed = discord.Embed(title=f"Case #{case_id} — AUTOMOD: INVITE LINK",
                              color=COLOR_WARNING, timestamp=now_dt())
        embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
        embed.add_field(name="Channel", value=message.channel.mention, inline=True)
        embed.set_footer(text=BOT_NAME)
        await send_mod_log(guild, embed)
        return

    # ── Mass mention ──────────────────────────────────────────────────────────
    if cfg.get("anti_mass_mention"):
        mention_count = len(message.mentions) + len(message.role_mentions)
        limit = cfg.get("mention_limit", AUTOMOD_MENTION_LIMIT)
        if mention_count >= limit:
            try:
                await message.delete()
            except Exception:
                pass
            dur = cfg.get("mention_timeout_mins", 10)
            try:
                await member.timeout(datetime.timedelta(minutes=dur),
                                     reason=f"[Automod] Mass mention ({mention_count} mentions)")
            except Exception:
                pass
            case_id = create_case(guild.id, member.id, bot.user.id, "automod-massmention",
                                  f"Mass mention: {mention_count} targets", dur)
            embed = discord.Embed(title=f"Case #{case_id} — AUTOMOD: MASS MENTION",
                                  color=COLOR_ERROR, timestamp=now_dt())
            embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
            embed.add_field(name="Mentions", value=str(mention_count), inline=True)
            embed.add_field(name="Timeout", value=f"{dur} minutes", inline=True)
            embed.set_footer(text=BOT_NAME)
            await send_mod_log(guild, embed)
            return

    # ── Spam detection ────────────────────────────────────────────────────────
    if cfg.get("anti_spam"):
        threshold = cfg.get("spam_threshold", AUTOMOD_SPAM_THRESHOLD)
        window = cfg.get("spam_window", AUTOMOD_SPAM_WINDOW)
        now_ts = now_dt().timestamp()
        tracker = _spam_tracker[guild.id][member.id]
        tracker.append(now_ts)
        # Prune old entries
        _spam_tracker[guild.id][member.id] = [t for t in tracker if now_ts - t <= window]
        if len(_spam_tracker[guild.id][member.id]) >= threshold:
            _spam_tracker[guild.id][member.id] = []
            action = cfg.get("action_spam", "timeout")
            dur = cfg.get("spam_timeout_mins", 10)
            try:
                await message.delete()
            except Exception:
                pass
            if action == "timeout":
                try:
                    await member.timeout(datetime.timedelta(minutes=dur),
                                         reason="[Automod] Spam detected")
                except Exception:
                    pass
            elif action == "kick":
                try:
                    await member.kick(reason="[Automod] Spam detected")
                except Exception:
                    pass
            case_id = create_case(guild.id, member.id, bot.user.id, "automod-spam",
                                  f"Spam: {threshold} messages in {window}s", dur if action == "timeout" else None)
            embed = discord.Embed(title=f"Case #{case_id} — AUTOMOD: SPAM",
                                  color=COLOR_WARNING, timestamp=now_dt())
            embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
            embed.add_field(name="Action", value=action.title(), inline=True)
            if action == "timeout":
                embed.add_field(name="Duration", value=f"{dur} minutes", inline=True)
            embed.set_footer(text=BOT_NAME)
            await send_mod_log(guild, embed)

# ─────────────────────────────────────────────────────────────────────────────
# APPEAL VIEWS & MODALS
# ─────────────────────────────────────────────────────────────────────────────
class AppealModal(discord.ui.Modal, title="Submit an Appeal"):
    def __init__(self, case_id: str, guild_id: int, guild: discord.Guild):
        super().__init__()
        self.case_id = case_id
        self.guild_id = guild_id
        self.guild = guild

    appeal_message = discord.ui.TextInput(
        label="Appeal Message",
        style=discord.TextStyle.paragraph,
        placeholder="Explain why you believe this action should be reversed...",
        min_length=20, max_length=1000
    )

    async def on_submit(self, interaction: discord.Interaction):
        appeal_id = str(uuid.uuid4())[:8].upper()
        save_appeal(appeal_id, self.case_id, self.guild_id,
                    interaction.user.id, self.appeal_message.value)
        config = get_guild_config(self.guild_id)
        ch_id = config.get("appeals_channel_id")
        embed = discord.Embed(title=f"New Appeal — #{appeal_id}", color=COLOR_INFO, timestamp=now_dt())
        embed.add_field(name="Appeal ID", value=f"`{appeal_id}`", inline=True)
        embed.add_field(name="Case ID", value=f"`{self.case_id}`", inline=True)
        embed.add_field(name="User", value=f"<@{interaction.user.id}> ({interaction.user.id})", inline=False)
        embed.add_field(name="Message", value=self.appeal_message.value, inline=False)
        embed.set_footer(text=f"{BOT_NAME} • Pending Review")
        view = AppealReviewView(appeal_id, self.case_id, self.guild_id, interaction.user.id)
        posted = False
        if ch_id:
            ch = self.guild.get_channel(int(ch_id))
            if ch:
                try:
                    await ch.send(embed=embed, view=view)
                    posted = True
                except discord.Forbidden:
                    pass
        if not posted:
            for ch in self.guild.text_channels:
                try:
                    await ch.send(embed=embed, view=view)
                    break
                except discord.Forbidden:
                    continue
        confirm = discord.Embed(
            title="Appeal Submitted",
            description=f"Your appeal `{appeal_id}` for Case `{self.case_id}` is pending staff review. You will be notified of the decision via DM.",
            color=COLOR_SUCCESS
        )
        confirm.set_footer(text=BOT_NAME)
        await interaction.response.send_message(embed=confirm, ephemeral=True)

class AppealButton(discord.ui.View):
    def __init__(self, case_id, guild_id, guild):
        super().__init__(timeout=None)
        self.case_id = case_id
        self.guild_id = guild_id
        self.guild = guild

    @discord.ui.button(label="Appeal This Action", style=discord.ButtonStyle.secondary)
    async def appeal_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_modal(AppealModal(self.case_id, self.guild_id, self.guild))

class AppealReviewView(discord.ui.View):
    def __init__(self, appeal_id, case_id, guild_id, appellant_id):
        super().__init__(timeout=None)
        self.appeal_id = appeal_id
        self.case_id = case_id
        self.guild_id = guild_id
        self.appellant_id = appellant_id

    @discord.ui.button(label="Accept", style=discord.ButtonStyle.success)
    async def accept(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_moderator(interaction):
            await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
            return
        appeal = get_appeal(self.appeal_id)
        if not appeal or appeal["status"] != "pending":
            await interaction.response.send_message("This appeal has already been reviewed.", ephemeral=True)
            return
        update_appeal_status(self.appeal_id, "accepted", interaction.user.id)
        for child in self.children:
            child.disabled = True
        await interaction.message.edit(view=self)
        case = get_case(self.case_id, self.guild_id)
        unbanned = False
        if case and case["action_type"].lower() in ("ban","softban","tempban"):
            try:
                user = await bot.fetch_user(self.appellant_id)
                await interaction.guild.unban(user, reason=f"Appeal #{self.appeal_id} accepted")
                unbanned = True
            except Exception:
                pass
        # Remove the case from history since the appeal was accepted
        expunge_case(self.case_id, self.guild_id)
        embed = discord.Embed(title=f"Appeal #{self.appeal_id} — ACCEPTED", color=COLOR_SUCCESS, timestamp=now_dt())
        embed.add_field(name="Reviewed By", value=interaction.user.mention, inline=True)
        embed.add_field(name="Case Removed", value=f"Case `{self.case_id}` has been expunged from the user's record.", inline=False)
        if unbanned:
            embed.add_field(name="Ban Reversed", value="The associated ban has been lifted.", inline=False)
        embed.set_footer(text=BOT_NAME)
        await interaction.response.send_message(embed=embed)
        try:
            user = await bot.fetch_user(self.appellant_id)
            dm = discord.Embed(
                title=f"Appeal Accepted — Case #{self.case_id}",
                description=f"Your appeal `{self.appeal_id}` has been **accepted** by staff. The case has been removed from your record.",
                color=COLOR_SUCCESS
            )
            if unbanned:
                dm.add_field(name="Ban Lifted", value="Your ban has been removed. You may rejoin the server.", inline=False)
            dm.set_footer(text=BOT_NAME)
            await user.send(embed=dm)
        except Exception:
            pass

    @discord.ui.button(label="Deny", style=discord.ButtonStyle.danger)
    async def deny(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_moderator(interaction):
            await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
            return
        appeal = get_appeal(self.appeal_id)
        if not appeal or appeal["status"] != "pending":
            await interaction.response.send_message("This appeal has already been reviewed.", ephemeral=True)
            return
        update_appeal_status(self.appeal_id, "denied", interaction.user.id)
        for child in self.children:
            child.disabled = True
        await interaction.message.edit(view=self)
        embed = discord.Embed(title=f"Appeal #{self.appeal_id} — DENIED", color=COLOR_ERROR, timestamp=now_dt())
        embed.add_field(name="Reviewed By", value=interaction.user.mention, inline=True)
        embed.set_footer(text=BOT_NAME)
        await interaction.response.send_message(embed=embed)
        try:
            user = await bot.fetch_user(self.appellant_id)
            dm = discord.Embed(
                title=f"Appeal Decision — Case #{self.case_id}",
                description=f"Your appeal `{self.appeal_id}` has been **denied**. The moderation action remains in effect.",
                color=COLOR_ERROR
            )
            dm.set_footer(text=BOT_NAME)
            await user.send(embed=dm)
        except Exception:
            pass

class ReportReviewView(discord.ui.View):
    def __init__(self, report_id):
        super().__init__(timeout=None)
        self.report_id = report_id

    @discord.ui.button(label="Mark Resolved", style=discord.ButtonStyle.success)
    async def resolve(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_moderator(interaction):
            await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
            return
        resolve_report(self.report_id, interaction.user.id)
        for child in self.children:
            child.disabled = True
        await interaction.message.edit(view=self)
        await interaction.response.send_message(f"Report `{self.report_id}` marked as resolved.", ephemeral=True)

# ─────────────────────────────────────────────────────────────────────────────
# SETUP WIZARD
# ─────────────────────────────────────────────────────────────────────────────
# ─────────────────────────────────────────────────────────────────────────────
# SETUP — Sequential single-select views, one message per step
# ─────────────────────────────────────────────────────────────────────────────

class SetupRoleView(discord.ui.View):
    """Step 1 — pick Moderator Role."""
    def __init__(self, guild_id: int):
        super().__init__(timeout=120)
        self.guild_id = guild_id

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="Select Moderator Role", min_values=1, max_values=1)
    async def pick_mod_role(self, interaction: discord.Interaction, select: discord.ui.Select):
        upsert_guild_config(self.guild_id, moderator_role_id=select.values[0].id)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content=f"✅ Moderator role set to {select.values[0].mention}.", view=self
        )
        await interaction.followup.send(
            content="**Step 2 of 5** — Select your **Admin Role** (has access to config commands):",
            view=SetupAdminRoleView(self.guild_id),
            ephemeral=True
        )

class SetupAdminRoleView(discord.ui.View):
    """Step 2 — pick Admin Role."""
    def __init__(self, guild_id: int):
        super().__init__(timeout=120)
        self.guild_id = guild_id

    @discord.ui.select(cls=discord.ui.RoleSelect, placeholder="Select Admin Role", min_values=1, max_values=1)
    async def pick_admin_role(self, interaction: discord.Interaction, select: discord.ui.Select):
        upsert_guild_config(self.guild_id, admin_role_id=select.values[0].id)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content=f"✅ Admin role set to {select.values[0].mention}.", view=self
        )
        await interaction.followup.send(
            content="**Step 3 of 5** — Select your **Mod Log channel** (where moderation actions are posted):",
            view=SetupModLogView(self.guild_id),
            ephemeral=True
        )

class SetupModLogView(discord.ui.View):
    """Step 3 — pick mod log channel."""
    def __init__(self, guild_id: int):
        super().__init__(timeout=120)
        self.guild_id = guild_id

    @discord.ui.select(cls=discord.ui.ChannelSelect, placeholder="Select Mod Log Channel",
                       channel_types=[discord.ChannelType.text], min_values=1, max_values=1)
    async def pick_modlog(self, interaction: discord.Interaction, select: discord.ui.Select):
        upsert_guild_config(self.guild_id, mod_log_channel_id=select.values[0].id)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content=f"✅ Mod log channel set to {select.values[0].mention}.", view=self
        )
        await interaction.followup.send(
            content="**Step 4 of 5** — Select your **Appeals channel** (where appeal submissions are sent):",
            view=SetupAppealsView(self.guild_id),
            ephemeral=True
        )

class SetupAppealsView(discord.ui.View):
    """Step 4 — pick appeals channel."""
    def __init__(self, guild_id: int):
        super().__init__(timeout=120)
        self.guild_id = guild_id

    @discord.ui.select(cls=discord.ui.ChannelSelect, placeholder="Select Appeals Channel",
                       channel_types=[discord.ChannelType.text], min_values=1, max_values=1)
    async def pick_appeals(self, interaction: discord.Interaction, select: discord.ui.Select):
        upsert_guild_config(self.guild_id, appeals_channel_id=select.values[0].id)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content=f"✅ Appeals channel set to {select.values[0].mention}.", view=self
        )
        await interaction.followup.send(
            content="**Step 5 of 5** — Select your **Event Log channel** (joins, leaves, edits, deletes, voice):",
            view=SetupEventLogView(self.guild_id),
            ephemeral=True
        )

class SetupEventLogView(discord.ui.View):
    """Step 5 — pick event log channel."""
    def __init__(self, guild_id: int):
        super().__init__(timeout=120)
        self.guild_id = guild_id

    @discord.ui.select(cls=discord.ui.ChannelSelect, placeholder="Select Event Log Channel",
                       channel_types=[discord.ChannelType.text], min_values=1, max_values=1)
    async def pick_eventlog(self, interaction: discord.Interaction, select: discord.ui.Select):
        upsert_guild_config(self.guild_id, event_log_channel_id=select.values[0].id, setup_complete=1)
        for child in self.children:
            child.disabled = True
        await interaction.response.edit_message(
            content=f"✅ Event log channel set to {select.values[0].mention}.", view=self
        )
        cfg = get_guild_config(self.guild_id)
        embed = discord.Embed(
            title="✅ Sentinel Setup Complete",
            description="All settings have been saved. Sentinel is now active on this server.",
            color=COLOR_SUCCESS,
            timestamp=now_dt()
        )
        embed.add_field(name="Moderator Role",
                        value=f"<@&{cfg['moderator_role_id']}>" if cfg.get("moderator_role_id") else "_Not set_", inline=True)
        embed.add_field(name="Admin Role",
                        value=f"<@&{cfg['admin_role_id']}>" if cfg.get("admin_role_id") else "_Not set_", inline=True)
        embed.add_field(name="Mod Log", value=f"<#{cfg['mod_log_channel_id']}>" if cfg.get("mod_log_channel_id") else "_Not set_", inline=True)
        embed.add_field(name="Appeals", value=f"<#{cfg['appeals_channel_id']}>" if cfg.get("appeals_channel_id") else "_Not set_", inline=True)
        embed.add_field(name="Event Log", value=f"<#{cfg['event_log_channel_id']}>" if cfg.get("event_log_channel_id") else "_Not set_", inline=True)
        embed.set_footer(text=BOT_NAME)
        await interaction.followup.send(embed=embed, ephemeral=True)

# ─────────────────────────────────────────────────────────────────────────────
# BOT EVENTS
# ─────────────────────────────────────────────────────────────────────────────
@bot.event
async def on_ready():
    init_db()
    await bot.tree.sync()
    check_temp_bans.start()
    print(f"[Sentinel] Online as {bot.user} (ID: {bot.user.id}) — {len(bot.guilds)} guild(s)")

@bot.event
async def on_guild_join(guild: discord.Guild):
    embed = discord.Embed(
        title=f"✅ Thank You for Adding {BOT_NAME}",
        description=(
            "Thank you for adding Averin Holdings' Sentinel to your server. Sentinel is an advanced moderation and governance bot "
            "developed to maintain order, enforce community standards, and provide staff teams with structured, reliable moderation tooling. "
            "It is designed for stability, transparency, and scalable server management across both private and public communities.\n\n"
            "**Setup Instructions:** Run `/setup` and follow the guided configuration process to initialize Sentinel."
        ),
        color=COLOR_INFO,
        timestamp=now_dt()
    )
    embed.add_field(name="📜 Ownership & Usage Notice", value=(
        "Averin Holdings' Sentinel is proprietary software and the exclusive property of Averin Holdings. "
        "Unauthorized copying, redistribution, reverse engineering, or misuse of Sentinel is strictly prohibited."
    ), inline=False)
    embed.add_field(name="📑 Terms of Service", value=(
        "• Sentinel is provided \"as-is\" without warranties of any kind.\n"
        "• Averin Holdings may update, modify, or terminate Sentinel at any time.\n"
        "• Server administrators are solely responsible for Sentinel's use within their server.\n"
        "• Sentinel may not be used for harassment, surveillance, data exploitation, or violations of Discord's ToS.\n"
        "• Abuse may result in immediate access revocation."
    ), inline=False)
    embed.add_field(name="🔒 Privacy Policy", value=(
        "Sentinel collects User IDs, server IDs, command usage, moderation logs, and performance metrics. "
        "Data is not sold or monetized and is retained only as long as operationally necessary."
    ), inline=False)
    embed.set_footer(text=f"{BOT_NAME} v{BOT_VERSION} • Every action creates a Case ID • Users may appeal via DM")
    for channel in guild.text_channels:
        perms = channel.permissions_for(guild.me)
        if perms.send_messages and perms.embed_links:
            try:
                await channel.send(embed=embed)
                return
            except discord.Forbidden:
                continue

@bot.event
async def on_message(message: discord.Message):
    if message.author.bot or not message.guild:
        return
    await automod_process(message)
    await bot.process_commands(message)

@bot.event
async def on_member_join(member: discord.Member):
    guild = member.guild
    config = get_guild_config(guild.id)

    # Anti-raid check
    automod_cfg = get_automod_config(guild.id)
    if automod_cfg.get("anti_raid"):
        now_ts = now_dt().timestamp()
        window = automod_cfg.get("raid_join_window", AUTOMOD_RAID_WINDOW)
        threshold = automod_cfg.get("raid_join_count", AUTOMOD_RAID_JOIN_COUNT)
        _raid_tracker[guild.id].append(now_ts)
        _raid_tracker[guild.id] = [t for t in _raid_tracker[guild.id] if now_ts - t <= window]
        if len(_raid_tracker[guild.id]) >= threshold and not _raid_mode[guild.id]:
            _raid_mode[guild.id] = True
            embed = discord.Embed(
                title="⚠️ RAID MODE ACTIVATED",
                description=f"**{len(_raid_tracker[guild.id])}** members joined within **{window}** seconds. Raid mode is now active. New joins will be logged.",
                color=COLOR_ERROR,
                timestamp=now_dt()
            )
            embed.set_footer(text=f"{BOT_NAME} • Use /automod raidmode off to deactivate")
            await send_mod_log(guild, embed)

    # Event log — member join
    if not config.get("log_joins", 1):
        return
    embed = discord.Embed(title="Member Joined", color=COLOR_SUCCESS, timestamp=now_dt())
    embed.set_author(name=str(member), icon_url=member.display_avatar.url)
    embed.add_field(name="User", value=f"{member.mention} ({member.id})", inline=True)
    account_age = now_dt() - member.created_at
    embed.add_field(name="Account Age", value=f"{account_age.days} days", inline=True)
    if account_age.days < 7:
        embed.add_field(name="⚠️ New Account", value="Account is less than 7 days old.", inline=False)
    embed.set_footer(text=f"Member #{guild.member_count}")
    await send_event_log(guild, embed)

@bot.event
async def on_member_remove(member: discord.Member):
    config = get_guild_config(member.guild.id)
    if not config.get("log_leaves", 1):
        return
    embed = discord.Embed(title="Member Left", color=COLOR_WARNING, timestamp=now_dt())
    embed.set_author(name=str(member), icon_url=member.display_avatar.url)
    embed.add_field(name="User", value=f"{member} ({member.id})", inline=True)
    roles = [r.mention for r in member.roles if r.name != "@everyone"]
    if roles:
        embed.add_field(name="Roles", value=" ".join(roles[:10]), inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_event_log(member.guild, embed)

@bot.event
async def on_message_edit(before: discord.Message, after: discord.Message):
    if before.author.bot or not before.guild:
        return
    if before.content == after.content:
        return
    config = get_guild_config(before.guild.id)
    if not config.get("log_edits", 1):
        return
    embed = discord.Embed(title="Message Edited", color=COLOR_INFO, timestamp=now_dt())
    embed.set_author(name=str(before.author), icon_url=before.author.display_avatar.url)
    embed.add_field(name="Channel", value=before.channel.mention, inline=True)
    embed.add_field(name="Author", value=before.author.mention, inline=True)
    embed.add_field(name="Before", value=before.content[:500] or "_empty_", inline=False)
    embed.add_field(name="After", value=after.content[:500] or "_empty_", inline=False)
    embed.add_field(name="Jump", value=f"[View Message]({after.jump_url})", inline=True)
    embed.set_footer(text=f"User ID: {before.author.id}")
    await send_event_log(before.guild, embed)

@bot.event
async def on_message_delete(message: discord.Message):
    if message.author.bot or not message.guild:
        return
    config = get_guild_config(message.guild.id)
    if not config.get("log_deletes", 1):
        return
    embed = discord.Embed(title="Message Deleted", color=COLOR_ERROR, timestamp=now_dt())
    embed.set_author(name=str(message.author), icon_url=message.author.display_avatar.url)
    embed.add_field(name="Channel", value=message.channel.mention, inline=True)
    embed.add_field(name="Author", value=message.author.mention, inline=True)
    embed.add_field(name="Content", value=message.content[:1000] or "_empty_", inline=False)
    embed.set_footer(text=f"User ID: {message.author.id}")
    await send_event_log(message.guild, embed)

@bot.event
async def on_member_update(before: discord.Member, after: discord.Member):
    config = get_guild_config(before.guild.id)
    if not config.get("log_roles", 1):
        return
    added = set(after.roles) - set(before.roles)
    removed = set(before.roles) - set(after.roles)
    if not added and not removed:
        return
    embed = discord.Embed(title="Member Roles Updated", color=COLOR_LOG, timestamp=now_dt())
    embed.set_author(name=str(after), icon_url=after.display_avatar.url)
    embed.add_field(name="User", value=after.mention, inline=True)
    if added:
        embed.add_field(name="Roles Added", value=" ".join(r.mention for r in added), inline=False)
    if removed:
        embed.add_field(name="Roles Removed", value=" ".join(r.mention for r in removed), inline=False)
    embed.set_footer(text=f"User ID: {after.id}")
    await send_event_log(before.guild, embed)

@bot.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    config = get_guild_config(member.guild.id)
    if not config.get("log_voice", 1):
        return
    if before.channel == after.channel:
        return
    if before.channel is None:
        action = f"Joined **{after.channel.name}**"
        color = COLOR_SUCCESS
    elif after.channel is None:
        action = f"Left **{before.channel.name}**"
        color = COLOR_WARNING
    else:
        action = f"Moved from **{before.channel.name}** → **{after.channel.name}**"
        color = COLOR_INFO
    embed = discord.Embed(title="Voice State Update", description=action, color=color, timestamp=now_dt())
    embed.set_author(name=str(member), icon_url=member.display_avatar.url)
    embed.set_footer(text=f"User ID: {member.id}")
    await send_event_log(member.guild, embed)

# ─────────────────────────────────────────────────────────────────────────────
# BACKGROUND TASK — TEMP BAN EXPIRY
# ─────────────────────────────────────────────────────────────────────────────
@tasks.loop(minutes=1)
async def check_temp_bans():
    pending = get_pending_temp_bans()
    now = now_dt()
    for ban in pending:
        try:
            expires = datetime.datetime.fromisoformat(ban["expires_at"])
            if expires.tzinfo is None:
                expires = expires.replace(tzinfo=datetime.timezone.utc)
            if now >= expires:
                guild = bot.get_guild(ban["guild_id"])
                if guild:
                    user = await bot.fetch_user(ban["user_id"])
                    try:
                        await guild.unban(user, reason=f"[Sentinel] Temp ban expired — Case #{ban['case_id']}")
                        embed = discord.Embed(
                            title="Temp Ban Expired",
                            description=f"{user} ({user.id}) has been automatically unbanned.",
                            color=COLOR_SUCCESS,
                            timestamp=now_dt()
                        )
                        embed.add_field(name="Case ID", value=ban["case_id"], inline=True)
                        embed.set_footer(text=BOT_NAME)
                        await send_mod_log(guild, embed)
                    except discord.NotFound:
                        pass
                mark_temp_ban_processed(ban["id"])
        except Exception:
            mark_temp_ban_processed(ban["id"])

# ─────────────────────────────────────────────────────────────────────────────
# SETUP COMMAND
# ─────────────────────────────────────────────────────────────────────────────
@bot.tree.command(name="setup", description="Configure Sentinel for this server. (Admin only)")
async def setup_command(interaction: discord.Interaction):
    if not is_admin(interaction):
        return await interaction.response.send_message("Requires Admin Role or Administrator permission.", ephemeral=True)
    await interaction.response.send_message(
        content="**Step 1 of 5** — Select your **Moderator Role** (can use mod commands):",
        view=SetupRoleView(interaction.guild_id),
        ephemeral=True
    )


# ─────────────────────────────────────────────────────────────────────────────
# MOD COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
mod_group = app_commands.Group(name="mod", description="Moderation commands.")

@mod_group.command(name="ban", description="Permanently ban a user.")
@app_commands.describe(user="User to ban", reason="Reason", delete_days="Days of messages to delete (0-7)")
async def mod_ban(interaction: discord.Interaction, user: discord.Member,
                  reason: Optional[str] = None, delete_days: Optional[int] = 0):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if user.top_role >= interaction.user.top_role and not interaction.user.guild_permissions.administrator:
        return await interaction.response.send_message("Cannot moderate a user with equal or higher role.", ephemeral=True)
    delete_days = max(0, min(7, delete_days or 0))
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "ban", reason)
    try:
        await interaction.guild.ban(user, reason=reason, delete_message_days=delete_days)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions to ban this user.", ephemeral=True)
    embed = discord.Embed(title=f"Case #{case_id} — BAN", color=COLOR_ERROR, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "ban", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="tempban", description="Temporarily ban a user for a set duration.")
@app_commands.describe(user="User to ban", duration="Duration (e.g. 1d, 12h, 30m)", reason="Reason")
async def mod_tempban(interaction: discord.Interaction, user: discord.Member,
                      duration: str, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if user.top_role >= interaction.user.top_role and not interaction.user.guild_permissions.administrator:
        return await interaction.response.send_message("Cannot moderate a user with equal or higher role.", ephemeral=True)

    # Parse duration string
    units = {"d": 1440, "h": 60, "m": 1}
    total_minutes = 0
    pattern = re.findall(r"(\d+)([dhm])", duration.lower())
    if not pattern:
        return await interaction.response.send_message(
            "Invalid duration format. Use combinations like `1d`, `12h`, `30m`, or `1d12h`.", ephemeral=True)
    for val, unit in pattern:
        total_minutes += int(val) * units[unit]
    if total_minutes <= 0:
        return await interaction.response.send_message("Duration must be greater than zero.", ephemeral=True)

    expires_at = (now_dt() + datetime.timedelta(minutes=total_minutes)).isoformat()
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "tempban",
                          reason, total_minutes, expires_at)
    try:
        await interaction.guild.ban(user, reason=f"[Temp Ban] {reason}", delete_message_days=0)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)

    add_temp_ban(interaction.guild_id, user.id, expires_at, case_id)
    embed = discord.Embed(title=f"Case #{case_id} — TEMP BAN", color=COLOR_ERROR, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Duration", value=duration, inline=True)
    embed.add_field(name="Expires", value=expires_at[:19].replace("T", " ") + " UTC", inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "tempban", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="softban", description="Ban then immediately unban to purge recent messages.")
@app_commands.describe(user="User to softban", reason="Reason")
async def mod_softban(interaction: discord.Interaction, user: discord.Member, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if user.top_role >= interaction.user.top_role and not interaction.user.guild_permissions.administrator:
        return await interaction.response.send_message("Cannot moderate a user with equal or higher role.", ephemeral=True)
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "softban", reason)
    try:
        await interaction.guild.ban(user, reason=f"[Softban] {reason}", delete_message_days=7)
        await interaction.guild.unban(user, reason="[Softban] Auto-unban")
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    embed = discord.Embed(title=f"Case #{case_id} — SOFTBAN", color=COLOR_ERROR, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "softban", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="unban", description="Unban a user by ID.")
@app_commands.describe(user_id="User ID to unban", reason="Reason")
async def mod_unban(interaction: discord.Interaction, user_id: str, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    try:
        uid = int(user_id)
        user = await bot.fetch_user(uid)
    except (ValueError, discord.NotFound):
        return await interaction.response.send_message("Invalid user ID.", ephemeral=True)
    try:
        await interaction.guild.unban(user, reason=reason)
    except discord.NotFound:
        return await interaction.response.send_message("User is not banned.", ephemeral=True)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "unban", reason)
    embed = discord.Embed(title=f"Case #{case_id} — UNBAN", color=COLOR_SUCCESS, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="kick", description="Kick a user from the server.")
@app_commands.describe(user="User to kick", reason="Reason")
async def mod_kick(interaction: discord.Interaction, user: discord.Member, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if user.top_role >= interaction.user.top_role and not interaction.user.guild_permissions.administrator:
        return await interaction.response.send_message("Cannot moderate a user with equal or higher role.", ephemeral=True)
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "kick", reason)
    try:
        await user.kick(reason=reason)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    embed = discord.Embed(title=f"Case #{case_id} — KICK", color=COLOR_WARNING, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "kick", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="timeout", description="Timeout a user for a specified duration.")
@app_commands.describe(user="User to timeout", minutes="Duration in minutes", reason="Reason")
async def mod_timeout(interaction: discord.Interaction, user: discord.Member,
                      minutes: int, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if user.top_role >= interaction.user.top_role and not interaction.user.guild_permissions.administrator:
        return await interaction.response.send_message("Cannot moderate a user with equal or higher role.", ephemeral=True)
    if not 1 <= minutes <= 40320:
        return await interaction.response.send_message("Duration must be between 1 and 40320 minutes.", ephemeral=True)
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "timeout", reason, minutes)
    try:
        await user.timeout(datetime.timedelta(minutes=minutes), reason=reason)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    embed = discord.Embed(title=f"Case #{case_id} — TIMEOUT", color=COLOR_WARNING, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Duration", value=f"{minutes} minute(s)", inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "timeout", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="untimeout", description="Remove a user's timeout.")
@app_commands.describe(user="User to untimeout", reason="Reason")
async def mod_untimeout(interaction: discord.Interaction, user: discord.Member, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "untimeout", reason)
    try:
        await user.timeout(None, reason=reason)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    embed = discord.Embed(title=f"Case #{case_id} — UNTIMEOUT", color=COLOR_SUCCESS, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="warn", description="Issue a formal warning to a user.")
@app_commands.describe(user="User to warn", reason="Reason")
async def mod_warn(interaction: discord.Interaction, user: discord.Member, reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    config = get_guild_config(interaction.guild_id)
    case_id = create_case(interaction.guild_id, user.id, interaction.user.id, "warn", reason)
    embed = discord.Embed(title=f"Case #{case_id} — WARN", color=COLOR_MOD, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    if config.get("dm_on_action", DEFAULT_DM_ON_ACTION):
        await dm_user_action(user, "warn", interaction.guild.name, reason or "No reason provided.",
                             case_id, bool(config.get("appeals_enabled")), interaction.guild_id, interaction.guild)
    await interaction.response.send_message(embed=embed)
    # Check ladder
    strikes = count_active_strikes(user.id, interaction.guild_id)
    await run_ladder(interaction.guild, user, strikes)

@mod_group.command(name="warnings", description="View warnings for a user.")
@app_commands.describe(user="User to check")
async def mod_warnings(interaction: discord.Interaction, user: discord.Member):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    cases = get_user_cases(user.id, interaction.guild_id)
    warnings = [c for c in cases if c["action_type"].lower() == "warn"]
    embed = discord.Embed(title=f"Warnings — {user}", color=COLOR_MOD, timestamp=now_dt())
    embed.set_thumbnail(url=user.display_avatar.url)
    if not warnings:
        embed.description = "No warnings on record."
    else:
        embed.description = f"**{len(warnings)}** warning(s) on record."
        for w in warnings[:10]:
            embed.add_field(name=f"Case #{w['case_id']} — {w['timestamp'][:10]}",
                            value=w["reason"] or "No reason provided.", inline=False)
        if len(warnings) > 10:
            embed.set_footer(text=f"{BOT_NAME} • Showing 10 of {len(warnings)}")
        else:
            embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

@mod_group.command(name="purge", description="Delete messages in bulk.")
@app_commands.describe(amount="Number of messages to delete (1-100)")
async def mod_purge(interaction: discord.Interaction, amount: int):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if not 1 <= amount <= 100:
        return await interaction.response.send_message("Amount must be between 1 and 100.", ephemeral=True)
    await interaction.response.defer(ephemeral=True)
    try:
        deleted = await interaction.channel.purge(limit=amount)
    except discord.Forbidden:
        return await interaction.followup.send("Missing permissions to delete messages.", ephemeral=True)
    log_embed = discord.Embed(title="Channel Purge", color=COLOR_NEUTRAL, timestamp=now_dt())
    log_embed.add_field(name="Channel", value=interaction.channel.mention, inline=True)
    log_embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    log_embed.add_field(name="Deleted", value=str(len(deleted)), inline=True)
    log_embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, log_embed)
    await interaction.followup.send(f"Deleted **{len(deleted)}** message(s).", ephemeral=True)

@mod_group.command(name="lock", description="Lock a channel, preventing members from sending messages.")
@app_commands.describe(channel="Channel to lock (defaults to current)", reason="Reason")
async def mod_lock(interaction: discord.Interaction,
                   channel: Optional[discord.TextChannel] = None,
                   reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    target = channel or interaction.channel
    overwrite = target.overwrites_for(interaction.guild.default_role)
    overwrite.send_messages = False
    try:
        await target.set_permissions(interaction.guild.default_role, overwrite=overwrite,
                                     reason=reason or "Channel locked by moderator")
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions to lock this channel.", ephemeral=True)
    embed = discord.Embed(title="Channel Locked", color=COLOR_ERROR, timestamp=now_dt())
    embed.add_field(name="Channel", value=target.mention, inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.add_field(name="Reason", value=reason or "No reason provided.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await target.send(embed=discord.Embed(
        description="🔒 This channel has been locked by a moderator.",
        color=COLOR_ERROR
    ))
    await interaction.response.send_message(embed=embed, ephemeral=True)

@mod_group.command(name="unlock", description="Unlock a previously locked channel.")
@app_commands.describe(channel="Channel to unlock (defaults to current)", reason="Reason")
async def mod_unlock(interaction: discord.Interaction,
                     channel: Optional[discord.TextChannel] = None,
                     reason: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    target = channel or interaction.channel
    overwrite = target.overwrites_for(interaction.guild.default_role)
    overwrite.send_messages = None
    try:
        await target.set_permissions(interaction.guild.default_role, overwrite=overwrite,
                                     reason=reason or "Channel unlocked by moderator")
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions to unlock this channel.", ephemeral=True)
    embed = discord.Embed(title="Channel Unlocked", color=COLOR_SUCCESS, timestamp=now_dt())
    embed.add_field(name="Channel", value=target.mention, inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await target.send(embed=discord.Embed(
        description="🔓 This channel has been unlocked.",
        color=COLOR_SUCCESS
    ))
    await interaction.response.send_message(embed=embed, ephemeral=True)

@mod_group.command(name="slowmode", description="Set slowmode for a channel.")
@app_commands.describe(seconds="Slowmode delay in seconds (0 to disable, max 21600)", channel="Target channel")
async def mod_slowmode(interaction: discord.Interaction, seconds: int,
                       channel: Optional[discord.TextChannel] = None):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if not 0 <= seconds <= 21600:
        return await interaction.response.send_message("Slowmode must be between 0 and 21600 seconds.", ephemeral=True)
    target = channel or interaction.channel
    try:
        await target.edit(slowmode_delay=seconds)
    except discord.Forbidden:
        return await interaction.response.send_message("Missing permissions.", ephemeral=True)
    label = f"{seconds}s" if seconds > 0 else "Disabled"
    embed = discord.Embed(title="Slowmode Updated", color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="Channel", value=target.mention, inline=True)
    embed.add_field(name="Delay", value=label, inline=True)
    embed.add_field(name="Moderator", value=interaction.user.mention, inline=True)
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await interaction.response.send_message(embed=embed)

bot.tree.add_command(mod_group)

# ─────────────────────────────────────────────────────────────────────────────
# NOTE COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
note_group = app_commands.Group(name="note", description="Moderator notes on users.")

@note_group.command(name="add", description="Add a private staff note to a user.")
@app_commands.describe(user="Target user", content="Note content")
async def note_add(interaction: discord.Interaction, user: discord.Member, content: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    note_id = add_note(interaction.guild_id, user.id, interaction.user.id, content)
    embed = discord.Embed(title=f"Note Added — #{note_id}", color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="User", value=f"{user} ({user.id})", inline=True)
    embed.add_field(name="Note ID", value=f"`{note_id}`", inline=True)
    embed.add_field(name="Content", value=content, inline=False)
    embed.set_footer(text=f"{BOT_NAME} • Added by {interaction.user}")
    await interaction.response.send_message(embed=embed, ephemeral=True)

@note_group.command(name="list", description="View all notes for a user.")
@app_commands.describe(user="Target user")
async def note_list(interaction: discord.Interaction, user: discord.Member):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    notes = get_notes(user.id, interaction.guild_id)
    embed = discord.Embed(title=f"Staff Notes — {user}", color=COLOR_INFO, timestamp=now_dt())
    embed.set_thumbnail(url=user.display_avatar.url)
    if not notes:
        embed.description = "No notes on record for this user."
    else:
        for n in notes[:10]:
            embed.add_field(
                name=f"#{n['note_id']} — {n['timestamp'][:10]}",
                value=f"{n['content']}\n_by <@{n['moderator_id']}>_",
                inline=False
            )
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed, ephemeral=True)

@note_group.command(name="delete", description="Delete a note by ID.")
@app_commands.describe(note_id="Note ID to delete")
async def note_delete(interaction: discord.Interaction, note_id: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    delete_note(note_id.upper(), interaction.guild_id)
    await interaction.response.send_message(f"Note `{note_id.upper()}` deleted.", ephemeral=True)

bot.tree.add_command(note_group)

# ─────────────────────────────────────────────────────────────────────────────
# AUTOMOD COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
automod_group = app_commands.Group(name="automod", description="Automoderation configuration.")

@automod_group.command(name="status", description="View current automod configuration.")
async def automod_status(interaction: discord.Interaction):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    cfg = get_automod_config(interaction.guild_id)
    embed = discord.Embed(title="Automod Configuration", color=COLOR_MOD, timestamp=now_dt())
    embed.add_field(name="Enabled", value="Yes" if cfg.get("enabled") else "No", inline=True)
    embed.add_field(name="Anti-Spam",
                    value=f"{'On' if cfg.get('anti_spam') else 'Off'} — {cfg.get('spam_threshold')} msgs/{cfg.get('spam_window')}s → {cfg.get('action_spam')} ({cfg.get('spam_timeout_mins')}m)",
                    inline=False)
    embed.add_field(name="Anti-Invite",
                    value=f"{'On' if cfg.get('anti_invite') else 'Off'} — action: {cfg.get('action_invite')}",
                    inline=False)
    embed.add_field(name="Anti-Mass Mention",
                    value=f"{'On' if cfg.get('anti_mass_mention') else 'Off'} — limit: {cfg.get('mention_limit')} → {cfg.get('action_mention')} ({cfg.get('mention_timeout_mins')}m)",
                    inline=False)
    embed.add_field(name="Anti-Raid",
                    value=f"{'On' if cfg.get('anti_raid') else 'Off'} — {cfg.get('raid_join_count')} joins/{cfg.get('raid_join_window')}s",
                    inline=False)
    embed.add_field(name="Word Filter",
                    value=f"{'On' if cfg.get('word_filter') else 'Off'} — {len(cfg.get('blocked_words', []))} word(s) blocked",
                    inline=False)
    embed.add_field(name="Raid Mode Active",
                    value="Yes ⚠️" if _raid_mode.get(interaction.guild_id) else "No", inline=True)
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed, ephemeral=True)

@automod_group.command(name="toggle", description="Enable or disable automod or a specific module.")
@app_commands.describe(module="Module to toggle",
                       enabled="Enable (true) or disable (false)")
@app_commands.choices(module=[
    app_commands.Choice(name="all", value="enabled"),
    app_commands.Choice(name="anti_spam", value="anti_spam"),
    app_commands.Choice(name="anti_invite", value="anti_invite"),
    app_commands.Choice(name="anti_mass_mention", value="anti_mass_mention"),
    app_commands.Choice(name="anti_raid", value="anti_raid"),
    app_commands.Choice(name="word_filter", value="word_filter"),
])
async def automod_toggle(interaction: discord.Interaction, module: str, enabled: bool):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    upsert_automod_config(interaction.guild_id, **{module: int(enabled)})
    await interaction.response.send_message(
        f"Automod module `{module}` {'enabled' if enabled else 'disabled'}.", ephemeral=True)

@automod_group.command(name="setspam", description="Configure spam detection thresholds.")
@app_commands.describe(threshold="Messages to trigger (default 5)", window="Time window in seconds (default 5)",
                        action="Action to take", timeout_mins="Timeout duration if action is timeout")
@app_commands.choices(action=[
    app_commands.Choice(name="timeout", value="timeout"),
    app_commands.Choice(name="kick", value="kick"),
    app_commands.Choice(name="warn", value="warn"),
])
async def automod_setspam(interaction: discord.Interaction, threshold: int, window: int,
                          action: str = "timeout", timeout_mins: int = 10):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    upsert_automod_config(interaction.guild_id,
                          spam_threshold=threshold, spam_window=window,
                          action_spam=action, spam_timeout_mins=timeout_mins)
    await interaction.response.send_message(
        f"Spam config updated: **{threshold}** messages in **{window}s** → **{action}**{'(' + str(timeout_mins) + 'm)' if action == 'timeout' else ''}.",
        ephemeral=True)

@automod_group.command(name="wordfilter", description="Manage the blocked word list.")
@app_commands.describe(action="Add or remove a word", word="The word to add or remove")
@app_commands.choices(action=[
    app_commands.Choice(name="add", value="add"),
    app_commands.Choice(name="remove", value="remove"),
    app_commands.Choice(name="list", value="list"),
])
async def automod_wordfilter(interaction: discord.Interaction, action: str, word: Optional[str] = None):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    cfg = get_automod_config(interaction.guild_id)
    words = cfg.get("blocked_words", [])
    if action == "list":
        display = ", ".join(f"`{w}`" for w in words) if words else "_No words blocked._"
        embed = discord.Embed(title="Blocked Words", description=display, color=COLOR_MOD)
        return await interaction.response.send_message(embed=embed, ephemeral=True)
    if not word:
        return await interaction.response.send_message("You must provide a word.", ephemeral=True)
    if action == "add":
        if word.lower() not in words:
            words.append(word.lower())
            upsert_automod_config(interaction.guild_id, blocked_words=words)
        await interaction.response.send_message(f"Word `{word}` added to filter.", ephemeral=True)
    elif action == "remove":
        if word.lower() in words:
            words.remove(word.lower())
            upsert_automod_config(interaction.guild_id, blocked_words=words)
            await interaction.response.send_message(f"Word `{word}` removed from filter.", ephemeral=True)
        else:
            await interaction.response.send_message(f"Word `{word}` not in filter.", ephemeral=True)

@automod_group.command(name="raidmode", description="Manually toggle raid mode.")
@app_commands.describe(enabled="Enable or disable raid mode")
async def automod_raidmode(interaction: discord.Interaction, enabled: bool):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    _raid_mode[interaction.guild_id] = enabled
    status = "ACTIVATED" if enabled else "DEACTIVATED"
    embed = discord.Embed(
        title=f"Raid Mode {status}",
        description=f"Raid mode has been manually {'activated' if enabled else 'deactivated'} by {interaction.user.mention}.",
        color=COLOR_ERROR if enabled else COLOR_SUCCESS,
        timestamp=now_dt()
    )
    embed.set_footer(text=BOT_NAME)
    await send_mod_log(interaction.guild, embed)
    await interaction.response.send_message(embed=embed)

bot.tree.add_command(automod_group)

# ─────────────────────────────────────────────────────────────────────────────
# LADDER COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
ladder_group = app_commands.Group(name="ladder", description="Configure the automated punishment escalation ladder.")

@ladder_group.command(name="view", description="View the current punishment ladder.")
async def ladder_view(interaction: discord.Interaction):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    rows = get_ladder(interaction.guild_id)
    embed = discord.Embed(title="Punishment Ladder", color=COLOR_MOD, timestamp=now_dt())
    if not rows:
        embed.description = "No escalation rules configured. Use `/ladder set` to add rules."
    else:
        for row in rows:
            dur = f" for {row['duration_min']}m" if row.get("duration_min") else ""
            embed.add_field(
                name=f"Threshold: {row['threshold']} active strike(s)",
                value=f"Action: **{row['action'].upper()}**{dur}",
                inline=False
            )
    embed.set_footer(text=f"{BOT_NAME} • Active strikes expire after the configured expiry period")
    await interaction.response.send_message(embed=embed)

@ladder_group.command(name="set", description="Set a ladder rule for a strike threshold.")
@app_commands.describe(threshold="Number of active strikes to trigger this rule",
                        action="Action to perform", duration_minutes="Duration in minutes (for timeout)")
@app_commands.choices(action=[
    app_commands.Choice(name="timeout", value="timeout"),
    app_commands.Choice(name="kick", value="kick"),
    app_commands.Choice(name="ban", value="ban"),
])
async def ladder_set(interaction: discord.Interaction, threshold: int, action: str,
                     duration_minutes: Optional[int] = 0):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    conn = get_db()
    c = conn.cursor()
    c.execute("""
        INSERT INTO punishment_ladder (guild_id, threshold, action, duration_min)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(guild_id, threshold) DO UPDATE SET action=excluded.action, duration_min=excluded.duration_min
    """, (interaction.guild_id, threshold, action, duration_minutes or 0))
    conn.commit()
    conn.close()
    dur_str = f" for {duration_minutes}m" if duration_minutes else ""
    await interaction.response.send_message(
        f"Ladder rule set: **{threshold}** active strikes → **{action.upper()}**{dur_str}.", ephemeral=True)

@ladder_group.command(name="remove", description="Remove a ladder rule by threshold.")
@app_commands.describe(threshold="Threshold to remove")
async def ladder_remove(interaction: discord.Interaction, threshold: int):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    conn = get_db()
    c = conn.cursor()
    c.execute("DELETE FROM punishment_ladder WHERE guild_id=? AND threshold=?",
              (interaction.guild_id, threshold))
    conn.commit()
    conn.close()
    await interaction.response.send_message(f"Ladder rule for threshold **{threshold}** removed.", ephemeral=True)

bot.tree.add_command(ladder_group)

# ─────────────────────────────────────────────────────────────────────────────
# CASE COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
case_group = app_commands.Group(name="case", description="Case management.")

@case_group.command(name="view", description="View a specific case.")
@app_commands.describe(case_id="Case ID")
async def case_view(interaction: discord.Interaction, case_id: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    case = get_case(case_id.upper(), interaction.guild_id)
    if not case:
        return await interaction.response.send_message(f"No case found with ID `{case_id.upper()}`.", ephemeral=True)
    await interaction.response.send_message(embed=build_case_embed(case, interaction.guild))

@case_group.command(name="history", description="View full moderation history for a user.")
@app_commands.describe(user="Target user")
async def case_history(interaction: discord.Interaction, user: discord.Member):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    cases = get_user_cases(user.id, interaction.guild_id)
    embed = discord.Embed(title=f"Moderation History — {user}", color=COLOR_NEUTRAL, timestamp=now_dt())
    embed.set_thumbnail(url=user.display_avatar.url)
    embed.add_field(name="User ID", value=str(user.id), inline=True)
    embed.add_field(name="Total Cases", value=str(len(cases)), inline=True)
    embed.add_field(name="Active Strikes", value=str(count_active_strikes(user.id, interaction.guild_id)), inline=True)
    if not cases:
        embed.description = "No moderation history found."
    else:
        for c in cases[:15]:
            ts = c["timestamp"][:16].replace("T", " ")
            dur = f" ({c['duration_minutes']}m)" if c.get("duration_minutes") else ""
            embed.add_field(
                name=f"[{c['case_id']}] {c['action_type'].upper()}{dur} — {ts}",
                value=c["reason"] or "No reason provided.",
                inline=False
            )
        if len(cases) > 15:
            embed.set_footer(text=f"{BOT_NAME} • Showing 15 of {len(cases)}")
        else:
            embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

@case_group.command(name="expunge", description="Permanently delete a case from the record.")
@app_commands.describe(case_id="Case ID to expunge")
async def case_expunge(interaction: discord.Interaction, case_id: str):
    if not await enforce_setup(interaction):
        return
    if not is_admin(interaction):
        return await interaction.response.send_message("This command requires the Admin Role or Administrator permission.", ephemeral=True)
    case = get_case(case_id.upper(), interaction.guild_id)
    if not case:
        return await interaction.response.send_message(f"No case found with ID `{case_id.upper()}`.", ephemeral=True)
    expunge_case(case_id.upper(), interaction.guild_id)
    embed = discord.Embed(title=f"Case #{case_id.upper()} Expunged",
                          description=f"Case `{case_id.upper()}` has been permanently removed from the record.",
                          color=COLOR_SUCCESS, timestamp=now_dt())
    embed.set_footer(text=f"{BOT_NAME} • Expunged by {interaction.user}")
    await interaction.response.send_message(embed=embed)
    await send_mod_log(interaction.guild, embed)

bot.tree.add_command(case_group)

# ─────────────────────────────────────────────────────────────────────────────
# REPORT COMMAND
# ─────────────────────────────────────────────────────────────────────────────
@bot.tree.command(name="report", description="Report a user to server staff.")
@app_commands.describe(user="User you are reporting", reason="Reason for the report")
async def report_command(interaction: discord.Interaction, user: discord.Member, reason: str):
    if not await enforce_setup(interaction):
        return
    if user.id == interaction.user.id:
        return await interaction.response.send_message("You cannot report yourself.", ephemeral=True)
    if user.bot:
        return await interaction.response.send_message("You cannot report bots.", ephemeral=True)
    report_id = create_report(interaction.guild_id, interaction.user.id, user.id, reason)
    config = get_guild_config(interaction.guild_id)
    ch_id = config.get("mod_log_channel_id")
    embed = discord.Embed(title=f"New User Report — #{report_id}", color=COLOR_WARNING, timestamp=now_dt())
    embed.add_field(name="Report ID", value=f"`{report_id}`", inline=True)
    embed.add_field(name="Reporter", value=f"{interaction.user.mention} ({interaction.user.id})", inline=True)
    embed.add_field(name="Target", value=f"{user.mention} ({user.id})", inline=True)
    embed.add_field(name="Reason", value=reason, inline=False)
    embed.set_footer(text=f"{BOT_NAME} • Pending staff review")
    view = ReportReviewView(report_id)
    posted = False
    if ch_id:
        ch = interaction.guild.get_channel(int(ch_id))
        if ch:
            try:
                await ch.send(embed=embed, view=view)
                posted = True
            except discord.Forbidden:
                pass
    if not posted:
        for ch in interaction.guild.text_channels:
            if ch.permissions_for(interaction.guild.me).send_messages:
                try:
                    await ch.send(embed=embed, view=view)
                    break
                except discord.Forbidden:
                    continue
    confirm = discord.Embed(
        title="Report Submitted",
        description=f"Your report (`{report_id}`) has been submitted to server staff for review.",
        color=COLOR_SUCCESS
    )
    confirm.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=confirm, ephemeral=True)

# ─────────────────────────────────────────────────────────────────────────────
# WHOIS COMMAND
# ─────────────────────────────────────────────────────────────────────────────
@bot.tree.command(name="whois", description="View detailed information about a user.")
@app_commands.describe(user="Target user")
async def whois_command(interaction: discord.Interaction, user: discord.Member):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    cases = get_user_cases(user.id, interaction.guild_id)
    active_strikes = count_active_strikes(user.id, interaction.guild_id)
    notes = get_notes(user.id, interaction.guild_id)

    action_counts: dict[str, int] = {}
    for c in cases:
        action_counts[c["action_type"]] = action_counts.get(c["action_type"], 0) + 1

    embed = discord.Embed(title=f"User Profile — {user}", color=COLOR_NEUTRAL, timestamp=now_dt())
    embed.set_thumbnail(url=user.display_avatar.url)

    embed.add_field(name="User ID", value=str(user.id), inline=True)
    embed.add_field(name="Display Name", value=user.display_name, inline=True)
    embed.add_field(name="Bot", value="Yes" if user.bot else "No", inline=True)

    created_ago = (now_dt() - user.created_at).days
    embed.add_field(name="Account Created",
                    value=f"{user.created_at.strftime('%Y-%m-%d')} ({created_ago} days ago)", inline=True)
    joined_ago = (now_dt() - user.joined_at).days if user.joined_at else "?"
    embed.add_field(name="Joined Server",
                    value=f"{user.joined_at.strftime('%Y-%m-%d') if user.joined_at else 'Unknown'} ({joined_ago} days ago)",
                    inline=True)

    timeout_status = "Active" if user.is_timed_out() else "None"
    embed.add_field(name="Timeout Status", value=timeout_status, inline=True)

    roles = [r.mention for r in user.roles if r.name != "@everyone"]
    embed.add_field(name=f"Roles ({len(roles)})",
                    value=" ".join(roles[:10]) if roles else "_None_", inline=False)

    summary_parts = []
    for action, count in sorted(action_counts.items()):
        summary_parts.append(f"{action.upper()}: {count}")
    embed.add_field(name=f"Mod History ({len(cases)} total)",
                    value="\n".join(summary_parts) if summary_parts else "_Clean record_", inline=True)
    embed.add_field(name="Active Strikes", value=str(active_strikes), inline=True)
    embed.add_field(name="Staff Notes", value=str(len(notes)), inline=True)

    # Risk indicator
    if active_strikes >= 5 or action_counts.get("ban", 0) > 0:
        risk = "🔴 High"
    elif active_strikes >= 2 or action_counts.get("kick", 0) > 0:
        risk = "🟡 Medium"
    else:
        risk = "🟢 Low"
    embed.add_field(name="Risk Level", value=risk, inline=True)

    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

# ─────────────────────────────────────────────────────────────────────────────
# STATS COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
stats_group = app_commands.Group(name="stats", description="Moderation statistics.")

@stats_group.command(name="server", description="View server-wide moderation statistics.")
async def stats_server(interaction: discord.Interaction):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    conn = get_db()
    c = conn.cursor()
    c.execute("SELECT action_type, COUNT(*) as cnt FROM mod_cases WHERE guild_id=? GROUP BY action_type",
              (interaction.guild_id,))
    action_rows = c.fetchall()
    c.execute("SELECT moderator_id, COUNT(*) as cnt FROM mod_cases WHERE guild_id=? GROUP BY moderator_id ORDER BY cnt DESC LIMIT 5",
              (interaction.guild_id,))
    top_mods = c.fetchall()
    c.execute("SELECT COUNT(*) FROM mod_cases WHERE guild_id=?", (interaction.guild_id,))
    total = c.fetchone()[0]
    c.execute("SELECT COUNT(*) FROM appeals WHERE guild_id=?", (interaction.guild_id,))
    total_appeals = c.fetchone()[0]
    c.execute("SELECT COUNT(*) FROM appeals WHERE guild_id=? AND status='pending'", (interaction.guild_id,))
    pending_appeals = c.fetchone()[0]
    conn.close()

    embed = discord.Embed(title=f"Moderation Statistics — {interaction.guild.name}",
                          color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="Total Cases", value=str(total), inline=True)
    embed.add_field(name="Total Appeals", value=str(total_appeals), inline=True)
    embed.add_field(name="Pending Appeals", value=str(pending_appeals), inline=True)

    breakdown = "\n".join(f"{r['action_type'].upper()}: **{r['cnt']}**" for r in action_rows) or "_No data_"
    embed.add_field(name="Case Breakdown", value=breakdown, inline=False)

    mod_lines = []
    for row in top_mods:
        mod_lines.append(f"<@{row['moderator_id']}>: **{row['cnt']}** actions")
    embed.add_field(name="Top Moderators", value="\n".join(mod_lines) or "_No data_", inline=False)
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

@stats_group.command(name="user", description="View moderation statistics for a specific user.")
@app_commands.describe(user="Target user")
async def stats_user(interaction: discord.Interaction, user: discord.Member):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    cases = get_user_cases(user.id, interaction.guild_id)
    active_strikes = count_active_strikes(user.id, interaction.guild_id)
    action_counts: dict[str, int] = {}
    for c in cases:
        action_counts[c["action_type"]] = action_counts.get(c["action_type"], 0) + 1

    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT COUNT(*) FROM appeals WHERE guild_id=? AND user_id=?",
                (interaction.guild_id, user.id))
    appeal_count = cur.fetchone()[0]
    conn.close()

    embed = discord.Embed(title=f"User Statistics — {user}", color=COLOR_NEUTRAL, timestamp=now_dt())
    embed.set_thumbnail(url=user.display_avatar.url)
    embed.add_field(name="Total Cases", value=str(len(cases)), inline=True)
    embed.add_field(name="Active Strikes", value=str(active_strikes), inline=True)
    embed.add_field(name="Appeals Filed", value=str(appeal_count), inline=True)
    breakdown = "\n".join(f"{a.upper()}: {cnt}" for a, cnt in sorted(action_counts.items())) or "_Clean record_"
    embed.add_field(name="Breakdown", value=breakdown, inline=False)
    if cases:
        last = cases[0]
        embed.add_field(name="Most Recent Action",
                        value=f"`{last['action_type'].upper()}` on {last['timestamp'][:10]}", inline=False)
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

bot.tree.add_command(stats_group)

# ─────────────────────────────────────────────────────────────────────────────
# TAG COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
tag_group = app_commands.Group(name="tag", description="Manage and use custom response tags.")

@tag_group.command(name="use", description="Send a tag response. (Moderator only)")
@app_commands.describe(name="Tag name")
async def tag_use(interaction: discord.Interaction, name: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Tag commands are restricted to moderators.", ephemeral=True)
    tag = get_tag(interaction.guild_id, name)
    if not tag:
        return await interaction.response.send_message(f"No tag found with name `{name}`.", ephemeral=True)
    increment_tag_uses(interaction.guild_id, name)
    await interaction.response.send_message(tag["content"])

@tag_group.command(name="create", description="Create a new tag.")
@app_commands.describe(name="Tag name (no spaces)", content="Tag content")
async def tag_create(interaction: discord.Interaction, name: str, content: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    if " " in name:
        return await interaction.response.send_message("Tag names cannot contain spaces.", ephemeral=True)
    if len(content) > 2000:
        return await interaction.response.send_message("Tag content cannot exceed 2000 characters.", ephemeral=True)
    success = create_tag(interaction.guild_id, name, content, interaction.user.id)
    if success:
        await interaction.response.send_message(f"Tag `{name}` created successfully.", ephemeral=True)
    else:
        await interaction.response.send_message(f"A tag named `{name}` already exists.", ephemeral=True)

@tag_group.command(name="delete", description="Delete a tag.")
@app_commands.describe(name="Tag name to delete")
async def tag_delete(interaction: discord.Interaction, name: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Insufficient permissions.", ephemeral=True)
    success = delete_tag(interaction.guild_id, name)
    if success:
        await interaction.response.send_message(f"Tag `{name}` deleted.", ephemeral=True)
    else:
        await interaction.response.send_message(f"No tag named `{name}` found.", ephemeral=True)

@tag_group.command(name="list", description="List all tags in this server. (Moderator only)")
async def tag_list(interaction: discord.Interaction):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Tag commands are restricted to moderators.", ephemeral=True)
    tags = list_tags(interaction.guild_id)
    embed = discord.Embed(title="Server Tags", color=COLOR_INFO, timestamp=now_dt())
    if not tags:
        embed.description = "No tags created yet. Use `/tag create` to add one."
    else:
        lines = [f"`{t['name']}` — {t['uses']} uses" for t in tags]
        embed.description = "\n".join(lines[:30])
        if len(tags) > 30:
            embed.set_footer(text=f"{BOT_NAME} • Showing 30 of {len(tags)}")
        else:
            embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

@tag_group.command(name="info", description="View information about a specific tag. (Moderator only)")
@app_commands.describe(name="Tag name")
async def tag_info(interaction: discord.Interaction, name: str):
    if not await enforce_setup(interaction):
        return
    if not is_moderator(interaction):
        return await interaction.response.send_message("Tag commands are restricted to moderators.", ephemeral=True)
    tag = get_tag(interaction.guild_id, name)
    if not tag:
        return await interaction.response.send_message(f"No tag found with name `{name}`.", ephemeral=True)
    embed = discord.Embed(title=f"Tag — {tag['name']}", color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="Name", value=tag["name"], inline=True)
    embed.add_field(name="Uses", value=str(tag["uses"]), inline=True)
    embed.add_field(name="Created By", value=f"<@{tag['creator_id']}>", inline=True)
    embed.add_field(name="Created", value=tag["timestamp"][:10], inline=True)
    embed.add_field(name="Content Preview", value=tag["content"][:300], inline=False)
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed, ephemeral=True)

bot.tree.add_command(tag_group)

# ─────────────────────────────────────────────────────────────────────────────
# SENTINEL INFO COMMAND GROUP
# ─────────────────────────────────────────────────────────────────────────────
sentinel_group = app_commands.Group(name="sentinel", description="Information and policy commands.")

@sentinel_group.command(name="about", description="About Sentinel.")
async def sentinel_about(interaction: discord.Interaction):
    embed = discord.Embed(title=f"About {BOT_NAME}", color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="Overview", value=(
        f"{BOT_NAME} is an advanced moderation and governance bot developed to maintain order, "
        "enforce community standards, and provide staff teams with structured, reliable moderation tooling."
    ), inline=False)
    embed.add_field(name="Version", value=BOT_VERSION, inline=True)
    embed.add_field(name="Developer", value="Averin Holdings", inline=True)
    embed.add_field(name="Case System", value="Every action generates a unique Case ID.", inline=False)
    embed.add_field(name="Appeals", value="Users may appeal actions directly via DM.", inline=False)
    embed.set_footer(text=BOT_NAME)
    await interaction.response.send_message(embed=embed)

@sentinel_group.command(name="help", description="View all Sentinel commands.")
async def sentinel_help(interaction: discord.Interaction):
    embed = discord.Embed(title=f"{BOT_NAME} — Command Reference", color=COLOR_INFO, timestamp=now_dt())
    embed.add_field(name="⚙️ Setup", value="`/setup`", inline=False)
    embed.add_field(name="🛡️ Moderation", value=(
        "`/mod ban` `/mod tempban` `/mod softban` `/mod unban` `/mod kick`\n"
        "`/mod timeout` `/mod untimeout` `/mod warn` `/mod warnings`\n"
        "`/mod purge` `/mod lock` `/mod unlock` `/mod slowmode`"
    ), inline=False)
    embed.add_field(name="📋 Cases", value="`/case view` `/case history` `/case expunge`", inline=False)
    embed.add_field(name="🤖 Automod", value=(
        "`/automod status` `/automod raidmode` — Moderator\n"
        "`/automod toggle` `/automod setspam` `/automod wordfilter` — Admin only"
    ), inline=False)
    embed.add_field(name="⚡ Ladder (Admin only)", value="`/ladder view` `/ladder set` `/ladder remove`", inline=False)
    embed.add_field(name="📝 Notes", value="`/note add` `/note list` `/note delete`", inline=False)
    embed.add_field(name="🏷️ Tags (Moderator only)", value="`/tag use` `/tag create` `/tag delete` `/tag list` `/tag info`", inline=False)
    embed.add_field(name="📊 Stats", value="`/stats server` `/stats user`", inline=False)
    embed.add_field(name="🔍 Lookup", value="`/whois` `/report`", inline=False)
    embed.add_field(name="ℹ️ Info", value="`/sentinel about` `/sentinel help` `/sentinel tos` `/sentinel privacy`", inline=False)
    embed.set_footer(text=f"{BOT_NAME} v{BOT_VERSION}")
    await interaction.response.send_message(embed=embed)

@sentinel_group.command(name="tos", description="View Terms of Service.")
async def sentinel_tos(interaction: discord.Interaction):
    embed = discord.Embed(title=f"{BOT_NAME} — Terms of Service", color=COLOR_NEUTRAL, timestamp=now_dt())
    embed.description = "By using Averin Holdings' Sentinel, you agree to the following terms:"
    embed.add_field(name="1. Warranty Disclaimer", value="Sentinel is provided \"as-is\" without warranties of any kind, expressed or implied.", inline=False)
    embed.add_field(name="2. Modifications & Availability", value="Averin Holdings reserves the right to update, modify, suspend, or terminate Sentinel at any time without prior notice.", inline=False)
    embed.add_field(name="3. Administrator Responsibility", value="Server owners and administrators are solely responsible for how Sentinel is configured and used within their server.", inline=False)
    embed.add_field(name="4. Prohibited Use", value="Sentinel may not be used for harassment, surveillance beyond moderation, data exploitation, or any activity violating Discord's ToS or applicable laws.", inline=False)
    embed.add_field(name="5. Enforcement", value="Abuse, exploitation, or attempts to bypass safeguards may result in immediate access revocation.", inline=False)
    embed.add_field(name="Acceptance", value="Continued use constitutes acceptance of these terms and any future revisions.", inline=False)
    embed.set_footer(text=f"{BOT_NAME} • Averin Holdings")
    await interaction.response.send_message(embed=embed)

@sentinel_group.command(name="privacy", description="View Privacy Policy.")
async def sentinel_privacy(interaction: discord.Interaction):
    embed = discord.Embed(title=f"{BOT_NAME} — Privacy Policy", color=COLOR_NEUTRAL, timestamp=now_dt())
    embed.add_field(name="Data Collected", value="User IDs, server IDs, command usage, moderation logs, and performance metrics.", inline=False)
    embed.add_field(name="Data Usage", value="Data is used solely for moderation functionality. It is not sold, traded, or monetized.", inline=False)
    embed.add_field(name="Retention", value="Data is retained only as long as operationally necessary.", inline=False)
    embed.add_field(name="Security", value="All data handling follows industry-standard security practices.", inline=False)
    embed.add_field(name="Consent", value="By using Sentinel, you consent to data collection as described above.", inline=False)
    embed.set_footer(text=f"{BOT_NAME} • Averin Holdings")
    await interaction.response.send_message(embed=embed)

bot.tree.add_command(sentinel_group)




# ─────────────────────────────────────────────────────────────────────────────
# OWNER-ONLY SLASH COMMAND — /staff_panel
# ─────────────────────────────────────────────────────────────────────────────
async def _is_bot_owner(interaction: discord.Interaction) -> bool:
    # Use the shared constant
    if interaction.user.id == BOT_OWNER_ID:
        return True
    # Fallback: Discord app owner check
    try:
        app = await bot.application_info()
        return interaction.user.id == app.owner.id
    except Exception:
        return False

@bot.tree.command(name="staff_panel", description="[Owner only] View all servers Sentinel is in.")
async def staff_panel(interaction: discord.Interaction):
    if not await _is_bot_owner(interaction):
        return await interaction.response.send_message(
            "This command is restricted to the bot owner.", ephemeral=True
        )

    await interaction.response.defer(ephemeral=True)

    guilds = sorted(bot.guilds, key=lambda g: g.name.lower())
    lines = []

    for guild in guilds:
        invite_url = "_(no permission)_"
        for channel in guild.text_channels:
            perms = channel.permissions_for(guild.me)
            if perms.create_instant_invite and perms.read_messages:
                try:
                    inv = await channel.create_invite(
                        max_age=0,
                        max_uses=0,
                        unique=True,
                        reason="[Sentinel] Owner staff panel"
                    )
                    invite_url = inv.url
                except discord.Forbidden:
                    invite_url = "_(no permission)_"
                except Exception:
                    invite_url = "_(error)_"
                break

        owner_tag = str(guild.owner) if guild.owner else f"ID {guild.owner_id}"
        lines.append(
            f"**{guild.name}** `{guild.id}`\n"
            f"Owner: {owner_tag} | Members: {guild.member_count} | {invite_url}"
        )

    chunk_size = 10
    chunks = [lines[i:i + chunk_size] for i in range(0, len(lines), chunk_size)]

    header = discord.Embed(
        title=f"Sentinel Staff Panel — {len(guilds)} Server(s)",
        description=f"Generated <t:{int(now_dt().timestamp())}:R>.",
        color=COLOR_INFO,
        timestamp=now_dt()
    )
    header.set_footer(text=f"{BOT_NAME} • Owner Only")
    await interaction.followup.send(embed=header, ephemeral=True)

    for i, chunk in enumerate(chunks):
        embed = discord.Embed(
            title=f"Servers {i * chunk_size + 1}–{min((i + 1) * chunk_size, len(guilds))}",
            description="\n\n".join(chunk),
            color=COLOR_NEUTRAL,
            timestamp=now_dt()
        )
        embed.set_footer(text=f"Page {i + 1} of {len(chunks)}")
        await interaction.followup.send(embed=embed, ephemeral=True)

# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    init_db()
    bot.run(BOT_TOKEN)