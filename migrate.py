#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""Discord backup -> Fluxer migration tool.

Migrates a Discord server backup (SQLite) into a Fluxer instance running the
Postgres KV backend, preserving original timestamps and message ordering by
reusing Discord snowflake IDs (Discord and Fluxer share the 2015 epoch).

Users are NOT created by this tool: an admin pre-creates Fluxer users and maps
Discord user IDs to Fluxer user IDs in the config's `user_map` (see
`gen-user-map`). All settings live in one `config.json` passed with `--config`.

Subcommands:
    gen-user-map   Fill the config's user_map from the backup's users.
    preflight      Validate config/connectivity/users without writing.
    migrate        Run the migration.
    verify         Compare migrated counts against the backup.
    purge          Delete what the migration created (for a clean re-run).

Run `python migrate.py --config <file> <subcommand> --help` for options.
"""

import argparse
import io
import json
import mimetypes
import os
import re
import shutil
import subprocess
import sys
import time

import psycopg2

from config import load_config, write_user_map
from discord_db import DiscordBackup, parse_ts, snowflake_to_ms
from kvstore import KvStore
from progress import Progress
from schema import Schema
from snowflake import make_bucket
from s3uploader import S3Uploader, cdn_key
from unicode_emojis import EmojiNormalizer, default_emoji_data_path
from klipy import (
    KlipyClient,
    is_tenor_view_url,
    replace_tenor_link,
    sign_media_proxy_url,
    slug_from_share_url,
)
from youtube import YouTubeClient, is_youtube_url

MENTION_USER_RE = re.compile(r"<@!?(\d+)>")
MENTION_ROLE_RE = re.compile(r"<@&(\d+)>")
MENTION_CHANNEL_RE = re.compile(r"<#(\d+)>")

# Discord channel type -> Fluxer channel type.
CHANNEL_TYPE_MAP = {0: 0, 2: 2, 4: 4, 5: 0, 13: 2, 15: 15, 16: 16}
# Without native threads a forum/media channel is flattened to a text channel.
FLAT_CHANNEL_TYPE_MAP = {**CHANNEL_TYPE_MAP, 15: 0, 16: 0}

# Mirrors @fluxer/constants ChannelConstants.ChannelTypes / ThreadConstants.
CHANNEL_GUILD_TEXT = 0
CHANNEL_ANNOUNCEMENT_THREAD = 10
CHANNEL_PUBLIC_THREAD = 11
CHANNEL_PRIVATE_THREAD = 12
THREAD_ONLY_CHANNEL_TYPES = frozenset({15, 16})  # GUILD_FORUM, GUILD_MEDIA
THREAD_AUTO_ARCHIVE_DURATIONS = (60, 1440, 4320, 10080)
DEFAULT_THREAD_AUTO_ARCHIVE_DURATION = 4320
MAX_ACTIVE_THREADS_PER_GUILD = 1000
MAX_THREAD_MEMBERS = 1000
THREAD_MEMBER_IDS_PREVIEW_SIZE = 8
MAX_APPLIED_TAGS_PER_THREAD = 5


class ChannelFlags:
    PINNED = 1 << 1
    REQUIRE_TAG = 1 << 4
    HIDE_MEDIA_DOWNLOAD_OPTIONS = 1 << 15


class ThreadMemberFlags:
    HAS_INTERACTED = 1 << 0


class ServerMessageFlags:
    HAS_THREAD = 1 << 5


MESSAGE_TYPE_THREAD_CREATED = 18
MESSAGE_TYPE_THREAD_STARTER = 21


# Mirrors @fluxer/constants ChannelConstants.MessageAttachmentFlags.
class MessageAttachmentFlags:
    IS_SPOILER = 1 << 3
    CONTAINS_EXPLICIT_MEDIA = 1 << 4
    IS_ANIMATED = 1 << 5


# Message types Fluxer accepts (MessageTypeSchema): DEFAULT, RECIPIENT_ADD,
# RECIPIENT_REMOVE, CALL, CHANNEL_NAME_CHANGE, CHANNEL_ICON_CHANGE,
# CHANNEL_PINNED_MESSAGE, USER_JOIN, REPLY. Discord emits other types
# (e.g. 20 APPLICATION_COMMAND) that Fluxer's response schema rejects,
# 500-ing the whole channel fetch.
ALLOWED_MESSAGE_TYPES = frozenset({0, 1, 2, 3, 4, 5, 6, 7, 19})
# With native threads, 18 THREAD_CREATED is a real stored message (see
# ThreadCreationService.createThreadCreatedMessage). 21 THREAD_STARTER_MESSAGE
# is never stored: Fluxer derives it from the thread id (see _migrate_one_message).
NATIVE_THREAD_MESSAGE_TYPES = ALLOWED_MESSAGE_TYPES | {MESSAGE_TYPE_THREAD_CREATED}


def coerce_message_type(raw, native_threads=False):
    t = int(raw or 0)
    allowed = NATIVE_THREAD_MESSAGE_TYPES if native_threads else ALLOWED_MESSAGE_TYPES
    return t if t in allowed else 0


# --------------------------------------------------------------------------- #
# User map
# --------------------------------------------------------------------------- #

def gen_user_map(cfg):
    """Populate the `user_map` section of the config file with every Discord
    user in the backup, preserving any fluxer_user_id already filled in."""
    db = DiscordBackup(cfg.backup_db)
    users = db.users()
    db.close()
    user_map_obj = {}
    for u in users:
        did = str(u["id"])
        existing = cfg.user_map_raw.get(did)
        fid = existing.get("fluxer_user_id", 0) if isinstance(existing, dict) else (existing or 0)
        user_map_obj[did] = {
            "name": u["display_name"] or u["username"],
            "fluxer_user_id": int(fid) if fid else 0,
        }
    write_user_map(cfg.config_path, user_map_obj)
    filled = sum(1 for v in user_map_obj.values() if v["fluxer_user_id"])
    print(f"Wrote user_map with {len(user_map_obj)} users into {cfg.config_path} "
          f"({filled} already mapped).")
    print("Fill in fluxer_user_id for each user, then run `preflight`.")


# --------------------------------------------------------------------------- #
# Preflight
# --------------------------------------------------------------------------- #

def preflight(cfg, owner_id=None, want_s3=True):
    """Validate everything needed for a migration *before* writing anything.

    Returns (problems, warnings) as lists of strings. `problems` are fatal
    (migration would produce a broken guild); `warnings` are non-fatal.
    Every check is defensive so misconfiguration yields a clear message
    instead of a traceback mid-run.
    """
    import psycopg2

    problems, warnings = [], []

    def ok(msg):
        print(f"  \033[32m✓\033[0m {msg}")

    def bad(msg):
        print(f"  \033[31m✗\033[0m {msg}")
        problems.append(msg)

    def warn(msg):
        print(f"  \033[33m!\033[0m {msg}")
        warnings.append(msg)

    print("Preflight checks:")

    # 1. Schema file
    try:
        Schema(cfg.schema_path)
        ok(f"schema loaded ({cfg.schema_path})")
    except Exception as e:  # noqa: BLE001
        bad(f"schema not loadable at {cfg.schema_path}: {e}")

    # 2. Backup DB + expected tables
    db = None
    try:
        db = DiscordBackup(cfg.backup_db)
        names = {r[0] for r in db.conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table'").fetchall()}
        required = {"guild_profile", "channels", "messages", "users"}
        missing = required - names
        if missing:
            bad(f"backup DB missing tables: {sorted(missing)}")
        elif db.guild() is None:
            bad("backup DB has no guild_profile row")
        else:
            ok(f"backup DB readable ({db.message_count()} messages)")
    except Exception as e:  # noqa: BLE001
        bad(f"cannot open backup DB at {cfg.backup_db}: {e}")

    # 2b. Thread strategy, and (for native threads) a Fluxer schema that has them
    if cfg.thread_mode not in ("native", "channel", "skip"):
        bad(f"options.thread_mode {cfg.thread_mode!r} must be native, channel or skip")
    elif cfg.thread_mode == "native":
        try:
            sch = Schema(cfg.schema_path)
            absent = [t for t in ("thread_state", "thread_stats", "thread_members",
                                  "threads_by_parent", "thread_parent_config")
                      if t not in sch.tables]
            if absent:
                bad(f"schema has no native thread tables ({absent}); update the "
                    "Fluxer checkout or set options.thread_mode to \"channel\"")
            else:
                ok("schema has native thread tables")
        except Exception:  # noqa: BLE001
            pass  # already reported by the schema check
        if db is not None:
            try:
                have = {r[1] for r in db.conn.execute("PRAGMA table_info(threads)")}
                if db.threads() and "owner_id" not in have:
                    warn("backup predates thread owners/flags (older disco-reaper); "
                         "thread owners fall back to the first poster")
            except Exception:  # noqa: BLE001
                pass

    # 3. Backup media directory (needed for attachment/emoji/sticker uploads)
    if want_s3:
        if os.path.isdir(cfg.backup_dir):
            ok(f"backup media dir present ({cfg.backup_dir})")
        else:
            warn(f"backup media dir not found ({cfg.backup_dir}); "
                 "attachments with missing files will be skipped")

    # 4. Postgres reachable + KV table exists
    conn = None
    try:
        conn = psycopg2.connect(cfg.pg_dsn)
        with conn.cursor() as cur:
            cur.execute("SELECT to_regclass(%s)", (cfg.kv_table,))
            if cur.fetchone()[0] is None:
                bad(f"Postgres reachable but table {cfg.kv_table!r} does not "
                    "exist (is Fluxer initialised / using the postgres backend?)")
            else:
                ok(f"Postgres reachable, {cfg.kv_table} present")
    except Exception as e:  # noqa: BLE001
        bad(f"cannot connect to Postgres ({cfg.pg_host}:{cfg.pg_port}): {e}")

    # 5. S3 reachable + bucket accessible
    if want_s3:
        try:
            s3 = S3Uploader(cfg)
            s3.client.head_bucket(Bucket=s3.bucket)
            ok(f"S3 reachable, bucket {s3.bucket!r} accessible")
        except Exception as e:  # noqa: BLE001
            warn(f"S3 bucket {cfg.s3_bucket_cdn!r} not reachable/accessible "
                 f"({cfg.s3_endpoint}): {e} — will be created on demand if "
                 "credentials allow")

    # 6/7. User map populated, and mapped users actually exist
    mapping = cfg.user_map
    if not cfg.user_map_raw:
        bad("config has no `user_map` — run `gen-user-map` first")
    elif not mapping:
        bad("user map has no mapped users (every fluxer_user_id is 0)")
    else:
        ok(f"user map has {len(mapping)} mapped user(s)")

    # Verify mapped + owner user ids exist in Fluxer's `users` table.
    if conn is not None and (mapping or owner_id):
        want = {str(v) for v in mapping.values()}
        if owner_id:
            want.add(str(owner_id))
        try:
            with conn.cursor() as cur:
                cur.execute(
                    f"SELECT row_data->'user_id'->>'value' FROM {cfg.kv_table} "
                    "WHERE table_name='users' "
                    "AND row_data->'user_id'->>'value' = ANY(%s)",
                    (list(want),),
                )
                present = {r[0] for r in cur.fetchall()}
            missing = sorted(want - present)
            if missing:
                bad(f"{len(missing)} mapped/owner Fluxer user id(s) do NOT exist "
                    f"in the instance — create them in the admin dashboard first: "
                    f"{missing}")
            else:
                ok(f"all {len(want)} mapped/owner Fluxer user(s) exist")
        except Exception as e:  # noqa: BLE001
            warn(f"could not verify Fluxer users exist: {e}")

    # GIF conversion: key present, and a live sanity check against KLIPY.
    if cfg.convert_gifs:
        if not cfg.klipy_api_key:
            bad("convert_gifs is on but no KLIPY api key resolved "
                "(set klipy_api_key)")
        else:
            try:
                from klipy import KlipyClient
                probe = KlipyClient(cfg.klipy_api_key,
                                    customer_id=cfg.klipy_customer_id or "flushcord")
                if probe._search("hello"):
                    ok("KLIPY api key works (search returned results)")
                else:
                    warn("KLIPY api key set but a probe search returned nothing")
            except Exception as e:  # noqa: BLE001
                warn(f"could not reach KLIPY to verify the api key: {e}")

    # YouTube embeds: key works, and the media proxy that supplies the
    # thumbnail's metadata is configured. Opt-in by setting youtube_api_key --
    # so when it's absent, say what the backup will lose rather than stay quiet.
    if cfg.youtube_api_key:
        try:
            from youtube import YouTubeClient
            probe = YouTubeClient(cfg.youtube_api_key, verbose=True)
            if probe._fetch("dQw4w9WgXcQ"):
                ok("YouTube api key works (videos.list returned a video)")
            else:
                bad("YouTube api key set but videos.list returned nothing — the "
                    "key is invalid, or the YouTube Data API v3 is not enabled "
                    "for its project")
        except Exception as e:  # noqa: BLE001
            warn(f"could not reach the YouTube Data API to verify the key: {e}")
        if not (cfg.media_proxy_endpoint and cfg.media_proxy_secret):
            warn("youtube_api_key is set but media_proxy_endpoint/media_proxy_secret "
                 "is not; YouTube thumbnails will migrate without a ThumbHash "
                 "placeholder or content hash")
    elif db is not None:
        try:
            from youtube import is_youtube_url
            n = sum(1 for (u,) in db.conn.execute("SELECT url FROM embeds")
                    if is_youtube_url(u))
            if n:
                warn(f"{n} YouTube link(s) in the backup but no youtube_api_key set; "
                     "they will migrate as bare title cards (no player, no image)")
        except Exception:  # noqa: BLE001
            pass  # advisory only; never fail preflight on it

    # 8. Owner set + valid
    if not owner_id:
        bad("no guild owner set — pass `--owner <fluxer_user_id>` "
            "(or set FLUSHCORD_GUILD_OWNER_USER_ID)")
    else:
        ok(f"guild owner set ({owner_id})")

    if db is not None:
        db.close()
    if conn is not None:
        conn.close()

    print()
    if problems:
        print(f"\033[31mPreflight FAILED: {len(problems)} problem(s).\033[0m")
    elif warnings:
        print(f"\033[33mPreflight OK with {len(warnings)} warning(s).\033[0m")
    else:
        print("\033[32mPreflight OK.\033[0m")
    return problems, warnings


# --------------------------------------------------------------------------- #
# Migrator
# --------------------------------------------------------------------------- #

class Migrator:
    def __init__(self, cfg):
        self.cfg = cfg
        self.schema = Schema(cfg.schema_path)
        self.db = DiscordBackup(cfg.backup_db)
        self.kv = KvStore(self.schema, cfg.pg_dsn, cfg.kv_table)
        self.user_map = cfg.user_map
        self.s3 = S3Uploader(cfg) if cfg.upload_attachments else None
        self.guild_id = None
        self.owner_id = cfg.guild_owner_user_id or None
        # per-channel running state: channel_id -> (max_msg_id, max_bucket)
        self.channel_last = {}
        self.channel_buckets = {}  # channel_id -> set(bucket)
        # Native threads: ids of threads started from a message in their parent
        # (that message gets HAS_THREAD), and parent -> [(thread_id, name)] used
        # to point THREAD_CREATED messages at their thread.
        self._thread_source_ids = set()
        self._threads_by_parent_name = {}
        self._claimed_thread_created = set()
        # Custom emoji ids that are animated (for reaction rendering).
        self._animated_emoji_ids = {
            int(a["id"]) for a in self.db.server_assets("emoji")
            if self._is_animated_asset(a)
        }
        # Rewrites unicode emojis (content + reactions) to Fluxer's canonical
        # FE0F-qualified surrogate so they render as Twemoji sprites.
        emoji_data = cfg.emoji_data_path or default_emoji_data_path(cfg.schema_path)
        self._emoji = EmojiNormalizer.load(emoji_data)
        self._ffmpeg_ok = None  # lazily probed for video metadata
        # Tenor -> KLIPY GIF conversion (media stays on KLIPY's CDN, nothing
        # uploaded here). Disabled unless convert_gifs is on and a key is set.
        self._klipy = None
        if cfg.convert_gifs and cfg.klipy_api_key:
            self._klipy = KlipyClient(
                cfg.klipy_api_key,
                customer_id=cfg.klipy_customer_id or "flushcord",
                cache_path=cfg.klipy_cache_path or None,
                proxy_endpoint=cfg.media_proxy_endpoint or None,
                proxy_secret=cfg.media_proxy_secret or None,
            )
        elif cfg.convert_gifs:
            print("  ! convert_gifs is on but no KLIPY api key resolved; "
                  "Tenor embeds will be left as-is")
        self._gif_misses = []  # (message_id, tenor_url) with no KLIPY match
        # YouTube links -> real Fluxer video embeds (player + sized thumbnail),
        # rebuilt from the YouTube Data API like Fluxer's own unfurler. On when
        # a key is set; without media_proxy_* the thumbnail loses its ThumbHash.
        self._youtube = None
        if cfg.youtube_api_key:
            self._youtube = YouTubeClient(
                cfg.youtube_api_key,
                media_proxy_endpoint=cfg.media_proxy_endpoint or None,
                media_proxy_secret=cfg.media_proxy_secret or None,
                cache_path=cfg.youtube_cache_path or None,
            )
            if not (cfg.media_proxy_endpoint and cfg.media_proxy_secret):
                print("  ! youtube_api_key is set but media_proxy_* is not; "
                      "thumbnails will have no placeholder/content hash")
        self.stats = {"messages": 0, "attachments": 0, "reactions": 0,
                      "skipped": 0, "gifs": 0, "gif_misses": 0,
                      "youtube": 0, "youtube_misses": 0}
        self.progress = Progress()

    def close(self):
        self.db.close()
        self.kv.close()

    def map_user(self, discord_id):
        if discord_id is None:
            return None
        return self.user_map.get(int(discord_id))

    # -- guild / roles / members --------------------------------------------

    def migrate_guild(self):
        g = self.db.guild()
        if not g:
            sys.exit("No guild_profile row in backup.")
        self.guild_id = int(g["id"])
        if not self.owner_id:
            sys.exit(
                "No guild owner set. Pass --owner <fluxer_user_id> (the backup "
                "has no owner_id)."
            )
        row = {
            "guild_id": self.guild_id,
            "owner_id": self.owner_id,
            "name": g.get("name") or "Imported Server",
            "features": set(),
            "verification_level": 0,
            "mfa_level": 0,
            "nsfw_level": 0,
            "explicit_content_filter": 0,
            "default_message_notifications": 0,
            "afk_timeout": 300,
            "member_count": len(self.user_map),
            "version": 1,
        }
        self.kv.upsert("guilds", row)
        print(f"Guild '{row['name']}' ({self.guild_id}) -> owner {self.owner_id}")

    def migrate_roles(self):
        roles = self.db.roles()
        for r in roles:
            row = {
                "guild_id": self.guild_id,
                "role_id": int(r["id"]),
                "name": r.get("name") or "role",
                "permissions": int(r.get("permissions") or 0),
                "position": int(r.get("position") or 0),
                "color": int(r.get("color") or 0),
                "hoist": bool(r.get("hoist")),
                "hoist_position": int(r.get("position") or 0),
                "mentionable": bool(r.get("mentionable")),
                "version": 1,
            }
            self.kv.upsert("guild_roles", row)
        print(f"Migrated {len(roles)} roles")

    def migrate_members(self):
        join_ms = self.db.earliest_message_ms_by_author()
        guild_created_ms = snowflake_to_ms(self.guild_id)
        users = self.db.users()
        count = 0
        for u in users:
            fid = self.map_user(u["id"])
            if not fid:
                continue
            joined = join_ms.get(int(u["id"]), guild_created_ms)
            role_ids = set()
            raw_roles = u.get("roles")
            if raw_roles:
                try:
                    role_ids = {int(x) for x in json.loads(raw_roles)}
                except (ValueError, TypeError):
                    role_ids = set()
            member = {
                "guild_id": self.guild_id,
                "user_id": fid,
                "joined_at": joined,
                "nick": None,
                "role_ids": role_ids or None,
                "deaf": False,
                "mute": False,
                "version": 1,
            }
            self.kv.upsert("guild_members", member)
            self.kv.upsert(
                "guild_members_by_user_id",
                {"user_id": fid, "guild_id": self.guild_id},
            )
            count += 1
        self._invalidate_member_index(count)
        print(f"Migrated {count} guild members")

    def _invalidate_member_index(self, member_count):
        """Force Fluxer to rebuild the guild's member search index.

        The members page is served from a search index, not from
        `guild_members`: the app indexes each member as it joins
        (`addUserToGuild` -> `searchIndexService.indexMember`). Rows written
        straight into KV never pass through that, so migrated members would be
        missing from the page (and its role filters) even though the sidebar,
        which the gateway builds from `guild_members`, shows them.

        Fluxer self-heals — but only while the guild looks un-indexed:
        `guildMembersNeedReindexing()` (GuildMemberIndexingUtils.ts) is true
        exactly when `members_indexed_at` is unset, and the members-page
        controller then queues Fluxer's own `indexGuildMembers` job. Anything
        that already indexed this guild (e.g. opening the page mid-migration)
        stamps `members_indexed_at` and would otherwise pin the index to that
        stale snapshot forever. Clearing it re-arms the lazy re-index.
        """
        self.kv.patch(
            "guilds",
            {"guild_id": self.guild_id},
            {"member_count": member_count, "members_indexed_at": None},
        )

    # -- channels / threads -------------------------------------------------

    def _permission_overwrites(self, channel_id):
        perms = self.db.permissions(channel_id)
        if not perms:
            return None
        out = {}
        for p in perms:
            target = p.get("target_id")
            if target is None:
                continue
            ttype = 0 if (p.get("target_type") or "").lower() == "role" else 1
            out[int(target)] = {
                "type": ttype,
                "allow_": int(p.get("allow") or 0),
                "deny_": int(p.get("deny") or 0),
            }
        return out or None

    def _channel_category(self, discord_channel_id, channels_by_id):
        ch = channels_by_id.get(int(discord_channel_id))
        return ch.get("category_id") if ch else None

    @property
    def native_threads(self):
        return self.cfg.thread_mode == "native"

    def migrate_channels(self):
        channels = self.db.channels()
        channels_by_id = {int(c["id"]): c for c in channels}
        type_map = CHANNEL_TYPE_MAP if self.native_threads else FLAT_CHANNEL_TYPE_MAP
        self._fluxer_types = {}
        self._parent_configs = {}
        for c in channels:
            dtype = int(c.get("type") or 0)
            ftype = type_map.get(dtype, 0)
            self._fluxer_types[int(c["id"])] = ftype
            row = {
                "channel_id": int(c["id"]),
                "soft_deleted": False,
                "guild_id": self.guild_id,
                "type": ftype,
                "name": c.get("name"),
                "topic": c.get("topic"),
                "parent_id": int(c["category_id"]) if c.get("category_id") else None,
                "position": int(c.get("position") or 0),
                "nsfw": bool(c.get("nsfw")),
                "rate_limit_per_user": int(c.get("slowmode_delay") or 0),
                "bitrate": int(c.get("bitrate")) if c.get("bitrate") else None,
                "permission_overwrites": self._permission_overwrites(int(c["id"])),
                "version": 1,
            }
            self.kv.upsert("channels", row)
            # Mirrors ChannelDataRepository.afterWrite: thread-only channels
            # are indexed in their own table, not in channels_by_guild_id.
            index_table = (
                "thread_only_channels_by_guild"
                if ftype in THREAD_ONLY_CHANNEL_TYPES
                else "channels_by_guild_id"
            )
            self.kv.upsert(index_table, {"guild_id": self.guild_id, "channel_id": int(c["id"])})
            if self.native_threads:
                cfg_row = self._parent_config_row(c, ftype)
                if cfg_row:
                    self._parent_configs[int(c["id"])] = cfg_row
        print(f"Migrated {len(channels)} channels")

        if self.cfg.thread_mode == "native":
            self._migrate_threads_native(channels_by_id)
        elif self.cfg.thread_mode == "channel":
            self._migrate_threads_as_channels(channels_by_id)

    def _migrate_threads_as_channels(self, channels_by_id):
        threads = self.db.threads()
        for t in threads:
            parent_category = self._channel_category(t["parent_id"], channels_by_id)
            row = {
                "channel_id": int(t["id"]),
                "soft_deleted": False,
                "guild_id": self.guild_id,
                "type": 0,
                "name": f"{self.cfg.thread_name_prefix}{t.get('name') or 'thread'}",
                "parent_id": int(parent_category) if parent_category else None,
                "position": 0,
                "nsfw": False,
                "version": 1,
            }
            self.kv.upsert("channels", row)
            self.kv.upsert(
                "channels_by_guild_id",
                {"guild_id": self.guild_id, "channel_id": int(t["id"])},
            )
        if threads:
            print(f"Migrated {len(threads)} threads as channels")

    # -- native threads / forums ---------------------------------------------
    #
    # Mirrors ThreadRepository.create() (fluxer_api/src/api/channel/
    # repositories/ThreadRepository.ts) and ThreadCreationService: a thread is a
    # `channels` row (type 10/11/12) plus thread_state, threads_by_parent, the
    # active/archived index, members (+ by_user), stats and the parent's
    # thread_parent_config.has_threads.

    def _parent_config_row(self, c, ftype):
        """thread_parent_config row for a channel that can parent threads."""
        cid = int(c["id"])
        row = {"guild_id": self.guild_id, "channel_id": cid}
        auto = c.get("default_auto_archive_duration")
        if auto in THREAD_AUTO_ARCHIVE_DURATIONS:
            row["default_auto_archive_duration"] = int(auto)
        slow = c.get("default_thread_slowmode_delay")
        if slow:
            row["default_thread_rate_limit_per_user"] = int(slow)
        if ftype not in THREAD_ONLY_CHANNEL_TYPES:
            return row if len(row) > 2 else None

        tags = []
        for t in self.db.forum_tags(cid):
            emoji_id = int(t["emoji_id"]) if t.get("emoji_id") else None
            emoji_name = t.get("emoji_name")
            if emoji_name and not emoji_id:
                emoji_name = self._emoji.surrogate(emoji_name) or emoji_name
            tags.append({
                "id": int(t["id"]),
                "name": t.get("name") or "tag",
                "moderated": bool(t.get("moderated")),
                "emoji_id": emoji_id,
                "emoji_name": emoji_name,
            })
        row["available_tags"] = tags or None
        # Only the flags Fluxer lets a forum/media channel carry
        # (settableChannelFlags); REQUIRE_TAG needs a tag a non-moderator can use.
        settable = ChannelFlags.REQUIRE_TAG
        if ftype == 16:
            settable |= ChannelFlags.HIDE_MEDIA_DOWNLOAD_OPTIONS
        flags = int(c.get("flags") or 0) & settable
        if flags & ChannelFlags.REQUIRE_TAG and not any(not t["moderated"] for t in tags):
            flags &= ~ChannelFlags.REQUIRE_TAG
        row["flags"] = flags
        emoji = c.get("default_reaction_emoji")
        if emoji:
            try:
                e = json.loads(emoji) if isinstance(emoji, str) else emoji
                if e.get("id"):
                    row["default_reaction_emoji_id"] = int(e["id"])
                elif e.get("name"):
                    row["default_reaction_emoji_name"] = (
                        self._emoji.surrogate(e["name"]) or e["name"]
                    )
            except (ValueError, TypeError, AttributeError):
                pass
        if c.get("default_sort_order") is not None:
            row["default_sort_order"] = int(c["default_sort_order"])
        if ftype == 15 and c.get("default_layout") is not None:
            row["default_forum_layout"] = int(c["default_layout"])
        return row

    def _thread_type(self, thread, parent_ftype):
        """Fluxer thread type for a Discord thread under its mapped parent
        (publicThreadTypeFor / resolveTextThreadType): announcement threads
        need an announcement parent, which this tool maps to plain text."""
        if int(thread.get("type") or CHANNEL_PUBLIC_THREAD) == CHANNEL_PRIVATE_THREAD \
                and parent_ftype not in THREAD_ONLY_CHANNEL_TYPES:
            return CHANNEL_PRIVATE_THREAD
        return CHANNEL_PUBLIC_THREAD

    def _migrate_threads_native(self, channels_by_id):
        threads = self.db.threads()
        self._thread_source_ids = set()
        self._threads_by_parent_name = {}
        if not threads and not self._parent_configs:
            return

        prepared = []
        for t in threads:
            tid = int(t["id"])
            pid = int(t["parent_id"]) if t.get("parent_id") else None
            ptype = self._fluxer_types.get(pid)
            if ptype not in (CHANNEL_GUILD_TEXT, *THREAD_ONLY_CHANNEL_TYPES):
                print(f"  ! skipped thread {tid} ({t.get('name')!r}): parent {pid} "
                      "is not a text, forum or media channel in the backup")
                self.stats["skipped"] += 1
                continue
            prepared.append((t, tid, pid, ptype))

        # Last activity decides which threads stay active if the guild is over
        # Fluxer's active-thread cap (the cap is only enforced by the API).
        def last_activity(tid):
            r = self.db.conn.execute(
                "SELECT MAX(id) FROM messages WHERE channel_id = ?", (tid,)
            ).fetchone()
            return int(r[0]) if r and r[0] else tid

        active = [x for x in prepared if not x[0].get("archived")]
        overflow = set()
        if len(active) > MAX_ACTIVE_THREADS_PER_GUILD:
            active.sort(key=lambda x: last_activity(x[1]), reverse=True)
            overflow = {x[1] for x in active[MAX_ACTIVE_THREADS_PER_GUILD:]}
            print(f"  ! {len(active)} active threads exceed Fluxer's cap of "
                  f"{MAX_ACTIVE_THREADS_PER_GUILD}; importing the {len(overflow)} "
                  "least recently active as archived")

        pinned_forums = set()
        parents_with_threads = set()
        newest_in_forum = {}
        for t, tid, pid, ptype in prepared:
            force_archive = tid in overflow
            self._write_native_thread(t, tid, pid, ptype, force_archive,
                                      pinned_forums, newest_in_forum)
            parents_with_threads.add(pid)
            self._threads_by_parent_name.setdefault(pid, []).append(
                (tid, (t.get("name") or ""))
            )

        for pid in parents_with_threads:
            self._parent_configs.setdefault(
                pid, {"guild_id": self.guild_id, "channel_id": pid}
            )["has_threads"] = True
        for row in self._parent_configs.values():
            self.kv.upsert("thread_parent_config", row)
        # ThreadRepository.create(): a forum's last_message_id is the newest post.
        for pid, newest in newest_in_forum.items():
            self.kv.patch("channels", {"channel_id": pid, "soft_deleted": False},
                          {"last_message_id": newest})
        # Permissions are migrated verbatim from the backup (Discord's thread
        # permission bits equal Fluxer's), so mark them seeded exactly as guild
        # creation does; otherwise Fluxer would lazily rewrite every overwrite.
        now = _now()
        self.kv.upsert("guild_thread_state", {
            "guild_id": self.guild_id,
            "first_active_at": now,
            "perms_seeded_at": now,
        })
        print(f"Migrated {len(prepared)} threads natively "
              f"({len(self._parent_configs)} thread-capable channels)")

    def _write_native_thread(self, t, tid, pid, ptype, force_archive,
                             pinned_forums, newest_in_forum):
        ttype = self._thread_type(t, ptype)
        is_private = ttype == CHANNEL_PRIVATE_THREAD
        forum_post = ptype in THREAD_ONLY_CHANNEL_TYPES
        created_at = _ms_to_dt(snowflake_to_ms(tid))
        authors = self.db.thread_authors(tid)

        # Owner: backup owner_id -> mapped Fluxer user -> first mapped poster
        # -> guild owner (Fluxer requires an owner_id).
        owner = self.map_user(t.get("owner_id"))
        if owner is None:
            for author_id, _ in authors:
                owner = self.map_user(author_id)
                if owner:
                    break
        owner = owner or self.owner_id

        # Members: the owner, plus everyone who posted (Fluxer auto-joins a
        # sender with HAS_INTERACTED), each joined at their first message.
        members = {owner: created_at}
        for author_id, first_id in authors:
            fid = self.map_user(author_id)
            if fid and fid not in members:
                members[fid] = _ms_to_dt(snowflake_to_ms(first_id))
        member_ids = list(members)[:MAX_THREAD_MEMBERS]

        has_starter = forum_post or self.db.message_exists(pid, tid)
        if not forum_post and has_starter:
            self._thread_source_ids.add(tid)

        archived = bool(t.get("archived")) or force_archive
        archive_ts = parse_ts(t["archive_timestamp"]) if t.get("archive_timestamp") else created_at
        if force_archive and not t.get("archived"):
            last = self.db.conn.execute(
                "SELECT MAX(id) FROM messages WHERE channel_id = ?", (tid,)
            ).fetchone()[0]
            archive_ts = _ms_to_dt(snowflake_to_ms(last or tid))
        auto = t.get("auto_archive_duration")
        auto = int(auto) if auto in THREAD_AUTO_ARCHIVE_DURATIONS else DEFAULT_THREAD_AUTO_ARCHIVE_DURATION

        flags = 0
        if forum_post and (int(t.get("flags") or 0) & ChannelFlags.PINNED) \
                and not archived and pid not in pinned_forums:
            flags = ChannelFlags.PINNED  # Fluxer allows one pinned post per forum
            pinned_forums.add(pid)
            self.kv.upsert("forum_pinned_thread", {"parent_id": pid, "thread_id": tid})

        applied = []
        if forum_post and t.get("applied_tags"):
            try:
                known = {x["id"] for x in
                         (self._parent_configs.get(pid, {}).get("available_tags") or [])}
                applied = [int(x) for x in json.loads(t["applied_tags"]) if int(x) in known]
            except (ValueError, TypeError):
                applied = []
            applied = applied[:MAX_APPLIED_TAGS_PER_THREAD]

        self.kv.upsert("channels", {
            "channel_id": tid,
            "soft_deleted": False,
            "guild_id": self.guild_id,
            "type": ttype,
            "name": (t.get("name") or "thread")[:100],
            "parent_id": pid,
            "owner_id": owner,
            "rate_limit_per_user": int(t.get("slowmode_delay") or 0),
            "version": 1,
        })
        self.kv.upsert("threads_by_parent", {
            "parent_id": pid, "thread_id": tid, "guild_id": self.guild_id, "type": ttype,
        })
        state = {
            "thread_id": tid,
            "guild_id": self.guild_id,
            "parent_id": pid,
            "type": ttype,
            "archived": archived,
            "locked": bool(t.get("locked")),
            "invitable": (True if t.get("invitable") is None else bool(t["invitable"]))
            if is_private else None,
            "auto_archive_duration": auto,
            "archive_timestamp": archive_ts,
            "created_at": created_at,
            "flags": flags,
            "applied_tags": applied or None,
            "member_count": len(member_ids),
            # previewWith([], ids): newest first, capped
            "member_ids_preview": (list(reversed(member_ids))[:THREAD_MEMBER_IDS_PREVIEW_SIZE]
                                   or None),
            "has_starter": has_starter,
            "state_version": 1,
        }
        self.kv.upsert("thread_state", state)
        count = self.db.thread_message_count(tid)
        self.kv.upsert("thread_stats", {
            "thread_id": tid, "message_count": count, "total_message_sent": count,
        })
        for uid in member_ids:
            self.kv.upsert("thread_members", {
                "thread_id": tid, "user_id": uid, "guild_id": self.guild_id,
                "parent_id": pid, "join_timestamp": members[uid],
                "flags": ThreadMemberFlags.HAS_INTERACTED, "muted": False,
            })
            self.kv.upsert("thread_members_by_user", {
                "user_id": uid, "guild_id": self.guild_id, "parent_id": pid,
                "is_private": is_private, "thread_id": tid,
            })
        if archived:
            self.kv.upsert("archived_threads_by_parent", {
                "parent_id": pid, "is_private": is_private,
                "archive_timestamp": archive_ts, "thread_id": tid,
                "guild_id": self.guild_id,
            })
        else:
            self.kv.upsert("active_threads_by_guild", {
                "guild_id": self.guild_id, "thread_id": tid, "parent_id": pid, "type": ttype,
            })
        if forum_post and tid > newest_in_forum.get(pid, 0):
            newest_in_forum[pid] = tid

    # -- emojis / stickers --------------------------------------------------

    @staticmethod
    def _is_animated_asset(asset):
        ct = (asset.get("content_type") or "").lower()
        fn = (asset.get("filename") or "").lower()
        return ct in ("image/gif", "image/apng") or fn.endswith((".gif", ".apng"))

    def _asset_path(self, asset):
        """Resolve the on-disk file for a server_assets row."""
        fn = asset.get("filename")
        if fn:
            p = os.path.join(self.cfg.backup_dir, "server_assets", fn)
            if os.path.exists(p):
                return p
        return None

    def migrate_emojis(self):
        assets = self.db.server_assets("emoji")
        creator = self.owner_id
        count = 0
        for a in assets:
            emoji_id = int(a["id"])
            animated = self._is_animated_asset(a)
            path = self._asset_path(a)
            if self.s3:
                if not path:
                    continue
                key = f"emojis/{emoji_id}"
                try:
                    if not self.s3.exists(key):
                        self.s3.upload_file(path, key, a.get("content_type"))
                except Exception as e:  # noqa: BLE001
                    print(f"  ! emoji upload failed ({a.get('name')}): {e}")
                    continue
            base = {
                "guild_id": self.guild_id,
                "emoji_id": emoji_id,
                "name": a.get("name") or "emoji",
                "creator_id": creator,
                "animated": animated,
                "nsfw": False,
            }
            self.kv.upsert("guild_emojis", {**base, "version": 1})
            self.kv.upsert("guild_emojis_by_emoji_id", base)
            count += 1
        if assets:
            print(f"Migrated {count} emojis")

    def migrate_stickers(self):
        assets = self.db.server_assets("sticker")
        creator = self.owner_id
        count = 0
        for a in assets:
            sticker_id = int(a["id"])
            animated = self._is_animated_asset(a)
            path = self._asset_path(a)
            if self.s3:
                if not path:
                    continue
                key = f"stickers/{sticker_id}"
                try:
                    if not self.s3.exists(key):
                        self.s3.upload_file(path, key, a.get("content_type"))
                except Exception as e:  # noqa: BLE001
                    print(f"  ! sticker upload failed ({a.get('name')}): {e}")
                    continue
            base = {
                "guild_id": self.guild_id,
                "sticker_id": sticker_id,
                "name": a.get("name") or "sticker",
                "creator_id": creator,
                "animated": animated,
                "nsfw": False,
                "tags": [],
                "description": None,
            }
            self.kv.upsert("guild_stickers", {**base, "version": 1})
            self.kv.upsert("guild_stickers_by_sticker_id", base)
            count += 1
        if assets:
            print(f"Migrated {count} stickers")

    # -- messages -----------------------------------------------------------

    def _rewrite_mentions(self, content):
        """Rewrite ``<@discord_id>`` / ``<@!discord_id>`` tokens to
        ``<@fluxer_id>`` so the client can resolve them. Unmapped users and
        role/channel mentions (whose IDs are reused verbatim) are left as-is."""
        if not content:
            return content

        def repl(match):
            fid = self.map_user(int(match.group(1)))
            return f"<@{fid}>" if fid else match.group(0)

        return MENTION_USER_RE.sub(repl, content)

    def _build_mentions(self, content):
        mention_users, mention_roles, mention_channels = set(), set(), set()
        for m in MENTION_USER_RE.findall(content or ""):
            fid = self.map_user(int(m))
            if fid:
                mention_users.add(fid)
        for m in MENTION_ROLE_RE.findall(content or ""):
            mention_roles.add(int(m))
        for m in MENTION_CHANNEL_RE.findall(content or ""):
            mention_channels.add(int(m))
        mention_everyone = "@everyone" in (content or "") or "@here" in (content or "")
        return mention_users, mention_roles, mention_channels, mention_everyone

    def _build_attachments(self, message_id, channel_id):
        atts = self.db.attachments(message_id)
        result = []
        for a in atts:
            filename = a.get("filename") or "file"
            attachment_id = int(a["id"])
            local_hash = a.get("local_hash")
            content_type = a.get("content_type")

            # Resolve the backed-up file on disk (needed for upload and to read
            # image dimensions), independent of whether we upload this run.
            media = self.db.media(local_hash) if local_hash else None
            local_path = None
            if media and media.get("local_path"):
                p = os.path.join(self.cfg.backup_dir, media["local_path"])
                if os.path.exists(p):
                    local_path = p
            if not content_type and media:
                content_type = media.get("content_type")
            # Fluxer's search serializer calls contentType.trim() unconditionally,
            # so a null content type crashes message indexing. Guess from the
            # filename and fall back to a generic binary type — never null.
            if not content_type:
                content_type = mimetypes.guess_type(filename)[0] or "application/octet-stream"
            # MIDI is tagged audio/* (e.g. audio/sp-midi) but browsers can't play
            # it, so Fluxer's content-type-driven audio player would render dead.
            # Demote to a generic type so it shows as a downloadable file instead.
            if filename.lower().endswith(self._MIDI_EXTS) or "midi" in content_type.lower():
                content_type = "application/octet-stream"

            # Upload to the CDN when enabled; skip the attachment entirely if
            # its file is unavailable, to avoid a broken link.
            if self.s3:
                if not local_path:
                    self.stats["skipped"] += 1
                    continue
                key = cdn_key(channel_id, attachment_id, filename)
                try:
                    if not self.s3.exists(key):
                        self.s3.upload_file(local_path, key, content_type)
                except Exception as e:  # noqa: BLE001
                    print(f"  ! attachment upload failed ({filename}): {e}")
                    self.stats["skipped"] += 1
                    continue

            meta = self._image_meta(local_path, content_type)
            if not meta:
                meta = self._video_meta(local_path, content_type)
            flags = 0
            if meta.get("animated"):
                flags |= MessageAttachmentFlags.IS_ANIMATED
            att = {
                "attachment_id": attachment_id,
                "filename": filename,
                "title": filename,
                "size": int(a.get("size") or 0),
                "content_type": content_type,
                "content_hash": local_hash,
                "flags": flags,
                "nsfw": False,
            }
            if meta.get("width") and meta.get("height"):
                att["width"] = meta["width"]
                att["height"] = meta["height"]
            if meta.get("placeholder"):
                att["placeholder"] = meta["placeholder"]
            if meta.get("duration") is not None:
                att["duration"] = meta["duration"]
            result.append(att)
            self.stats["attachments"] += 1
        return result

    _IMAGE_EXTS = (".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".tiff")
    _MIDI_EXTS = (".mid", ".midi", ".kar", ".rmi")

    def _image_meta(self, local_path, content_type):
        """Return image metadata {width, height, placeholder, animated}.

        Dimensions and the lazy-load placeholder (a ThumbHash) are not in the
        backup, so we derive them from the file on disk. Used by the client to
        render inline image previews with a blur-up placeholder.
        """
        if not local_path:
            return {}
        ct = (content_type or "").lower()
        is_image = ct.startswith("image/") or local_path.lower().endswith(self._IMAGE_EXTS)
        if not is_image or ct == "image/svg+xml":
            return {}
        try:
            from PIL import Image
            from thumbhash import image_placeholder
            with Image.open(local_path) as im:
                meta = {
                    "width": int(im.width),
                    "height": int(im.height),
                    "animated": bool(getattr(im, "is_animated", False)),
                }
                try:
                    meta["placeholder"] = image_placeholder(im)
                except Exception:  # noqa: BLE001
                    pass
                return meta
        except Exception:  # noqa: BLE001
            return {}

    _VIDEO_EXTS = (".mp4", ".mov", ".webm", ".mkv", ".m4v", ".avi", ".gif")

    def _ffmpeg_available(self):
        """Whether ffprobe/ffmpeg are on PATH (cached; warns once if missing)."""
        if self._ffmpeg_ok is None:
            self._ffmpeg_ok = bool(shutil.which("ffprobe") and shutil.which("ffmpeg"))
            if not self._ffmpeg_ok:
                print("  ! ffprobe/ffmpeg not found — videos migrate as plain "
                      "file attachments (no inline player). Install ffmpeg for parity.")
        return self._ffmpeg_ok

    def _video_meta(self, local_path, content_type):
        """Return video metadata {width, height, duration, placeholder}.

        Fluxer renders the inline video player only when width/height are
        present; duration and a ThumbHash placeholder (from a representative
        frame) bring it to parity with a natively-uploaded video. Needs
        ffprobe/ffmpeg; returns {} when unavailable or not a video.
        """
        if not local_path:
            return {}
        ct = (content_type or "").lower()
        is_video = ct.startswith("video/") or local_path.lower().endswith(self._VIDEO_EXTS)
        if not is_video or not self._ffmpeg_available():
            return {}
        try:
            out = subprocess.run(
                ["ffprobe", "-v", "error", "-select_streams", "v:0",
                 "-show_entries", "stream=width,height:format=duration",
                 "-of", "json", local_path],
                capture_output=True, text=True, timeout=60,
            )
            probe = json.loads(out.stdout or "{}")
            stream = (probe.get("streams") or [{}])[0]
            width, height = stream.get("width"), stream.get("height")
            if not width or not height:
                return {}
            meta = {"width": int(width), "height": int(height)}
            dur = (probe.get("format") or {}).get("duration")
            if dur is not None:
                meta["duration"] = round(float(dur))
            placeholder = self._video_placeholder(local_path)
            if placeholder:
                meta["placeholder"] = placeholder
            return meta
        except Exception:  # noqa: BLE001
            return {}

    def _video_placeholder(self, local_path):
        """ThumbHash from a representative video frame, or None on failure."""
        try:
            from PIL import Image
            from thumbhash import image_placeholder
            out = subprocess.run(
                ["ffmpeg", "-v", "error", "-i", local_path, "-vf", "thumbnail",
                 "-frames:v", "1", "-f", "image2pipe", "-vcodec", "png", "-"],
                capture_output=True, timeout=120,
            )
            if not out.stdout:
                return None
            with Image.open(io.BytesIO(out.stdout)) as im:
                return image_placeholder(im)
        except Exception:  # noqa: BLE001
            return None

    def _build_embeds(self, message_id, content):
        """Build a message's embeds. Returns ``(embeds, content)``.

        Tenor GIF embeds are converted to KLIPY ``gifv`` embeds when possible
        (and the Tenor link in the content is swapped for the KLIPY share URL);
        an unmatched Tenor embed is left as its original rich embed and logged.

        YouTube embeds are rebuilt from the YouTube Data API into the ``video``
        embed Fluxer would have produced. Only links Discord itself unfurled are
        touched: a link Discord left bare (``<url>`` syntax, a code block, a dead
        video) has no embed row, and stays bare. A video that no longer resolves
        keeps its original rich embed and is logged.
        """
        out = []
        for e in self.db.embeds(message_id):
            url = e.get("url") or ""
            if self._klipy and is_tenor_view_url(url):
                gifv = self._klipy.resolve_embed(url)
                if gifv:
                    content = replace_tenor_link(content, url, gifv["url"])
                    out.append(gifv)
                    self.stats["gifs"] += 1
                    continue
                self.stats["gif_misses"] += 1
                self._gif_misses.append((message_id, url))
            elif self._youtube and is_youtube_url(url):
                video = self._youtube.resolve_embed(url)
                if video:
                    out.append(video)
                    self.stats["youtube"] += 1
                    continue
                self.stats["youtube_misses"] += 1
            out.append(self._rich_embed(e))
        return out, content

    def _rich_embed(self, e):
        embed = {"type": "rich"}
        if e.get("title"):
            embed["title"] = e["title"]
        if e.get("description"):
            embed["description"] = e["description"]
        if e.get("url"):
            embed["url"] = e["url"]
        if e.get("color") is not None:
            embed["color"] = int(e["color"])
        if e.get("timestamp"):
            embed["timestamp"] = parse_ts(e["timestamp"])
        if e.get("author_name"):
            embed["author"] = {
                "name": e.get("author_name"),
                "url": e.get("author_url"),
                "icon_url": e.get("author_icon_url"),
            }
        if e.get("footer_text"):
            embed["footer"] = {
                "text": e.get("footer_text"),
                "icon_url": e.get("footer_icon_url"),
            }
        if e.get("image_url"):
            embed["image"] = {"url": e["image_url"], "flags": 0}
        if e.get("thumbnail_url"):
            embed["thumbnail"] = {"url": e["thumbnail_url"], "flags": 0}
        if e.get("fields"):
            try:
                fields = json.loads(e["fields"])
                embed["fields"] = [
                    {
                        "name": f.get("name"),
                        "value": f.get("value"),
                        "inline": bool(f.get("inline")),
                    }
                    for f in fields
                ]
            except (ValueError, TypeError):
                pass
        return embed

    def _build_stickers(self, message_id):
        rows = self.db.stickers(message_id)
        out = []
        for s in rows:
            out.append({
                "sticker_id": int(s["sticker_id"]),
                "name": s.get("name"),
                "format_type": int(s.get("format_type") or 1),
                "animated": False,
                "nsfw": False,
            })
        return out

    def migrate_messages(self):
        channels = self.db.distinct_message_channels()
        names = {int(c["id"]): c.get("name") for c in self.db.channels()}
        thread_ids = set()
        for t in self.db.threads():
            names[int(t["id"])] = t.get("name")
            thread_ids.add(int(t["id"]))
        progress = self.progress
        progress.begin_messages(self.db.message_count())
        print(f"== messages: {progress.total:,} across {len(channels)} channels")
        for ci, channel_id in enumerate(channels, 1):
            channel_id = int(channel_id)
            msgs = self.db.messages(channel_id)
            kind = "thread" if channel_id in thread_ids else "channel"
            label = f"{kind} #{names.get(channel_id) or channel_id}"
            progress.set_phase(label)
            print(f"[{ci}/{len(channels)}] {label}: starting, {len(msgs):,} messages")
            started = time.monotonic()
            last_log = started
            buckets = set()
            for mi, m in enumerate(msgs, 1):
                try:
                    self._migrate_one_message(m, channel_id, buckets)
                except psycopg2.Error:
                    # A DB error poisons the transaction; the channel's writes
                    # can't be salvaged, so abort and let the caller roll back.
                    raise
                except Exception as e:  # noqa: BLE001
                    # Malformed source row: log, skip, keep going.
                    print(f"  ! skipped message {m.get('id')}: {e}")
                    self.stats["skipped"] += 1
                progress.advance()
                # Big channels: a line every ~10s so a long one doesn't look hung.
                now = time.monotonic()
                if now - last_log >= 10 and mi < len(msgs):
                    last_log = now
                    print(f"  {label}: {mi:,}/{len(msgs):,}")
            # Record bucket index rows for this channel.
            for b in buckets:
                self.kv.upsert(
                    "channel_message_buckets",
                    {"channel_id": channel_id, "bucket": b, "updated_at": _now()},
                )
            self.kv.commit()
            if self._klipy:
                self._klipy.save_cache()  # persist resolutions incrementally
            print(f"[{ci}/{len(channels)}] {label}: done, {len(msgs):,} messages "
                  f"in {time.monotonic() - started:.1f}s")
            progress.log_plain()
        progress.set_phase("finalizing channel state")
        self._finalize_channel_state()

    def _migrate_one_message(self, m, channel_id, buckets):
        author_fid = self.map_user(m.get("author_id"))
        if author_fid is None:
            if self.cfg.unmapped_author_mode == "owner":
                author_fid = self.owner_id
            else:
                self.stats["skipped"] += 1
                return
        message_id = int(m["id"])
        mtype = int(m.get("type") or 0)
        if self.native_threads and mtype == MESSAGE_TYPE_THREAD_STARTER:
            # Fluxer derives a thread's starter message from the thread id
            # (ThreadMessageResponses.getStarter); storing one 500s the fetch.
            return
        thread_created_ref = None
        if self.native_threads and mtype == MESSAGE_TYPE_THREAD_CREATED:
            thread_created_ref = self._thread_for_created_message(m, channel_id)
            if thread_created_ref is None:
                self.stats["skipped"] += 1  # thread not in the backup
                return
        bucket = make_bucket(message_id)
        buckets.add(bucket)
        content = m.get("content") or ""
        mu, mr, mc, me = self._build_mentions(content)
        content = self._rewrite_mentions(content)
        content = self._emoji.qualify(content)
        attachments = self._build_attachments(message_id, channel_id)
        embeds, content = self._build_embeds(message_id, content)
        stickers = self._build_stickers(message_id)
        pinned = parse_ts(m["timestamp"]) if m.get("is_pinned") else None

        message_reference = None
        if m.get("message_reference"):
            message_reference = {
                "channel_id": channel_id,
                "message_id": int(m["message_reference"]),
                "guild_id": self.guild_id,
                "type": 0,
            }

        if thread_created_ref is not None:
            # createThreadCreatedMessage(): points at the thread channel, no message.
            message_reference = {
                "channel_id": thread_created_ref,
                "message_id": None,
                "guild_id": self.guild_id,
                "type": 0,
            }

        reaction_rows = self._reaction_rows(message_id)
        has_reaction = bool(reaction_rows)

        row = {
            "channel_id": channel_id,
            "bucket": bucket,
            "message_id": message_id,
            "author_id": author_fid,
            "type": coerce_message_type(m.get("type"), self.native_threads),
            "content": content,
            "edited_timestamp": None,
            "pinned_timestamp": pinned,
            "flags": ServerMessageFlags.HAS_THREAD
            if message_id in self._thread_source_ids else 0,
            "mention_everyone": me,
            "mention_users": mu or None,
            "mention_roles": mr or None,
            "mention_channels": mc or None,
            "attachments": attachments or None,
            "embeds": embeds or None,
            "sticker_items": stickers or None,
            "message_reference": message_reference,
            "has_reaction": has_reaction,
            "version": 1,
        }
        self.kv.upsert("messages", row)
        self.kv.upsert(
            "messages_by_author_id_v2",
            {"author_id": author_fid, "channel_id": channel_id, "message_id": message_id},
        )
        if pinned:
            self.kv.upsert(
                "channel_pins",
                {"channel_id": channel_id, "message_id": message_id, "pinned_timestamp": pinned},
            )
        for att in attachments:
            self.kv.upsert(
                "attachment_lookup",
                {
                    "channel_id": channel_id,
                    "attachment_id": att["attachment_id"],
                    "filename": att["filename"],
                    "message_id": message_id,
                },
            )
        if reaction_rows:
            self._write_reactions(reaction_rows, channel_id, bucket, message_id, m)

        # Track channel last-message / buckets.
        prev_id, _ = self.channel_last.get(channel_id, (0, 0))
        if message_id > prev_id:
            self.channel_last[channel_id] = (message_id, bucket)
        self.stats["messages"] += 1

    def _thread_for_created_message(self, m, channel_id):
        """Thread a THREAD_CREATED message announces. Discord's reference (the
        thread channel) isn't kept in the backup, so match by name: the newest
        not-yet-claimed thread of this channel with that name created before
        the message."""
        message_id = int(m["id"])
        name = (m.get("content") or "")
        best = None
        for tid, tname in self._threads_by_parent_name.get(channel_id, []):
            if tname == name and tid <= message_id \
                    and tid not in self._claimed_thread_created \
                    and (best is None or tid > best):
                best = tid
        if best is not None:
            self._claimed_thread_created.add(best)
        return best

    def _reaction_rows(self, message_id):
        """Resolve the per-user reaction rows to write for a message.

        'real'  : one row per (emoji, mapped reactor) from the backup's
                  user_ids (unmapped reactors are dropped).
        'owner' : one row per emoji attributed to the guild owner (legacy,
                  for backups that lack reactor ids).
        'skip'  : none.
        Returns a list of (emoji_id, emoji_name, user_id, animated).
        """
        mode = self.cfg.reaction_mode
        if mode == "skip":
            return []
        rows = []
        for r in self.db.reactions(message_id):
            emoji_id = int(r["emoji_id"]) if r.get("emoji_id") else 0
            emoji_name = r.get("emoji_name") or ""
            animated = emoji_id in self._animated_emoji_ids
            # Built-in (unicode) reactions: store Fluxer's canonical surrogate
            # (FE0F-qualified) so they render and match the native picker, e.g.
            # bare "🗣" -> "🗣️".
            if not emoji_id:
                emoji_name = self._emoji.surrogate(emoji_name) or emoji_name
            if mode == "owner":
                if self.owner_id:
                    rows.append((emoji_id, emoji_name, self.owner_id, animated))
                continue
            # 'real': map each reacting Discord user to its Fluxer id.
            raw = r.get("user_ids")
            if not raw:
                continue
            try:
                dids = json.loads(raw)
            except (ValueError, TypeError):
                continue
            for did in dids:
                fid = self.map_user(did)
                if fid:
                    rows.append((emoji_id, emoji_name, fid, animated))
        return rows

    def _write_reactions(self, reaction_rows, channel_id, bucket, message_id, m):
        created = parse_ts(m["timestamp"])
        for emoji_id, emoji_name, user_id, animated in reaction_rows:
            self.kv.upsert(
                "message_reactions",
                {
                    "channel_id": channel_id,
                    "bucket": bucket,
                    "message_id": message_id,
                    "emoji_id": emoji_id,
                    "emoji_name": emoji_name,
                    "user_id": user_id,
                    "emoji_animated": animated,
                    "created_at": created,
                },
            )
            self.stats["reactions"] += 1

    def _finalize_channel_state(self):
        for channel_id, (last_id, last_bucket) in self.channel_last.items():
            created_bucket = make_bucket(channel_id)
            self.kv.patch(
                "channel_state",
                {"channel_id": channel_id},
                {
                    "created_bucket": created_bucket,
                    "has_messages": True,
                    "last_message_id": last_id,
                    "last_message_bucket": last_bucket,
                    "updated_at": _now(),
                },
            )
            self.kv.patch(
                "channels",
                {"channel_id": channel_id, "soft_deleted": False},
                {"last_message_id": last_id},
            )
        self.kv.commit()
        print(f"Finalized channel_state for {len(self.channel_last)} channels")

    def run(self):
        self.progress.start()
        try:
            self._run()
        finally:
            self.progress.stop()

    def _run(self):
        if self.s3:
            self.s3.ensure_bucket()
        for label, step in (
            ("guild", self.migrate_guild),
            ("roles", self.migrate_roles),
            ("members", self.migrate_members),
            ("channels", self.migrate_channels),
            ("emojis", self.migrate_emojis),
            ("stickers", self.migrate_stickers),
        ):
            self.progress.set_phase(f"setting up: {label}")
            print(f"== {label}")
            step()
        self.kv.commit()
        self.migrate_messages()
        if self._klipy:
            self._klipy.save_cache()
            print(f"KLIPY: {self.stats['gifs']} GIFs converted, "
                  f"{self.stats['gif_misses']} unmatched "
                  f"({self._klipy.api_calls} API calls)")
            self._report_gif_misses()
        if self._youtube:
            self._youtube.save_cache()
            print(f"YouTube: {self.stats['youtube']} embeds rebuilt, "
                  f"{self.stats['youtube_misses']} unresolved "
                  f"({self._youtube.api_calls} API calls)")
        print("\nDone. Stats:", json.dumps(self.stats))

    def _report_gif_misses(self):
        """List Tenor embeds that found no KLIPY match (their link is kept)."""
        if not self._gif_misses:
            return
        # Dedupe by URL; several messages often share the same GIF.
        urls = sorted({url for _, url in self._gif_misses})
        print(f"  {len(urls)} distinct Tenor GIF(s) with no KLIPY match "
              f"(link left intact):")
        for url in urls[:50]:
            print(f"    - {url}")
        if len(urls) > 50:
            print(f"    ... and {len(urls) - 50} more")

    # -- purge (reset for a clean re-run) -----------------------------------

    # Tables keyed within the guild; deleted by guild_id.
    _PURGE_GUILD_TABLES = [
        "guilds", "guild_roles", "guild_members", "guild_members_by_user_id",
        "channels", "channels_by_guild_id",
        # native threads / forums
        "thread_only_channels_by_guild", "thread_parent_config", "thread_state",
        "threads_by_parent", "active_threads_by_guild",
        "archived_threads_by_parent", "thread_members",
        "thread_members_by_user", "guild_thread_state",
    ]
    # Tables keyed per channel/message; deleted by channel_id of our channels.
    _PURGE_CHANNEL_TABLES = [
        "messages", "messages_by_author_id_v2", "channel_state",
        "channel_message_buckets", "channel_pins", "attachment_lookup",
        "message_reactions", "channel_empty_buckets",
    ]

    def purge(self, purge_s3=False, dry_run=False):
        """Delete everything this migration created for the guild, scoped so
        that other guilds, manually-created emojis/stickers, and unrelated
        messages are left untouched. Idempotent; safe to run before a re-run.
        """
        guild = self.db.guild()
        if not guild:
            sys.exit("No guild_profile row in backup.")
        gid = str(int(guild["id"]))
        channel_ids = [str(int(c["id"])) for c in self.db.channels()]
        channel_ids += [str(int(t["id"])) for t in self.db.threads()]
        emoji_ids = [str(int(a["id"])) for a in self.db.server_assets("emoji")]
        sticker_ids = [str(int(a["id"])) for a in self.db.server_assets("sticker")]

        print(f"Purging guild {gid}: {len(channel_ids)} channels, "
              f"{len(emoji_ids)} emojis, {len(sticker_ids)} stickers"
              + (" (dry-run)" if dry_run else ""))
        tbl = self.kv._ident
        total = 0
        with self.kv.conn.cursor() as cur:
            def run_delete(table, field, value, array=False):
                nonlocal total
                op = "= ANY(%s)" if array else "= %s"
                cur.execute(
                    f"DELETE FROM {tbl} WHERE table_name = %s "
                    f"AND row_data->'{field}'->>'value' {op}",
                    (table, value),
                )
                total += cur.rowcount
                if cur.rowcount:
                    print(f"  {table}: {cur.rowcount}")

            for t in self._PURGE_GUILD_TABLES:
                run_delete(t, "guild_id", gid)
            # Emoji/sticker: scope to the backup's asset IDs so manually-added
            # assets in the same guild are preserved.
            if emoji_ids:
                for t in ("guild_emojis", "guild_emojis_by_emoji_id"):
                    run_delete(t, "emoji_id", emoji_ids, array=True)
            if sticker_ids:
                for t in ("guild_stickers", "guild_stickers_by_sticker_id"):
                    run_delete(t, "sticker_id", sticker_ids, array=True)
            if channel_ids:
                for t in self._PURGE_CHANNEL_TABLES:
                    run_delete(t, "channel_id", channel_ids, array=True)
                # Thread tables without a guild_id / channel_id column.
                run_delete("thread_stats", "thread_id", channel_ids, array=True)
                run_delete("forum_pinned_thread", "parent_id", channel_ids, array=True)

        print(f"Total rows deleted: {total}")
        if dry_run:
            self.kv.rollback()
            print("Dry run: rolled back (nothing actually deleted).")
        else:
            self.kv.commit()

        if purge_s3 and not dry_run:
            s3 = self.s3 or S3Uploader(self.cfg)
            removed = 0
            for cid in channel_ids:
                removed += s3.delete_prefix(f"attachments/{cid}/")
            for eid in emoji_ids:
                s3.delete_key(f"emojis/{eid}")
            for sid in sticker_ids:
                s3.delete_key(f"stickers/{sid}")
            print(f"S3 objects deleted: {removed} attachments + "
                  f"{len(emoji_ids)} emojis + {len(sticker_ids)} stickers")


def _now():
    from datetime import datetime, timezone
    return datetime.now(timezone.utc)


def _ms_to_dt(ms):
    from datetime import datetime, timezone
    return datetime.fromtimestamp(ms / 1000, tz=timezone.utc)


# --------------------------------------------------------------------------- #
# Verify
# --------------------------------------------------------------------------- #

def verify(cfg):
    db = DiscordBackup(cfg.backup_db)
    print("Discord backup counts:")
    print("  messages   :", db.message_count())
    print("  channels   :", len(db.channels()))
    print("  threads    :", len(db.threads()))
    print("  roles      :", len(db.roles()))
    print("  users      :", len(db.users()))
    db.close()
    schema = Schema(cfg.schema_path)
    kv = KvStore(schema, cfg.pg_dsn, cfg.kv_table)
    with kv.conn.cursor() as cur:
        for table in ("messages", "channels", "guild_members", "guild_roles",
                      "message_reactions", "attachment_lookup", "thread_state",
                      "thread_only_channels_by_guild"):
            cur.execute(
                f"SELECT count(*) FROM {kv._ident} WHERE table_name = %s", (table,)
            )
            print(f"  Fluxer {table:18}:", cur.fetchone()[0])
    kv.close()


def reindex_members(cfg):
    """Re-arm Fluxer's member search index for an already-migrated guild.

    Same repair as `_invalidate_member_index`, for instances migrated before
    this existed (or indexed mid-migration): clears `members_indexed_at` and
    resets `member_count` from the rows actually present. Fluxer queues its own
    `indexGuildMembers` job the next time someone opens the members page.
    """
    schema = Schema(cfg.schema_path)
    kv = KvStore(schema, cfg.pg_dsn, cfg.kv_table)
    with kv.conn.cursor() as cur:
        cur.execute(
            f"SELECT row_data FROM {kv._ident} WHERE table_name = 'guilds'"
        )
        guilds = [r[0] for r in cur.fetchall()]
        cur.execute(
            f"SELECT row_data FROM {kv._ident} WHERE table_name = 'guild_members'"
        )
        members = [r[0] for r in cur.fetchall()]
    if not guilds:
        kv.close()
        sys.exit("No guilds row in Fluxer — nothing to re-index.")
    for g in guilds:
        guild_id = _tagged_int(g.get("guild_id"))
        count = sum(1 for m in members
                    if _tagged_int(m.get("guild_id")) == guild_id)
        was = g.get("members_indexed_at")
        kv.patch(
            "guilds",
            {"guild_id": guild_id},
            {"member_count": count, "members_indexed_at": None},
        )
        print(f"Guild {guild_id}: member_count -> {count}, cleared "
              f"members_indexed_at ({'was ' + str(_tagged_value(was)) if was else 'was already unset'})")
    kv.commit()
    kv.close()
    print("\nOpen the guild's members page in Fluxer to trigger the re-index.")


def _tagged_value(v):
    """Unwrap a tagged-JSON value ({'__fluxer_type':..,'value':..}) if tagged."""
    return v.get("value") if isinstance(v, dict) else v


def _tagged_int(v):
    v = _tagged_value(v)
    return int(v) if v is not None else None


def gif_report(cfg):
    """Resolve every Tenor embed against KLIPY without touching the database.

    Pre-warms the resolution cache and prints the match rate, so you can gauge
    conversion quality (and spot-check the cache) before running the migration.
    """
    if not cfg.klipy_api_key:
        sys.exit("No KLIPY api key resolved. Set klipy_api_key in the config.")
    client = KlipyClient(
        cfg.klipy_api_key,
        customer_id=cfg.klipy_customer_id or "flushcord",
        cache_path=cfg.klipy_cache_path or None,
    )
    db = DiscordBackup(cfg.backup_db)
    urls = [r[0] for r in db.conn.execute(
        "SELECT DISTINCT url FROM embeds WHERE url LIKE '%tenor.com/view/%'"
    ).fetchall()]
    db.close()
    print(f"Resolving {len(urls)} distinct Tenor GIF link(s) via KLIPY...")
    matched, missed = 0, []
    for i, url in enumerate(urls, 1):
        if client.resolve_embed(url):
            matched += 1
        else:
            missed.append(url)
        if i % 100 == 0:
            print(f"  {i}/{len(urls)} ({matched} matched)", flush=True)
            client.save_cache()
    client.save_cache()
    print(f"\nMatched {matched}/{len(urls)} "
          f"({100 * matched / max(len(urls), 1):.1f}%); "
          f"{len(missed)} unmatched; {client.api_calls} API calls.")
    for url in missed[:50]:
        print(f"  no match: {url}")
    if len(missed) > 50:
        print(f"  ... and {len(missed) - 50} more")
    print(f"Cache written to {cfg.klipy_cache_path}")


def _embed_klipy_media(embed):
    """Yield the embed's media dicts whose URL lives on KLIPY's CDN."""
    for key in ("video", "thumbnail", "image"):
        media = embed.get(key)
        if isinstance(media, dict) and "klipy.com" in (media.get("url") or "").lower():
            yield media


def _embed_references_klipy(embed):
    if "klipy.com" in (embed.get("url") or "").lower():
        return True
    return any(True for _ in _embed_klipy_media(embed))


def _is_renderable_gifv(embed):
    """True if the embed is a gifv with at least one fully-dimensioned media."""
    if embed.get("type") != "gifv":
        return False
    for key in ("video", "thumbnail"):
        m = embed.get(key)
        if (isinstance(m, dict) and m.get("url")
                and isinstance(m.get("width"), int) and isinstance(m.get("height"), int)):
            return True
    return False


def fix_gif_embeds(cfg):
    """Backfill signed proxy_url on migrated KLIPY GIF embeds (in place).

    Fluxer's client only renders embed media when it carries a proxy_url. The
    direct-write migration bypasses the server normaliser that would set it, so
    converted GIFs show only their link. This repairs two populations:

      * gifv embeds we built (correct media, missing proxy_url) -> just sign.
      * degraded ``rich`` embeds from bare klipy.com links Fluxer unfurled
        without dimensions -> re-resolve the slug into a proper gifv.

    Rewrites only the ``embeds`` field of each affected message row; message
    ids/timestamps/authorship are untouched.
    """
    if not (cfg.media_proxy_endpoint and cfg.media_proxy_secret):
        sys.exit("Media-proxy signing is not configured. Set media_proxy_endpoint "
                 "and media_proxy_secret (or the FLUXER_MEDIA_PROXY_* env vars).")
    if not cfg.klipy_api_key:
        sys.exit("No KLIPY api key resolved (needed to upgrade degraded rich embeds).")

    client = KlipyClient(
        cfg.klipy_api_key,
        customer_id=cfg.klipy_customer_id or "flushcord",
        cache_path=cfg.klipy_cache_path or None,
        proxy_endpoint=cfg.media_proxy_endpoint,
        proxy_secret=cfg.media_proxy_secret,
    )
    conn = psycopg2.connect(cfg.pg_dsn)
    tbl = cfg.kv_table
    signed = upgraded = unresolved = rows_changed = 0
    slug_embeds = {}  # slug -> resolved gifv embed (dedupes API calls)

    with conn.cursor() as read_cur:
        read_cur.execute(
            f"SELECT row_key, row_data FROM {tbl} WHERE table_name='messages'"
        )
        batch = read_cur.fetchall()

    print(f"Scanning {len(batch)} message row(s) for KLIPY embeds to repair...")
    write = conn.cursor()
    for i, (row_key, row_data) in enumerate(batch, 1):
        data = row_data if isinstance(row_data, dict) else json.loads(row_data)
        embeds = data.get("embeds")
        if not embeds:
            continue
        changed = False
        for idx, embed in enumerate(embeds):
            if not _embed_references_klipy(embed):
                continue
            if _is_renderable_gifv(embed):
                for media in _embed_klipy_media(embed):
                    if media.get("url") and not media.get("proxy_url"):
                        media["proxy_url"] = sign_media_proxy_url(
                            cfg.media_proxy_endpoint, cfg.media_proxy_secret, media["url"]
                        )
                        signed += 1
                        changed = True
                continue
            # Degraded klipy embed: re-resolve the slug into a real gifv.
            slug = slug_from_share_url(embed.get("url"))
            if not slug:
                for media in _embed_klipy_media(embed):
                    slug = slug_from_share_url(media.get("url"))
                    if slug:
                        break
            if not slug:
                unresolved += 1
                continue
            if slug not in slug_embeds:
                slug_embeds[slug] = client.resolve_by_slug(slug)
            new_embed = slug_embeds[slug]
            if new_embed:
                embeds[idx] = new_embed
                upgraded += 1
                changed = True
            else:
                unresolved += 1
        if changed:
            data["embeds"] = embeds
            write.execute(
                f"UPDATE {tbl} SET row_data = %s::jsonb, updated_at = now() "
                f"WHERE table_name='messages' AND row_key = %s",
                (json.dumps(data, ensure_ascii=False), row_key),
            )
            rows_changed += 1
        if i % 5000 == 0:
            conn.commit()
            print(f"  {i}/{len(batch)} scanned "
                  f"({signed} signed, {upgraded} upgraded)", flush=True)

    conn.commit()
    client.save_cache()
    write.close()
    conn.close()
    print(f"\nDone. Rows updated: {rows_changed}; media signed: {signed}; "
          f"rich->gifv upgraded: {upgraded}; unresolved: {unresolved}; "
          f"KLIPY API calls: {client.api_calls}.")


def fix_youtube_embeds(cfg, dry_run=False):
    """Rebuild migrated YouTube embeds in place (for an instance already migrated).

    Same conversion `migrate` now does, applied to rows already in the database:
    each flat ``rich`` embed pointing at a YouTube link becomes the ``video``
    embed Fluxer's own unfurler would have written — player, sized thumbnail,
    ThumbHash placeholder. Videos that no longer resolve keep their rich embed.

    Only the ``embeds`` field of an affected message is rewritten; ids,
    timestamps, authorship and content are untouched.
    """
    if not cfg.youtube_api_key:
        sys.exit("No YouTube api key resolved. Set youtube_api_key in the config.")
    if not (cfg.media_proxy_endpoint and cfg.media_proxy_secret):
        print("  ! media_proxy_* is not configured; thumbnails will have no "
              "placeholder/content hash")

    client = YouTubeClient(
        cfg.youtube_api_key,
        media_proxy_endpoint=cfg.media_proxy_endpoint or None,
        media_proxy_secret=cfg.media_proxy_secret or None,
        cache_path=cfg.youtube_cache_path or None,
    )
    conn = psycopg2.connect(cfg.pg_dsn)
    tbl = cfg.kv_table
    rebuilt = unresolved = rows_changed = 0

    with conn.cursor() as read_cur:
        read_cur.execute(
            f"SELECT row_key, row_data FROM {tbl} WHERE table_name='messages'"
        )
        batch = read_cur.fetchall()

    print(f"Scanning {len(batch)} message row(s) for YouTube embeds to rebuild...")
    write = conn.cursor()
    for i, (row_key, row_data) in enumerate(batch, 1):
        data = row_data if isinstance(row_data, dict) else json.loads(row_data)
        embeds = data.get("embeds")
        if not embeds:
            continue
        changed = False
        for idx, embed in enumerate(embeds):
            url = embed.get("url") or ""
            # Already a rebuilt video embed? Leave it alone.
            if embed.get("type") == "video" or not is_youtube_url(url):
                continue
            video = client.resolve_embed(url)
            if video:
                embeds[idx] = video
                rebuilt += 1
                changed = True
            else:
                unresolved += 1
        if changed and not dry_run:
            data["embeds"] = embeds
            write.execute(
                f"UPDATE {tbl} SET row_data = %s::jsonb, updated_at = now() "
                f"WHERE table_name='messages' AND row_key = %s",
                (json.dumps(data, ensure_ascii=False), row_key),
            )
        if changed:
            rows_changed += 1
        if i % 5000 == 0:
            if not dry_run:
                conn.commit()
            client.save_cache()
            print(f"  {i}/{len(batch)} scanned ({rebuilt} rebuilt)", flush=True)

    if not dry_run:
        conn.commit()
    client.save_cache()
    write.close()
    conn.close()
    what = "would update" if dry_run else "updated"
    print(f"\nDone. Rows {what}: {rows_changed}; embeds rebuilt: {rebuilt}; "
          f"unresolved: {unresolved}; YouTube API calls: {client.api_calls}.")


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def main():
    parser = argparse.ArgumentParser(description="Discord -> Fluxer migration tool")
    parser.add_argument("--config", required=True,
                        help="path to the server's config.json (see config.example.json)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("gen-user-map",
                   help="fill the config's user_map with every Discord user in the backup")

    mig = sub.add_parser("migrate", help="run the migration")
    mig.add_argument("--owner", type=int, help="Fluxer user id that owns the guild")
    mig.add_argument("--no-attachments", action="store_true", help="skip S3 uploads")
    mig.add_argument("--reactions", choices=["skip", "real", "owner"],
                     help="reaction strategy (default: real)")
    mig.add_argument("--dry-run", action="store_true", help="rollback at the end")
    mig.add_argument("--skip-preflight", action="store_true",
                     help="skip the pre-migration validation checks")

    pf = sub.add_parser("preflight", help="validate config/connectivity/users without writing")
    pf.add_argument("--owner", type=int, help="Fluxer user id that will own the guild")
    pf.add_argument("--no-attachments", action="store_true",
                    help="skip the S3/media checks")

    sub.add_parser("verify", help="compare backup vs migrated counts")

    sub.add_parser("gif-report",
                   help="resolve Tenor->KLIPY for all GIF links and report the "
                        "match rate (pre-warms the cache; writes nothing to the DB)")

    sub.add_parser("fix-gifs",
                   help="backfill signed proxy_url on already-migrated KLIPY GIF "
                        "embeds so they render (repairs a migration run done before "
                        "media-proxy signing was configured)")

    sub.add_parser("reindex-members",
                   help="make Fluxer rebuild the guild's member search index, so "
                        "migrated members show up on the members page with their "
                        "roles (repairs a guild indexed before/during migration)")

    fy = sub.add_parser("fix-youtube",
                        help="rebuild already-migrated YouTube embeds into real "
                             "Fluxer video embeds (player + sized thumbnail), for an "
                             "instance migrated before youtube_api_key was set")
    fy.add_argument("--dry-run", action="store_true",
                    help="resolve and report without writing to the DB")

    pg = sub.add_parser(
        "purge", help="delete everything the migration created (for a clean re-run)"
    )
    pg.add_argument("--s3", action="store_true",
                    help="also delete uploaded attachment/emoji/sticker objects from S3")
    pg.add_argument("--dry-run", action="store_true",
                    help="show what would be deleted, then roll back")

    args = parser.parse_args()
    cfg = load_config(args.config)

    if args.cmd == "gen-user-map":
        gen_user_map(cfg)
        return
    if args.cmd == "verify":
        verify(cfg)
        return
    if args.cmd == "gif-report":
        gif_report(cfg)
        return
    if args.cmd == "fix-gifs":
        fix_gif_embeds(cfg)
        return
    if args.cmd == "reindex-members":
        reindex_members(cfg)
        return
    if args.cmd == "fix-youtube":
        fix_youtube_embeds(cfg, dry_run=args.dry_run)
        return
    if args.cmd == "preflight":
        owner = args.owner or cfg.guild_owner_user_id or None
        problems, _ = preflight(cfg, owner_id=owner, want_s3=not args.no_attachments)
        sys.exit(1 if problems else 0)
    if args.cmd == "purge":
        m = Migrator(cfg)
        try:
            m.purge(purge_s3=args.s3, dry_run=args.dry_run)
        except Exception:
            m.kv.rollback()
            raise
        finally:
            m.close()
        return

    # migrate
    if args.owner:
        cfg.guild_owner_user_id = args.owner
    if args.no_attachments:
        cfg.upload_attachments = False
    if args.reactions:
        cfg.reaction_mode = args.reactions

    if not args.skip_preflight:
        problems, _ = preflight(
            cfg,
            owner_id=cfg.guild_owner_user_id or None,
            want_s3=cfg.upload_attachments,
        )
        if problems:
            sys.exit("\nAborting: fix the problems above, or pass "
                     "--skip-preflight to override.")
        print()

    m = Migrator(cfg)
    try:
        m.run()
        if args.dry_run:
            m.kv.rollback()
            print("Dry run: rolled back all writes.")
    except Exception:
        m.kv.rollback()
        raise
    finally:
        m.close()


if __name__ == "__main__":
    main()
