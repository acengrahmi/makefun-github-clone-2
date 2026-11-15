#!/usr/bin/env python3
"""forge2 - a standalone GitHub-compatible git forge in one process.

Serves four surfaces from one in-memory store:
  * git smart HTTP (upload-pack protocol v2 + v0, receive-pack v0)
  * REST v3 under /api/v3
  * GraphQL at /api/graphql
  * MCP (JSON-RPC over streamable HTTP) at /mcp

Design notes (performance first, because three of the four timed workloads
are per-request-overhead bound and the fourth is concurrency bound):

  * The HTTP layer is a hand-rolled keep-alive server on raw sockets.  It
    parses just the request line and headers it needs and writes each reply
    with a single sendall, so a warm issue read costs a few dict lookups.
  * Objects are immutable and content-addressed, so fetch paths snapshot
    the ref table under a short lock and then walk the object graph
    lock-free.  Clone/fetch pack bytes are cached per (repo generation,
    wants, haves, depth) - the 50 concurrent shallow clones in the bench
    all ask for the same pack, so it is built once and then only copied.
  * REST issue reads serve pre-serialised JSON bytes that are refreshed
    whenever the issue changes, never re-encoded per request.
  * One re-entrant lock serialises mutations only; reads of immutable
    objects never wait on it.

Standard library only.  The harness contract: bind port 0, POST the port
to $MAKEFUN_ENV_URL/register, serve, long-poll /done, exit 0 when told.
"""

import base64
import hashlib
import json
import os
import re
import socket
import socketserver
import sys
import threading
import time
import urllib.request
import zlib
from urllib.parse import parse_qs, unquote, urlsplit

# --------------------------------------------------------------------------
# process configuration

ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
ZERO_OID = "0" * 40

VIEWER = {"login": "adaiversen", "id": 1000, "name": "ada iversen",
          "email": "adaiversen@example.invalid"}
KNOWN_USERS = {
    "adaiversen": VIEWER,
    "quinnkeller": {"login": "quinnkeller", "id": 1001, "name": "quinn keller",
                    "email": "quinnkeller@example.invalid"},
    "olgabauer": {"login": "olgabauer", "id": 1002, "name": "olga bauer",
                  "email": "olgabauer@example.invalid"},
}

# --------------------------------------------------------------------------
# deterministic clock + id sequences
#
# Nothing in a reply may depend on the wall clock (a trial is replayed and
# the exports must match), so timestamps come from a tick counter anchored
# at a fixed epoch and ids from plain counters.

_EPOCH = 1767225600  # 2026-01-01T00:00:00Z
_tick_lock = threading.Lock()
_tick = [0]


def tick():
    with _tick_lock:
        _tick[0] += 1
        return _EPOCH + _tick[0]


def iso8601(epoch_seconds):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(epoch_seconds))


def now_iso():
    return iso8601(tick())


_req_counter = [0]
_req_lock = threading.Lock()


def request_id():
    with _req_lock:
        _req_counter[0] += 1
        return "F2%012X" % _req_counter[0]


# --------------------------------------------------------------------------
# JSON helpers

def dumps(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def err_body(message, **extra):
    body = {"message": message}
    body.update(extra)
    return dumps(body)


# --------------------------------------------------------------------------
# git object model
#
# One content-addressed store shared by every repository: oid ->
# (type, payload).  Objects are never mutated or deleted, which is what
# makes lock-free reads safe.

TYPE_TO_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TO_TYPE = {v: k for k, v in TYPE_TO_CODE.items()}


def hash_object(otype, payload):
    head = ("%s %d\0" % (otype, len(payload))).encode("ascii")
    return hashlib.sha1(head + payload).hexdigest()


class ObjectStore:
    def __init__(self):
        self.objects = {}

    def put(self, otype, payload):
        oid = hash_object(otype, payload)
        if oid not in self.objects:
            self.objects[oid] = (otype, payload)
        return oid

    def put_raw(self, oid, otype, payload):
        if oid not in self.objects:
            self.objects[oid] = (otype, payload)

    def get(self, oid):
        return self.objects.get(oid)

    def has(self, oid):
        return oid in self.objects

    def type_of(self, oid):
        item = self.objects.get(oid)
        return item[0] if item else None


STORE = ObjectStore()


# ---- commits, trees, tags -------------------------------------------------

def parse_commit(payload):
    """Return (tree, parents, author_line, committer_line, message)."""
    head, _, message = payload.partition(b"\n\n")
    tree = None
    parents = []
    author = ""
    committer = ""
    for line in head.decode("utf-8", "replace").split("\n"):
        if line.startswith("tree "):
            tree = line[5:]
        elif line.startswith("parent "):
            parents.append(line[7:])
        elif line.startswith("author "):
            author = line[7:]
        elif line.startswith("committer "):
            committer = line[10:]
    return tree, parents, author, committer, message.decode("utf-8", "replace")


def commit_info(oid):
    """Cached (tree, parents, timestamp) for a commit oid, or None."""
    cached = _commit_cache.get(oid)
    if cached is not None:
        return cached
    item = STORE.get(oid)
    if not item or item[0] != "commit":
        return None
    tree, parents, author, _committer, _msg = parse_commit(item[1])
    ts = 0
    m = re.search(r"> (\d+) [+-]\d{4}$", author)
    if m:
        ts = int(m.group(1))
    info = (tree, parents, ts)
    if len(_commit_cache) < 200000:
        _commit_cache[oid] = info
    return info


_commit_cache = {}


def parse_tag(payload):
    head, _, message = payload.partition(b"\n\n")
    fields = {}
    for line in head.decode("utf-8", "replace").split("\n"):
        key, _, value = line.partition(" ")
        fields[key] = value
    return fields.get("object"), fields.get("type"), fields.get("tag"), \
        message.decode("utf-8", "replace")


def peel_to_commit(oid):
    """Follow tag objects until a commit (or None)."""
    seen = 0
    while oid and seen < 10:
        item = STORE.get(oid)
        if not item:
            return None
        if item[0] == "commit":
            return oid
        if item[0] != "tag":
            return None
        oid, _t, _n, _m = parse_tag(item[1])
        seen += 1
    return None


def parse_tree(payload):
    entries = []
    pos = 0
    end = len(payload)
    while pos < end:
        sp = payload.index(b" ", pos)
        mode = payload[pos:sp].decode("ascii")
        nul = payload.index(b"\0", sp + 1)
        name = payload[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = payload[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        pos = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    return (name + "/" if mode == "40000" else name).encode("utf-8", "surrogateescape")


def build_tree(entries):
    parts = []
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        parts.append(("%s %s\0" % (mode, name)).encode("utf-8", "surrogateescape"))
        parts.append(bytes.fromhex(oid))
    return b"".join(parts)


def flatten_tree(tree_oid, prefix=""):
    """Map every path under a tree to (mode, oid), recursively."""
    out = {}
    item = STORE.get(tree_oid)
    if not item or item[0] != "tree":
        return out
    for mode, name, oid in parse_tree(item[1]):
        path = prefix + name
        if mode == "40000":
            out.update(flatten_tree(oid, path + "/"))
        else:
            out[path] = (mode, oid)
    return out


def tree_from_flat(flat):
    """Build (and store) nested trees from {path: (mode, oid)}; return root oid."""
    root = {}
    for path, value in flat.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = value

    def emit(node):
        entries = []
        for name, value in node.items():
            if isinstance(value, dict):
                entries.append(("40000", name, emit(value)))
            else:
                entries.append((value[0], name, value[1]))
        return STORE.put("tree", build_tree(entries))

    return emit(root)


def make_commit(tree_oid, parents, message, when=None):
    if when is None:
        when = tick()
    ident = "%s <%s> %d +0000" % (VIEWER["name"], VIEWER["email"], when)
    lines = ["tree %s" % tree_oid]
    for parent in parents:
        lines.append("parent %s" % parent)
    lines.append("author %s" % ident)
    lines.append("committer %s" % ident)
    payload = ("\n".join(lines) + "\n\n" + message).encode("utf-8")
    return STORE.put("commit", payload)


def is_ancestor(maybe_ancestor, descendant):
    """True when maybe_ancestor is reachable from descendant via parents."""
    if maybe_ancestor == descendant:
        return True
    seen = set()
    stack = [descendant]
    while stack:
        current = stack.pop()
        if current == maybe_ancestor:
            return True
        if current in seen:
            continue
        seen.add(current)
        info = commit_info(current)
        if info:
            stack.extend(info[1])
    return False


def merge_base(a, b):
    """A best common ancestor of two commits, or None."""
    ancestors = set()
    stack = [a]
    while stack:
        current = stack.pop()
        if current in ancestors:
            continue
        ancestors.add(current)
        info = commit_info(current)
        if info:
            stack.extend(info[1])
    seen = set()
    queue = [b]
    while queue:
        current = queue.pop(0)
        if current in ancestors:
            return current
        if current in seen:
            continue
        seen.add(current)
        info = commit_info(current)
        if info:
            queue.extend(info[1])
    return None


# ---- packfiles --------------------------------------------------------------

def _read_varint(buf, pos):
    value = 0
    shift = 0
    while True:
        byte = buf[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            return value, pos


def apply_delta(base, delta):
    def read_varint(pos):
        value = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return value, pos

    src_size, pos = read_varint(0)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    dst_size, pos = read_varint(pos)
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            if op & 0x01:
                cp_off = delta[pos]; pos += 1
            if op & 0x02:
                cp_off |= delta[pos] << 8; pos += 1
            if op & 0x04:
                cp_off |= delta[pos] << 16; pos += 1
            if op & 0x08:
                cp_off |= delta[pos] << 24; pos += 1
            if op & 0x10:
                cp_size = delta[pos]; pos += 1
            if op & 0x20:
                cp_size |= delta[pos] << 8; pos += 1
            if op & 0x40:
                cp_size |= delta[pos] << 16; pos += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != dst_size:
        raise ValueError("delta result size mismatch")
    return bytes(out)


def read_pack(data, store):
    """Parse a packfile into `store`.  Returns the number of objects read."""
    if len(data) < 12 + 20 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    pending = []  # (oid or None, typecode, payload, base_ref)
    raw_objects = []
    for _ in range(count):
        byte = data[pos]
        pos += 1
        otype_code = (byte >> 4) & 0x07
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[pos]
            pos += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        base_ref = None
        if otype_code == 6:  # OFS_DELTA
            byte = data[pos]
            pos += 1
            offset = byte & 0x7F
            while byte & 0x80:
                byte = data[pos]
                pos += 1
                offset = ((offset + 1) << 7) | (byte & 0x7F)
            base_ref = ("ofs", offset)
        elif otype_code == 7:  # REF_DELTA
            base_ref = ("ref", data[pos:pos + 20].hex())
            pos += 20
        decomp = zlib.decompressobj()
        payload = decomp.decompress(data[pos:])
        consumed = len(data[pos:]) - len(decomp.unused_data)
        pos += consumed
        raw_objects.append((otype_code, payload, base_ref, pos))
    # resolve in passes: plain objects first, then deltas whose base exists
    resolved = [None] * len(raw_objects)
    remaining = set(range(len(raw_objects)))
    # offsets: entry i starts where its header began; recompute start offsets
    starts = []
    pos = 12
    for otype_code, payload, base_ref, end_pos in raw_objects:
        starts.append(pos)
        pos = end_pos
    by_start = {starts[i]: i for i in range(len(raw_objects))}
    progress = True
    while remaining and progress:
        progress = False
        for i in sorted(remaining):
            otype_code, payload, base_ref, _end = raw_objects[i]
            if otype_code in CODE_TO_TYPE:
                otype = CODE_TO_TYPE[otype_code]
                oid = hash_object(otype, payload)
                store.put_raw(oid, otype, payload)
                resolved[i] = oid
                remaining.discard(i)
                progress = True
            elif otype_code == 6:
                base_start = starts[i] - base_ref[1]
                j = by_start.get(base_start)
                if j is not None and resolved[j] is not None:
                    base_item = store.get(resolved[j])
                    full = apply_delta(base_item[1], payload)
                    oid = hash_object(base_item[0], full)
                    store.put_raw(oid, base_item[0], full)
                    resolved[i] = oid
                    remaining.discard(i)
                    progress = True
            elif otype_code == 7:
                base_item = store.get(base_ref[1])
                if base_item:
                    full = apply_delta(base_item[1], payload)
                    oid = hash_object(base_item[0], full)
                    store.put_raw(oid, base_item[0], full)
                    resolved[i] = oid
                    remaining.discard(i)
                    progress = True
    if remaining:
        raise ValueError("pack has unresolvable deltas")
    return count


def write_pack(oids):
    """Serialise the given objects (full form only) into a packfile."""
    out = bytearray()
    out += b"PACK"
    out += (2).to_bytes(4, "big")
    out += len(oids).to_bytes(4, "big")
    for oid in oids:
        otype, payload = STORE.get(oid)
        code = TYPE_TO_CODE[otype]
        rest = len(payload) >> 4
        byte0 = (code << 4) | (len(payload) & 0x0F)
        if rest:
            byte0 |= 0x80
        header = bytearray([byte0])
        while rest:
            byte = rest & 0x7F
            rest >>= 7
            if rest:
                byte |= 0x80
            header.append(byte)
        out += header
        out += zlib.compress(payload, 6)
    out += hashlib.sha1(bytes(out)).digest()
    return bytes(out)


# --------------------------------------------------------------------------
# forge state
#
# A Repo owns refs into the shared object store plus the collaboration
# records (labels, issues, pull requests, comments).  Issues and pull
# requests share one per-repo number sequence, as on GitHub.

STORE_LOCK = threading.RLock()
_id_lock = threading.Lock()
_PACK_BUILD_LOCK = threading.Lock()
_next_repo_id = [1]
_next_global_id = [1]  # issue/PR/comment global ids (GraphQL databaseId)


def alloc_repo_id():
    with _id_lock:
        value = _next_repo_id[0]
        _next_repo_id[0] += 1
        return value


def alloc_global_id():
    with _id_lock:
        value = _next_global_id[0]
        _next_global_id[0] += 1
        return value


class Repo:
    def __init__(self, owner, name, description, private):
        self.owner = owner
        self.name = name
        self.id = alloc_repo_id()
        self.dbid = self.id
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.refs = {}            # refname -> oid
        self.labels = {}          # name -> label dict
        self.items = {}           # number -> issue or pull dict
        self.next_number = 1
        self.gen = 0              # bumped on every ref change (pack cache)
        self.pack_cache = {}
        self.created_tick = tick()
        self.updated_tick = self.created_tick

    @property
    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def head_ref(self):
        return "refs/heads/%s" % self.default_branch

    def ref_oid(self, ref):
        return self.refs.get(ref)

    def branch_oid(self, branch):
        return self.refs.get("refs/heads/%s" % branch)

    def set_ref(self, ref, oid):
        if oid == ZERO_OID:
            self.refs.pop(ref, None)
        else:
            self.refs[ref] = oid
        self.gen += 1
        self.pack_cache.clear()
        self.updated_tick = tick()

    def open_count(self):
        return sum(1 for it in self.items.values() if it["state"] == "open")


class Forge:
    def __init__(self):
        self.repos = {}  # full_name -> Repo

    def get(self, owner, name):
        if owner != VIEWER["login"]:
            return None
        return self.repos.get("%s/%s" % (owner, name))

    def create(self, name, description, private):
        repo = Repo(VIEWER["login"], name, description, private)
        self.repos[repo.full_name] = repo
        return repo

    def delete(self, repo):
        self.repos.pop(repo.full_name, None)

    def user_repos(self):
        return sorted(self.repos.values(), key=lambda r: r.id)


FORGE = Forge()


# ---- record factories -------------------------------------------------------

def new_label(repo, name, color=None, description=None):
    label = {
        "id": alloc_global_id(),
        "name": name,
        "color": color or "ededed",
        "description": description or "",
        "default": False,
    }
    repo.labels[name] = label
    return label


def new_issue(repo, title, body, label_names, author=VIEWER["login"]):
    number = repo.next_number
    repo.next_number += 1
    when = tick()
    issue = {
        "kind": "issue",
        "gid": alloc_global_id(),
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "labels": list(label_names or []),
        "user": author,
        "comments": [],
        "created": when,
        "updated": when,
        "closed": None,
        "_json": None,
    }
    repo.items[number] = issue
    refresh_issue_json(repo, issue)
    return issue


def new_pull(repo, title, body, head, base, author=VIEWER["login"]):
    number = repo.next_number
    repo.next_number += 1
    when = tick()
    pull = {
        "kind": "pr",
        "gid": alloc_global_id(),
        "number": number,
        "title": title or "",
        "body": body or "",
        "state": "open",
        "labels": [],
        "user": author,
        "comments": [],
        "created": when,
        "updated": when,
        "closed": None,
        "head": head,
        "base": base,
        "merged": False,
        "merged_at": None,
        "merge_sha": None,
        "_json": None,
    }
    repo.items[number] = pull
    return pull


def new_comment(item, body, author=VIEWER["login"]):
    when = tick()
    comment = {
        "gid": alloc_global_id(),
        "body": body or "",
        "user": author,
        "created": when,
        "updated": when,
    }
    item["comments"].append(comment)
    item["updated"] = when
    return comment


# ---- JSON representations ---------------------------------------------------

URL_BASE = "http://forge.invalid"


def user_json(login):
    user = KNOWN_USERS.get(login, {"login": login, "id": 0, "name": login,
                                   "email": ""})
    return {
        "login": user["login"],
        "id": user["id"],
        "node_id": node_id("User", user["id"]),
        "avatar_url": "%s/avatars/%s" % (URL_BASE, user["id"]),
        "gravatar_id": "",
        "url": "%s/api/v3/users/%s" % (URL_BASE, user["login"]),
        "html_url": "%s/%s" % (URL_BASE, user["login"]),
        "type": "User",
        "site_admin": False,
        "name": user["name"],
        "email": user["email"],
    }


def repo_json(repo):
    full = repo.full_name
    return {
        "id": repo.id,
        "node_id": node_id("Repository", repo.id),
        "name": repo.name,
        "full_name": full,
        "owner": user_json(repo.owner),
        "private": repo.private,
        "html_url": "%s/%s" % (URL_BASE, full),
        "description": repo.description,
        "fork": False,
        "url": "%s/api/v3/repos/%s" % (URL_BASE, full),
        "created_at": iso8601(repo.created_tick),
        "updated_at": iso8601(repo.updated_tick),
        "pushed_at": iso8601(repo.updated_tick),
        "git_url": "git://forge.invalid/%s.git" % full,
        "ssh_url": "git@forge.invalid:%s.git" % full,
        "clone_url": "%s/%s.git" % (URL_BASE, full),
        "homepage": "",
        "size": 0,
        "stargazers_count": 0,
        "watchers_count": 0,
        "language": None,
        "has_issues": True,
        "has_projects": True,
        "has_downloads": True,
        "has_wiki": True,
        "has_pages": False,
        "forks_count": 0,
        "mirror_url": None,
        "archived": False,
        "disabled": False,
        "open_issues_count": repo.open_count(),
        "license": None,
        "forks": 0,
        "open_issues": repo.open_count(),
        "watchers": 0,
        "default_branch": repo.default_branch,
        "visibility": "private" if repo.private else "public",
        "topics": [],
        "permissions": {"admin": True, "maintain": True, "push": True,
                        "triage": True, "pull": True},
    }


def label_json(repo, label):
    return {
        "id": label["id"],
        "node_id": node_id("Label", label["id"]),
        "url": "%s/api/v3/repos/%s/labels/%s" % (URL_BASE, repo.full_name,
                                                 label["name"]),
        "name": label["name"],
        "color": label["color"],
        "default": label["default"],
        "description": label["description"],
    }


def issue_json_obj(repo, issue):
    full = repo.full_name
    obj = {
        "id": issue["gid"],
        "node_id": node_id("Issue", issue["gid"]),
        "url": "%s/api/v3/repos/%s/issues/%d" % (URL_BASE, full, issue["number"]),
        "repository_url": "%s/api/v3/repos/%s" % (URL_BASE, full),
        "labels_url": "%s/api/v3/repos/%s/issues/%d/labels{/name}" % (
            URL_BASE, full, issue["number"]),
        "comments_url": "%s/api/v3/repos/%s/issues/%d/comments" % (
            URL_BASE, full, issue["number"]),
        "events_url": "%s/api/v3/repos/%s/issues/%d/events" % (
            URL_BASE, full, issue["number"]),
        "html_url": "%s/%s/issues/%d" % (URL_BASE, full, issue["number"]),
        "number": issue["number"],
        "state": issue["state"],
        "state_reason": "completed" if issue["state"] == "closed" else None,
        "title": issue["title"],
        "body": issue["body"],
        "user": user_json(issue["user"]),
        "labels": [label_json(repo, repo.labels[name])
                   for name in issue["labels"] if name in repo.labels],
        "assignee": None,
        "assignees": [],
        "milestone": None,
        "locked": False,
        "active_lock_reason": None,
        "comments": len(issue["comments"]),
        "pull_request": None,
        "closed_at": iso8601(issue["closed"]) if issue["closed"] else None,
        "created_at": iso8601(issue["created"]),
        "updated_at": iso8601(issue["updated"]),
        "author_association": "OWNER",
    }
    if issue["kind"] == "pr":
        obj["pull_request"] = {
            "url": "%s/api/v3/repos/%s/pulls/%d" % (URL_BASE, full,
                                                    issue["number"]),
            "html_url": "%s/%s/pull/%d" % (URL_BASE, full, issue["number"]),
            "diff_url": "%s/%s/pull/%d.diff" % (URL_BASE, full, issue["number"]),
            "patch_url": "%s/%s/pull/%d.patch" % (URL_BASE, full, issue["number"]),
        }
    else:
        del obj["pull_request"]
    return obj


def refresh_issue_json(repo, issue):
    issue["_json"] = dumps(issue_json_obj(repo, issue))


def comment_json(repo, item, comment):
    full = repo.full_name
    return {
        "id": comment["gid"],
        "node_id": node_id("IssueComment", comment["gid"]),
        "url": "%s/api/v3/repos/%s/issues/comments/%d" % (
            URL_BASE, full, comment["gid"]),
        "html_url": "%s/%s/issues/%d#issuecomment-%d" % (
            URL_BASE, full, item["number"], comment["gid"]),
        "body": comment["body"],
        "user": user_json(comment["user"]),
        "created_at": iso8601(comment["created"]),
        "updated_at": iso8601(comment["updated"]),
        "issue_url": "%s/api/v3/repos/%s/issues/%d" % (
            URL_BASE, full, item["number"]),
        "author_association": "OWNER",
    }


def find_comment(repo, gid):
    for item in repo.items.values():
        for comment in item["comments"]:
            if comment["gid"] == gid:
                return item, comment
    return None, None


# ---- node ids (GraphQL global ids) -------------------------------------------

def node_id(kind, dbid):
    raw = "%s:%d" % (kind, dbid)
    return base64.b64encode(raw.encode("ascii")).decode("ascii")


def parse_node_id(value):
    try:
        raw = base64.b64decode(value.encode("ascii"), validate=False)
        kind, _, dbid = raw.decode("ascii").partition(":")
        return kind, int(dbid)
    except Exception:
        return None, None


# ---- pull request geometry: merge base, diffs, 3-way merge -------------------

def branch_tip(repo, branch):
    oid = repo.branch_oid(branch)
    return peel_to_commit(oid) if oid else None


def ref_side(repo, branch):
    oid = repo.branch_oid(branch)
    return {
        "label": "%s:%s" % (repo.owner, branch),
        "ref": branch,
        "sha": oid or ZERO_OID,
        "user": user_json(repo.owner),
        "repo": repo_json(repo),
    }


def pr_files(repo, pull):
    """Changed files between merge-base and head, GitHub /files shape."""
    base_tip = branch_tip(repo, pull["base"])
    head_tip = branch_tip(repo, pull["head"])
    if not head_tip:
        return []
    anchor = merge_base(base_tip, head_tip) if base_tip else None
    before = {}
    after = {}
    if anchor:
        info = commit_info(anchor)
        if info:
            before = flatten_tree(info[0])
    info = commit_info(head_tip)
    if info:
        after = flatten_tree(info[0])
    files = []
    for path in sorted(set(before) | set(after)):
        old = before.get(path)
        new = after.get(path)
        if old == new:
            continue
        if old is None:
            status = "added"
        elif new is None:
            status = "removed"
        else:
            status = "modified"
        additions, deletions, patch = _diff_stats(old, new)
        entry = {
            "sha": new[1] if new else old[1],
            "filename": path,
            "status": status,
            "additions": additions,
            "deletions": deletions,
            "changes": additions + deletions,
            "blob_url": "%s/%s/blob/%s/%s" % (URL_BASE, repo.full_name,
                                              pull["head"], path),
            "raw_url": "%s/%s/raw/%s/%s" % (URL_BASE, repo.full_name,
                                            pull["head"], path),
            "contents_url": "%s/api/v3/repos/%s/contents/%s?ref=%s" % (
                URL_BASE, repo.full_name, path, pull["head"]),
        }
        if patch is not None:
            entry["patch"] = patch
        if status == "renamed":
            entry["previous_filename"] = path
        files.append(entry)
    return files


def _blob_text(oid):
    item = STORE.get(oid) if oid else None
    if not item or item[0] != "blob":
        return None
    return item[1]


def _diff_stats(old, new):
    """Line-level addition/deletion counts via a simple LCS on lines."""
    old_data = _blob_text(old[1]) if old else b""
    new_data = _blob_text(new[1]) if new else b""
    if old_data is None:
        old_data = b""
    if new_data is None:
        new_data = b""
    old_lines = old_data.decode("utf-8", "replace").split("\n")
    new_lines = new_data.decode("utf-8", "replace").split("\n")
    if old_data and old_lines and old_lines[-1] == "":
        old_lines.pop()
    if new_data and new_lines and new_lines[-1] == "":
        new_lines.pop()
    # LCS length with the classic DP, bounded to sane sizes
    if len(old_lines) * len(new_lines) <= 4_000_000:
        prev = [0] * (len(new_lines) + 1)
        for i in range(len(old_lines) - 1, -1, -1):
            cur = [0] * (len(new_lines) + 1)
            for j in range(len(new_lines) - 1, -1, -1):
                if old_lines[i] == new_lines[j]:
                    cur[j] = prev[j + 1] + 1
                else:
                    cur[j] = max(prev[j], cur[j + 1])
            prev = cur
        common = prev[0]
    else:
        common = 0
    additions = len(new_lines) - common
    deletions = len(old_lines) - common
    patch_lines = ["@@ -1,%d +1,%d @@" % (len(old_lines), len(new_lines))]
    for line in old_lines:
        patch_lines.append("-" + line)
    for line in new_lines:
        patch_lines.append("+" + line)
    patch = "\n".join(patch_lines) if (old_lines or new_lines) else None
    return additions, deletions, patch


def try_merge_trees(base_tree, head_tree, anchor_tree):
    """3-way merge of flattened trees.  Returns (merged_flat, conflicted)."""
    base_flat = flatten_tree(base_tree) if base_tree else {}
    head_flat = flatten_tree(head_tree) if head_tree else {}
    anchor_flat = flatten_tree(anchor_tree) if anchor_tree else {}
    merged = {}
    conflict = False
    for path in set(base_flat) | set(head_flat) | set(anchor_flat):
        base_v = base_flat.get(path)
        head_v = head_flat.get(path)
        anchor_v = anchor_flat.get(path)
        if head_v == anchor_v:
            chosen = base_v          # head did not touch it: take base
        elif base_v == anchor_v:
            chosen = head_v          # base did not touch it: take head
        elif base_v == head_v:
            chosen = base_v          # both made the same change
        else:
            conflict = True
            chosen = head_v
        if chosen is not None:
            merged[path] = chosen
    return merged, conflict


def pull_mergeable(repo, pull):
    """True/False mergeability of an open pull, computed on demand."""
    if pull["merged"]:
        return True
    base_tip = branch_tip(repo, pull["base"])
    head_tip = branch_tip(repo, pull["head"])
    if not base_tip or not head_tip:
        return False
    if is_ancestor(head_tip, base_tip):
        return True
    anchor = merge_base(base_tip, head_tip)
    base_info = commit_info(base_tip)
    head_info = commit_info(head_tip)
    anchor_tree = commit_info(anchor)[0] if anchor else None
    _merged, conflict = try_merge_trees(base_info[0], head_info[0], anchor_tree)
    return not conflict


def squash_merge(repo, pull):
    """Squash pull's head onto its base.  Returns (sha, conflicted)."""
    base_tip = branch_tip(repo, pull["base"])
    head_tip = branch_tip(repo, pull["head"])
    if not base_tip or not head_tip:
        return None, True
    anchor = merge_base(base_tip, head_tip)
    base_info = commit_info(base_tip)
    head_info = commit_info(head_tip)
    anchor_tree = commit_info(anchor)[0] if anchor else None
    merged_flat, conflict = try_merge_trees(base_info[0], head_info[0],
                                            anchor_tree)
    if conflict:
        return None, True
    tree_oid = tree_from_flat(merged_flat)
    message = "%s (#%d)\n" % (pull["title"], pull["number"])
    if pull["body"]:
        message += "\n%s\n" % pull["body"]
    sha = make_commit(tree_oid, [base_tip], message)
    repo.set_ref("refs/heads/%s" % pull["base"], sha)
    return sha, False


def pull_json_obj(repo, pull):
    files = pr_files(repo, pull)
    additions = sum(f["additions"] for f in files)
    deletions = sum(f["deletions"] for f in files)
    mergeable = None
    if pull["state"] == "open":
        mergeable = pull_mergeable(repo, pull)
    obj = {
        "id": pull["gid"],
        "node_id": node_id("PullRequest", pull["gid"]),
        "url": "%s/api/v3/repos/%s/pulls/%d" % (URL_BASE, repo.full_name,
                                                pull["number"]),
        "html_url": "%s/%s/pull/%d" % (URL_BASE, repo.full_name, pull["number"]),
        "diff_url": "%s/%s/pull/%d.diff" % (URL_BASE, repo.full_name,
                                            pull["number"]),
        "patch_url": "%s/%s/pull/%d.patch" % (URL_BASE, repo.full_name,
                                              pull["number"]),
        "issue_url": "%s/api/v3/repos/%s/issues/%d" % (URL_BASE, repo.full_name,
                                                      pull["number"]),
        "number": pull["number"],
        "state": "closed" if pull["merged"] else pull["state"],
        "locked": False,
        "title": pull["title"],
        "user": user_json(pull["user"]),
        "body": pull["body"],
        "created_at": iso8601(pull["created"]),
        "updated_at": iso8601(pull["updated"]),
        "closed_at": iso8601(pull["closed"]) if pull["closed"] else None,
        "merged_at": iso8601(pull["merged_at"]) if pull["merged_at"] else None,
        "merge_commit_sha": pull["merge_sha"],
        "assignee": None,
        "assignees": [],
        "requested_reviewers": [],
        "requested_teams": [],
        "labels": [],
        "milestone": None,
        "draft": False,
        "commits_url": "%s/api/v3/repos/%s/pulls/%d/commits" % (
            URL_BASE, repo.full_name, pull["number"]),
        "review_comments_url": "%s/api/v3/repos/%s/pulls/%d/comments" % (
            URL_BASE, repo.full_name, pull["number"]),
        "review_comment_url": "%s/api/v3/repos/%s/pulls/comments{/number}" % (
            URL_BASE, repo.full_name),
        "comments_url": "%s/api/v3/repos/%s/issues/%d/comments" % (
            URL_BASE, repo.full_name, pull["number"]),
        "statuses_url": "%s/statuses/%s" % (URL_BASE, pull["merge_sha"] or ""),
        "head": ref_side(repo, pull["head"]),
        "base": ref_side(repo, pull["base"]),
        "_links": {
            "self": {"href": "%s/api/v3/repos/%s/pulls/%d" % (
                URL_BASE, repo.full_name, pull["number"])},
            "html": {"href": "%s/%s/pull/%d" % (
                URL_BASE, repo.full_name, pull["number"])},
            "issue": {"href": "%s/api/v3/repos/%s/issues/%d" % (
                URL_BASE, repo.full_name, pull["number"])},
            "comments": {"href": "%s/api/v3/repos/%s/issues/%d/comments" % (
                URL_BASE, repo.full_name, pull["number"])},
            "review_comments": {"href": "%s/api/v3/repos/%s/pulls/%d/comments" % (
                URL_BASE, repo.full_name, pull["number"])},
            "review_comment": {"href": "%s/api/v3/repos/%s/pulls/comments{/number}" % (
                URL_BASE, repo.full_name)},
            "commits": {"href": "%s/api/v3/repos/%s/pulls/%d/commits" % (
                URL_BASE, repo.full_name, pull["number"])},
            "statuses": {"href": "%s/statuses/%s" % (URL_BASE,
                                                     pull["merge_sha"] or "")},
        },
        "author_association": "OWNER",
        "auto_merge": None,
        "merged": pull["merged"],
        "mergeable": mergeable,
        "rebaseable": mergeable,
        "mergeable_state": ("clean" if mergeable else "dirty")
                           if mergeable is not None else "unknown",
        "merged_by": user_json(VIEWER["login"]) if pull["merged"] else None,
        "comments": len(pull["comments"]),
        "review_comments": 0,
        "maintainer_can_modify": False,
        "commits": _pr_commit_count(repo, pull),
        "additions": additions,
        "deletions": deletions,
        "changed_files": len(files),
    }
    return obj


def _pr_commit_count(repo, pull):
    base_tip = branch_tip(repo, pull["base"])
    head_tip = branch_tip(repo, pull["head"])
    if not head_tip:
        return 0
    count = 0
    seen = set()
    stack = [head_tip]
    while stack:
        current = stack.pop()
        if current in seen or (base_tip and is_ancestor(current, base_tip)):
            continue
        if base_tip and current == base_tip:
            continue
        seen.add(current)
        count += 1
        info = commit_info(current)
        if info:
            stack.extend(info[1])
        if count > 10000:
            break
    return count


# --------------------------------------------------------------------------
# HTTP core
#
# A threaded raw-socket HTTP/1.1 server.  Each connection thread runs a
# keep-alive loop over a buffered reader; a reply is one sendall of
# header-block + body.  Only the parsing the surfaces need is done:
# request line, a small header dict, Content-Length or chunked bodies.

REASONS = {
    200: "OK", 201: "Created", 202: "Accepted", 204: "No Content",
    301: "Moved Permanently", 302: "Found", 304: "Not Modified",
    400: "Bad Request", 401: "Unauthorized", 403: "Forbidden",
    404: "Not Found", 405: "Method Not Allowed", 409: "Conflict",
    422: "Unprocessable Entity", 500: "Internal Server Error",
}


class Request:
    __slots__ = ("method", "path", "query", "headers", "body", "host")

    def __init__(self, method, target, headers, body):
        self.method = method
        split = urlsplit(target)
        self.path = unquote(split.path)
        self.query = parse_qs(split.query)
        self.headers = headers
        self.body = body
        self.host = headers.get("host", "127.0.0.1")

    def header(self, name):
        return self.headers.get(name)

    def q(self, name, default=None):
        values = self.query.get(name)
        return values[0] if values else default

    def json(self):
        return json.loads(self.body.decode("utf-8"))


class Response:
    __slots__ = ("status", "body", "content_type", "headers")

    def __init__(self, status, body=b"", content_type="application/json",
                 headers=None):
        self.status = status
        self.body = body if isinstance(body, bytes) else body.encode("utf-8")
        self.content_type = content_type
        self.headers = headers or {}


def json_response(status, obj, headers=None):
    return Response(status, dumps(obj), "application/json", headers)


def api_error(status, message, **extra):
    return json_response(status, {"message": message, **extra})


class ConnectionHandler(socketserver.BaseRequestHandler):
    def handle(self):
        conn = self.request
        try:
            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        buf = b""
        while True:
            try:
                request, buf = self._read_request(conn, buf)
            except (ConnectionError, OSError):
                return
            if request is None:
                return
            try:
                response = dispatch(request)
            except Exception as exc:  # never hang a connection on a bug
                import traceback
                traceback.print_exc()
                response = api_error(500, "Internal error: %s" % exc)
            if not self._write_response(conn, request, response):
                return

    def _read_request(self, conn, buf):
        # headers
        while b"\r\n\r\n" not in buf:
            chunk = conn.recv(65536)
            if not chunk:
                return None, buf
            buf += chunk
            if len(buf) > 1 << 20:
                return None, buf
        head, buf = buf.split(b"\r\n\r\n", 1)
        lines = head.split(b"\r\n")
        parts = lines[0].decode("latin-1").split(" ")
        if len(parts) < 2:
            return None, buf
        method, target = parts[0], parts[1]
        headers = {}
        for line in lines[1:]:
            name, _, value = line.decode("latin-1").partition(":")
            headers[name.strip().lower()] = value.strip()
        # body
        body = b""
        if headers.get("expect", "").lower() == "100-continue":
            conn.sendall(b"HTTP/1.1 100 Continue\r\n\r\n")
        if "chunked" in headers.get("transfer-encoding", "").lower():
            while True:
                while b"\r\n" not in buf:
                    chunk = conn.recv(65536)
                    if not chunk:
                        return None, buf
                    buf += chunk
                size_line, buf = buf.split(b"\r\n", 1)
                size = int(size_line.split(b";")[0].strip(), 16)
                if size == 0:
                    # trailers up to the blank line
                    while not buf.startswith(b"\r\n"):
                        while b"\r\n" not in buf:
                            chunk = conn.recv(65536)
                            if not chunk:
                                return None, buf
                            buf += chunk
                        _line, buf = buf.split(b"\r\n", 1)
                    buf = buf[2:]
                    break
                while len(buf) < size + 2:
                    chunk = conn.recv(65536)
                    if not chunk:
                        return None, buf
                    buf += chunk
                body += buf[:size]
                buf = buf[size + 2:]
        else:
            length = int(headers.get("content-length") or 0)
            while len(buf) < length:
                chunk = conn.recv(65536)
                if not chunk:
                    return None, buf
                buf += chunk
            body, buf = buf[:length], buf[length:]
        return Request(method, target, headers, body), buf

    def _write_response(self, conn, request, response):
        keep_alive = request.headers.get("connection", "").lower() != "close"
        head = ["HTTP/1.1 %d %s" % (response.status,
                                    REASONS.get(response.status, ""))]
        if response.content_type:
            head.append("Content-Type: %s" % response.content_type)
        head.append("Content-Length: %d" % len(response.body))
        for name, value in response.headers.items():
            head.append("%s: %s" % (name, value))
        head.append("Connection: %s" % ("keep-alive" if keep_alive else "close"))
        payload = ("\r\n".join(head) + "\r\n\r\n").encode("latin-1") + response.body
        try:
            conn.sendall(payload)
        except (ConnectionError, OSError):
            return False
        return keep_alive


class ForgeServer(socketserver.ThreadingTCPServer):
    daemon_threads = True
    block_on_close = False
    request_queue_size = 512
    allow_reuse_address = True

    def get_request(self):
        conn, addr = super().get_request()
        try:
            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        return conn, addr


# --------------------------------------------------------------------------
# dispatch

def authed(request):
    return request.header("authorization") == "Bearer %s" % TOKEN


def dispatch(request):
    path = request.path
    if path == "/healthz":
        return json_response(200, {"status": "ok"})
    if path != "/" and path.endswith("/"):
        path = path.rstrip("/")
    if path.startswith("/api/v3") or path == "/api/graphql" or path == "/mcp":
        if not authed(request):
            return with_req_id(request, api_error(401, "Requires authentication"))
        if path.startswith("/api/v3"):
            return with_req_id(request, rest_dispatch(request, path))
        if path == "/api/graphql":
            return graphql_dispatch(request)
        return mcp_dispatch(request)
    if path == "/api" or path.startswith("/api/"):
        if not authed(request):
            return with_req_id(request, api_error(401, "Requires authentication"))
        return with_req_id(request, api_error(404, "Not Found"))
    return git_dispatch(request, path)


def with_req_id(request, response):
    if isinstance(response, Response):
        response.headers.setdefault("X-GitHub-Request-Id", request_id())
    return response


# --------------------------------------------------------------------------
# harness lifecycle: register the port, poll /done, exit when told

_done = threading.Event()


def _env_post(path, payload):
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(ENV_URL + path, data=data,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=10) as resp:
        return resp.read()


def _register(port):
    for _attempt in range(120):
        try:
            _env_post("/register", {"port": port})
            return True
        except Exception:
            time.sleep(0.5)
    return False


def _poll_done():
    while not _done.is_set():
        try:
            req = urllib.request.Request(ENV_URL + "/done")
            with urllib.request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            if data.get("done"):
                _done.set()
                return
        except Exception:
            pass
        time.sleep(0.4)


def main():
    if not ENV_URL:
        print("MAKEFUN_ENV_URL is not set", file=sys.stderr)
        return 1
    server = ForgeServer(("0.0.0.0", 0), ConnectionHandler)
    port = server.server_address[1]
    if not _register(port):
        print("could not register with the env", file=sys.stderr)
        return 1
    poller = threading.Thread(target=_poll_done, daemon=True)
    poller.start()
    server.timeout = 0.5
    while not _done.is_set():
        server.handle_request()
    server.server_close()
    return 0


# --------------------------------------------------------------------------
# git smart HTTP

FLUSH = b"0000"
DELIM = b"0001"


def pkt(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def parse_pkts(data):
    """Split a pkt-line stream into (packets, trailing_bytes).

    packets: list of ('data', bytes) | ('flush',) | ('delim',).
    Raises ValueError on malformed framing.
    """
    packets = []
    pos = 0
    total = len(data)
    while pos < total:
        if pos + 4 > total:
            raise ValueError("truncated pkt-line")
        try:
            length = int(data[pos:pos + 4].decode("ascii"), 16)
        except (ValueError, UnicodeDecodeError):
            raise ValueError("bad pkt-line length")
        if length == 0:
            packets.append(("flush",))
            pos += 4
            break
        if length == 1:
            packets.append(("delim",))
            pos += 4
            continue
        if length == 2:
            packets.append(("response-end",))
            pos += 4
            continue
        if length < 4 or pos + length > total:
            raise ValueError("bad pkt-line length")
        packets.append(("data", data[pos + 4:pos + length]))
        pos += length
    return packets, data[pos:]


def _sorted_refs(repo):
    return sorted(repo.refs.items())


def _peeled(oid):
    """Fully peel a tag object to the object it names (one ^{} step per git:
    the non-tag target)."""
    item = STORE.get(oid)
    if item and item[0] == "tag":
        target, _t, _n, _m = parse_tag(item[1])
        return target
    return None


def v0_advertisement(repo, service):
    if service == "git-upload-pack":
        caps = ("multi_ack_detailed side-band-64k thin-pack ofs-delta shallow "
                "agent=forge2/1.0 symref=HEAD:%s" % repo.head_ref())
        preamble = "# service=git-upload-pack\n"
    else:
        caps = ("report-status side-band-64k delete-refs ofs-delta quiet "
                "agent=forge2/1.0 symref=HEAD:%s" % repo.head_ref())
        preamble = "# service=git-receive-pack\n"
    out = [pkt(preamble), FLUSH]
    refs = _sorted_refs(repo)
    head_oid = repo.refs.get(repo.head_ref(), ZERO_OID)
    lines = []
    if not refs:
        lines.append("%s capabilities^{}\0%s" % (ZERO_OID, caps))
    else:
        lines.append("%s HEAD\0%s" % (head_oid, caps))
        for name, oid in refs:
            lines.append("%s %s" % (oid, name))
            peeled = _peeled(oid)
            if peeled:
                lines.append("%s %s^{}" % (peeled, name))
    for line in lines:
        out.append(pkt(line + "\n"))
    out.append(FLUSH)
    return b"".join(out)


def v2_advertisement(repo):
    lines = [
        "version 2",
        "agent=forge2/1.0",
        "ls-refs=unborn",
        "fetch=shallow wait-for-done thin-pack ofs-delta filter",
        "server-option",
        "object-format=sha1",
    ]
    return b"".join(pkt(line + "\n") for line in lines) + FLUSH


def parse_all_pkts(data):
    """Like parse_pkts but keeps going past flush packets (upload-pack v0
    sends two sections separated by a flush)."""
    packets = []
    pos = 0
    total = len(data)
    while pos < total:
        if pos + 4 > total:
            raise ValueError("truncated pkt-line")
        try:
            length = int(data[pos:pos + 4].decode("ascii"), 16)
        except (ValueError, UnicodeDecodeError):
            raise ValueError("bad pkt-line length")
        if length == 0:
            packets.append(("flush",))
            pos += 4
            continue
        if length == 1:
            packets.append(("delim",))
            pos += 4
            continue
        if length == 2:
            packets.append(("response-end",))
            pos += 4
            continue
        if length < 4 or pos + length > total:
            raise ValueError("bad pkt-line length")
        packets.append(("data", data[pos + 4:pos + length]))
        pos += length
    return packets


def ls_refs_response(repo, args):
    peel = "peel" in args
    symrefs = "symrefs" in args
    unborn = "unborn" in args
    prefixes = [a[len("ref-prefix "):] for a in args
                if a.startswith("ref-prefix ")]

    def wanted(name):
        return not prefixes or any(name.startswith(p) for p in prefixes)

    out = []
    head_ref = repo.head_ref()
    head_oid = repo.refs.get(head_ref)
    if wanted("HEAD"):
        if head_oid:
            line = "%s HEAD" % head_oid
            if symrefs:
                line += " symref-target:%s" % head_ref
            out.append(line)
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:%s" % head_ref
            out.append(line)
    for name, oid in _sorted_refs(repo):
        if not wanted(name):
            continue
        line = "%s %s" % (oid, name)
        if peel:
            peeled = _peeled(oid)
            if peeled:
                line += " peeled:%s" % peeled
        out.append(line)
    return b"".join(pkt(line + "\n") for line in out) + FLUSH


# ---- fetch machinery --------------------------------------------------------

def _object_closure(commit_oids):
    """All object ids (commits, trees, blobs, tags) reachable from commits."""
    seen = set()
    stack = list(commit_oids)
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        item = STORE.get(oid)
        if not item:
            continue
        seen.add(oid)
        otype, payload = item
        if otype == "commit":
            tree, parents, _a, _c, _m = parse_commit(payload)
            stack.append(tree)
            stack.extend(parents)
        elif otype == "tree":
            for _mode, _name, child in parse_tree(payload):
                stack.append(child)
        elif otype == "tag":
            target, _t, _n, _m = parse_tag(payload)
            if target:
                stack.append(target)
    return seen


def _object_closure_shallow(commit_oids):
    """The listed commits plus their trees/blobs — parents NOT followed."""
    seen = set()
    stack = []
    for oid in commit_oids:
        if oid not in seen:
            seen.add(oid)
            info = commit_info(oid)
            if info:
                stack.append(info[0])
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        item = STORE.get(oid)
        if not item:
            continue
        seen.add(oid)
        if item[0] == "tree":
            for _mode, _name, child in parse_tree(item[1]):
                stack.append(child)
        elif item[0] == "tag":
            target, _t, _n, _m = parse_tag(item[1])
            if target:
                stack.append(target)
    return seen


def compute_fetch(repo, wants, haves, client_shallow, depth, deepen_since,
                  deepen_not, filter_spec):
    """Work out (pack_bytes, shallow, unshallow) for one fetch request."""
    key = (repo.gen, tuple(sorted(wants)), tuple(sorted(haves)),
           tuple(sorted(client_shallow)), depth, deepen_since,
           tuple(sorted(deepen_not)), filter_spec)
    with STORE_LOCK:
        hit = repo.pack_cache.get(key)
    if hit is not None:
        return hit
    with _PACK_BUILD_LOCK:
        with STORE_LOCK:
            hit = repo.pack_cache.get(key)
        if hit is not None:
            return hit
        return _compute_fetch_locked(repo, key, wants, haves, client_shallow,
                                     depth, deepen_since, deepen_not,
                                     filter_spec)


def _compute_fetch_locked(repo, key, wants, haves, client_shallow, depth,
                          deepen_since, deepen_not, filter_spec):

    excluded_commits = set()
    # Haves the client itself lists as shallow do not exclude their
    # ancestry: a deepen request renegotiates that boundary.
    stack = [c for c in haves if c not in client_shallow]
    stack += list(deepen_not)
    while stack:
        current = stack.pop()
        if current in excluded_commits:
            continue
        info = commit_info(current)
        if not info:
            continue
        excluded_commits.add(current)
        stack.extend(info[1])
    excluded_objects = _object_closure(excluded_commits)

    # BFS from the wants, honouring depth / deepen-since cut-offs
    from collections import deque
    distance = {}
    queue = deque()
    extra_roots = []
    for want in wants:
        item = STORE.get(want)
        if not item:
            continue
        if item[0] == "commit":
            if want not in distance:
                distance[want] = 0
                queue.append(want)
        elif item[0] == "tag":
            extra_roots.append(want)
            target = peel_to_commit(want)
            if target and target not in distance:
                distance[target] = 0
                queue.append(target)
        else:
            extra_roots.append(want)
    shallow_new = set()
    while queue:
        current = queue.popleft()
        dist = distance[current]
        info = commit_info(current)
        if not info:
            continue
        for parent in info[1]:
            if parent in excluded_commits:
                continue
            if depth is not None and dist + 1 >= depth:
                shallow_new.add(current)
                continue
            pinfo = commit_info(parent)
            if deepen_since is not None and pinfo and pinfo[2] < deepen_since:
                shallow_new.add(current)
                continue
            if parent not in distance:
                distance[parent] = dist + 1
                queue.append(parent)
    included_commits = [c for c in distance if c not in excluded_commits]
    # a commit whose parents are all present is not a boundary any more
    shallow_new = {c for c in shallow_new
                   if c in distance and c not in client_shallow}
    unshallow = []
    for oid in client_shallow:
        if oid in distance:
            info = commit_info(oid)
            if info and any(p in distance for p in info[1]):
                unshallow.append(oid)

    included = _object_closure_shallow(included_commits)
    for root in extra_roots:
        item = STORE.get(root)
        if not item:
            continue
        if item[0] == "tree":
            included |= _object_closure_tree(root)
        else:
            included.add(root)
    send = [oid for oid in included if oid not in excluded_objects]
    if filter_spec:
        send = _apply_filter(send, filter_spec)
    commits = [oid for oid in send if STORE.type_of(oid) == "commit"]
    others = [oid for oid in send if STORE.type_of(oid) != "commit"]
    pack = write_pack(commits + others)
    result = (pack, sorted(shallow_new), sorted(unshallow))
    with STORE_LOCK:
        if len(repo.pack_cache) < 512:
            repo.pack_cache[key] = result
    return result


def _object_closure_tree(tree_oid):
    seen = set()
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        item = STORE.get(oid)
        if not item:
            continue
        seen.add(oid)
        if item[0] == "tree":
            for _m, _n, child in parse_tree(item[1]):
                stack.append(child)
    return seen


def _apply_filter(oids, filter_spec):
    if filter_spec.startswith("blob:none"):
        return [o for o in oids if STORE.type_of(o) != "blob"]
    if filter_spec.startswith("tree:0"):
        return [o for o in oids if STORE.type_of(o) == "commit"]
    if filter_spec.startswith("blob:limit="):
        try:
            limit = int(filter_spec[len("blob:limit="):])
        except ValueError:
            return oids
        return [o for o in oids
                if STORE.type_of(o) != "blob" or len(STORE.get(o)[1]) <= limit]
    return oids


def _sideband_packets(pack):
    out = []
    for start in range(0, len(pack), 65515):
        out.append(pkt(b"\x01" + pack[start:start + 65515]))
    if not out:
        out.append(pkt(b"\x01"))
    return b"".join(out)


def fetch_v2(repo, args, raw_args):
    wants, haves, shallow_in = [], [], []
    depth = None
    deepen_since = None
    deepen_not = []
    filter_spec = None
    done = False
    for arg in args:
        if arg.startswith("want "):
            wants.append(arg[5:])
        elif arg.startswith("have "):
            haves.append(arg[5:])
        elif arg.startswith("shallow "):
            shallow_in.append(arg[8:])
        elif arg.startswith("deepen-since "):
            try:
                deepen_since = int(arg[len("deepen-since "):])
            except ValueError:
                pass
        elif arg.startswith("deepen-not "):
            deepen_not.append(arg[len("deepen-not "):])
        elif arg.startswith("deepen "):
            try:
                depth = int(arg[len("deepen "):])
            except ValueError:
                pass
        elif arg.startswith("filter "):
            filter_spec = arg[len("filter "):]
        elif arg == "done":
            done = True
    pack, shallow_new, unshallow = compute_fetch(
        repo, wants, haves, shallow_in, depth, deepen_since, deepen_not,
        filter_spec)
    out = []
    if done or haves:
        out.append(pkt("acknowledgments\n"))
        acked = [h for h in haves if STORE.has(h)]
        if acked:
            out.append(pkt("ACK %s\n" % acked[0]))
        else:
            out.append(pkt("NAK\n"))
        out.append(FLUSH)
    if shallow_new or unshallow:
        out.append(pkt("shallow-info\n"))
        for oid in shallow_new:
            out.append(pkt("shallow %s\n" % oid))
        for oid in unshallow:
            out.append(pkt("unshallow %s\n" % oid))
        out.append(FLUSH)
    out.append(pkt("packfile\n"))
    out.append(_sideband_packets(pack))
    out.append(FLUSH)
    return b"".join(out)


def fetch_v0(repo, packets):
    wants, haves, shallow_in = [], [], []
    depth = None
    deepen_since = None
    deepen_not = []
    filter_spec = None
    for kind, *rest in packets:
        if kind != "data":
            continue
        line = rest[0].decode("utf-8", "replace").rstrip("\n")
        if line.startswith("want "):
            wants.append(line[5:].split(" ")[0])
        elif line.startswith("have "):
            haves.append(line[5:])
        elif line.startswith("shallow "):
            shallow_in.append(line[8:])
        elif line.startswith("deepen-since "):
            try:
                deepen_since = int(line[len("deepen-since "):])
            except ValueError:
                pass
        elif line.startswith("deepen-not "):
            deepen_not.append(line[len("deepen-not "):])
        elif line.startswith("deepen "):
            try:
                depth = int(line[len("deepen "):])
            except ValueError:
                pass
        elif line.startswith("filter "):
            filter_spec = line[len("filter "):]
    pack, shallow_new, unshallow = compute_fetch(
        repo, wants, haves, shallow_in, depth, deepen_since, deepen_not,
        filter_spec)
    out = []
    for oid in shallow_new:
        out.append(pkt("shallow %s\n" % oid))
    for oid in unshallow:
        out.append(pkt("unshallow %s\n" % oid))
    acked = [h for h in haves if STORE.has(h)]
    if acked:
        out.append(pkt("ACK %s\n" % acked[0]))
    else:
        out.append(pkt("NAK\n"))
    out.append(_sideband_packets(pack))
    out.append(FLUSH)
    return b"".join(out)


def receive_pack(repo, body):
    try:
        packets, rest = parse_pkts(body)
    except ValueError:
        return None
    commands = []
    caps = []
    for kind, *data in packets:
        if kind == "flush":
            break
        if kind != "data":
            continue
        line = data[0].decode("utf-8", "replace").rstrip("\n")
        if "\0" in line:
            line, capstr = line.split("\0", 1)
            caps = capstr.split(" ")
        parts = line.split(" ")
        if len(parts) == 3:
            commands.append((parts[0], parts[1], parts[2]))
    unpack_ok = True
    unpack_detail = "ok"
    if rest:
        try:
            with STORE_LOCK:
                read_pack(rest, STORE)
        except Exception as exc:
            unpack_ok = False
            unpack_detail = "index-pack failed: %s" % exc
    reports = []
    with STORE_LOCK:
        for old, new, ref in commands:
            if not unpack_ok:
                reports.append((ref, False, "unpack failed"))
                continue
            current = repo.refs.get(ref, ZERO_OID)
            if old != current:
                reports.append((ref, False, "reference update failed"))
                continue
            if new == ZERO_OID:
                repo.set_ref(ref, ZERO_OID)
                reports.append((ref, True, ""))
                continue
            if not STORE.has(new):
                reports.append((ref, False, "missing object"))
                continue
            if ref.startswith("refs/heads/") and old != ZERO_OID:
                new_commit = peel_to_commit(new)
                old_commit = peel_to_commit(old)
                if not new_commit or not old_commit or \
                        not is_ancestor(old_commit, new_commit):
                    reports.append((ref, False, "non-fast-forward"))
                    continue
            repo.set_ref(ref, new)
            reports.append((ref, True, ""))
    lines = ["unpack %s" % unpack_detail]
    for ref, ok, reason in reports:
        lines.append("ok %s" % ref if ok else "ng %s %s" % (ref, reason))
    stream = b"".join(pkt(line + "\n") for line in lines) + FLUSH
    if "side-band-64k" in caps:
        wrapped = []
        for start in range(0, len(stream), 65519):
            wrapped.append(pkt(b"\x01" + stream[start:start + 65515]))
        wrapped.append(FLUSH)
        return b"".join(wrapped)
    return stream


GIT_PATH_RE = re.compile(r"^/([^/]+)/(.+)\.git/(info/refs|git-upload-pack|"
                         r"git-receive-pack)$")


def git_dispatch(request, path):
    match = GIT_PATH_RE.match(path)
    if not match:
        return api_error(404, "Not Found")
    owner, name, service = match.group(1), match.group(2), match.group(3)
    if not authed(request):
        return api_error(401, "Requires authentication")
    repo = FORGE.get(owner, name)
    if repo is None:
        return api_error(404, "Not Found")
    if service == "info/refs":
        wanted = request.q("service")
        if wanted == "git-upload-pack":
            proto = request.header("git-protocol") or ""
            if "version=2" in proto:
                return Response(200, v2_advertisement(repo),
                                "application/x-git-upload-pack-advertisement")
            return Response(200, v0_advertisement(repo, "git-upload-pack"),
                            "application/x-git-upload-pack-advertisement")
        if wanted == "git-receive-pack":
            return Response(200, v0_advertisement(repo, "git-receive-pack"),
                            "application/x-git-receive-pack-advertisement")
        return api_error(400, "Bad service")
    if service == "git-upload-pack":
        body = request.body
        if b"command=" in body[:64]:
            try:
                packets = parse_all_pkts(body)
            except ValueError:
                return api_error(400, "Malformed upload-pack request")
            sections = [[]]
            command = None
            for kind, *data in packets:
                if kind == "delim":
                    sections.append([])
                    continue
                if kind == "flush":
                    break
                line = data[0].decode("utf-8", "replace").rstrip("\n")
                if line.startswith("command="):
                    command = line[len("command="):]
                else:
                    sections[-1].append(line)
            args = [a for section in sections for a in section]
            if command == "ls-refs":
                return Response(200, ls_refs_response(repo, args),
                                "application/x-git-upload-pack-result")
            if command == "fetch":
                return Response(200, fetch_v2(repo, args, body),
                                "application/x-git-upload-pack-result")
            return api_error(400, "Unknown command")
        try:
            packets = parse_all_pkts(body)
        except ValueError:
            return api_error(400, "Malformed upload-pack request")
        return Response(200, fetch_v0(repo, packets),
                        "application/x-git-upload-pack-result")
    # git-receive-pack
    result = receive_pack(repo, request.body)
    if result is None:
        return api_error(400, "Malformed receive-pack request")
    return Response(200, result, "application/x-git-receive-pack-result")


# --------------------------------------------------------------------------
# REST v3

def _pagination(request, items):
    try:
        per_page = int(request.q("per_page", "30"))
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(request.q("page", "1"))
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    chunk = items[start:start + per_page]
    headers = {}
    last_page = max(1, -(-total // per_page))
    if page < last_page or start + per_page < total:
        base = "http://%s%s" % (request.host, request.path)
        links = []
        nxt = "%s?page=%d&per_page=%d" % (base, page + 1, per_page)
        links.append('<%s>; rel="next"' % nxt)
        links.append('<%s?page=%d&per_page=%d>; rel="last"'
                     % (base, last_page, per_page))
        if page > 1:
            links.append('<%s?page=%d&per_page=%d>; rel="first"'
                         % (base, 1, per_page))
            links.append('<%s?page=%d&per_page=%d>; rel="prev"'
                         % (base, page - 1, per_page))
        headers["Link"] = ", ".join(links)
    return chunk, headers


def _body_json(request):
    """Parsed JSON body; {} for an empty body; None when malformed."""
    if not request.body:
        return {}
    try:
        value = json.loads(request.body.decode("utf-8"))
    except Exception:
        return None
    return value if isinstance(value, dict) else {"_value": value}


def _ident_json(ident_line):
    m = re.match(r"^(.*?) <(.*?)> (\d+) ([+-]\d{4})$", ident_line or "")
    if not m:
        return {"name": "", "email": "", "date": iso8601(_EPOCH)}
    return {"name": m.group(1), "email": m.group(2),
            "date": iso8601(int(m.group(3)))}


def commit_json(oid):
    item = STORE.get(oid)
    if not item or item[0] != "commit":
        return None
    tree, parents, author, committer, message = parse_commit(item[1])
    return {
        "sha": oid,
        "node_id": node_id("Commit", int(oid[:8], 16)),
        "url": "%s/api/v3/repos/commits/%s" % (URL_BASE, oid),
        "html_url": "%s/commit/%s" % (URL_BASE, oid),
        "author": _ident_json(author),
        "committer": _ident_json(committer),
        "message": message,
        "tree": {"sha": tree, "url": "%s/api/v3/git/trees/%s" % (URL_BASE, tree)},
        "parents": [{"sha": p, "url": "%s/api/v3/commits/%s" % (URL_BASE, p),
                     "html_url": "%s/commit/%s" % (URL_BASE, p)}
                    for p in parents],
        "comment_count": 0,
        "verification": {"verified": False, "reason": "unsigned",
                         "signature": None, "payload": None},
    }


def _full_commit_json(repo, oid):
    """The GitHub commit shape: top-level sha plus a nested commit object."""
    entry = commit_json(oid)
    if entry is None:
        return None
    entry["url"] = "%s/api/v3/repos/%s/commits/%s" % (
        URL_BASE, repo.full_name, oid)
    entry["html_url"] = "%s/%s/commit/%s" % (URL_BASE, repo.full_name, oid)
    full = dict(entry)
    full["commit"] = {
        "author": entry["author"], "committer": entry["committer"],
        "message": entry["message"], "tree": entry["tree"],
        "url": entry["url"], "comment_count": 0,
        "verification": entry["verification"],
    }
    full["author"] = user_json(VIEWER["login"])
    full["committer"] = user_json(VIEWER["login"])
    return full


def commit_list_json(repo, tip):
    out = []
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid in seen or not STORE.has(oid):
            continue
        seen.add(oid)
        entry = _full_commit_json(repo, oid)
        if entry is None:
            continue
        out.append(entry)
        info = commit_info(oid)
        if info:
            for parent in reversed(info[1]):
                stack.append(parent)
    return out


# ---- repositories -----------------------------------------------------------

def rest_root(request):
    urls = {key: "%s%s" % (URL_BASE, tpl) for key, tpl in {
        "current_user_url": "/api/v3/user",
        "current_user_authorizations_html_url": "/settings/connections/applications",
        "authorizations_url": "/api/v3/authorizations",
        "code_search_url": "/api/v3/search/code?q={query}",
        "commit_search_url": "/api/v3/search/commits?q={query}",
        "emails_url": "/api/v3/user/emails",
        "emojis_url": "/api/v3/emojis",
        "events_url": "/api/v3/events",
        "feeds_url": "/api/v3/feeds",
        "following_url": "/api/v3/user/following{/target}",
        "gists_url": "/api/v3/gists{/gist_id}",
        "hub_url": "/api/v3/hub",
        "issue_search_url": "/api/v3/search/issues?q={query}",
        "issues_url": "/api/v3/issues",
        "keys_url": "/api/v3/user/keys",
        "label_search_url": "/api/v3/search/labels?q={query}&repository_id={repository_id}",
        "notifications_url": "/api/v3/notifications",
        "organization_url": "/api/v3/orgs{/org}",
        "organization_repositories_url": "/api/v3/orgs{/org}/repos",
        "public_gists_url": "/api/v3/gists/public",
        "rate_limit_url": "/api/v3/rate_limit",
        "repository_url": "/api/v3/repos{/owner}{/repo}",
        "repository_search_url": "/api/v3/search/repositories?q={query}",
        "starred_url": "/api/v3/user/starred{/owner}{/repo}",
        "starred_gists_url": "/api/v3/gists/starred",
        "team_url": "/api/v3/teams",
        "user_url": "/api/v3/users{/user}",
        "user_organizations_url": "/api/v3/user/orgs",
        "user_repositories_url": "/api/v3/user/repos",
        "user_search_url": "/api/v3/search/users?q={query}",
    }.items()}
    return json_response(200, urls,
                         headers={"X-OAuth-Scopes": "repo, user, admin:org"})


def rest_create_repo(request):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    name = body.get("name")
    if not name or not isinstance(name, str):
        return api_error(422, "Validation Failed",
                         errors=[{"resource": "Repository", "code": "missing_field",
                                  "field": "name"}])
    with STORE_LOCK:
        if FORGE.get(VIEWER["login"], name) is not None:
            return api_error(422, "Repository creation failed.",
                             errors=[{"resource": "Repository",
                                      "code": "custom", "field": "name",
                                      "message": "name already exists on this account"}])
        repo = FORGE.create(name, body.get("description") or "",
                            body.get("private", False))
        if body.get("auto_init"):
            flat = {}
            if body.get("readme") is not False:
                blob = STORE.put("blob", ("# %s\n" % name).encode("utf-8"))
                flat["README.md"] = ("100644", blob)
            tree = tree_from_flat(flat)
            sha = make_commit(tree, [], "Initial commit")
            repo.set_ref(repo.head_ref(), sha)
        return json_response(201, repo_json(repo))


def rest_get_repo(repo):
    return json_response(200, repo_json(repo))


def rest_patch_repo(request, repo):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        if "description" in body:
            repo.description = body["description"] or ""
        if "private" in body:
            repo.private = bool(body["private"])
        if "default_branch" in body and body["default_branch"]:
            repo.default_branch = body["default_branch"]
        if "has_issues" in body:
            pass
        new_name = body.get("name")
        if new_name and new_name != repo.name:
            FORGE.repos.pop(repo.full_name, None)
            repo.name = new_name
            FORGE.repos[repo.full_name] = repo
        repo.updated_tick = tick()
        return json_response(200, repo_json(repo))


def rest_delete_repo(repo):
    with STORE_LOCK:
        FORGE.delete(repo)
    return Response(204, b"", None)


def rest_list_user_repos(request):
    repos = [repo_json(r) for r in FORGE.user_repos()]
    chunk, headers = _pagination(request, repos)
    return json_response(200, chunk, headers)


# ---- contents ---------------------------------------------------------------

def _tree_entry_at(tree_oid, path):
    """(mode, oid) for path inside a tree, or None."""
    if not path:
        return ("40000", tree_oid)
    parts = path.split("/")
    current = tree_oid
    for index, part in enumerate(parts):
        item = STORE.get(current)
        if not item or item[0] != "tree":
            return None
        found = None
        for mode, name, oid in parse_tree(item[1]):
            if name == part:
                found = (mode, oid)
                break
        if found is None:
            return None
        if index == len(parts) - 1:
            return found
        if found[0] != "40000":
            return None
        current = found[1]
    return None


def _dir_listing(repo, tree_oid, path):
    item = STORE.get(tree_oid)
    entries = []
    if not item or item[0] != "tree":
        return entries
    for mode, name, oid in parse_tree(item[1]):
        child_path = "%s/%s" % (path, name) if path else name
        entry = {
            "name": name,
            "path": child_path,
            "sha": oid,
            "size": 0,
            "url": "%s/api/v3/repos/%s/contents/%s" % (
                URL_BASE, repo.full_name, child_path),
            "html_url": "%s/%s/blob/%s/%s" % (
                URL_BASE, repo.full_name, repo.default_branch, child_path),
            "git_url": "%s/api/v3/repos/%s/git/blobs/%s" % (
                URL_BASE, repo.full_name, oid),
            "download_url": None,
            "type": "dir" if mode == "40000" else "file",
            "_links": {
                "self": "%s/api/v3/repos/%s/contents/%s" % (
                    URL_BASE, repo.full_name, child_path),
                "git": "%s/api/v3/repos/%s/git/blobs/%s" % (
                    URL_BASE, repo.full_name, oid),
                "html": "%s/%s/blob/%s/%s" % (
                    URL_BASE, repo.full_name, repo.default_branch, child_path),
            },
        }
        if mode != "40000":
            blob = STORE.get(oid)
            entry["size"] = len(blob[1]) if blob else 0
            entry["download_url"] = "%s/%s/raw/%s/%s" % (
                URL_BASE, repo.full_name, repo.default_branch, child_path)
        entries.append(entry)
    return entries


def _content_file_json(repo, path, mode, oid, ref_name):
    blob = STORE.get(oid)
    data = blob[1] if blob else b""
    encoded = base64.b64encode(data).decode("ascii")
    wrapped = "\n".join(encoded[i:i + 60] for i in range(0, len(encoded), 60))
    if wrapped:
        wrapped += "\n"
    return {
        "name": path.split("/")[-1],
        "path": path,
        "sha": oid,
        "size": len(data),
        "url": "%s/api/v3/repos/%s/contents/%s" % (URL_BASE, repo.full_name, path),
        "html_url": "%s/%s/blob/%s/%s" % (URL_BASE, repo.full_name, ref_name, path),
        "git_url": "%s/api/v3/repos/%s/git/blobs/%s" % (
            URL_BASE, repo.full_name, oid),
        "download_url": "%s/%s/raw/%s/%s" % (URL_BASE, repo.full_name,
                                             ref_name, path),
        "type": "file",
        "content": wrapped,
        "encoding": "base64",
        "_links": {
            "self": "%s/api/v3/repos/%s/contents/%s" % (
                URL_BASE, repo.full_name, path),
            "git": "%s/api/v3/repos/%s/git/blobs/%s" % (
                URL_BASE, repo.full_name, oid),
            "html": "%s/%s/blob/%s/%s" % (URL_BASE, repo.full_name, ref_name,
                                          path),
        },
    }


def _resolve_commit(repo, ref_name):
    if not ref_name:
        ref_name = repo.default_branch
    oid = repo.branch_oid(ref_name)
    if oid:
        return peel_to_commit(oid), ref_name
    if STORE.has(ref_name):
        return peel_to_commit(ref_name), ref_name
    tagged = repo.refs.get("refs/tags/%s" % ref_name)
    if tagged:
        return peel_to_commit(tagged), ref_name
    return None, ref_name


def rest_get_contents(request, repo, path):
    ref_name = request.q("ref")
    commit, ref_name = _resolve_commit(repo, ref_name)
    if not commit:
        if path:
            return api_error(404, "Not Found")
        return json_response(200, [])
    info = commit_info(commit)
    found = _tree_entry_at(info[0], path)
    if found is None:
        return api_error(404, "Not Found")
    mode, oid = found
    if mode == "40000":
        return json_response(200, _dir_listing(repo, oid, path))
    return json_response(200, _content_file_json(repo, path, mode, oid,
                                                 ref_name))


def rest_put_contents(request, repo, path):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    if not path:
        return api_error(422, "Validation Failed")
    content_b64 = body.get("content")
    if content_b64 is None:
        return api_error(422, "Validation Failed",
                         errors=[{"resource": "Content", "code": "missing_field",
                                  "field": "content"}])
    try:
        data = base64.b64decode(content_b64)
    except Exception:
        return api_error(422, "Validation Failed")
    branch = body.get("branch") or repo.default_branch
    message = body.get("message") or ("Update %s" % path)
    with STORE_LOCK:
        tip = branch_tip(repo, branch)
        flat = {}
        if tip:
            info = commit_info(tip)
            flat = flatten_tree(info[0])
        existing = flat.get(path)
        sha_given = body.get("sha")
        if existing is not None:
            if sha_given is None:
                return api_error(422, "Validation Failed",
                                 errors=[{"resource": "Content",
                                          "code": "missing_field",
                                          "field": "sha",
                                          "message": "\"sha\" wasn't supplied"}])
            if sha_given != existing[1]:
                return api_error(409, "%s does not match %s" % (
                    sha_given, existing[1]))
            status = 200
        else:
            if sha_given:
                return api_error(422, "Validation Failed")
            status = 201
        blob_oid = STORE.put("blob", data)
        flat[path] = (existing[0] if existing else "100644", blob_oid)
        tree = tree_from_flat(flat)
        parents = [tip] if tip else []
        sha = make_commit(tree, parents, message)
        repo.set_ref("refs/heads/%s" % branch, sha)
        content = _content_file_json(repo, path, flat[path][0], blob_oid,
                                     branch)
        return json_response(status, {"content": content,
                                      "commit": commit_json(sha)})


def rest_delete_contents(request, repo, path):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    branch = body.get("branch") or repo.default_branch
    message = body.get("message") or ("Delete %s" % path)
    with STORE_LOCK:
        tip = branch_tip(repo, branch)
        if not tip:
            return api_error(404, "Not Found")
        info = commit_info(tip)
        flat = flatten_tree(info[0])
        existing = flat.get(path)
        if existing is None:
            return api_error(404, "Not Found")
        sha_given = body.get("sha")
        if sha_given and sha_given != existing[1]:
            return api_error(409, "%s does not match %s" % (
                sha_given, existing[1]))
        del flat[path]
        tree = tree_from_flat(flat)
        sha = make_commit(tree, [tip], message)
        repo.set_ref("refs/heads/%s" % branch, sha)
        return json_response(200, {"content": None,
                                   "commit": commit_json(sha)})


# ---- labels -------------------------------------------------------------------

def rest_list_labels(request, repo):
    labels = [label_json(repo, repo.labels[name])
              for name in sorted(repo.labels)]
    chunk, headers = _pagination(request, labels)
    return json_response(200, chunk, headers)


def rest_create_label(request, repo):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    name = body.get("name")
    if not name:
        return api_error(422, "Validation Failed")
    with STORE_LOCK:
        if name in repo.labels:
            return api_error(422, "Validation Failed",
                             errors=[{"resource": "Label", "code": "already_exists",
                                      "field": "name"}])
        label = new_label(repo, name, body.get("color"),
                          body.get("description"))
        return json_response(201, label_json(repo, label))


def rest_get_label(repo, name):
    label = repo.labels.get(name)
    if label is None:
        return api_error(404, "Not Found")
    return json_response(200, label_json(repo, label))


def rest_patch_label(request, repo, name):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        label = repo.labels.get(name)
        if label is None:
            return api_error(404, "Not Found")
        new_name = body.get("new_name") or body.get("name")
        if "color" in body:
            label["color"] = body["color"]
        if "description" in body:
            label["description"] = body["description"]
        if new_name and new_name != name:
            del repo.labels[name]
            label["name"] = new_name
            repo.labels[new_name] = label
            for item in repo.items.values():
                item["labels"] = [new_name if n == name else n
                                  for n in item["labels"]]
        return json_response(200, label_json(repo, label))


def rest_delete_label(repo, name):
    with STORE_LOCK:
        if name not in repo.labels:
            return api_error(404, "Not Found")
        del repo.labels[name]
    return Response(204, b"", None)


# ---- issues & comments --------------------------------------------------------

def _label_names_from(body, repo):
    """Resolve a body's labels field to names; None when one is unknown."""
    raw = body.get("labels")
    if raw is None:
        return []
    names = []
    for entry in raw:
        name = entry.get("name") if isinstance(entry, dict) else entry
        if name not in repo.labels:
            return None
        names.append(name)
    return names


def rest_create_issue(request, repo):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    title = body.get("title")
    if title is None:
        return api_error(422, "Validation Failed",
                         errors=[{"resource": "Issue", "code": "missing_field",
                                  "field": "title"}])
    with STORE_LOCK:
        names = _label_names_from(body, repo)
        if names is None:
            bad = [e.get("name") if isinstance(e, dict) else e
                   for e in body.get("labels") or []]
            return api_error(422, "Validation Failed",
                             errors=[{"resource": "Label", "code": "invalid",
                                      "field": "labels", "value": bad}])
        issue = new_issue(repo, title, body.get("body") or "", names)
        return Response(201, issue["_json"], "application/json")


def _filter_items(request, repo, kind):
    state = request.q("state", "open")
    items = [it for it in repo.items.values() if it["kind"] == kind]
    if state == "open":
        items = [it for it in items if it["state"] == "open"]
    elif state == "closed":
        items = [it for it in items if it["state"] == "closed"]
    labels_q = request.q("labels")
    if labels_q:
        wanted = [n.strip() for n in labels_q.split(",") if n.strip()]
        items = [it for it in items
                 if all(n in it["labels"] for n in wanted)]
    sort = request.q("sort", "created")
    direction = request.q("direction", "desc")
    key = {"created": "created", "updated": "updated"}.get(sort, "created")
    if sort == "comments":
        items.sort(key=lambda it: len(it["comments"]),
                   reverse=(direction != "asc"))
    else:
        items.sort(key=lambda it: (it[key], it["number"]),
                   reverse=(direction != "asc"))
    return items


def rest_list_issues(request, repo):
    items = _filter_items(request, repo, "issue")
    objs = [issue_json_obj(repo, it) for it in items]
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_get_issue(repo, number):
    item = repo.items.get(number)
    if item is None:
        return api_error(404, "Not Found")
    if item["kind"] == "issue":
        return Response(200, item["_json"], "application/json")
    return json_response(200, issue_json_obj(repo, item))


def rest_patch_issue(request, repo, number):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        item = repo.items.get(number)
        if item is None:
            return api_error(404, "Not Found")
        if "labels" in body and body["labels"] is not None:
            names = _label_names_from(body, repo)
            if names is None:
                return api_error(422, "Validation Failed",
                                 errors=[{"resource": "Label", "code": "invalid",
                                          "field": "labels"}])
            item["labels"] = names
        if "title" in body:
            item["title"] = body["title"] or ""
        if "body" in body:
            item["body"] = body["body"] or ""
        if "state" in body:
            new_state = body["state"]
            if new_state in ("open", "closed"):
                if new_state == "closed" and item["state"] == "open":
                    item["closed"] = tick()
                if new_state == "open":
                    item["closed"] = None
                item["state"] = new_state
        item["updated"] = tick()
        if item["kind"] == "issue":
            refresh_issue_json(repo, item)
            return Response(200, item["_json"], "application/json")
        return json_response(200, pull_json_obj(repo, item))


def rest_list_comments(request, repo, number):
    item = repo.items.get(number)
    if item is None:
        return api_error(404, "Not Found")
    objs = [comment_json(repo, item, c) for c in item["comments"]]
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_create_comment(request, repo, number):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        item = repo.items.get(number)
        if item is None:
            return api_error(404, "Not Found")
        if body.get("body") is None:
            return api_error(422, "Validation Failed",
                             errors=[{"resource": "IssueComment",
                                      "code": "missing_field", "field": "body"}])
        comment = new_comment(item, body.get("body"))
        if item["kind"] == "issue":
            refresh_issue_json(repo, item)
        return json_response(201, comment_json(repo, item, comment))


def rest_get_comment(repo, gid):
    item, comment = find_comment(repo, gid)
    if comment is None:
        return api_error(404, "Not Found")
    return json_response(200, comment_json(repo, item, comment))


def rest_patch_comment(request, repo, gid):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        item, comment = find_comment(repo, gid)
        if comment is None:
            return api_error(404, "Not Found")
        if "body" in body:
            comment["body"] = body["body"] or ""
        comment["updated"] = tick()
        return json_response(200, comment_json(repo, item, comment))


def rest_delete_comment(repo, gid):
    with STORE_LOCK:
        item, comment = find_comment(repo, gid)
        if comment is None:
            return api_error(404, "Not Found")
        item["comments"].remove(comment)
        if item["kind"] == "issue":
            refresh_issue_json(repo, item)
    return Response(204, b"", None)


# ---- pull requests --------------------------------------------------------------

def _split_head(head):
    """'owner:branch' or 'branch' -> branch name."""
    if ":" in head:
        return head.split(":", 1)[1]
    return head


def rest_create_pull(request, repo):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    title = body.get("title")
    head = body.get("head")
    base = body.get("base")
    if title is None or head is None or base is None:
        return api_error(422, "Validation Failed",
                         errors=[{"resource": "PullRequest",
                                  "code": "missing_field",
                                  "field": "title" if title is None else
                                           "head" if head is None else "base"}])
    head_branch = _split_head(head)
    with STORE_LOCK:
        if repo.branch_oid(head_branch) is None:
            return api_error(422, "Validation Failed",
                             errors=[{"resource": "PullRequest", "code": "invalid",
                                      "field": "head",
                                      "message": "head branch does not exist"}])
        if repo.branch_oid(base) is None:
            return api_error(422, "Validation Failed",
                             errors=[{"resource": "PullRequest", "code": "invalid",
                                      "field": "base",
                                      "message": "base branch does not exist"}])
        for item in repo.items.values():
            if item["kind"] == "pr" and item["state"] == "open" and \
                    item["head"] == head_branch and item["base"] == base:
                return api_error(422, "Validation Failed",
                                 errors=[{"resource": "PullRequest",
                                          "code": "custom",
                                          "message": "A pull request already exists for %s." % head_branch}])
        pull = new_pull(repo, title, body.get("body") or "", head_branch, base)
        return json_response(201, pull_json_obj(repo, pull))


def rest_list_pulls(request, repo):
    items = _filter_items(request, repo, "pr")
    objs = [pull_json_obj(repo, it) for it in items]
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def _get_pull(repo, number):
    item = repo.items.get(number)
    if item is None or item["kind"] != "pr":
        return None
    return item


def rest_get_pull(repo, number):
    pull = _get_pull(repo, number)
    if pull is None:
        return api_error(404, "Not Found")
    return json_response(200, pull_json_obj(repo, pull))


def rest_patch_pull(request, repo, number):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        pull = _get_pull(repo, number)
        if pull is None:
            return api_error(404, "Not Found")
        if "title" in body:
            pull["title"] = body["title"] or ""
        if "body" in body:
            pull["body"] = body["body"] or ""
        if "state" in body and body["state"] in ("open", "closed"):
            if body["state"] == "closed" and pull["state"] == "open":
                pull["closed"] = tick()
            if body["state"] == "open":
                pull["closed"] = None
            pull["state"] = body["state"]
        if "base" in body and body["base"]:
            pull["base"] = body["base"]
        pull["updated"] = tick()
        return json_response(200, pull_json_obj(repo, pull))


def rest_pull_files(request, repo, number):
    pull = _get_pull(repo, number)
    if pull is None:
        return api_error(404, "Not Found")
    files = pr_files(repo, pull)
    chunk, headers = _pagination(request, files)
    return json_response(200, chunk, headers)


def rest_pull_commits(request, repo, number):
    pull = _get_pull(repo, number)
    if pull is None:
        return api_error(404, "Not Found")
    head_tip = branch_tip(repo, pull["head"])
    base_tip = branch_tip(repo, pull["base"])
    objs = []
    if head_tip:
        for entry in commit_list_json(repo, head_tip):
            if base_tip and is_ancestor(entry["sha"], base_tip):
                continue
            objs.append(entry)
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_merge_pull(request, repo, number):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    with STORE_LOCK:
        pull = _get_pull(repo, number)
        if pull is None:
            return api_error(404, "Not Found")
        if pull["merged"]:
            return api_error(405, "Pull Request is not mergeable")
        if pull["state"] == "closed":
            return api_error(405, "Pull Request is not mergeable")
        sha, conflict = squash_merge(repo, pull)
        if conflict:
            return api_error(405, "Pull Request is not mergeable")
        pull["merged"] = True
        pull["state"] = "closed"
        pull["merged_at"] = tick()
        pull["closed"] = pull["merged_at"]
        pull["merge_sha"] = sha
        pull["updated"] = pull["merged_at"]
        return json_response(200, {
            "sha": sha,
            "merged": True,
            "message": "Pull Request successfully merged",
        })


def rest_pull_merged(repo, number):
    pull = _get_pull(repo, number)
    if pull is None:
        return api_error(404, "Not Found")
    if pull["merged"]:
        return Response(204, b"", None)
    return api_error(404, "Not Found")


# ---- branches, commits, refs, tags ----------------------------------------------

def _branch_json(repo, name):
    oid = repo.branch_oid(name)
    return {
        "name": name,
        "commit": {"sha": oid,
                   "url": "%s/api/v3/repos/%s/commits/%s" % (
                       URL_BASE, repo.full_name, oid)},
        "protected": False,
        "_links": {
            "self": "%s/api/v3/repos/%s/branches/%s" % (
                URL_BASE, repo.full_name, name),
            "html": "%s/%s/tree/%s" % (URL_BASE, repo.full_name, name),
        },
    }


def rest_list_branches(request, repo):
    names = sorted(ref[len("refs/heads/"):] for ref in repo.refs
                   if ref.startswith("refs/heads/"))
    objs = [_branch_json(repo, name) for name in names]
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_get_branch(repo, name):
    if repo.branch_oid(name) is None:
        return api_error(404, "Not Found")
    obj = _branch_json(repo, name)
    tip = branch_tip(repo, name)
    if tip:
        obj["commit"] = commit_list_json(repo, tip)[0]
    return json_response(200, obj)


def rest_list_commits(request, repo):
    ref_name = request.q("sha") or repo.default_branch
    commit, _ref = _resolve_commit(repo, ref_name)
    if not commit:
        return json_response(200, [])
    objs = commit_list_json(repo, commit)
    per = request.q("per_page")
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_get_commit(repo, sha):
    full = _full_commit_json(repo, sha)
    if full is None:
        return api_error(404, "Not Found")
    return json_response(200, full)


def _ref_json(repo, ref):
    oid = repo.refs[ref]
    otype = STORE.type_of(oid) or "commit"
    return {
        "ref": ref,
        "node_id": node_id("Ref", int(oid[:8], 16)),
        "url": "%s/api/v3/repos/%s/git/refs/%s" % (
            URL_BASE, repo.full_name, ref[len("refs/"):]),
        "object": {"type": otype, "sha": oid,
                   "url": "%s/api/v3/repos/%s/git/commits/%s" % (
                       URL_BASE, repo.full_name, oid)},
    }


def rest_list_refs(request, repo, namespace=None):
    refs = sorted(repo.refs)
    if namespace:
        prefix = "refs/%s/" % namespace
        refs = [r for r in refs if r.startswith(prefix)]
    objs = [_ref_json(repo, r) for r in refs]
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


def rest_get_ref(repo, refname):
    ref = "refs/%s" % refname
    if ref not in repo.refs:
        # namespace listing fallback
        prefix = ref + "/"
        matches = [r for r in sorted(repo.refs) if r.startswith(prefix)]
        if matches:
            return json_response(200, [_ref_json(repo, r) for r in matches])
        return api_error(404, "Not Found")
    return json_response(200, _ref_json(repo, ref))


def rest_create_ref(request, repo):
    body = _body_json(request)
    if body is None:
        return api_error(400, "Problems parsing JSON")
    ref = body.get("ref") or ""
    sha = body.get("sha") or ""
    if not ref.startswith("refs/") or not STORE.has(sha):
        return api_error(422, "Validation Failed")
    with STORE_LOCK:
        if ref in repo.refs:
            return api_error(422, "Reference already exists")
        repo.set_ref(ref, sha)
        return json_response(201, _ref_json(repo, ref))


def rest_delete_ref(repo, refname):
    ref = "refs/%s" % refname
    with STORE_LOCK:
        if ref not in repo.refs:
            return api_error(422, "Reference does not exist")
        repo.set_ref(ref, ZERO_OID)
    return Response(204, b"", None)


def rest_list_tags(request, repo):
    objs = []
    for ref in sorted(repo.refs):
        if not ref.startswith("refs/tags/"):
            continue
        oid = repo.refs[ref]
        target = peel_to_commit(oid) or oid
        objs.append({
            "name": ref[len("refs/tags/"):],
            "commit": {"sha": target,
                       "url": "%s/api/v3/repos/%s/commits/%s" % (
                           URL_BASE, repo.full_name, target)},
            "zipball_url": "%s/api/v3/repos/%s/zipball/%s" % (
                URL_BASE, repo.full_name, ref[len("refs/tags/"):]),
            "tarball_url": "%s/api/v3/repos/%s/tarball/%s" % (
                URL_BASE, repo.full_name, ref[len("refs/tags/"):]),
            "node_id": node_id("Tag", int(oid[:8], 16)),
        })
    chunk, headers = _pagination(request, objs)
    return json_response(200, chunk, headers)


# ---- search -----------------------------------------------------------------------

def rest_search(request, kind):
    query = request.q("q", "") or ""
    needle = query.lower()
    if kind == "repositories":
        items = [repo_json(r) for r in FORGE.user_repos()
                 if needle in r.name.lower() or needle in r.full_name.lower()
                 or needle in r.description.lower()]
    elif kind == "issues":
        items = []
        for repo in FORGE.user_repos():
            for item in repo.items.values():
                if item["kind"] == "issue" and (
                        needle in item["title"].lower()
                        or needle in item["body"].lower()):
                    items.append(issue_json_obj(repo, item))
    else:  # users
        items = [user_json(u["login"]) for u in KNOWN_USERS.values()
                 if needle in u["login"].lower()]
    chunk, headers = _pagination(request, items)
    return json_response(200, {
        "total_count": len(items),
        "incomplete_results": False,
        "items": chunk,
    }, headers)


# ---- router ---------------------------------------------------------------------------

_REPO = r"/api/v3/repos/([^/]+)/([^/]+)"


def rest_dispatch(request, path):
    method = request.method
    if path == "/api/v3":
        if method == "GET":
            return rest_root(request)
        return api_error(404, "Not Found")
    if path == "/api/v3/meta":
        if method == "GET":
            return json_response(200, {
                "verifiable_password_authentication": False,
                "ssh_key_fingerprints": {"SHA256_RSA": "", "SHA256_ECDSA": "",
                                         "SHA256_ED25519": ""},
                "ssh_keys": [],
                "hooks": [],
                "github_services_sha": "forge2",
                "installed_version": "3.10.0.forge2",
            })
        return api_error(404, "Not Found")
    if path == "/api/v3/user":
        if method == "GET":
            return json_response(200, user_json(VIEWER["login"]))
        return api_error(404, "Not Found")
    if path == "/api/v3/rate_limit":
        if method == "GET":
            reset = _EPOCH + 3600
            rate = {"limit": 5000, "used": 1, "remaining": 4999,
                    "reset": reset}
            return json_response(200, {
                "resources": {
                    "core": dict(rate), "search": {
                        "limit": 30, "used": 0, "remaining": 30,
                        "reset": reset},
                    "graphql": dict(rate), "integration_manifest": dict(rate),
                    "code_scanning_upload": dict(rate),
                },
                "rate": dict(rate),
            })
        return api_error(404, "Not Found")
    if path == "/api/v3/user/repos":
        if method == "GET":
            return rest_list_user_repos(request)
        if method == "POST":
            return rest_create_repo(request)
        return api_error(404, "Not Found")
    m = re.match(r"^/api/v3/users/([^/]+)$", path)
    if m:
        if method == "GET":
            login = m.group(1)
            if login in KNOWN_USERS:
                return json_response(200, user_json(login))
            return api_error(404, "Not Found")
        return api_error(404, "Not Found")
    m = re.match(r"^/api/v3/users/([^/]+)/repos$", path)
    if m:
        if method == "GET":
            if m.group(1) == VIEWER["login"]:
                return rest_list_user_repos(request)
            chunk, headers = _pagination(request, [])
            return json_response(200, chunk, headers)
        return api_error(404, "Not Found")
    m = re.match(r"^/api/v3/orgs/([^/]+)/repos$", path)
    if m:
        if method == "GET":
            chunk, headers = _pagination(request, [])
            return json_response(200, chunk, headers)
        return api_error(404, "Not Found")
    m = re.match(r"^/api/v3/search/(repositories|issues|users)$", path)
    if m:
        if method == "GET":
            return rest_search(request, m.group(1))
        return api_error(404, "Not Found")
    m = re.match(r"^" + _REPO + r"$", path)
    if m:
        repo = FORGE.get(m.group(1), m.group(2))
        if repo is None:
            return api_error(404, "Not Found")
        if method == "GET":
            return rest_get_repo(repo)
        if method == "PATCH":
            return rest_patch_repo(request, repo)
        if method == "DELETE":
            return rest_delete_repo(repo)
        return api_error(404, "Not Found")
    m = re.match(r"^" + _REPO + r"/(.*)$", path)
    if not m:
        return api_error(404, "Not Found")
    repo = FORGE.get(m.group(1), m.group(2))
    if repo is None:
        return api_error(404, "Not Found")
    sub = m.group(3)
    return _repo_sub_dispatch(request, repo, sub)


def _repo_sub_dispatch(request, repo, sub):
    method = request.method
    if sub == "branches":
        if method == "GET":
            return rest_list_branches(request, repo)
        return api_error(404, "Not Found")
    if sub.startswith("branches/"):
        if method == "GET":
            return rest_get_branch(repo, sub[len("branches/"):])
        return api_error(404, "Not Found")
    if sub == "commits":
        if method == "GET":
            return rest_list_commits(request, repo)
        return api_error(404, "Not Found")
    if sub.startswith("commits/"):
        if method == "GET":
            return rest_get_commit(repo, sub[len("commits/"):])
        return api_error(404, "Not Found")
    if sub == "tags":
        if method == "GET":
            return rest_list_tags(request, repo)
        return api_error(404, "Not Found")
    if sub == "git/refs":
        if method == "GET":
            return rest_list_refs(request, repo)
        if method == "POST":
            return rest_create_ref(request, repo)
        return api_error(404, "Not Found")
    if sub.startswith("git/refs/"):
        refname = sub[len("git/refs/"):]
        if method == "GET":
            return rest_get_ref(repo, refname)
        if method == "DELETE":
            return rest_delete_ref(repo, refname)
        return api_error(404, "Not Found")
    if sub == "contents" or sub.startswith("contents/"):
        path = sub[len("contents/"):] if sub.startswith("contents/") else ""
        if method == "GET":
            return rest_get_contents(request, repo, path)
        if method == "PUT":
            return rest_put_contents(request, repo, path)
        if method == "DELETE":
            return rest_delete_contents(request, repo, path)
        return api_error(404, "Not Found")
    if sub == "labels":
        if method == "GET":
            return rest_list_labels(request, repo)
        if method == "POST":
            return rest_create_label(request, repo)
        return api_error(404, "Not Found")
    if sub.startswith("labels/"):
        name = unquote(sub[len("labels/"):])
        if method == "GET":
            return rest_get_label(repo, name)
        if method == "PATCH":
            return rest_patch_label(request, repo, name)
        if method == "DELETE":
            return rest_delete_label(repo, name)
        return api_error(404, "Not Found")
    if sub == "issues":
        if method == "GET":
            return rest_list_issues(request, repo)
        if method == "POST":
            return rest_create_issue(request, repo)
        return api_error(404, "Not Found")
    m = re.match(r"^issues/(\d+)$", sub)
    if m:
        number = int(m.group(1))
        if method == "GET":
            return rest_get_issue(repo, number)
        if method == "PATCH":
            return rest_patch_issue(request, repo, number)
        return api_error(404, "Not Found")
    m = re.match(r"^issues/(\d+)/comments$", sub)
    if m:
        number = int(m.group(1))
        if method == "GET":
            return rest_list_comments(request, repo, number)
        if method == "POST":
            return rest_create_comment(request, repo, number)
        return api_error(404, "Not Found")
    m = re.match(r"^issues/comments/(\d+)$", sub)
    if m:
        gid = int(m.group(1))
        if method == "GET":
            return rest_get_comment(repo, gid)
        if method == "PATCH":
            return rest_patch_comment(request, repo, gid)
        if method == "DELETE":
            return rest_delete_comment(repo, gid)
        return api_error(404, "Not Found")
    if sub == "pulls":
        if method == "GET":
            return rest_list_pulls(request, repo)
        if method == "POST":
            return rest_create_pull(request, repo)
        return api_error(404, "Not Found")
    m = re.match(r"^pulls/(\d+)$", sub)
    if m:
        number = int(m.group(1))
        if method == "GET":
            return rest_get_pull(repo, number)
        if method == "PATCH":
            return rest_patch_pull(request, repo, number)
        return api_error(404, "Not Found")
    m = re.match(r"^pulls/(\d+)/files$", sub)
    if m and method == "GET":
        return rest_pull_files(request, repo, int(m.group(1)))
    m = re.match(r"^pulls/(\d+)/commits$", sub)
    if m and method == "GET":
        return rest_pull_commits(request, repo, int(m.group(1)))
    m = re.match(r"^pulls/(\d+)/merge$", sub)
    if m:
        number = int(m.group(1))
        if method == "PUT":
            return rest_merge_pull(request, repo, number)
        if method == "GET":
            return rest_pull_merged(repo, number)
        return api_error(404, "Not Found")
    return api_error(404, "Not Found")


# --------------------------------------------------------------------------
# GraphQL: a small lexer / parser / executor

class GQLSyntax(Exception):
    pass


_GQL_TOKEN_RE = re.compile(r"""
    (?P<ws>[\s,]+)
  | (?P<comment>\#[^\n]*)
  | (?P<spread>\.\.\.)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?)
  | (?P<int>-?\d+)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<blockstring>\"\"\"[\s\S]*?\"\"\")
  | (?P<punct>[!$():=@\[\]{}|&])
""", re.VERBOSE)


def _gql_tokens(text):
    tokens = []
    pos = 0
    while pos < len(text):
        m = _GQL_TOKEN_RE.match(text, pos)
        if not m:
            raise GQLSyntax("unexpected character %r" % text[pos])
        pos = m.end()
        kind = m.lastgroup
        if kind in ("ws", "comment"):
            continue
        value = m.group()
        if kind == "string":
            value = json.loads(value)
        elif kind == "blockstring":
            value = value[3:-3]
        elif kind == "int":
            value = int(value)
        elif kind == "float":
            value = float(value)
        tokens.append((kind, value))
    tokens.append(("eof", None))
    return tokens


class _GQLParser:
    def __init__(self, text):
        self.tokens = _gql_tokens(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect_punct(self, ch):
        kind, value = self.next()
        if kind != "punct" or value != ch:
            raise GQLSyntax("expected %r" % ch)

    def skip_punct(self, ch):
        kind, value = self.peek()
        if kind == "punct" and value == ch:
            self.pos += 1
            return True
        return False

    def expect_name(self):
        kind, value = self.next()
        if kind != "name":
            raise GQLSyntax("expected name")
        return value

    def parse_document(self):
        operations = []
        fragments = {}
        while self.peek()[0] != "eof":
            kind, value = self.peek()
            if kind == "punct" and value == "{":
                operations.append({
                    "kind": "query", "name": None, "variables": {},
                    "selection": self.parse_selection_set(),
                })
            elif kind == "name" and value in ("query", "mutation",
                                              "subscription"):
                self.next()
                name = None
                if self.peek()[0] == "name":
                    name = self.next()[1]
                var_defs = {}
                if self.peek() == ("punct", "("):
                    var_defs = self.parse_variable_defs()
                self.parse_directives()
                operations.append({
                    "kind": value, "name": name, "variables": var_defs,
                    "selection": self.parse_selection_set(),
                })
            elif kind == "name" and value == "fragment":
                self.next()
                fname = self.expect_name()
                on_kw = self.expect_name()
                if on_kw != "on":
                    raise GQLSyntax("expected 'on' in fragment")
                type_cond = self.expect_name()
                self.parse_directives()
                fragments[fname] = {
                    "type": type_cond,
                    "selection": self.parse_selection_set(),
                }
            else:
                raise GQLSyntax("unexpected token %r" % (value,))
        return operations, fragments

    def parse_variable_defs(self):
        defs = {}
        self.expect_punct("(")
        while not self.skip_punct(")"):
            self.expect_punct("$")
            name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            default = None
            if self.skip_punct("="):
                default = self.parse_value(const=True)
            self.parse_directives()
            defs[name] = default
        return defs

    def parse_type(self):
        kind, value = self.peek()
        if kind == "punct" and value == "[":
            self.next()
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        self.skip_punct("!")

    def parse_directives(self):
        while self.peek() == ("punct", "@"):
            self.next()
            self.expect_name()
            if self.peek() == ("punct", "("):
                self.parse_arguments()

    def parse_selection_set(self):
        self.expect_punct("{")
        selections = []
        while not self.skip_punct("}"):
            selections.append(self.parse_selection())
        return selections

    def parse_selection(self):
        kind, value = self.peek()
        if kind == "spread":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] != "on":
                return {"kind": "spread", "name": self.next()[1]}
            type_cond = None
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_cond = self.expect_name()
            self.parse_directives()
            return {"kind": "inline", "type": type_cond,
                    "selection": self.parse_selection_set()}
        first = self.expect_name()
        alias = None
        name = first
        if self.skip_punct(":"):
            alias = first
            name = self.expect_name()
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        self.parse_directives()
        selection = None
        if self.peek() == ("punct", "{"):
            selection = self.parse_selection_set()
        return {"kind": "field", "name": name, "alias": alias,
                "args": args, "selection": selection}

    def parse_arguments(self):
        args = {}
        self.expect_punct("(")
        while not self.skip_punct(")"):
            name = self.expect_name()
            self.expect_punct(":")
            args[name] = self.parse_value()
        return args

    def parse_value(self, const=False):
        kind, value = self.peek()
        if kind == "punct" and value == "$":
            if const:
                raise GQLSyntax("variable in constant value")
            self.next()
            return ("var", self.expect_name())
        if kind == "punct" and value == "[":
            self.next()
            items = []
            while not self.skip_punct("]"):
                items.append(self.parse_value(const))
            return ("list", items)
        if kind == "punct" and value == "{":
            self.next()
            obj = {}
            while not self.skip_punct("}"):
                key = self.expect_name()
                self.expect_punct(":")
                obj[key] = self.parse_value(const)
            return ("object", obj)
        self.next()
        if kind in ("int", "float", "string"):
            return ("value", value)
        if kind == "name":
            if value == "true":
                return ("value", True)
            if value == "false":
                return ("value", False)
            if value == "null":
                return ("value", None)
            return ("enum", value)
        raise GQLSyntax("unexpected value token")


def _gql_eval(node, variables):
    kind = node[0]
    if kind == "var":
        return variables.get(node[1])
    if kind == "value":
        return node[1]
    if kind == "enum":
        return node[1]
    if kind == "list":
        return [_gql_eval(v, variables) for v in node[1]]
    if kind == "object":
        return {k: _gql_eval(v, variables) for k, v in node[1].items()}
    return None


def _gql_args(raw_args, variables):
    return {k: _gql_eval(v, variables) for k, v in raw_args.items()}


def _g_user(login):
    return {"__gql_type": "User", "login": login}


def _g_repo(repo):
    return {"__gql_type": "Repository", "repo": repo}


def _g_issue(repo, item):
    return {"__gql_type": "Issue", "repo": repo, "item": item}


def _g_pull(repo, item):
    return {"__gql_type": "PullRequest", "repo": repo, "item": item}


def _g_label(repo, label):
    return {"__gql_type": "Label", "repo": repo, "label": label}


def _g_comment(repo, item, comment):
    return {"__gql_type": "IssueComment", "repo": repo, "item": item,
            "comment": comment}


def _g_ref(repo, refname):
    return {"__gql_type": "Ref", "repo": repo, "ref": refname}


def _g_commit(oid):
    return {"__gql_type": "Commit", "oid": oid}


def _paginate_nodes(nodes, args):
    """Apply after/before/first/last to a node list; cursors are indices."""
    total = len(nodes)
    start = 0
    end = total
    after = args.get("after")
    before = args.get("before")
    if after is not None:
        try:
            start = int(after) + 1
        except (TypeError, ValueError):
            start = 0
    if before is not None:
        try:
            end = min(end, int(before))
        except (TypeError, ValueError):
            pass
    if args.get("first") is not None:
        end = min(end, start + int(args["first"]))
    if args.get("last") is not None:
        start = max(start, end - int(args["last"]))
    page = [(idx, nodes[idx]) for idx in range(start, min(end, total))]
    return page, start, end, total


def _g_connection(conn_type, nodes, args):
    page, start, end, total = _paginate_nodes(nodes, args)
    return {
        "__gql_type": conn_type,
        "page_nodes": [node for _idx, node in page],
        "edges": [{"node": node, "cursor": str(idx)} for idx, node in page],
        "total": total,
        "page_info": {
            "hasNextPage": end < total,
            "hasPreviousPage": start > 0,
            "startCursor": str(page[0][0]) if page else None,
            "endCursor": str(page[-1][0]) if page else None,
        },
    }


def _sort_items(items, order_by):
    field = "CREATED_AT"
    direction = "DESC"
    if isinstance(order_by, dict):
        field = order_by.get("field") or field
        direction = order_by.get("direction") or direction
    reverse = direction != "ASC"
    if field == "UPDATED_AT":
        items.sort(key=lambda it: (it["updated"], it["number"]),
                   reverse=reverse)
    elif field == "COMMENTS":
        items.sort(key=lambda it: (len(it["comments"]), it["number"]),
                   reverse=reverse)
    else:
        items.sort(key=lambda it: (it["created"], it["number"]),
                   reverse=reverse)
    return items


def _state_filter(items, states):
    if not states:
        return items
    wanted = set()
    for state in states:
        wanted.add(str(state).lower())
    if "merged" in wanted:
        return [it for it in items if it["merged"] or it["state"] in wanted]
    return [it for it in items if it["state"] in wanted]


def _repo_issues_connection(repo, args, kind):
    items = [it for it in repo.items.values() if it["kind"] == kind]
    items = _state_filter(items, args.get("states"))
    labels = args.get("labels")
    if labels:
        items = [it for it in items
                 if all(name in it["labels"] for name in labels)]
    items = _sort_items(items, args.get("orderBy"))
    wrap = _g_issue if kind == "issue" else _g_pull
    nodes = [wrap(repo, it) for it in items]
    conn_type = "IssueConnection" if kind == "issue" else "PullRequestConnection"
    return _g_connection(conn_type, nodes, args)


def _item_state_gql(item):
    if item["kind"] == "pr" and item["merged"]:
        return "MERGED"
    return item["state"].upper()


# ---- field resolvers ----------------------------------------------------------

def _r_query_viewer(obj, args, ctx):
    return _g_user(VIEWER["login"])


def _r_query_repository(obj, args, ctx):
    owner = args.get("owner") or ""
    name = args.get("name") or ""
    repo = FORGE.get(owner, name)
    if repo is None:
        return None
    return _g_repo(repo)


def _r_query_node(obj, args, ctx):
    return _node_lookup(args.get("id") or "")


def _r_query_search(obj, args, ctx):
    query = (args.get("query") or "").lower()
    stype = str(args.get("type") or "ISSUE").upper()
    nodes = []
    if stype == "REPOSITORY":
        for repo in FORGE.user_repos():
            if query in repo.name.lower() or query in repo.full_name.lower():
                nodes.append(_g_repo(repo))
    elif stype == "USER":
        for login in KNOWN_USERS:
            if query in login.lower():
                nodes.append(_g_user(login))
    else:
        for repo in FORGE.user_repos():
            for item in repo.items.values():
                if item["kind"] == "issue" and (
                        query in item["title"].lower()
                        or query in item["body"].lower()):
                    nodes.append(_g_issue(repo, item))
    conn = _g_connection("SearchResultItemConnection", nodes, args)
    conn["issue_count"] = len(nodes) if stype == "ISSUE" else 0
    conn["repo_count"] = len(nodes) if stype == "REPOSITORY" else 0
    conn["user_count"] = len(nodes) if stype == "USER" else 0
    return conn


def _r_query_user(obj, args, ctx):
    login = args.get("login") or ""
    if login in KNOWN_USERS:
        return _g_user(login)
    return None


def _r_query_type(obj, args, ctx):
    return _type_by_name(args.get("name") or "")


def _r_query_schema(obj, args, ctx):
    return {"__gql_type": "__Schema"}


def _node_lookup(node):
    parsed = parse_node_id(node)
    if parsed is None:
        return None
    kind, dbid = parsed
    if kind == "User":
        for login, record in KNOWN_USERS.items():
            if record["id"] == dbid:
                return _g_user(login)
        return None
    if kind == "Repository":
        for repo in FORGE.repos.values():
            if repo.dbid == dbid:
                return _g_repo(repo)
        return None
    if kind in ("Issue", "PullRequest"):
        repo_dbid, number = divmod(dbid, 100000)
        for repo in FORGE.repos.values():
            if repo.dbid == repo_dbid:
                item = repo.items.get(number)
                if item is None:
                    return None
                if kind == "Issue" and item["kind"] == "issue":
                    return _g_issue(repo, item)
                if kind == "PullRequest" and item["kind"] == "pr":
                    return _g_pull(repo, item)
                return None
        return None
    if kind == "IssueComment":
        for repo in FORGE.repos.values():
            item, comment = find_comment(repo, dbid)
            if comment is not None:
                return _g_comment(repo, item, comment)
        return None
    if kind == "Label":
        repo_dbid, label_id = divmod(dbid, 100000)
        for repo in FORGE.repos.values():
            if repo.dbid == repo_dbid:
                for label in repo.labels.values():
                    if label["id"] == label_id:
                        return _g_label(repo, label)
        return None
    return None


def _payload_input(args):
    data = args.get("input")
    if isinstance(data, dict):
        return data
    return args


def _repo_from_node(node):
    parsed = parse_node_id(node or "")
    if parsed and parsed[0] == "Repository":
        for repo in FORGE.repos.values():
            if repo.dbid == parsed[1]:
                return repo
    return None


def _item_from_node(node):
    obj = _node_lookup(node or "")
    if obj and obj["__gql_type"] in ("Issue", "PullRequest"):
        return obj["repo"], obj["item"]
    return None, None


def _r_mut_create_issue(obj, args, ctx):
    data = _payload_input(args)
    repo = _repo_from_node(data.get("repositoryId"))
    if repo is None:
        raise GQLFieldError("repository not found")
    with STORE_LOCK:
        names = []
        for label_id in data.get("labelIds") or []:
            target = _node_lookup(label_id)
            if target and target["__gql_type"] == "Label":
                names.append(target["label"]["name"])
        issue = new_issue(repo, data.get("title") or "",
                          data.get("body") or "", names)
    return {"__gql_type": "CreateIssuePayload",
            "issue": _g_issue(repo, issue),
            "clientMutationId": data.get("clientMutationId")}


def _r_mut_close_issue(obj, args, ctx):
    data = _payload_input(args)
    repo, item = _item_from_node(data.get("issueId"))
    if item is None:
        raise GQLFieldError("issue not found")
    with STORE_LOCK:
        if item["state"] == "open":
            item["state"] = "closed"
            item["closed"] = tick()
            item["updated"] = item["closed"]
            if item["kind"] == "issue":
                refresh_issue_json(repo, item)
    return {"__gql_type": "CloseIssuePayload",
            "issue": _g_issue(repo, item),
            "clientMutationId": data.get("clientMutationId")}


def _r_mut_reopen_issue(obj, args, ctx):
    data = _payload_input(args)
    repo, item = _item_from_node(data.get("issueId"))
    if item is None:
        raise GQLFieldError("issue not found")
    with STORE_LOCK:
        item["state"] = "open"
        item["closed"] = None
        item["updated"] = tick()
        if item["kind"] == "issue":
            refresh_issue_json(repo, item)
    return {"__gql_type": "ReopenIssuePayload",
            "issue": _g_issue(repo, item),
            "clientMutationId": data.get("clientMutationId")}


def _r_mut_create_pull(obj, args, ctx):
    data = _payload_input(args)
    repo = _repo_from_node(data.get("repositoryId"))
    if repo is None:
        raise GQLFieldError("repository not found")
    with STORE_LOCK:
        pull = new_pull(repo, data.get("title") or "", data.get("body") or "",
                        data.get("headRefName") or "",
                        data.get("baseRefName") or "")
    return {"__gql_type": "CreatePullRequestPayload",
            "pullRequest": _g_pull(repo, pull),
            "clientMutationId": data.get("clientMutationId")}


def _r_mut_merge_pull(obj, args, ctx):
    data = _payload_input(args)
    repo, item = _item_from_node(data.get("pullRequestId"))
    if item is None or item["kind"] != "pr":
        raise GQLFieldError("pull request not found")
    with STORE_LOCK:
        if not item["merged"] and item["state"] == "open":
            sha, conflict = squash_merge(repo, item)
            if not conflict:
                item["merged"] = True
                item["state"] = "closed"
                item["merged_at"] = tick()
                item["closed"] = item["merged_at"]
                item["merge_sha"] = sha
                item["updated"] = item["merged_at"]
    return {"__gql_type": "MergePullRequestPayload",
            "pullRequest": _g_pull(repo, item),
            "clientMutationId": data.get("clientMutationId")}


def _r_mut_add_comment(obj, args, ctx):
    data = _payload_input(args)
    repo, item = _item_from_node(data.get("subjectId"))
    if item is None:
        raise GQLFieldError("subject not found")
    with STORE_LOCK:
        comment = new_comment(item, data.get("body") or "")
        if item["kind"] == "issue":
            refresh_issue_json(repo, item)
    comment_obj = _g_comment(repo, item, comment)
    subject = _g_issue(repo, item) if item["kind"] == "issue" \
        else _g_pull(repo, item)
    return {"__gql_type": "AddCommentPayload",
            "commentEdge": {"__gql_type": "IssueCommentEdge",
                            "node": comment_obj,
                            "cursor": str(len(item["comments"]) - 1)},
            "subject": subject,
            "clientMutationId": data.get("clientMutationId")}


class GQLFieldError(Exception):
    pass


GQL_RESOLVERS = {
    "Query": {
        "viewer": _r_query_viewer,
        "repository": _r_query_repository,
        "node": _r_query_node,
        "nodes": lambda o, a, c: [_node_lookup(x) for x in a.get("ids") or []],
        "search": _r_query_search,
        "user": _r_query_user,
        "organization": lambda o, a, c: None,
        "rateLimit": lambda o, a, c: {"__gql_type": "RateLimit", "limit": 5000,
                                      "cost": 1, "remaining": 4999,
                                      "resetAt": iso8601(_EPOCH + 3600),
                                      "used": 1, "nodeCount": 0},
        "__type": _r_query_type,
        "__schema": _r_query_schema,
    },
    "Mutation": {
        "createIssue": _r_mut_create_issue,
        "closeIssue": _r_mut_close_issue,
        "reopenIssue": _r_mut_reopen_issue,
        "createPullRequest": _r_mut_create_pull,
        "mergePullRequest": _r_mut_merge_pull,
        "addComment": _r_mut_add_comment,
    },
    "User": {
        "id": lambda o, a, c: node_id("User", KNOWN_USERS[o["login"]]["id"]),
        "databaseId": lambda o, a, c: KNOWN_USERS[o["login"]]["id"],
        "login": lambda o, a, c: o["login"],
        "name": lambda o, a, c: KNOWN_USERS[o["login"]]["name"],
        "url": lambda o, a, c: "%s/%s" % (URL_BASE, o["login"]),
        "avatarUrl": lambda o, a, c: "https://avatars.example.test/u/%d" %
                                     KNOWN_USERS[o["login"]]["id"],
        "repositories": lambda o, a, c: _g_connection(
            "RepositoryConnection",
            [_g_repo(r) for r in FORGE.user_repos()]
            if o["login"] == VIEWER["login"] else [], a),
        "isViewer": lambda o, a, c: o["login"] == VIEWER["login"],
    },
    "Repository": {
        "id": lambda o, a, c: node_id("Repository", o["repo"].dbid),
        "databaseId": lambda o, a, c: o["repo"].dbid,
        "name": lambda o, a, c: o["repo"].name,
        "nameWithOwner": lambda o, a, c: o["repo"].full_name,
        "owner": lambda o, a, c: _g_user(o["repo"].owner),
        "description": lambda o, a, c: o["repo"].description or None,
        "isPrivate": lambda o, a, c: o["repo"].private,
        "visibility": lambda o, a, c: "PRIVATE" if o["repo"].private
                                      else "PUBLIC",
        "url": lambda o, a, c: "%s/%s" % (URL_BASE, o["repo"].full_name),
        "createdAt": lambda o, a, c: iso8601(_EPOCH + o["repo"].created_tick),
        "updatedAt": lambda o, a, c: iso8601(_EPOCH + o["repo"].updated_tick),
        "viewerPermission": lambda o, a, c: "ADMIN",
        "hasIssuesEnabled": lambda o, a, c: True,
        "hasPullRequestsEnabled": lambda o, a, c: True,
        "defaultBranchRef": lambda o, a, c: (
            _g_ref(o["repo"], "refs/heads/%s" % o["repo"].default_branch)
            if o["repo"].branch_oid(o["repo"].default_branch) else None),
        "issue": lambda o, a, c: (
            _g_issue(o["repo"], o["repo"].items[a["number"]])
            if o["repo"].items.get(a.get("number") or -1, {})
            .get("kind") == "issue" else None),
        "pullRequest": lambda o, a, c: (
            _g_pull(o["repo"], o["repo"].items[a["number"]])
            if o["repo"].items.get(a.get("number") or -1, {})
            .get("kind") == "pr" else None),
        "issues": lambda o, a, c: _repo_issues_connection(o["repo"], a,
                                                          "issue"),
        "pullRequests": lambda o, a, c: _repo_issues_connection(o["repo"], a,
                                                                "pr"),
        "labels": lambda o, a, c: _g_connection(
            "LabelConnection",
            [_g_label(o["repo"], o["repo"].labels[name])
             for name in sorted(o["repo"].labels)], a),
        "label": lambda o, a, c: (
            _g_label(o["repo"], o["repo"].labels[a["name"]])
            if a.get("name") in o["repo"].labels else None),
        "ref": lambda o, a, c: (
            _g_ref(o["repo"], a["qualifiedName"])
            if a.get("qualifiedName") in o["repo"].refs else None),
        "refs": lambda o, a, c: _g_connection(
            "RefConnection",
            [_g_ref(o["repo"], r) for r in sorted(o["repo"].refs)
             if r.startswith(a.get("refPrefix") or "refs/")], a),
        "stargazerCount": lambda o, a, c: 0,
        "forkCount": lambda o, a, c: 0,
        "isEmpty": lambda o, a, c: not o["repo"].refs,
    },
    "Issue": {
        "id": lambda o, a, c: node_id("Issue", o["repo"].dbid * 100000
                                      + o["item"]["number"]),
        "databaseId": lambda o, a, c: o["repo"].dbid * 100000
                                      + o["item"]["number"],
        "number": lambda o, a, c: o["item"]["number"],
        "title": lambda o, a, c: o["item"]["title"],
        "body": lambda o, a, c: o["item"]["body"],
        "bodyText": lambda o, a, c: o["item"]["body"],
        "state": lambda o, a, c: _item_state_gql(o["item"]),
        "url": lambda o, a, c: "%s/%s/issues/%d" % (
            URL_BASE, o["repo"].full_name, o["item"]["number"]),
        "createdAt": lambda o, a, c: iso8601(_EPOCH + o["item"]["created"]),
        "updatedAt": lambda o, a, c: iso8601(_EPOCH + o["item"]["updated"]),
        "closedAt": lambda o, a, c: (
            iso8601(_EPOCH + o["item"]["closed"])
            if o["item"]["closed"] else None),
        "author": lambda o, a, c: _g_user(VIEWER["login"]),
        "repository": lambda o, a, c: _g_repo(o["repo"]),
        "labels": lambda o, a, c: _g_connection(
            "LabelConnection",
            [_g_label(o["repo"], o["repo"].labels[name])
             for name in o["item"]["labels"] if name in o["repo"].labels], a),
        "comments": lambda o, a, c: _g_connection(
            "IssueCommentConnection",
            [_g_comment(o["repo"], o["item"], cm)
             for cm in o["item"]["comments"]], a),
    },
    "PullRequest": {
        "id": lambda o, a, c: node_id("PullRequest", o["repo"].dbid * 100000
                                      + o["item"]["number"]),
        "databaseId": lambda o, a, c: o["repo"].dbid * 100000
                                      + o["item"]["number"],
        "number": lambda o, a, c: o["item"]["number"],
        "title": lambda o, a, c: o["item"]["title"],
        "body": lambda o, a, c: o["item"]["body"],
        "state": lambda o, a, c: _item_state_gql(o["item"]),
        "merged": lambda o, a, c: o["item"]["merged"],
        "mergedAt": lambda o, a, c: (
            iso8601(_EPOCH + o["item"]["merged_at"])
            if o["item"]["merged_at"] else None),
        "mergeable": lambda o, a, c: "MERGEABLE" if pull_mergeable(
            o["repo"], o["item"]) else "CONFLICTING",
        "headRefName": lambda o, a, c: o["item"]["head"],
        "baseRefName": lambda o, a, c: o["item"]["base"],
        "headRef": lambda o, a, c: (
            _g_ref(o["repo"], "refs/heads/%s" % o["item"]["head"])
            if o["repo"].branch_oid(o["item"]["head"]) else None),
        "baseRef": lambda o, a, c: (
            _g_ref(o["repo"], "refs/heads/%s" % o["item"]["base"])
            if o["repo"].branch_oid(o["item"]["base"]) else None),
        "url": lambda o, a, c: "%s/%s/pull/%d" % (
            URL_BASE, o["repo"].full_name, o["item"]["number"]),
        "createdAt": lambda o, a, c: iso8601(_EPOCH + o["item"]["created"]),
        "updatedAt": lambda o, a, c: iso8601(_EPOCH + o["item"]["updated"]),
        "closedAt": lambda o, a, c: (
            iso8601(_EPOCH + o["item"]["closed"])
            if o["item"]["closed"] else None),
        "author": lambda o, a, c: _g_user(VIEWER["login"]),
        "repository": lambda o, a, c: _g_repo(o["repo"]),
        "labels": lambda o, a, c: _g_connection(
            "LabelConnection",
            [_g_label(o["repo"], o["repo"].labels[name])
             for name in o["item"]["labels"] if name in o["repo"].labels], a),
        "comments": lambda o, a, c: _g_connection(
            "IssueCommentConnection",
            [_g_comment(o["repo"], o["item"], cm)
             for cm in o["item"]["comments"]], a),
        "files": lambda o, a, c: _g_connection(
            "PullRequestChangedFileConnection",
            [{"__gql_type": "PullRequestChangedFile", "file": f}
             for f in pr_files(o["repo"], o["item"])], a),
        "changedFiles": lambda o, a, c: len(pr_files(o["repo"], o["item"])),
        "additions": lambda o, a, c: sum(
            f["additions"] for f in pr_files(o["repo"], o["item"])),
        "deletions": lambda o, a, c: sum(
            f["deletions"] for f in pr_files(o["repo"], o["item"])),
        "commits": lambda o, a, c: _pr_commits_connection(o["repo"],
                                                          o["item"], a),
        "mergeCommit": lambda o, a, c: (
            _g_commit(o["item"]["merge_sha"])
            if o["item"]["merge_sha"] else None),
    },
    "Label": {
        "id": lambda o, a, c: node_id("Label", o["repo"].dbid * 100000
                                      + o["label"]["id"]),
        "name": lambda o, a, c: o["label"]["name"],
        "color": lambda o, a, c: o["label"]["color"],
        "description": lambda o, a, c: o["label"]["description"],
        "url": lambda o, a, c: "%s/%s/labels/%s" % (
            URL_BASE, o["repo"].full_name,
            quote(o["label"]["name"], safe="")),
    },
    "IssueComment": {
        "id": lambda o, a, c: node_id("IssueComment", o["comment"]["gid"]),
        "databaseId": lambda o, a, c: o["comment"]["gid"],
        "body": lambda o, a, c: o["comment"]["body"],
        "bodyText": lambda o, a, c: o["comment"]["body"],
        "author": lambda o, a, c: _g_user(VIEWER["login"]),
        "createdAt": lambda o, a, c: iso8601(_EPOCH + o["comment"]["created"]),
        "updatedAt": lambda o, a, c: iso8601(_EPOCH + o["comment"]["updated"]),
        "url": lambda o, a, c: "%s/%s/issues/%d#issuecomment-%d" % (
            URL_BASE, o["repo"].full_name, o["item"]["number"],
            o["comment"]["gid"]),
    },
    "Ref": {
        "id": lambda o, a, c: node_id("Ref", int(
            (o["repo"].refs.get(o["ref"]) or ZERO_OID)[:8], 16)),
        "name": lambda o, a, c: o["ref"].split("/")[-1]
        if not o["ref"].startswith("refs/heads/")
        else o["ref"][len("refs/heads/"):],
        "prefix": lambda o, a, c: o["ref"][:len(o["ref"])
                                           - len(o["ref"].split("/")[-1])],
        "qualifiedName": lambda o, a, c: o["ref"],
        "target": lambda o, a, c: (
            _g_commit(peel_to_commit(o["repo"].refs[o["ref"]]))
            if o["ref"] in o["repo"].refs
            and peel_to_commit(o["repo"].refs[o["ref"]]) else None),
        "repository": lambda o, a, c: _g_repo(o["repo"]),
    },
    "Commit": {
        "id": lambda o, a, c: node_id("Commit", int(o["oid"][:8], 16)),
        "oid": lambda o, a, c: o["oid"],
        "message": lambda o, a, c: (commit_info(o["oid"]) or
                                    (None, None, None, None, ""))[4],
        "messageHeadline": lambda o, a, c: (
            (commit_info(o["oid"]) or (None, None, None, None, ""))[4]
            .split("\n")[0]),
        "committedDate": lambda o, a, c: _commit_date(o["oid"]),
        "authoredDate": lambda o, a, c: _commit_date(o["oid"]),
        "author": lambda o, a, c: _commit_actor(o["oid"], 2),
        "committer": lambda o, a, c: _commit_actor(o["oid"], 3),
        "tree": lambda o, a, c: {"__gql_type": "Tree",
                                 "oid": (commit_info(o["oid"]) or
                                         (ZERO_OID,))[0]},
        "url": lambda o, a, c: "%s/commit/%s" % (URL_BASE, o["oid"]),
    },
    "Tree": {
        "id": lambda o, a, c: node_id("Tree", int(o["oid"][:8], 16)),
        "oid": lambda o, a, c: o["oid"],
    },
    "PullRequestChangedFile": {
        "path": lambda o, a, c: o["file"]["filename"],
        "additions": lambda o, a, c: o["file"]["additions"],
        "deletions": lambda o, a, c: o["file"]["deletions"],
        "changeType": lambda o, a, c: {
            "added": "ADDED", "removed": "DELETED", "modified": "MODIFIED",
            "renamed": "RENAMED"}.get(o["file"]["status"], "MODIFIED"),
    },
    "RateLimit": {
        "limit": lambda o, a, c: o["limit"],
        "cost": lambda o, a, c: o["cost"],
        "remaining": lambda o, a, c: o["remaining"],
        "resetAt": lambda o, a, c: o["resetAt"],
        "used": lambda o, a, c: o["used"],
        "nodeCount": lambda o, a, c: o["nodeCount"],
    },
    "CreateIssuePayload": {
        "issue": lambda o, a, c: o["issue"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "CloseIssuePayload": {
        "issue": lambda o, a, c: o["issue"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "ReopenIssuePayload": {
        "issue": lambda o, a, c: o["issue"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "CreatePullRequestPayload": {
        "pullRequest": lambda o, a, c: o["pullRequest"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "MergePullRequestPayload": {
        "pullRequest": lambda o, a, c: o["pullRequest"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "AddCommentPayload": {
        "commentEdge": lambda o, a, c: o["commentEdge"],
        "subject": lambda o, a, c: o["subject"],
        "clientMutationId": lambda o, a, c: o["clientMutationId"],
    },
    "__Schema": {
        "types": lambda o, a, c: [_type_by_name(name)
                                  for name in sorted(GQL_TYPES)],
        "queryType": lambda o, a, c: _type_by_name("Query"),
        "mutationType": lambda o, a, c: _type_by_name("Mutation"),
        "subscriptionType": lambda o, a, c: None,
        "directives": lambda o, a, c: [],
    },
    "__Type": {
        "kind": lambda o, a, c: o["kind"],
        "name": lambda o, a, c: o["name"],
        "description": lambda o, a, c: o.get("description"),
        "fields": lambda o, a, c: o.get("field_objs"),
        "enumValues": lambda o, a, c: o.get("enum_objs"),
        "possibleTypes": lambda o, a, c: o.get("possible"),
        "inputFields": lambda o, a, c: o.get("input_fields"),
        "ofType": lambda o, a, c: o.get("ofType"),
        "specifiedByURL": lambda o, a, c: None,
    },
    "__Field": {
        "name": lambda o, a, c: o["name"],
        "description": lambda o, a, c: None,
        "args": lambda o, a, c: [],
        "type": lambda o, a, c: o["type"],
        "isDeprecated": lambda o, a, c: False,
        "deprecationReason": lambda o, a, c: None,
    },
    "__EnumValue": {
        "name": lambda o, a, c: o["name"],
        "description": lambda o, a, c: None,
        "isDeprecated": lambda o, a, c: False,
        "deprecationReason": lambda o, a, c: None,
    },
}


def _commit_date(oid):
    info = commit_info(oid)
    if not info:
        return iso8601(_EPOCH)
    ident = _ident_json(info[2])
    return ident["date"]


def _commit_actor(oid, index):
    info = commit_info(oid)
    if not info:
        return {"__gql_type": "GitActor", "name": "", "email": "",
                "date": iso8601(_EPOCH)}
    ident = _ident_json(info[index])
    return {"__gql_type": "GitActor", "name": ident["name"],
            "email": ident["email"], "date": ident["date"]}


GQL_RESOLVERS["GitActor"] = {
    "name": lambda o, a, c: o["name"],
    "email": lambda o, a, c: o["email"],
    "date": lambda o, a, c: o["date"],
    "user": lambda o, a, c: _g_user(VIEWER["login"]),
    "avatarUrl": lambda o, a, c: "https://avatars.example.test/u/1000",
}


def _pr_commits_connection(repo, item, args):
    head_tip = branch_tip(repo, item["head"])
    base_tip = branch_tip(repo, item["base"])
    nodes = []
    if head_tip:
        seen = set()
        stack = [head_tip]
        while stack:
            oid = stack.pop()
            if oid in seen or not STORE.has(oid):
                continue
            seen.add(oid)
            if base_tip and is_ancestor(oid, base_tip):
                continue
            nodes.append({"__gql_type": "PullRequestCommit",
                          "commit": _g_commit(oid)})
            info = commit_info(oid)
            if info:
                for parent in reversed(info[1]):
                    stack.append(parent)
    return _g_connection("PullRequestCommitConnection", nodes, args)


GQL_RESOLVERS["PullRequestCommit"] = {
    "id": lambda o, a, c: o["commit"]["id"] if "id" in o["commit"]
    else node_id("Commit", int(o["commit"]["oid"][:8], 16)),
    "commit": lambda o, a, c: o["commit"],
    "resourcePath": lambda o, a, c: "/commit/%s" % o["commit"]["oid"],
    "url": lambda o, a, c: "%s/commit/%s" % (URL_BASE, o["commit"]["oid"]),
}


# ---- introspection data ---------------------------------------------------------

def _type_ref(name, kind="OBJECT"):
    return {"__gql_type": "__Type", "kind": kind, "name": name,
            "field_objs": None, "enum_objs": None, "possible": None,
            "input_fields": None, "ofType": None, "description": None}


def _field_obj(name, type_name="String", kind="SCALAR"):
    return {"__gql_type": "__Field", "name": name,
            "type": _type_ref(type_name, kind)}


GQL_TYPES = {
    "Query": {"kind": "OBJECT", "fields": [
        "viewer", "repository", "node", "nodes", "search", "user",
        "organization", "rateLimit", "__type", "__schema"]},
    "Mutation": {"kind": "OBJECT", "fields": [
        "createIssue", "closeIssue", "reopenIssue", "createPullRequest",
        "mergePullRequest", "addComment"]},
    "User": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "login", "name", "url", "avatarUrl",
        "repositories", "isViewer"]},
    "Repository": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "name", "nameWithOwner", "owner", "description",
        "isPrivate", "visibility", "url", "createdAt", "updatedAt",
        "viewerPermission", "hasIssuesEnabled", "hasPullRequestsEnabled",
        "defaultBranchRef", "issue", "issues", "pullRequest", "pullRequests",
        "labels", "label", "ref", "refs", "stargazerCount", "forkCount",
        "isEmpty"]},
    "Issue": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "number", "title", "state", "body", "bodyText",
        "url", "createdAt", "updatedAt", "closedAt", "author", "repository",
        "labels", "comments"]},
    "PullRequest": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "number", "title", "body", "state", "merged",
        "mergedAt", "mergeable", "headRefName", "baseRefName", "headRef",
        "baseRef", "url", "createdAt", "updatedAt", "closedAt", "author",
        "repository", "labels", "comments", "files", "changedFiles",
        "additions", "deletions", "commits", "mergeCommit"]},
    "Label": {"kind": "OBJECT", "fields": [
        "id", "name", "color", "description", "url"]},
    "IssueComment": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "body", "bodyText", "author", "createdAt",
        "updatedAt", "url"]},
    "Ref": {"kind": "OBJECT", "fields": [
        "id", "name", "prefix", "qualifiedName", "target", "repository"]},
    "Commit": {"kind": "OBJECT", "fields": [
        "id", "oid", "message", "messageHeadline", "committedDate",
        "authoredDate", "author", "committer", "tree", "url"]},
    "Tree": {"kind": "OBJECT", "fields": ["id", "oid"]},
    "GitActor": {"kind": "OBJECT", "fields": [
        "name", "email", "date", "user", "avatarUrl"]},
    "PageInfo": {"kind": "OBJECT", "fields": [
        "hasNextPage", "hasPreviousPage", "startCursor", "endCursor"]},
    "IssueConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "IssueEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "PullRequestConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "PullRequestEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "LabelConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "LabelEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "IssueCommentConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "IssueCommentEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "RepositoryConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "RepositoryEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "RefConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "RefEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "PullRequestChangedFileConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "PullRequestChangedFileEdge": {"kind": "OBJECT", "fields": [
        "node", "cursor"]},
    "PullRequestChangedFile": {"kind": "OBJECT", "fields": [
        "path", "additions", "deletions", "changeType"]},
    "PullRequestCommitConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes"]},
    "PullRequestCommitEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "PullRequestCommit": {"kind": "OBJECT", "fields": [
        "id", "commit", "resourcePath", "url"]},
    "SearchResultItemConnection": {"kind": "OBJECT", "fields": [
        "totalCount", "pageInfo", "edges", "nodes", "codeCount",
        "issueCount", "repositoryCount", "userCount", "wikiCount",
        "discussionCount"]},
    "SearchResultItemEdge": {"kind": "OBJECT", "fields": ["node", "cursor"]},
    "SearchType": {"kind": "ENUM",
                   "values": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"]},
    "IssueState": {"kind": "ENUM", "values": ["OPEN", "CLOSED"]},
    "PullRequestState": {"kind": "ENUM",
                         "values": ["OPEN", "CLOSED", "MERGED"]},
    "MergeableState": {"kind": "ENUM",
                       "values": ["MERGEABLE", "CONFLICTING", "UNKNOWN"]},
    "MergePullRequestMethod": {"kind": "ENUM",
                               "values": ["MERGE", "SQUASH", "REBASE"]},
    "RepositoryVisibility": {"kind": "ENUM",
                             "values": ["PUBLIC", "PRIVATE", "INTERNAL"]},
    "Permission": {"kind": "ENUM", "values": [
        "READ", "TRIAGE", "WRITE", "MAINTAIN", "ADMIN"]},
    "RateLimit": {"kind": "OBJECT", "fields": [
        "limit", "cost", "remaining", "resetAt", "used", "nodeCount"]},
    "CreateIssuePayload": {"kind": "OBJECT", "fields": [
        "issue", "clientMutationId"]},
    "CloseIssuePayload": {"kind": "OBJECT", "fields": [
        "issue", "clientMutationId"]},
    "ReopenIssuePayload": {"kind": "OBJECT", "fields": [
        "issue", "clientMutationId"]},
    "CreatePullRequestPayload": {"kind": "OBJECT", "fields": [
        "pullRequest", "clientMutationId"]},
    "MergePullRequestPayload": {"kind": "OBJECT", "fields": [
        "pullRequest", "clientMutationId"]},
    "AddCommentPayload": {"kind": "OBJECT", "fields": [
        "commentEdge", "subject", "clientMutationId"]},
}


def _type_by_name(name):
    spec = GQL_TYPES.get(name)
    if spec is None:
        return None
    obj = _type_ref(name, spec["kind"])
    if spec["kind"] == "ENUM":
        obj["enum_objs"] = [{"__gql_type": "__EnumValue", "name": v}
                            for v in spec.get("values", [])]
    else:
        obj["field_objs"] = [_field_obj(f) for f in spec.get("fields", [])]
    return obj


# ---- executor ---------------------------------------------------------------------

class _GQLContext:
    def __init__(self, fragments):
        self.fragments = fragments
        self.errors = []


def _resolve_field(type_name, obj, field, args, ctx):
    if type_name.endswith("Connection"):
        if field == "totalCount":
            return obj["total"]
        if field == "pageInfo":
            return {"__gql_type": "PageInfo", "info": obj["page_info"]}
        if field == "edges":
            edge_type = type_name[:-len("Connection")] + "Edge"
            return [{"__gql_type": edge_type, "node": e["node"],
                     "cursor": e["cursor"]} for e in obj["edges"]]
        if field == "nodes":
            return obj["page_nodes"]
        if type_name == "SearchResultItemConnection":
            counts = {"codeCount": 0, "issueCount": obj.get("issue_count", 0),
                      "repositoryCount": obj.get("repo_count", 0),
                      "userCount": obj.get("user_count", 0), "wikiCount": 0,
                      "discussionCount": 0}
            if field in counts:
                return counts[field]
        return _MISSING
    if type_name.endswith("Edge"):
        if field == "node":
            return obj["node"]
        if field == "cursor":
            return obj["cursor"]
        return _MISSING
    if type_name == "PageInfo":
        if field in ("hasNextPage", "hasPreviousPage", "startCursor",
                     "endCursor"):
            return obj["info"][field]
        return _MISSING
    resolvers = GQL_RESOLVERS.get(type_name)
    if resolvers is None or field not in resolvers:
        return _MISSING
    return resolvers[field](obj, args, ctx)


class _Missing:
    pass


_MISSING = _Missing()


def _gql_complete(value, selection, ctx):
    if value is None:
        return None
    if isinstance(value, list):
        return [_gql_complete(v, selection, ctx) for v in value]
    if isinstance(value, dict) and "__gql_type" in value:
        if not selection:
            return {}
        return _gql_exec_set(value["__gql_type"], value, selection, ctx)
    return value


def _gql_exec_set(type_name, obj, selections, ctx):
    out = {}
    for sel in selections:
        if sel["kind"] == "spread":
            frag = ctx.fragments.get(sel["name"])
            if frag is None:
                ctx.errors.append({
                    "message": "Unknown fragment '%s'" % sel["name"]})
                continue
            if frag["type"] in (None, type_name):
                out.update(_gql_exec_set(type_name, obj, frag["selection"],
                                         ctx))
        elif sel["kind"] == "inline":
            if sel["type"] in (None, type_name):
                out.update(_gql_exec_set(type_name, obj, sel["selection"],
                                         ctx))
        else:
            key = sel["alias"] or sel["name"]
            if sel["name"] == "__typename":
                out[key] = type_name
                continue
            args = _gql_args(sel["args"], ctx.variables)
            try:
                value = _resolve_field(type_name, obj, sel["name"], args, ctx)
            except GQLFieldError as exc:
                ctx.errors.append({"message": str(exc)})
                out[key] = None
                continue
            if value is _MISSING:
                ctx.errors.append({
                    "message": "Field '%s' doesn't exist on type '%s'"
                               % (sel["name"], type_name)})
                out[key] = None
                continue
            out[key] = _gql_complete(value, sel["selection"], ctx)
    return out


def _gql_run_one(payload):
    query = payload.get("query")
    if not isinstance(query, str):
        return {"errors": [{"message": "query must be a string"}]}
    try:
        operations, fragments = _GQLParser(query).parse_document()
    except GQLSyntax as exc:
        return {"errors": [{"message": "Syntax error: %s" % exc}]}
    if not operations:
        return {"errors": [{"message": "no operation found"}]}
    op_name = payload.get("operationName")
    operation = None
    for candidate in operations:
        if op_name is None or candidate["name"] == op_name:
            operation = candidate
            break
    if operation is None:
        operation = operations[0]
    variables = {}
    for name, default in operation["variables"].items():
        if default is not None:
            variables[name] = _gql_eval(default, {})
    provided = payload.get("variables")
    if isinstance(provided, dict):
        variables.update(provided)
    ctx = _GQLContext(fragments)
    ctx.variables = variables
    root_type = "Mutation" if operation["kind"] == "mutation" else "Query"
    data = _gql_exec_set(root_type, {"__gql_type": root_type},
                         operation["selection"], ctx)
    result = {"data": data}
    if ctx.errors:
        result["errors"] = ctx.errors
    return result


def graphql_dispatch(request):
    payload = None
    if request.method == "GET":
        raw_vars = request.q("variables")
        variables = None
        if raw_vars:
            try:
                variables = json.loads(raw_vars)
            except Exception:
                variables = None
        payload = {"query": request.q("query"),
                   "variables": variables,
                   "operationName": request.q("operationName")}
        result = _gql_run_one(payload)
        return json_response(200, result)
    if not request.body:
        return json_response(200, {"errors": [{"message": "empty body"}]})
    try:
        payload = json.loads(request.body.decode("utf-8"))
    except Exception:
        return json_response(200, {"errors": [{"message": "invalid JSON"}]})
    if isinstance(payload, list):
        results = [_gql_run_one(entry) if isinstance(entry, dict)
                   else {"errors": [{"message": "invalid entry"}]}
                   for entry in payload]
        return json_response(200, results)
    if not isinstance(payload, dict):
        return json_response(200, {"errors": [{"message": "invalid payload"}]})
    return json_response(200, _gql_run_one(payload))


# --------------------------------------------------------------------------
# MCP (JSON-RPC over HTTP)

MCP_PROTOCOL_VERSIONS = ["2026-07-28", "2026-03-26", "2025-11-25",
                         "2025-06-18", "2025-03-26", "2024-11-05"]


def _mcp_tool(name, description, properties, required):
    return {
        "name": name,
        "description": description,
        "inputSchema": {
            "type": "object",
            "properties": properties,
            "required": required,
            "additionalProperties": True,
        },
    }


def _s_prop(description):
    return {"type": "string", "description": description}


def _i_prop(description):
    return {"type": "integer", "description": description}


MCP_TOOLS = [
    _mcp_tool("create_repo", "Create a new repository for the viewer.",
              {"name": _s_prop("Repository name"),
               "description": _s_prop("Repository description"),
               "private": {"type": "boolean",
                           "description": "Whether the repo is private"}},
              ["name"]),
    _mcp_tool("get_repo", "Get a repository by owner and name.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "name": _s_prop("Repository name"),
               "full_name": _s_prop("Full name in owner/repo form")},
              []),
    _mcp_tool("list_repos", "List repositories owned by the viewer.",
              {"owner": _s_prop("Owner login (optional)")}, []),
    _mcp_tool("create_issue", "Create an issue in a repository.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "title": _s_prop("Issue title"),
               "body": _s_prop("Issue body"),
               "labels": {"type": "array", "items": {"type": "string"},
                          "description": "Label names"}},
              ["owner", "repo", "title"]),
    _mcp_tool("list_issues", "List issues in a repository.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "state": _s_prop("Filter by state: open, closed or all")},
              ["owner", "repo"]),
    _mcp_tool("get_issue", "Get a single issue by number.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "issue_number": _i_prop("Issue number"),
               "number": _i_prop("Issue number")},
              ["owner", "repo"]),
    _mcp_tool("create_pull_request", "Create a pull request.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "title": _s_prop("Pull request title"),
               "body": _s_prop("Pull request body"),
               "head": _s_prop("Head branch name"),
               "base": _s_prop("Base branch name")},
              ["owner", "repo", "title", "head", "base"]),
    _mcp_tool("list_pull_requests", "List pull requests in a repository.",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "state": _s_prop("Filter by state: open, closed or all")},
              ["owner", "repo"]),
    _mcp_tool("merge_pull_request", "Merge a pull request (squash).",
              {"owner": _s_prop("Repository owner login"),
               "repo": _s_prop("Repository name"),
               "pull_number": _i_prop("Pull request number"),
               "number": _i_prop("Pull request number")},
              ["owner", "repo", "pull_number"]),
]

MCP_TOOLS_BY_NAME = {tool["name"]: tool for tool in MCP_TOOLS}


def _mcp_result(req_id, result):
    return json_response(200, {"jsonrpc": "2.0", "id": req_id,
                               "result": result})


def _mcp_error(req_id, code, message):
    return json_response(200, {"jsonrpc": "2.0", "id": req_id,
                               "error": {"code": code, "message": message}})


def _mcp_tool_result(req_id, payload, is_error=False):
    text = payload if isinstance(payload, str) else dumps(payload).decode("utf-8")
    result = {"content": [{"type": "text", "text": text}],
              "isError": is_error}
    if not is_error and isinstance(payload, (dict, list)):
        result["structuredContent"] = payload
    return _mcp_result(req_id, result)


def _mcp_arg(args, *names):
    for name in names:
        value = args.get(name)
        if value is not None:
            return value
    return None


def _mcp_repo_from_args(args):
    owner = _mcp_arg(args, "owner")
    repo_name = _mcp_arg(args, "repo", "name", "repository")
    full = _mcp_arg(args, "full_name", "fullName")
    if full and "/" in str(full):
        owner, repo_name = str(full).split("/", 1)
    if not owner:
        owner = VIEWER["login"]
    if not repo_name:
        return None
    return FORGE.get(str(owner), str(repo_name))


def _mcp_call_tool(req_id, name, args):
    tool = MCP_TOOLS_BY_NAME.get(name)
    if tool is None:
        return _mcp_error(req_id, -32602, "unknown tool: %s" % name)
    if not isinstance(args, dict):
        args = {}
    missing = [key for key in tool["inputSchema"].get("required", [])
               if args.get(key) is None]
    if missing:
        return _mcp_tool_result(
            req_id, "missing required argument(s): %s" % ", ".join(missing),
            is_error=True)
    with STORE_LOCK:
        if name == "create_repo":
            repo_name = args["name"]
            if FORGE.get(VIEWER["login"], repo_name) is not None:
                return _mcp_tool_result(
                    req_id, "repository already exists: %s" % repo_name,
                    is_error=True)
            repo = FORGE.create(repo_name, args.get("description") or "",
                                bool(args.get("private", False)))
            return _mcp_tool_result(req_id, repo_json(repo))
        if name == "list_repos":
            return _mcp_tool_result(
                req_id, [repo_json(r) for r in FORGE.user_repos()])
        repo = _mcp_repo_from_args(args)
        if repo is None:
            return _mcp_tool_result(req_id, "repository not found",
                                    is_error=True)
        if name == "get_repo":
            return _mcp_tool_result(req_id, repo_json(repo))
        if name == "create_issue":
            names = _label_names_from({"labels": args.get("labels")}, repo)
            if names is None:
                return _mcp_tool_result(req_id, "unknown label",
                                        is_error=True)
            issue = new_issue(repo, args["title"], args.get("body") or "",
                              names)
            return _mcp_tool_result(req_id, issue_json_obj(repo, issue))
        if name == "list_issues":
            state = args.get("state") or "all"
            items = [it for it in repo.items.values()
                     if it["kind"] == "issue"]
            if state in ("open", "closed"):
                items = [it for it in items if it["state"] == state]
            items.sort(key=lambda it: it["number"])
            return _mcp_tool_result(
                req_id, [issue_json_obj(repo, it) for it in items])
        if name == "get_issue":
            number = _mcp_arg(args, "issue_number", "number")
            item = repo.items.get(int(number)) if number is not None else None
            if item is None or item["kind"] != "issue":
                return _mcp_tool_result(req_id, "issue not found",
                                        is_error=True)
            return _mcp_tool_result(req_id, issue_json_obj(repo, item))
        if name == "create_pull_request":
            head = _split_head(str(args["head"]))
            base = str(args["base"])
            if repo.branch_oid(head) is None or \
                    repo.branch_oid(base) is None:
                return _mcp_tool_result(req_id, "head or base branch missing",
                                        is_error=True)
            pull = new_pull(repo, args["title"], args.get("body") or "",
                            head, base)
            return _mcp_tool_result(req_id, pull_json_obj(repo, pull))
        if name == "list_pull_requests":
            state = args.get("state") or "open"
            items = [it for it in repo.items.values() if it["kind"] == "pr"]
            if state in ("open", "closed"):
                items = [it for it in items if it["state"] == state]
            items.sort(key=lambda it: it["number"])
            return _mcp_tool_result(
                req_id, [pull_json_obj(repo, it) for it in items])
        if name == "merge_pull_request":
            number = _mcp_arg(args, "pull_number", "number")
            pull = repo.items.get(int(number)) if number is not None else None
            if pull is None or pull["kind"] != "pr":
                return _mcp_tool_result(req_id, "pull request not found",
                                        is_error=True)
            if pull["merged"] or pull["state"] == "closed":
                return _mcp_tool_result(req_id, "pull request not mergeable",
                                        is_error=True)
            sha, conflict = squash_merge(repo, pull)
            if conflict:
                return _mcp_tool_result(req_id, "pull request has conflicts",
                                        is_error=True)
            pull["merged"] = True
            pull["state"] = "closed"
            pull["merged_at"] = tick()
            pull["closed"] = pull["merged_at"]
            pull["merge_sha"] = sha
            pull["updated"] = pull["merged_at"]
            return _mcp_tool_result(req_id, {
                "sha": sha, "merged": True,
                "message": "Pull Request successfully merged",
                "pull_request": pull_json_obj(repo, pull),
            })
    return _mcp_error(req_id, -32601, "tool not implemented: %s" % name)


def mcp_dispatch(request):
    # Parse first: malformed JSON is a -32700 protocol error (HTTP 400),
    # reported before any auth verdict.
    try:
        payload = json.loads(request.body.decode("utf-8")) \
            if request.body else None
    except Exception:
        return json_response(400, {
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32700, "message": "Parse error"}})
    if not authed(request):
        return Response(401, b'{"error":"unauthorized"}',
                        "application/json")
    if payload is None:
        return json_response(400, {
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32700, "message": "Parse error"}})
    if isinstance(payload, list):
        if not payload:
            return json_response(400, {
                "jsonrpc": "2.0", "id": None,
                "error": {"code": -32600, "message": "Invalid Request"}})
        responses = []
        for entry in payload:
            resp = _mcp_handle_one(entry)
            if resp is not None:
                responses.append(resp)
        if not responses:
            return Response(202, b"", None)
        return json_response(200, responses)
    resp = _mcp_handle_one(payload)
    if resp is None:
        return Response(202, b"", None)
    return json_response(200, resp)


def _mcp_handle_one(entry):
    if not isinstance(entry, dict):
        return {"jsonrpc": "2.0", "id": None,
                "error": {"code": -32600, "message": "Invalid Request"}}
    method = entry.get("method")
    req_id = entry.get("id")
    params = entry.get("params") or {}
    if not isinstance(params, dict):
        params = {}
    is_notification = "id" not in entry
    if method == "server/discover":
        return {"jsonrpc": "2.0", "id": req_id, "result": {
            "supportedVersions": list(MCP_PROTOCOL_VERSIONS),
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge2", "version": "2.0.0"},
        }}
    if method == "initialize":
        requested = params.get("protocolVersion")
        version = requested if requested in MCP_PROTOCOL_VERSIONS \
            else MCP_PROTOCOL_VERSIONS[0]
        return {"jsonrpc": "2.0", "id": req_id, "result": {
            "protocolVersion": version,
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "forge2", "version": "2.0.0"},
        }}
    if method in ("notifications/initialized", "notifications/cancelled",
                  "notifications/progress"):
        return None
    if is_notification:
        return None
    if method == "ping":
        return {"jsonrpc": "2.0", "id": req_id, "result": {}}
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": req_id,
                "result": {"tools": MCP_TOOLS}}
    if method == "tools/call":
        name = params.get("name")
        args = params.get("arguments") or {}
        resp = _mcp_call_tool(req_id, name, args)
        return json.loads(resp.body.decode("utf-8"))
    if method in ("resources/list",):
        return {"jsonrpc": "2.0", "id": req_id, "result": {"resources": []}}
    if method in ("prompts/list",):
        return {"jsonrpc": "2.0", "id": req_id, "result": {"prompts": []}}
    return {"jsonrpc": "2.0", "id": req_id,
            "error": {"code": -32601,
                      "message": "Method not found: %s" % method}}


if __name__ == "__main__":
    raise SystemExit(main())
