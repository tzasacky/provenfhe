#!/usr/bin/env python3
"""SHA-256 of every .olean the gate's PinStatus can load, for the replay cache.   TRUSTED; see trust/LOCK.

Usage (under `lake env`, so that LEAN_PATH is the project's search path):
    lake env python3 -I -B scripts/olean_sha.py --memo|--fresh CACHE_DIR scripts/PinStatus.lean
    python3 -I -B scripts/olean_sha.py --publish CACHE_DIR

Writes, atomically (temporary file, then rename):
  CACHE_DIR/olean-sha256.txt   "<sha256> <path>" for every *.olean, *.olean.server, *.olean.private
                               under the LEAN_PATH directories and the toolchain's lib/lean
  CACHE_DIR/env-id.txt         one line: sha256 over the toolchain (lean --version, the lean binary,
                               the shared libraries under its lib/), PinStatus.lean and a format tag.
                               A replay cache recorded under another env-id is ignored.

Hashing ~7 GB of Mathlib and toolchain .oleans takes a few seconds on many cores, so results are
memoised keyed by the file's identity and state (device, inode, size, mtime_ns, ctime_ns): a file
whose stat is unchanged is not re-read (`--memo`). ctime cannot be set from user space, so a
rewrite that keeps size and mtime still changes the key. `--fresh` (used under STRICT=1, where the
gate only records replay results and never reads them) re-reads every file and ignores the memo
(it still records what it computed).

Shared store (development runs; `GATE_SHARED_CACHE`, default `~/.cache/lean-fhe-gate`; empty
disables it). Checkouts of the same machine share Mathlib's and the toolchain's .olean files (the
same inodes, through the `.lake/packages` symlink) and often byte-identical project .oleans, so:
  * the memo lives in the shared store (`olean-sha-memo.json`; per-checkout memo as fallback), so
    a new checkout does not re-hash Mathlib;
  * `--publish CACHE_DIR` copies `CACHE_DIR/replay-accepted.txt` (written by PinStatus, only after
    a replay) into `records/<its sha256>.txt` of the shared store (content-addressed, atomic
    rename; the 16 most recent are kept);
  * `--memo` then puts into `CACHE_DIR/replay-accepted.txt` the record, among the local one and the
    shared ones written under the same env-id, whose module hashes agree with the current .olean
    files most often (a heuristic choice only: PinStatus skips a root only if every constant of its
    closure is unchanged against the record it reads, whichever that is; see scripts/PinStatus.lean,
    "Replay cache").
A record is only ever written by PinStatus (via CACHE_DIR, then published unchanged), so the shared
store is trusted exactly as CACHE_DIR is: whoever can write it can make a development run skip
replay. The strict gate never reads either (`--fresh`; PinStatus gets `--replay-cache-write`).
"""
import concurrent.futures as cf
import glob
import hashlib
import json
import os
import subprocess
import sys

SUFFIXES = (".olean", ".olean.server", ".olean.private")
FORMAT = "replay-cache-v1"
KEEP_RECORDS = 16


def sha_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 22)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def stat_key(st: os.stat_result) -> list:
    return [st.st_size, st.st_mtime_ns, st.st_ctime_ns, st.st_ino, st.st_dev]


def ident(st: os.stat_result) -> str:
    return f"{st.st_dev}:{st.st_ino}"


def write_atomic(path: str, text: str) -> None:
    tmp = f"{path}.tmp.{os.getpid()}"
    with open(tmp, "w") as f:
        f.write(text)
    os.replace(tmp, path)


def shared_dir() -> str:
    d = os.environ.get("GATE_SHARED_CACHE", os.path.join(os.path.expanduser("~"), ".cache", "lean-fhe-gate"))
    if d:
        try:
            os.makedirs(os.path.join(d, "records"), exist_ok=True)
        except OSError:
            return ""
    return d


def load_json(path: str) -> dict:
    try:
        with open(path) as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def record_header(path: str):
    """(env-id, set of module hash strings) of a replay-accepted.txt, or None if unreadable."""
    env, mods = None, set()
    try:
        with open(path) as f:
            for line in f:
                p = line.rstrip("\n").split("\t")
                if p[0] == "ENV" and len(p) == 2:
                    env = p[1]
                elif p[0] == "M" and len(p) == 3:
                    mods.add(p[2])
                elif p[0] == "C":
                    break   # M lines precede the C lines
    except OSError:
        return None
    return env, mods


def mtime_or_zero(p: str) -> float:
    try:
        return os.stat(p).st_mtime
    except OSError:
        return 0.0


def publish(cache: str) -> int:
    """Best effort: a failure here (another checkout pruning or writing) only loses a record."""
    shared = shared_dir()
    src = os.path.join(cache, "replay-accepted.txt")
    if not shared or not os.path.isfile(src):
        return 0
    try:
        with open(src, "rb") as f:
            data = f.read()
        dst = os.path.join(shared, "records", f"{hashlib.sha256(data).hexdigest()}.txt")
        if os.path.exists(dst):
            os.utime(dst)
        else:
            tmp = f"{dst}.tmp.{os.getpid()}"
            with open(tmp, "wb") as g:
                g.write(data)
            os.replace(tmp, dst)
        recs = sorted(glob.glob(os.path.join(shared, "records", "*.txt")), key=lambda p: -mtime_or_zero(p))
        for p in recs[KEEP_RECORDS:]:
            try:
                os.remove(p)
            except OSError:
                pass
        print(f"olean_sha: published the replay record to {dst}")
    except OSError as e:
        print(f"olean_sha: replay record not published ({e})")
    return 0


def select_record(cache: str, env_id: str, cur: set) -> str:
    """Copy the best-matching record (local or shared) to CACHE_DIR/replay-accepted.txt. Best
    effort: on any error the local record stays as it is."""
    shared = shared_dir()
    local = os.path.join(cache, "replay-accepted.txt")
    best, best_score = None, -1
    try:
        cands = [local] + (sorted(glob.glob(os.path.join(shared, "records", "*.txt"))) if shared else [])
        for p in cands:
            hdr = record_header(p)
            if not hdr or hdr[0] != env_id:
                continue
            score = len(hdr[1] & cur)
            if score > best_score:
                best, best_score = p, score
        if best is None or best == local:
            return f"replay record: {'local' if best else 'none'}"
        with open(best, "rb") as f:
            data = f.read()
        tmp = f"{local}.tmp.{os.getpid()}"
        with open(tmp, "wb") as g:
            g.write(data)
        os.replace(tmp, local)
        return f"replay record: shared {os.path.basename(best)[:16]} ({best_score} modules agree)"
    except OSError as e:
        return f"replay record: local (shared store unreadable: {e})"


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == "--publish":
        return publish(sys.argv[2])
    if len(sys.argv) != 4 or sys.argv[1] not in ("--memo", "--fresh"):
        print(__doc__, file=sys.stderr)
        return 2
    fresh, cache, pinstatus = sys.argv[1] == "--fresh", sys.argv[2], sys.argv[3]
    os.makedirs(cache, exist_ok=True)
    prefix = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True,
                            check=True).stdout.strip()
    version = subprocess.run(["lean", "--version"], capture_output=True, text=True,
                             check=True).stdout.strip()
    dirs = [d for d in os.environ.get("LEAN_PATH", "").split(os.pathsep) if d]
    dirs.append(os.path.join(prefix, "lib", "lean"))
    files = []
    seen_dirs = set()
    for d in dirs:
        if d in seen_dirs or not os.path.isdir(d):
            continue
        seen_dirs.add(d)
        for root, _, names in os.walk(d, followlinks=True):
            for n in names:
                if n.endswith(SUFFIXES):
                    files.append(os.path.join(root, n))
    # the toolchain's own code: the kernel lives in the lean binary / shared libraries
    tool = [os.path.join(prefix, "bin", "lean")]
    libdir = os.path.join(prefix, "lib")
    for root, _, names in os.walk(libdir):
        tool += [os.path.join(root, n) for n in names if n.endswith((".so", ".dylib", ".dll"))]
    tool.sort()

    shared = shared_dir()
    memo_path = os.path.join(shared, "olean-sha-memo.json") if shared else os.path.join(cache, "olean-sha-memo.json")
    # memo: "<dev>:<ino>" -> [size, mtime_ns, ctime_ns, ino, dev, sha, a path of the file]
    memo = {} if fresh else load_json(memo_path)
    out: dict[str, str] = {}
    todo = []
    for p in files + tool + [pinstatus]:
        try:
            st = os.stat(p)
        except OSError:
            continue
        k = stat_key(st)
        m = memo.get(ident(st))
        if isinstance(m, list) and len(m) == 7 and m[:5] == k:
            out[p] = m[5]
        else:
            todo.append((p, k, ident(st)))
    workers = max(1, min(16, (os.cpu_count() or 2) // 2))
    new = {}
    with cf.ThreadPoolExecutor(workers) as ex:
        for (p, k, i), h in zip(todo, ex.map(lambda t: sha_file(t[0]), todo)):
            out[p] = h
            new[i] = k + [h, p]
    if new:
        # re-read just before writing: other checkouts update the same memo
        merged = load_json(memo_path)
        merged.update(new)
        # drop the entries of files that no longer exist under the recorded path (deleted
        # checkouts, rebuilt .oleans), so that the shared memo does not grow without bound
        def alive(v) -> bool:
            try:
                st = os.stat(v[6])
                return isinstance(v, list) and len(v) == 7 and stat_key(st) == v[:5]
            except (OSError, TypeError, IndexError):
                return False
        merged = {i: v for i, v in merged.items() if alive(v)}
        try:
            write_atomic(memo_path, json.dumps(merged))
        except OSError as e:
            print(f"olean_sha: memo not written ({e})")
    env_id = hashlib.sha256()
    env_id.update(f"{FORMAT}\n{version}\n".encode())
    for p in tool + [pinstatus]:
        env_id.update(f"{os.path.basename(p)} {out.get(p, 'MISSING')}\n".encode())
    write_atomic(os.path.join(cache, "olean-sha256.txt"),
                 "".join(f"{out[p]} {p}\n" for p in sorted(files) if p in out))
    write_atomic(os.path.join(cache, "env-id.txt"), env_id.hexdigest() + "\n")
    msg = ""
    if not fresh:
        cur = set()
        for p in files:
            if p.endswith(".olean") and p in out:
                cur.add(f"{out[p]}:{out.get(p + '.server', '-')}:{out.get(p + '.private', '-')}")
        msg = "; " + select_record(cache, env_id.hexdigest(), cur)
    print(f"olean_sha: {len(files)} files, {len(todo)} (re)hashed, env-id {env_id.hexdigest()[:16]}{msg}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
