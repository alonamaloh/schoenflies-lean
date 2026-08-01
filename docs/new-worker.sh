#!/bin/bash
# Provision a git worktree of schoenflies-lean that shares the main repo's built Mathlib.
#
#   new-worker.sh <name>     -> prints the worktree path
#
# The worktree is a real branch (wt/<name>) off main, so work is committed there and
# integrated by merging. Only .lake/packages is symlinked at the main repo — Mathlib is
# built and never changes — so provisioning is instant and `lake build` is a few seconds.
#
# Worktrees are parked in $SCHOENFLIES_WT_ROOT, defaulting to a fixed directory that does
# NOT depend on which agent session provisions them. An earlier version pointed at one
# session's scratchpad; when that session ended the path went stale and `git worktree list`
# was left full of unreachable entries.
set -e
NAME="$1"
[ -z "$NAME" ] && { echo "usage: new-worker.sh <name>" >&2; exit 1; }
SCRATCH="${SCHOENFLIES_WT_ROOT:-/tmp/claude-1000/schoenflies-worktrees}"
MAIN=/home/alvaro/claude/schoenflies-lean
DIR="$SCRATCH/wt-$NAME"

mkdir -p "$SCRATCH"
exec 9>"$SCRATCH/.worktree.lock"
flock 9

git -C "$MAIN" worktree remove --force "$DIR" 2>/dev/null || true
git -C "$MAIN" branch -D "wt/$NAME" 2>/dev/null || true
rm -rf "$DIR"

git -C "$MAIN" worktree add -q -b "wt/$NAME" "$DIR" main
flock -u 9
mkdir -p "$DIR/.lake"
ln -s "$MAIN/.lake/packages" "$DIR/.lake/packages"
echo "$DIR"
