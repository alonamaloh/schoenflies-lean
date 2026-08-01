#!/bin/bash
# Provision a git worktree of schoenflies-lean that shares the main repo's built Mathlib.
#
#   new-worker.sh <name>     -> prints the worktree path
#
# The worktree is a real branch (wt/<name>) off main, so work is committed there and
# integrated by merging. Only .lake/packages is symlinked at the main repo — Mathlib is
# built and never changes — so provisioning is instant and `lake build` is a few seconds.
set -e
NAME="$1"
[ -z "$NAME" ] && { echo "usage: new-worker.sh <name>" >&2; exit 1; }
SCRATCH=/tmp/claude-1000/-home-alvaro-claude-schoenflies/cd0a4752-0d99-41c7-a3ad-b4ee811d9c2d/scratchpad
MAIN=/home/alvaro/claude/schoenflies-lean
DIR="$SCRATCH/wt-$NAME"

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
