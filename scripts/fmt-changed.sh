#!/bin/sh
# Format (or check) Lean files changed from a base ref.
# Skips files deleted from the working tree.
#
# Usage: scripts/fmt-changed.sh [--check] [base-ref]
#   --check    check formatting instead of rewriting files
#   base-ref   ref to diff against (default: origin/main)
set -eu

check=""
if [ "${1:-}" = "--check" ]; then
  check="--check"
  shift
fi
base="${1:-origin/main}"

files=$(git diff --name-only --diff-filter=ACMR "$base..." -- '*.lean' \
  | while IFS= read -r f; do test -e "$f" && printf '%s\n' "$f"; done)

if [ -z "$files" ]; then
  echo "No changed Lean files to format."
  exit 0
fi

printf '%s\n' "$files" | xargs lake exe fmt $check
