#!/bin/sh
# Format (or check) Lean files changed from a base ref.
# Skips deleted files. Refuses staged, unstaged, and untracked Lean files unless
# --allow-dirty is given.
#
# Usage: scripts/fmt-changed.sh [--check] [--allow-dirty] [--base REF]
set -eu

usage() {
  cat <<'EOF'
Usage: scripts/fmt-changed.sh [--check] [--allow-dirty] [--base REF]

Format Lean files changed from REF (default: origin/main).

Options:
  --check        Check formatting instead of rewriting files.
  --allow-dirty  Also format staged, unstaged, and untracked Lean files.
  --base REF     Compare committed changes against REF.
  -h, --help     Show this help text.
EOF
}

check=""
allow_dirty=false
base=origin/main

while [ "$#" -gt 0 ]; do
  case "$1" in
  --check)
    check="--check"
    ;;
  --allow-dirty)
    allow_dirty=true
    ;;
  --base)
    shift
    if [ "$#" -eq 0 ]; then
      echo "--base requires a reference." >&2
      exit 2
    fi
    base=$1
    ;;
  -h | --help)
    usage
    exit 0
    ;;
  *)
    echo "Unknown option: $1" >&2
    usage >&2
    exit 2
    ;;
  esac
  shift
done

filter_existing_files() {
  while IFS= read -r file; do
    test -e "$file" && printf '%s\n' "$file"
  done
}

if [ "$allow_dirty" = false ]; then
  dirty_files=$(
    {
      git diff --cached --name-only --diff-filter=ACMR -- '*.lean'
      git diff --name-only --diff-filter=ACMR -- '*.lean'
      git ls-files --others --exclude-standard -- '*.lean'
    } \
      | sort -u \
      | filter_existing_files
  )

  if [ -n "$dirty_files" ]; then
    echo "Refusing to format dirty Lean files:" >&2
    printf '%s\n' "$dirty_files" | while IFS= read -r file; do
      printf '  %s\n' "$file" >&2
    done
    echo "Re-run with --allow-dirty to include them." >&2
    exit 2
  fi
fi

files=$(
  {
    git diff --name-only --diff-filter=ACMR "$base..." -- '*.lean'
    if [ "$allow_dirty" = true ]; then
      git diff --cached --name-only --diff-filter=ACMR -- '*.lean'
      git diff --name-only --diff-filter=ACMR -- '*.lean'
      git ls-files --others --exclude-standard -- '*.lean'
    fi
  } \
    | sort -u \
    | filter_existing_files
)

if [ -z "$files" ]; then
  echo "No changed Lean files to format."
  exit 0
fi

printf '%s\n' "$files" | xargs lake exe fmt $check
