#!/usr/bin/env bash
# Run from the Lean project root. No default-version or dependency changes.
set -euo pipefail
if [ "$#" -gt 1 ]; then
  printf 'Usage: bash check-lean.sh [FILE.lean|--build]\n' >&2
  exit 2
fi
if [ ! -f lean-toolchain ]; then
  printf 'Enter the project root containing lean-toolchain first.\n' >&2
  exit 2
fi
project_toolchain=$(tr -d '\r\n' < lean-toolchain)
if [ -z "$project_toolchain" ]; then
  printf 'lean-toolchain is empty.\n' >&2
  exit 2
fi
if [ "${1:-}" = --build ]; then
  printf 'Building project with %s...\n' "$project_toolchain" >&2
  exec elan run "$project_toolchain" lake build
fi
lean_file="${1:-MathlibSmoke.lean}"
if [ ! -f "$lean_file" ]; then
  printf 'File not found: %s\n' "$lean_file" >&2
  exit 2
fi
printf 'Checking %s with %s...\n' "$lean_file" "$project_toolchain" >&2
printf 'Large imports may load quietly for a while; first-time downloads/builds take longer.\n' >&2
exec elan run "$project_toolchain" lake env lean "$lean_file"
