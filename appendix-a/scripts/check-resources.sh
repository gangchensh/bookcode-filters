#!/usr/bin/env bash
# Read-only resource overview. Does not install or alter system settings.
set -eu
printf 'System: '; uname -s
printf '\nFilesystem capacity (check the Windows drive hosting WSL separately):\n'
df -h / "$PWD"
printf '\nMemory visible to Linux (WSL: guest memory, not total Windows RAM):\n'
free -h
printf '\nAvailable processing units: '; nproc
printf '\nDisk usage (not RAM): .elan=Lean toolchains; .opam=OCaml/Rocq environments; .lake=current project:\n'
for resource_dir in "${ELAN_HOME:-$HOME/.elan}" "${OPAMROOT:-$HOME/.opam}" "${XDG_CACHE_HOME:-$HOME/.cache}/mathlib" "$PWD/.lake"; do
  if [ -d "$resource_dir" ]; then
    du -sh "$resource_dir"
  else
    printf 'Not present: %s\n' "$resource_dir"
  fi
done
