#!/usr/bin/env bash
# Read-only inventory. Never installs, updates, uninstalls or removes anything.
# Usage: bash appendix-a/scripts/version-space.sh [LEAN_PROJECT_DIRECTORY]
set -euo pipefail

usage() {
  printf 'Usage: bash version-space.sh [LEAN_PROJECT_DIRECTORY]\n'
}
if [[ ${1:-} == --help || ${1:-} == -h ]]; then usage; exit 0; fi
if (( $# > 1 )); then usage >&2; exit 2; fi
if [[ ! -d ${1:-$PWD} ]]; then
  printf 'Directory does not exist: %s\n' "$1" >&2
  exit 2
fi
project_dir=$(cd -- "${1:-$PWD}" && pwd -P)
elan_root=${ELAN_HOME:-$HOME/.elan}
opam_root=${OPAMROOT:-$HOME/.opam}

report() {
  local entry=$1
  if [[ -L $entry ]]; then
    local resolved
    if resolved=$(readlink -f -- "$entry") && [[ -d $resolved ]]; then
      printf 'Linked directory: %s -> %s\n' "$entry" "$resolved"
      du -sh -- "$resolved" || printf 'Could not measure this directory.\n' >&2
    else
      printf 'Broken or unavailable link: %s\n' "$entry"
    fi
  elif [[ -d $entry ]]; then
    du -sh -- "$entry" || printf 'Could not measure: %s\n' "$entry" >&2
  else
    printf 'Not present: %s\n' "$entry"
  fi
}

printf 'Lean installation root: %s\n' "$elan_root"
printf 'Each directory below is one installed or linked toolchain.\n'
if [[ -d $elan_root/toolchains ]]; then
  shopt -s nullglob dotglob
  toolchains=("$elan_root/toolchains/"*)
  if (( ${#toolchains[@]} == 0 )); then printf 'No toolchain directories.\n'; fi
  for entry in "${toolchains[@]}"; do report "$entry"; done
  shopt -u nullglob dotglob
else
  printf 'No toolchain directory.\n'
fi

printf '\nOCaml/Rocq installation root: %s\n' "$opam_root"
if command -v opam >/dev/null 2>&1 && [[ -f $opam_root/config ]]; then
  if switch_names=$(opam switch list --root="$opam_root" --short); then
    while IFS= read -r switch_name; do
      [[ -n $switch_name ]] || continue
      printf '\nSwitch: %s\n' "$switch_name"
      if prefix=$(opam var prefix --root="$opam_root" --switch="$switch_name"); then
        report "$prefix"
        opam list --root="$opam_root" --switch="$switch_name" --installed \
          --short --columns=name,version |
          awk '$1 == "rocq-core" || $1 == "coq-core" || $1 == "ocaml-base-compiler"'
      else
        printf 'Could not locate prefix; inspect this switch with opam.\n' >&2
      fi
    done <<< "$switch_names"
  fi
else
  printf 'opam is unavailable or this root is not initialized.\n'
fi

printf '\nShared caches and opam total (do not add total to switch subtotals):\n'
report "$opam_root"
report "$opam_root/download-cache"
report "$opam_root/log"
report "${XDG_CACHE_HOME:-$HOME/.cache}/mathlib"
printf '\nLean project: %s\n' "$project_dir"
report "$project_dir/.lake"
report "$project_dir/.lake/build"
report "$project_dir/.lake/packages"
printf '\n.lake is the total; its build/packages lines are subtotals.\n'
printf 'Linked/shared directories may be counted more than once; do not sum blindly.\n'
printf 'This report has not changed any version or deleted any files.\n'
