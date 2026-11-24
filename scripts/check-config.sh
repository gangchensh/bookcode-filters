#!/usr/bin/env bash
# Read/syntax-check the supplied configurations; do not edit user startup files.
set -euo pipefail
code_root="$(cd -- "$(dirname -- "$0")/.." && pwd)"
bash -n "$code_root/config/bashrc.example"
verification_home="$(mktemp -d "${TMPDIR:-/tmp}/calculus-shell-check-XXXXXX")"
HOME="$verification_home" bash --noprofile --norc -ic '
  source "$1"
  test "$CALCULUS_WORK" = /mnt/d/calculus-work
  test "$CALCULUS_CODE" = /mnt/d/calculus-work/code
  test "$PS1" = "\W\$ "
  alias gst >/dev/null
  declare -F rocqenv >/dev/null
' _ "$code_root/config/bashrc.example"
printf 'Bash configuration syntax, prompt, variables, alias and function checks passed.\n'
