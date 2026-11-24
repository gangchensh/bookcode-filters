#!/usr/bin/env bash
# Run one workload, including its ordinary child processes, in a new cgroup.
# Requires systemd >= 253, a working user manager, and cgroup v2 memory control.
# Default example budget: WSL memory=8GB. No system configuration is changed.
# Optional environment overrides (set before bash when invoking this script):
# LIMIT_MEMORY_HIGH=3G LIMIT_MEMORY_MAX=4G LIMIT_SWAP_MAX=1G LIMIT_CPU_QUOTA=200%
# Usage: bash appendix-a/scripts/run-limited.sh bash
#        bash appendix-a/scripts/run-limited.sh make lean
set -euo pipefail
if [ "$#" -eq 0 ]; then
  printf 'Usage: bash %s COMMAND [ARG...]\n' "$0" >&2
  exit 2
fi
for required in systemd systemd-run systemctl stat; do
  command -v "$required" >/dev/null || {
    printf 'Required program not found: %s\n' "$required" >&2
    exit 1
  }
done
version_output=$(systemd --version)
read -r _ version_number _ <<< "${version_output%%$'\n'*}"
if [[ ! "$version_number" =~ ^[0-9]+$ ]] || (( version_number < 253 )); then
  printf 'This example requires systemd >= 253 (scope OOMPolicy).\n' >&2
  exit 1
fi
if [ "$(stat -fc %T /sys/fs/cgroup)" != cgroup2fs ]; then
  printf 'This example requires cgroup v2. No unbounded fallback is run.\n' >&2
  exit 1
fi
if ! grep -qw memory /sys/fs/cgroup/cgroup.controllers; then
  printf 'The cgroup memory controller is unavailable.\n' >&2
  exit 1
fi
if ! systemctl --user show-environment >/dev/null; then
  printf 'Cannot connect to the systemd user manager. Fix it before retrying.\n' >&2
  exit 1
fi
exec systemd-run --user --scope \
  -p "MemoryHigh=${LIMIT_MEMORY_HIGH:-3G}" \
  -p "MemoryMax=${LIMIT_MEMORY_MAX:-4G}" \
  -p "MemorySwapMax=${LIMIT_SWAP_MAX:-1G}" \
  -p "CPUQuota=${LIMIT_CPU_QUOTA:-200%}" \
  -p OOMPolicy=kill "$@"
