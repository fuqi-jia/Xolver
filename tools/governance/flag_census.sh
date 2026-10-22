#!/usr/bin/env bash
# Compatibility entry point for the source-backed census.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
exec python3 "$ROOT/tools/governance/flag_census.py" "$@"
