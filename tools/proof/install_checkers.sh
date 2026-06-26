#!/usr/bin/env bash
# Reproducibly install the INDEPENDENT external proof checkers Xolver's proofs
# are validated against. These are separate tools (separate authors) — Xolver
# never grades its own proof; an outside checker must accept it.
#
#   * drat-trim + lrat-check  — the Boolean-core checkers (DRAT/LRAT).
#       drat-trim does full forward RUP and is ADVERSARIALLY SOUND (it rejects a
#       bogus proof of a SAT formula); it is the gate. See
#       docs/proof/refs/checker-soundness-test.sh.
#   * carcara                 — the Alethe checker for theory sub-proofs (Phase C+).
#
# Usage: install_checkers.sh [install-dir]   (default: ./.proof-checkers)
# Prints the resolved binary paths on success.
set -euo pipefail
DEST="${1:-$(pwd)/.proof-checkers}"
mkdir -p "$DEST"
cd "$DEST"

echo "== drat-trim / lrat-check =="
if [ ! -x "$DEST/drat-trim/drat-trim" ]; then
  rm -rf "$DEST/drat-trim"
  git clone --depth 1 https://github.com/marijnheule/drat-trim.git
  ( cd drat-trim && make drat-trim && cc -O2 -o lrat-check lrat-check.c )
fi
echo "DRAT_TRIM=$DEST/drat-trim/drat-trim"
echo "LRAT_CHECK=$DEST/drat-trim/lrat-check"

echo "== carcara (Alethe) =="
if command -v cargo >/dev/null 2>&1; then
  if [ ! -x "$DEST/carcara/bin/carcara" ]; then
    cargo install --git https://github.com/ufmg-smite/carcara.git --root "$DEST/carcara" -j 2
  fi
  echo "CARCARA=$DEST/carcara/bin/carcara"
else
  echo "CARCARA=SKIPPED (cargo not found; needed only for the Phase C+ Alethe gate)"
fi

echo "== self-test the Boolean-core gate is adversarially sound =="
bash "$(dirname "$0")/../../docs/proof/refs/checker-soundness-test.sh" "$DEST/drat-trim/drat-trim"
echo "checkers ready under: $DEST"
