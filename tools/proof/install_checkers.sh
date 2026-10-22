#!/usr/bin/env bash
# Install pinned external proof checkers, retaining one incremental source tree.
# Usage: install_checkers.sh [install-dir] (default: ./.proof-checkers)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="${1:-$(pwd)/.proof-checkers}"
mkdir -p "$DEST"
DEST="$(cd "$DEST" && pwd)"
exec 9>"$DEST/.install.lock"
flock 9
DRAT_REV="${XOLVER_DRAT_TRIM_REV:-2e3b2dc0ecf938addbd779d42877b6ed69d9a985}"
CARCARA_REV="${XOLVER_CARCARA_REV:-20bf49c5ce31089ac83118574c888669355aaae1}"

if [ ! -d "$DEST/drat-trim/.git" ]; then
  # An existing non-repository directory is preserved; git clone will refuse it.
  git clone https://github.com/marijnheule/drat-trim.git "$DEST/drat-trim"
fi
if [ -n "$(git -C "$DEST/drat-trim" diff --name-only HEAD 2>/dev/null)" ]; then
  echo 'drat-trim has local source changes; refusing to overwrite them' >&2
  exit 1
fi
if ! git -C "$DEST/drat-trim" cat-file -e "$DRAT_REV^{commit}" 2>/dev/null; then
  git -C "$DEST/drat-trim" fetch --depth 1 origin "$DRAT_REV"
fi
git -C "$DEST/drat-trim" checkout --detach "$DRAT_REV"
"${CC:-cc}" -D_DEFAULT_SOURCE -std=c99 -O2 \
  "$DEST/drat-trim/drat-trim.c" -o "$DEST/drat-trim/drat-trim"
cc -O2 -o "$DEST/drat-trim/lrat-check" "$DEST/drat-trim/lrat-check.c"
printf '%s\n' "$DRAT_REV" > "$DEST/drat-trim.revision"
echo "DRAT_TRIM=$DEST/drat-trim/drat-trim"
echo "LRAT_CHECK=$DEST/drat-trim/lrat-check"

if command -v cargo >/dev/null 2>&1; then
  if [ ! -x "$DEST/carcara/bin/carcara" ] || \
     [ "$(cat "$DEST/carcara.revision" 2>/dev/null || true)" != "$CARCARA_REV" ]; then
    cargo install --locked --git https://github.com/ufmg-smite/carcara.git \
      --rev "$CARCARA_REV" --root "$DEST/carcara" --force -j 2
    printf '%s\n' "$CARCARA_REV" > "$DEST/carcara.revision"
  fi
  echo "CARCARA=$DEST/carcara/bin/carcara"
else
  echo 'CARCARA=UNAVAILABLE (cargo not found; theory proof checking is unavailable)'
fi
bash "$HERE/../../docs/proof/refs/checker-soundness-test.sh" "$DEST/drat-trim/drat-trim"
echo "checkers ready under: $DEST"
