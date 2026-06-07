#!/usr/bin/env bash
# Scan targeted_eqnia for high-memory / OOM cases (peak RSS > 1.5 GB).
set -u
cd /mnt/d/D_Study/BUAA/projects/zolver-eqnia
BIN=build/bin/xolver
A="XOLVER_COMB_ARRAY_BRIDGE_MODEL=1 XOLVER_EUF_PROP=1 XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 XOLVER_NIA_MODULAR=1 XOLVER_PP_SOLVE_EQS=1 XOLVER_PP_SOLVE_EQS_GAUSS=1 XOLVER_NIA_FARKAS_OR=1 XOLVER_NIA_LBBB=1 XOLVER_NRA_LINEARIZE=1"
tail -n +2 targeted_eqnia/MANIFEST.tsv | while IFS=$'\t' read -r logic category polarity size oracle xwas key; do
  [ -z "${key:-}" ] && continue
  f="targeted_eqnia/$key"; [ -f "$f" ] || continue
  rss=$( ulimit -v 4000000; env $A /usr/bin/time -v timeout 20 "$BIN" solve "$f" 2>&1 1>/dev/null | grep -oE "Maximum resident set size \(kbytes\): [0-9]+" | grep -oE "[0-9]+")
  [ -z "$rss" ] && rss=0
  mb=$((rss/1024))
  if [ "$mb" -gt 1500 ]; then echo "HIGH ${mb}MB [$logic] ${key##*/}"; fi
done
echo "OOM_SCAN_DONE"
