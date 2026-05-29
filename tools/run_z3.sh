#!/usr/bin/env bash
# =============================================================================
# run_z3.sh — 跑 z3 @1200s 做 oracle 缓存(用法跟 run_blan.sh 完全一样)。
# 结果存 z3_<LOGIC>_node<N>.csv,行格式: key,verdict,seconds
#   key = "<LOGIC>/<family>/<file>.smt2"(跟 blan CSV / Xolver 差分同 key)
#   verdict ∈ {sat, unsat, unknown, timeout, error}
# 以后每次 Xolver 差分直接 join 这个 CSV,不用再现场陪跑 z3。
#
# 用法(panda1 + panda7,2 路,-j230):
#   panda1:  nohup ./run_z3.sh 1 2 230 QF_NIA > z3_1.log 2>&1 &
#   panda7:  nohup ./run_z3.sh 2 2 230 QF_NIA > z3_7.log 2>&1 &
#   argv: <第几台> <共几台> <并行数> <logic>
#   看进度: wc -l z3_QF_NIA_node1.csv
#
# 可覆盖: Z3=  BENCH=  TIMEOUT=  MEMCAP_KB=  OUT=
# =============================================================================
set -u
NODE="${1:?用法: run_z3.sh <第几台> <共几台> <并行数> <logic>}"
NODES="${2:?共几台}"; JOBS="${3:?并行数}"; LOGIC="${4:?logic, 如 QF_NIA}"
TIMEOUT="${TIMEOUT:-1200}"               # 每文件墙钟超时(秒),默认 20 分钟
MEMCAP_KB="${MEMCAP_KB:-16000000}"       # 每进程地址空间上限 ~16GB
HERE="$(cd "$(dirname "$0")" && pwd)"
Z3="${Z3:-z3}"

command -v "$Z3" >/dev/null 2>&1 || { echo "ERROR: z3 不在 PATH (用 Z3=/路径 覆盖)"; exit 1; }

# 找 benchmark 目录
if [ -z "${BENCH:-}" ]; then
  for c in ./benchmark/non-incremental ../benchmark/non-incremental \
           /pub/data/jiafq/smt-comp-2025/benchmark/non-incremental; do
    [ -d "$c/$LOGIC" ] && { BENCH="$(readlink -f "$c")"; break; }
  done
fi
[ -d "${BENCH:-/nonexistent}/$LOGIC" ] || { echo "ERROR: 找不到 $LOGIC 目录 (用 BENCH=/路径/non-incremental 覆盖)"; exit 1; }

OUT="${OUT:-z3_${LOGIC}_node${NODE}.csv}"

# 本机切片(sorted, round-robin, 无重叠无缝隙)
LIST="$(mktemp)"
find "$BENCH/$LOGIC" -name '*.smt2' | LC_ALL=C sort | awk -v N="$NODES" -v i="$NODE" 'NR % N == (i-1)' > "$LIST"
TOTAL="$(wc -l < "$LIST")"
echo "z3     = $Z3"
echo "bench  = $BENCH/$LOGIC    本机 = $NODE/$NODES    并行 = $JOBS    超时 = ${TIMEOUT}s    文件 = $TOTAL"
echo "out    = $OUT"
[ "$TOTAL" -gt 0 ] || { echo "ERROR: 本切片 0 文件(检查 node/nodes)"; rm -f "$LIST"; exit 1; }

# 一个文件: z3 求解 → 打印 key,verdict,seconds
run_one() {
  f="$1"
  key="$LOGIC/${f##*$LOGIC/}"
  start="$(date +%s.%N)"
  out="$( ulimit -v "$MEMCAP_KB" 2>/dev/null; timeout "$TIMEOUT" "$Z3" "$f" 2>/dev/null )"
  rc=$?
  end="$(date +%s.%N)"
  sec="$(awk -v a="$start" -v b="$end" 'BEGIN{printf "%.2f", b-a}')"
  if [ "$rc" -eq 124 ]; then
    v="timeout"
  else
    v="$(printf '%s' "$out" | grep -Eoim1 'unsat|unknown|sat')"
    [ -z "$v" ] && v="error"
  fi
  printf '%s,%s,%s\n' "$key" "$v" "$sec"
}
export -f run_one
export Z3 TIMEOUT MEMCAP_KB LOGIC

echo "key,verdict,seconds" > "$OUT"
xargs -a "$LIST" -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {} >> "$OUT"
rm -f "$LIST"

DONE="$(($(wc -l < "$OUT") - 1))"
echo "=== node $NODE 完成: $DONE 条 -> $OUT ==="
echo "verdict 统计:"
tail -n +2 "$OUT" | cut -d, -f2 | sort | uniq -c
