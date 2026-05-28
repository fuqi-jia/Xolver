#!/usr/bin/env bash
# =============================================================================
# run_differential.sh — 跟 run_blan.sh 一样的用法。在一台服务器上,把 Xolver 在
# 某个 logic 的一份切片上跑两遍 —— baseline(原始) + candidate(开全部新优化) ——
# 每个文件再用 z3 当裁判,最后报告:多解了几个(recovery)、有没有解错(WRONG,必须=0)。
#
# 用法(每台空闲机一行,跟 BLAN 一样):
#   panda1:  ./run_differential.sh 1 3 127 QF_NIA
#   panda2:  ./run_differential.sh 2 3 127 QF_NIA
#   panda7:  ./run_differential.sh 3 3 127 QF_NIA
#   panda9:  ./run_differential.sh 1 1 80  QF_NRA
#   panda10: ./run_differential.sh 1 1 60  QF_UFNIA
#   argv: <第几台> <共几台> <并行数> <logic>
#
# 后台跑(关掉终端也不停):
#   nohup ./run_differential.sh 1 3 127 QF_NIA > d1.log 2>&1 &
#   看进度:  wc -l diff_QF_NIA_node1.csv
#
# 可用环境变量覆盖:  XOLVER=  Z3=  BENCH=  TIMEOUT=  MEMCAP_KB=  OUT=
# =============================================================================
set -u
NODE="${1:?用法: run_differential.sh <第几台> <共几台> <并行数> <logic>}"
NODES="${2:?共几台}"; JOBS="${3:?并行数}"; LOGIC="${4:?logic, 如 QF_NIA}"
TIMEOUT="${TIMEOUT:-24}"                 # 每个文件的墙钟超时(秒)
MEMCAP_KB="${MEMCAP_KB:-16000000}"       # 每个进程地址空间上限(~16GB,防跑飞)
HERE="$(cd "$(dirname "$0")" && pwd)"
XOLVER="${XOLVER:-$HERE/../build_static/bin/xolver}"   # 默认用 deploy_and_run.sh build 产物
Z3="${Z3:-z3}"

# candidate = 开全部新优化(= deploy_and_run.sh 的 --allon 优化集; 跨 logic 的开关是无害空操作)
CANDFLAGS="XOLVER_NIA_MODULAR=1 XOLVER_NIA_LOCALSEARCH=1 XOLVER_NIA_PRESOLVE_FULL=1 \
XOLVER_NIA_BITBLAST_FAST=1 XOLVER_NIA_DIVISOR_FACTOR=1 XOLVER_NIA_REFUTE=1 XOLVER_NIA_GCD=1 \
XOLVER_NIA_ICP=1 XOLVER_NIA_CDCAC=1 XOLVER_NIA_BV_CASCADE=1 XOLVER_NRA_SUBTROPICAL=1 \
XOLVER_NRA_SIGN_REFUTE=1 XOLVER_NRA_CAC=1 XOLVER_NRA_HYBRID=1 XOLVER_NRA_LAZARD_LIFT=1 \
XOLVER_NRA_PREELIM=1 XOLVER_NRA_LINEARIZE=1 XOLVER_COMB_ARRAY_NIA=1 XOLVER_REAL_DIV_PURIFY=1 \
XOLVER_PRESOLVE_DEDUP_ROWS=1 XOLVER_PRESOLVE_IIS=1 XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1"

[ -x "$XOLVER" ] || { echo "ERROR: 找不到可执行的 xolver: '$XOLVER' (用 XOLVER=/路径 覆盖)"; exit 1; }
command -v "$Z3" >/dev/null 2>&1 || { echo "ERROR: z3 不在 PATH (用 Z3=/路径 覆盖)"; exit 1; }

# 找 benchmark 目录
if [ -z "${BENCH:-}" ]; then
  for c in ./benchmark/non-incremental ../benchmark/non-incremental \
           /pub/data/jiafq/smt-comp-2025/benchmark/non-incremental; do
    [ -d "$c/$LOGIC" ] && { BENCH="$(readlink -f "$c")"; break; }
  done
fi
[ -d "${BENCH:-/nonexistent}/$LOGIC" ] || { echo "ERROR: 找不到 $LOGIC 目录 (用 BENCH=/路径/non-incremental 覆盖)"; exit 1; }

OUT="${OUT:-diff_${LOGIC}_node${NODE}.csv}"
LIST="$(mktemp)"
find "$BENCH/$LOGIC" -name '*.smt2' | LC_ALL=C sort | awk -v N="$NODES" -v i="$NODE" 'NR % N == (i-1)' > "$LIST"
TOTAL="$(wc -l < "$LIST")"
echo "xolver = $XOLVER"
echo "bench  = $BENCH/$LOGIC    本机切片: $NODE/$NODES    并行: $JOBS    超时: ${TIMEOUT}s    文件数: $TOTAL"
[ "$TOTAL" -gt 0 ] || { echo "ERROR: 本切片 0 个文件(检查 node/nodes)"; rm -f "$LIST"; exit 1; }

# 跑一条命令, 输出 sat/unsat/unknown/timeout/error
verdict() {
  local out rc
  out="$( ulimit -v "$MEMCAP_KB" 2>/dev/null; timeout "$TIMEOUT" "$@" 2>/dev/null )"; rc=$?
  [ "$rc" -eq 124 ] && { echo timeout; return; }
  local v; v="$(printf '%s' "$out" | grep -Eoim1 'unsat|unknown|sat')"
  echo "${v:-error}"
}
# 一个文件: baseline + candidate + z3 裁判 → 一行 CSV
run_one() {
  local f="$1" key
  key="$LOGIC/${f##*$LOGIC/}"
  printf '%s,%s,%s,%s\n' "$key" \
    "$(verdict "$XOLVER" solve "$f")" \
    "$(verdict env $CANDFLAGS "$XOLVER" solve "$f")" \
    "$(verdict "$Z3" "$f")"
}
export -f run_one verdict
export XOLVER Z3 TIMEOUT MEMCAP_KB LOGIC CANDFLAGS

echo "key,baseline,candidate,oracle" > "$OUT"
xargs -a "$LIST" -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {} >> "$OUT"
rm -f "$LIST"

echo "=== node $NODE 完成 -> $OUT ==="
awk -F, 'NR>1{
  if($2=="sat"||$2=="unsat") bs++;
  if($3=="sat"||$3=="unsat") cs++;
  if(($3=="sat"||$3=="unsat") && !($2=="sat"||$2=="unsat")) rec++;
  if(($3=="sat"||$3=="unsat") && ($4=="sat"||$4=="unsat") && $3!=$4){ wrong++; print "  WRONG: "$1" (xolver="$3" z3="$4")" > "/dev/stderr" }
}
END{
  printf "baseline 解出: %d\n", bs;
  printf "candidate 解出(开全优化): %d\n", cs;
  printf "新增解出(recovery): %d\n", rec;
  printf "解错(candidate vs z3 都确定却不一致, 必须=0): %d\n", (wrong+0);
}' "$OUT"
