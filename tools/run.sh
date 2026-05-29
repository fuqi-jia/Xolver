#!/usr/bin/env bash
# =============================================================================
# run.sh — 一键差分。每台 panda 只需输入它的编号即可:
#
#     ./run.sh 1            # 前台跑(看进度)
#     nohup ./run.sh 1 &    # 后台跑(断开终端也不停),日志进 nohup.out
#
# 它会:在该 panda 分到的 division 上,把 Xolver 跑两遍 —— baseline(默认) +
# candidate(开全部已验证优化) —— 每个文件再用 z3 当裁判,写 diff_<LOGIC>_node<编号>.csv,
# 并打印小结(baseline解出 / candidate解出 / 新增recovery / 解错WRONG[必须=0])。z3 只跑这一遍。
#
# ---- panda 编号 -> 任务预设(并行数已按"线程数"设,不是核数)----------------------
#   1   QF_NIA  分片1/3                         -j220   (256线程)
#   2   QF_NIA  分片2/3                         -j220   (256线程)
#   10  QF_NIA  分片3/3                         -j220   (256线程)
#   8   QF_NRA  整份                             -j220   (256线程; 按要求不在8上跑NIA)
#   9   6个小提交division + QF_LIA + QF_LRA      -j72    (80线程)
#   14  基础理论 QF_UF + QF_AX + QF_DT (查bug)   -j64    (72线程)
#   (提交的8个: NIA NRA NIRA UFNIA UFNRA ANIA AUFNIA UFDTNIA;
#    9号顺序跑 NIRA/AUFNIA/UFNRA/UFDTNIA/ANIA/UFNIA 这6个小的,再跑 LIA/LRA)
#
# ---- 可用环境变量覆盖 --------------------------------------------------------
#   TIMEOUT   每文件墙钟超时秒数(默认 20;想多覆盖就调到 15,想跑深就调大)
#   XOLVER    xolver 二进制路径(默认自动找 xolver-dist/bin/xolver)
#   Z3        z3 路径(默认走 PATH 里的 z3)
#   BENCH     benchmark/non-incremental 目录(默认自动找,含 /pub/data/jiafq/... 服务器路径)
#   JOBS      覆盖该预设的并行数
# =============================================================================
set -u
P="${1:?用法: ./run.sh <panda编号>   可用编号: 1 2 8 9 10 14}"
TIMEOUT="${TIMEOUT:-20}"
MEMCAP_KB="${MEMCAP_KB:-16000000}"      # 每进程虚拟内存上限 ~16GB(防个别 case 跑飞)
HERE="$(cd "$(dirname "$0")" && pwd)"

# ---- 预设: 每条任务是 "LOGIC NODE NODES" (NODE/NODES 用于把一个 division 切片到多台) ----
case "$P" in
  1)  TASKS=("QF_NIA 1 3");                                  JOBS_DEF=220 ;;
  2)  TASKS=("QF_NIA 2 3");                                  JOBS_DEF=220 ;;
  10) TASKS=("QF_NIA 3 3");                                  JOBS_DEF=220 ;;
  8)  TASKS=("QF_NRA 1 1");                                  JOBS_DEF=220 ;;
  9)  TASKS=("QF_NIRA 1 1" "QF_AUFNIA 1 1" "QF_UFNRA 1 1" \
             "QF_UFDTNIA 1 1" "QF_ANIA 1 1" "QF_UFNIA 1 1" \
             "QF_LIA 1 1" "QF_LRA 1 1");                     JOBS_DEF=72 ;;
  14) TASKS=("QF_UF 1 1" "QF_AX 1 1" "QF_DT 1 1");           JOBS_DEF=64 ;;
  *)  echo "未知 panda 编号: '$P' (可用: 1 2 8 9 10 14)"; exit 1 ;;
esac
JOBS="${JOBS:-$JOBS_DEF}"

# ---- 找 xolver 二进制 ----
if [ -z "${XOLVER:-}" ]; then
  for c in ./xolver-dist/bin/xolver ./bin/xolver ./xolver \
           "$HERE"/xolver-dist/bin/xolver "$HERE"/bin/xolver \
           "$HERE"/../bin/xolver "$HERE"/../xolver-dist/bin/xolver; do
    [ -x "$c" ] && { XOLVER="$(cd "$(dirname "$c")" && pwd)/$(basename "$c")"; break; }
  done
fi
XOLVER="${XOLVER:-./xolver-dist/bin/xolver}"
Z3="${Z3:-z3}"
[ -x "$XOLVER" ] || { echo "ERROR: 找不到可执行 xolver: '$XOLVER' (用 XOLVER=/路径 覆盖)"; exit 1; }
command -v "$Z3" >/dev/null 2>&1 || { echo "ERROR: z3 不在 PATH (用 Z3=/路径 覆盖)"; exit 1; }

# ---- 找 benchmark 目录(服务器上通常已在 /pub/data/jiafq/...)----
if [ -z "${BENCH:-}" ]; then
  for c in /pub/data/jiafq/smt-comp-2025/benchmark/non-incremental \
           ./benchmark/non-incremental "$HERE"/../benchmark/non-incremental \
           "$HERE"/benchmark/non-incremental; do
    [ -d "$c" ] && { BENCH="$(cd "$c" && pwd)"; break; }
  done
fi
[ -d "${BENCH:-/nonexistent}" ] || { echo "ERROR: 找不到 benchmark/non-incremental (用 BENCH=/路径 覆盖)"; exit 1; }

# ---- candidate = integration 已验证的 --allon 集(显式不开 COMB_ARRAY_NIA / IFACE_LIFECYCLE)----
CANDFLAGS="XOLVER_NIA_MODULAR=1 XOLVER_NIA_LOCALSEARCH=1 XOLVER_NIA_PRESOLVE_FULL=1 \
XOLVER_NIA_UNIVARIATE_FULL=1 XOLVER_NIA_BITBLAST_FAST=1 XOLVER_NIA_BV_CASCADE=1 \
XOLVER_NIA_NORM_CACHE=1 XOLVER_NIA_GCD=1 XOLVER_NIA_ICP=1 XOLVER_NIA_REFUTE=1 \
XOLVER_NIA_CDCAC=1 XOLVER_NIA_EAGER_BITBLAST=1 \
XOLVER_NRA_CAC=1 XOLVER_NRA_SUBTROPICAL=1 XOLVER_NRA_SIGN_REFUTE=1 XOLVER_NRA_HYBRID=1 \
XOLVER_NRA_UNSAT_CERT=1 XOLVER_NRA_CAC_DEADLINE_MS=2000 XOLVER_NRA_CAC_TRUST_UNSAT=1 \
XOLVER_ARRAY_CONGR_EXT=1 XOLVER_EUF_PROP=1 XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 \
XOLVER_REAL_DIV_PURIFY=1 XOLVER_PRESOLVE_DEDUP_ROWS=1 XOLVER_PRESOLVE_IIS=1"

verdict() {
  local out rc
  out="$( ulimit -v "$MEMCAP_KB" 2>/dev/null; timeout "$TIMEOUT" "$@" 2>/dev/null )"; rc=$?
  [ "$rc" -eq 124 ] && { echo timeout; return; }
  local v; v="$(printf '%s' "$out" | grep -Eoim1 'unsat|unknown|sat')"
  echo "${v:-error}"
}
run_one() {
  local f="$1" key
  key="$LOGIC/${f##*$LOGIC/}"
  printf '%s,%s,%s,%s\n' "$key" \
    "$(verdict "$XOLVER" solve "$f")" \
    "$(verdict env $CANDFLAGS "$XOLVER" solve "$f")" \
    "$(verdict "$Z3" "$f")"
}
export -f run_one verdict
export XOLVER Z3 TIMEOUT MEMCAP_KB CANDFLAGS

echo "xolver=$XOLVER   z3=$Z3   bench=$BENCH"
echo "panda$P   并行=$JOBS   超时=${TIMEOUT}s   任务: ${TASKS[*]}"
echo "=============================================================="

for t in "${TASKS[@]}"; do
  set -- $t; LOGIC="$1"; NODE="$2"; NODES="$3"; export LOGIC
  [ -d "$BENCH/$LOGIC" ] || { echo "[$LOGIC] 跳过(目录不存在)"; continue; }
  OUT="diff_${LOGIC}_node${P}.csv"
  LIST="$(mktemp)"
  find "$BENCH/$LOGIC" -name '*.smt2' | LC_ALL=C sort | awk -v N="$NODES" -v i="$NODE" 'NR % N == (i-1)' > "$LIST"
  TOTAL="$(wc -l < "$LIST")"
  echo ">>> $LOGIC  切片 $NODE/$NODES  文件 $TOTAL  -> $OUT"
  [ "$TOTAL" -gt 0 ] || { echo "    (0 文件,跳过)"; rm -f "$LIST"; continue; }
  echo "key,baseline,candidate,oracle" > "$OUT"
  xargs -a "$LIST" -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {} >> "$OUT"
  rm -f "$LIST"
  awk -F, 'NR>1{
    if($2=="sat"||$2=="unsat") bs++;
    if($3=="sat"||$3=="unsat") cs++;
    if(($3=="sat"||$3=="unsat") && !($2=="sat"||$2=="unsat")) rec++;
    if(($3=="sat"||$3=="unsat") && ($4=="sat"||$4=="unsat") && $3!=$4){ w++; print "    WRONG: "$1" (xolver="$3" z3="$4")" > "/dev/stderr" }
  } END{ printf "    [%s] baseline=%d  candidate=%d  recovery=%d  解错=%d\n", L, bs+0, cs+0, rec+0, w+0 }' L="$LOGIC" "$OUT"
done
echo "=============================================================="
echo "panda$P 完成。CSV: diff_*_node${P}.csv  (把它们拷回来给 E 打分)"
