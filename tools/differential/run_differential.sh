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
# 自动找 xolver 二进制(本地打包→上传解压的常见位置;也可 XOLVER=/路径 覆盖)
if [ -z "${XOLVER:-}" ]; then
  for c in "$HERE/bin/xolver" "$HERE/xolver" "$HERE/../bin/xolver" \
           ./bin/xolver ./xolver ./xolver-dist/bin/xolver "$HERE"/xolver-dist/bin/xolver \
           "$HERE"/*-dist/bin/xolver ./*-dist/bin/xolver "$HERE/../build_static/bin/xolver"; do
    [ -x "$c" ] && { XOLVER="$c"; break; }
  done
fi
XOLVER="${XOLVER:-./bin/xolver}"
Z3="${Z3:-z3}"
CVC5="${CVC5:-cvc5}"

# candidate = integration 5f909e6 合并后已验证的 --allon 优化集。跨 logic 的开关是无害空操作。
# 两类显式排除:
#   XOLVER_COMB_ARRAY_NIA   —— QF_ANIA 路由会卡在 ArrayReasoner 急合并(NIA gdb 定位),开了直接 timeout;
#                              等 EQNA 修好 array eager-merge + backtrack-sync 再开。
#   XOLVER_NIA_IFACE_LIFECYCLE —— prerequisite,单独开是延迟成本无收益(需配 Track 3),本轮 default-OFF。
# 已删除的旧名: DIVISOR_FACTOR(并入默认素因子分解)、NRA_LAZARD_LIFT/PREELIM/LINEARIZE(未进 NRA 验证集,Lazard 由 HYBRID 覆盖)。
# 2026-05-31 flag-cleanup-final: 17 promoted flag 已源码删 getenv,这里同步撤掉。
# 3 reverted flag(PRESOLVE_FULL / SYMBOLIC_DIVMOD_NONZERO / UNSAT_CERT)也不进 CANDFLAGS —
# 它们已知会引入 false-UNSAT/hang(本地 gate 抓到的完备性退步),放 candidate arm 只会污染数据。
# CANDFLAGS 现在只测 7 个真正还有未知答案的 flag:6 个 KEEP-gated 实验 + 1 numeric tunable。
# 2026-05-31 5min bisection: XOLVER_NIA_EAGER_BITBLAST removed (—222 MathProblems STC_* regression).
# 2026-06-01 QF_LIA -502 two-culprit bisection (lia-lra-deep + preprocess-deep co-investigation):
#   - XOLVER_LIA_CUTS + XOLVER_LIA_GMI_CUTS removed: 399 SAT regressors (Bromberger/CAV/dillig/slacks).
#   - XOLVER_PP_SOLVE_EQS_GAUSS removed: 103 UNSAT regressors (SMPT/nec) → preprocess-deep guard.
# 2026-06-01 PM CRISIS — 8-flag batch showed -9085 QF_NIA collateral loss.
#   ROOT CAUSE: lia-lra-deep bisection was single-division (QF_LIA only); GAUSS removal also tanked
#   QF_NIA by +9000+ cases (GAUSS ±1-pivot linear elim simplifies NIA-linear-able sub-portions).
#   FIX: restore GAUSS to CANDFLAGS (preprocess-deep guard 14c4410+858b4aa now protects -103 UNSAT
#   while keeping +9000 NIA + +22 convert). Net catalog = +8918+ (vastly different from -81 single-div).
#   CUTS+GMI staying out (real SAT regression on QF_LIA, no NIA collateral observed).
# 2026-06-01 PM DT REGRESSION — XOLVER_DT_VALIDATOR_STRICT at 5min wall floors 2693 sat→unknown
#   (20s EQNA analysis showed 55:1 ratio; 5min scale broke that). REMOVED from CANDFLAGS until
#   EQNA root-causes the 5min over-floor (likely model-build-completeness at higher timeouts).
# 2026-06-01 evening update:
# - PP_SOLVE_EQS_GAUSS attribution correction (preprocess source-verified): GAUSS-general gated
#   out for NIA/NRA/NIRA. The +9000 QF_NIA collateral comes from LIA_CUTS or LIA_GMI_CUTS via
#   theory combination, NOT GAUSS-general. Restoring all 3 to recover +9000.
# - lia-lra-deep P4 SHIPPED (fde9917 XOLVER_LRA_INCREMENTAL_BETA): 2.5x wall / 7x per-check on
#   nec-smt theory throughput; nec-smt 8/12 -> 12/12 at 60s. CANDFLAGS pair with LIA_INCREMENTAL.
# - DT_VALIDATOR_STRICT staying out (EQNA emergency root-cause pending).
CANDFLAGS="XOLVER_EUF_PROP=1 XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 \
XOLVER_ARRAY_CONGR_EXT=1 XOLVER_NRA_LOCALSEARCH=1 \
XOLVER_PP_SOLVE_EQS=1 XOLVER_PP_SOLVE_EQS_GAUSS=1 \
XOLVER_LIA_CUTS=1 XOLVER_LIA_GMI_CUTS=1 \
XOLVER_LIA_INCREMENTAL=1 XOLVER_LRA_INCREMENTAL_BETA=1 \
XOLVER_NRA_CAC_DEADLINE_MS=2000"

[ -x "$XOLVER" ] || { echo "ERROR: 找不到可执行的 xolver: '$XOLVER' (用 XOLVER=/路径 覆盖)"; exit 1; }
command -v "$Z3" >/dev/null 2>&1 || { echo "ERROR: z3 不在 PATH (用 Z3=/路径 覆盖)"; exit 1; }
# Hole 1: datatype 风味 logic 用 cvc5 当裁判
case "$LOGIC" in QF_DT|QF_UFDTNIA)
  command -v "$CVC5" >/dev/null 2>&1 || { echo "ERROR: $LOGIC 需要 cvc5 当裁判 (用 CVC5=/路径 覆盖)"; exit 1; } ;;
esac

# 共享底座
. "$HERE/diff_common.sh"
RUN_TS="${RUN_TS:-$(date -u +%Y-%m-%dT%H:%M:%SZ)}"
if [ -z "${GIT_TIP:-}" ]; then
  GIT_TIP="${XOLVER_GIT_TIP:-$(git -C "$HERE/.." rev-parse --short HEAD 2>/dev/null || echo unknown)}"
fi
PANDA_NODE="$NODE"
STAMP="$(printf '%s' "$RUN_TS" | tr -cd '0-9TZ')"
oracle_for_logic "$LOGIC"

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

export -f verdict_timed oracle_for_logic _oracle_verdict run_one_rich
export XOLVER Z3 CVC5 TIMEOUT MEMCAP_KB LOGIC CANDFLAGS \
       RUN_TS GIT_TIP PANDA_NODE ORACLE_NAME ORACLE_BIN ORACLE_TLIMIT_MS

echo "oracle = $ORACLE_NAME   git = $GIT_TIP   ts = $RUN_TS"
printf '%s\n' "$RICH_HEADER" > "$OUT"
xargs -a "$LIST" -P "$JOBS" -I{} bash -c 'run_one_rich "$@"' _ {} >> "$OUT"
rm -f "$LIST"

echo "=== node $NODE 完成 -> $OUT ==="
emit_node_sqlite "panda${NODE}_${STAMP}.sqlite" "panda${NODE}_${STAMP}.csv" "$OUT"
awk -F, 'NR>1{
  gsub(/"/,"");
  dv=$6; av=$8; ov=$11;
  bdec=(dv=="sat"||dv=="unsat"); cdec=(av=="sat"||av=="unsat"); odec=(ov=="sat"||ov=="unsat");
  if(bdec) bs++; if(cdec) cs++; if(cdec && !bdec) rec++;
  if(odec && ((bdec&&dv!=ov)||(cdec&&av!=ov))){ wrong++; print "  WRONG: "$1" (def="dv" allon="av" "$10"="ov")" > "/dev/stderr" }
}
END{
  printf "baseline 解出: %d\n", bs;
  printf "candidate 解出(开全优化): %d\n", cs;
  printf "新增解出(recovery): %d\n", rec;
  printf "解错(都确定却不一致, 必须=0): %d\n", (wrong+0);
}' "$OUT"
