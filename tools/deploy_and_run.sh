#!/bin/bash
# ============================================================================
# Zolver 极简部署脚本
#
# 默认目录结构（上传后保持这样）：
#   部署目录/
#   ├── zolver-dist/          <- 本脚本 + binary + Python 工具
#   │   ├── bin/zolver
#   │   └── tools/
#   │       ├── deploy_and_run.sh
#   │       ├── run_benchmark.py
#   │       └── analyze_benchmark.py
#   │
#   └── benchmark/              <- benchmark 数据集
#       └── non-incremental/
#           ├── QF_LIA/
#           ├── QF_NRA/
#           └── ...
#
# 用法（在"部署目录"下执行）：
#   ./zolver-dist/tools/deploy_and_run.sh build
#   ./zolver-dist/tools/deploy_and_run.sh run "lia,nia" -j 200 -t 100
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DIST_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BIN="${DIST_DIR}/bin/zolver"

GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

log()  { echo -e "${GREEN}[$(date +%H:%M:%S)]${NC} $*"; }
warn() { echo -e "${YELLOW}[$(date +%H:%M:%S)] WARNING${NC} $*"; }
err()  { echo -e "${RED}[$(date +%H:%M:%S)] ERROR${NC} $*"; exit 1; }

# ---------------------------------------------------------------------------
# build: 编译静态 binary（在源码仓库里执行，不是在部署目录）
# ---------------------------------------------------------------------------
cmd_build() {
    SRC_DIR="${DIST_DIR}"
    log "=== 编译静态 binary ==="
    cd "${SRC_DIR}"

    if [[ ! -f "third_party/cadical/configure" ]]; then
        log "初始化子模块..."
        git submodule update --init --recursive || warn "子模块初始化失败，继续尝试编译..."
    fi

    rm -rf build_static
    mkdir -p build_static
    cd build_static

    cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DZOLVER_STATIC_BUILD=ON \
        -DZOLVER_ENABLE_CASESTATS=ON \
        -DZOLVER_BUILD_TESTS=OFF

    cmake --build . -j$(nproc)
    cd ..

    BIN_BUILT="$(pwd)/build_static/bin/zolver"
    [[ -f "$BIN_BUILT" ]] || err "Binary 未生成"
    file "$BIN_BUILT" | grep -q "statically linked" || err "不是静态链接"

    mkdir -p "${DIST_DIR}/bin"
    cp "$BIN_BUILT" "${DIST_DIR}/bin/zolver"
    log "编译完成: ${DIST_DIR}/bin/zolver ($(du -h ${DIST_DIR}/bin/zolver | cut -f1))"
}

# ---------------------------------------------------------------------------
# package: 把 zolver-dist/ 打包成 tar.gz，方便上传
# ---------------------------------------------------------------------------
cmd_package() {
    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build。"

    PKG="$(pwd)/zolver-dist.tar.gz"
    log "打包: ${BIN} + tools/ -> ${PKG}"

    TMPDIR=$(mktemp -d)
    trap "rm -rf ${TMPDIR}" EXIT

    mkdir -p "${TMPDIR}/zolver-dist/bin"
    cp "$BIN" "${TMPDIR}/zolver-dist/bin/zolver"
    chmod +x "${TMPDIR}/zolver-dist/bin/zolver"

    mkdir -p "${TMPDIR}/zolver-dist/tools"
    for script in \
        deploy_and_run.sh \
        run_benchmark.py \
        analyze_benchmark.py \
        compare_benchmarks.py \
        bench_server.py \
        freeze_baseline.py \
        lia_mismatch_replay.py \
        run_lia_ablation.sh; do
        src="${SCRIPT_DIR}/${script}"
        if [[ -f "$src" ]]; then
            cp "$src" "${TMPDIR}/zolver-dist/tools/"
        fi
    done

    tar czf "$PKG" -C "$TMPDIR" zolver-dist

    log "打包完成: ${PKG} ($(du -h ${PKG} | cut -f1))"
    log "上传命令示例: scp ${PKG} user@server:/data/"
}

# ---------------------------------------------------------------------------
# run: 本地后台运行 benchmark
#   第一个非选项参数是 logic，其余透传给 run_benchmark.py
# ---------------------------------------------------------------------------
cmd_run() {
    shift  # 去掉 "run"

    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build，或把 zolver-dist 目录放完整。"
    [[ $# -gt 0 ]] || err "请指定逻辑，例如: ./zolver-dist/tools/deploy_and_run.sh run lia,nia"

    LOGIC="$1"
    shift

    # ALLON=1: bug-hunt preset — enable every optimization flag, but leave the
    # soundness FLOORS off (COMB_SAT_FLOOR / PP_STRICT_VALIDATION /
    # PP_VALIDATE_NONLINEAR_SAT / SAT_DEFER_EARLY_CONFLICT / NRA_UNSAT_CERT).
    # Floors downgrade unconfirmed answers to 'unknown' and would HIDE bugs; off,
    # a wrong answer shows as a zolver!=z3 MISMATCH. Use with --compare-with z3.
    if [[ "${ALLON:-}" == "1" ]]; then
        export ZOLVER_COMB_CAREGRAPH=1 ZOLVER_COMB_MODEL_BASED=1 \
               ZOLVER_COMB_SCALAR_BACKFILL=1 ZOLVER_COMB_UFARG_ARRANGE=1 \
               ZOLVER_LIA_CUTS=1 ZOLVER_LIA_REPAIR=1 \
               ZOLVER_LRA_BOUND_AXIOMS=1 ZOLVER_LRA_PIVOT_HEUR=1 ZOLVER_LRA_PROP=1 \
               ZOLVER_NIA_REFUTE=1 \
               ZOLVER_NRA_LAZARD_LIFT=1 ZOLVER_NRA_LIBPOLY_PSC=1 \
               ZOLVER_NRA_VARORDER=1 ZOLVER_NRA_VARORDER_SIMPLEX=1 \
               ZOLVER_PP_REWRITE=1 ZOLVER_PP_SOLVE_EQS=1 \
               ZOLVER_SAT_LEMMA_MGMT=1 ZOLVER_SAT_MIN=1 ZOLVER_STRAT_PRESETS=1 \
               ZOLVER_UF_DISEQ_WATCH=1 ZOLVER_UF_FAST_CC=1
        log "ALLON=1: optimizations ON, soundness floors OFF (bug-hunt; false answers surface vs z3)"
    fi

    # 默认 benchmark 路径: ./benchmark/non-incremental
    BENCH_DIR="$(pwd)/benchmark/non-incremental"
    if [[ ! -d "$BENCH_DIR" ]]; then
        warn "默认 benchmark 路径不存在: $BENCH_DIR"
        warn "请确保目录结构如下:"
        warn "  当前目录/"
        warn "  ├── zolver-dist/"
        warn "  └── benchmark/non-incremental/QF_*/"
    fi

    TIMESTAMP=$(date +%Y%m%d_%H%M%S)
    RUN_DIR="$(pwd)/results/run_${TIMESTAMP}"
    mkdir -p "$RUN_DIR"

    log "启动: logic=$LOGIC"
    log "binary: $BIN"
    log "benchmark: $BENCH_DIR"
    log "输出: $RUN_DIR"

    nohup python3 "${DIST_DIR}/tools/run_benchmark.py" \
        --solver "$BIN" \
        --logic "$LOGIC" \
        --benchmark-dir "$BENCH_DIR" \
        --dump-stats-dir "$RUN_DIR/stats" \
        --log-dir "$RUN_DIR/logs" \
        -o "$RUN_DIR" \
        "$@" \
        > "$RUN_DIR/bench.log" 2>&1 &

    log "后台运行 PID=$!"
    log "查看日志: tail -f $RUN_DIR/bench.log"
    log ""
    log "其他常用命令:"
    log "  ps aux | grep run_benchmark      # 查看进程"
    log "  tail -f $RUN_DIR/bench.log       # 实时日志"
}

# ---------------------------------------------------------------------------
# pack: 打包最新 benchmark 结果
# ---------------------------------------------------------------------------
cmd_pack() {
    RESULTS_DIR="$(pwd)/results"
    [[ -d "$RESULTS_DIR" ]] || err "找不到 results 目录: $RESULTS_DIR"

    RUN_DIR=$(ls -d "$RESULTS_DIR"/run_* 2>/dev/null | sort | tail -1)
    [[ -n "$RUN_DIR" ]] || err "results 目录下没有 run_* 文件夹"

    RUN_NAME=$(basename "$RUN_DIR")
    OUT="$(pwd)/zolver-$(hostname)-$RUN_NAME.tar.gz"

    log "打包: $RUN_NAME -> $OUT"

    # 收集核心文件
    FILES=()
    [[ -f "$RUN_DIR/bench.log" ]] && FILES+=("$RUN_DIR/bench.log")

    for logic_dir in "$RUN_DIR"/QF_*; do
        [[ -d "$logic_dir" ]] || continue
        for f in results.csv summary.txt statistics.json discrepancies.txt errors.txt; do
            [[ -f "$logic_dir/$f" ]] && FILES+=("$logic_dir/$f")
        done
    done

    [[ ${#FILES[@]} -eq 0 ]] && err "$RUN_NAME 下没有找到结果文件"

    tar czf "$OUT" -C "$(dirname "$RUN_DIR")" $(for f in "${FILES[@]}"; do echo "${f#$RESULTS_DIR/}"; done)

    log "打包完成: $OUT ($(du -h "$OUT" | cut -f1))"
}

# ---------------------------------------------------------------------------
# 主入口
# ---------------------------------------------------------------------------
case "${1:-}" in
    build)
        cmd_build
        ;;
    package)
        cmd_package
        ;;
    run)
        cmd_run "$@"
        ;;
    pack)
        cmd_pack
        ;;
    *)
        cat << 'EOF'
Zolver 极简部署脚本

默认目录结构:
  部署目录/
  ├── zolver-dist/          <- 本脚本 + binary + 工具
  │   ├── bin/zolver
  │   └── tools/
  │       ├── deploy_and_run.sh
  │       ├── run_benchmark.py
  │       └── analyze_benchmark.py
  └── benchmark/              <- benchmark 数据集
      └── non-incremental/
          ├── QF_LIA/
          ├── QF_NRA/
          └── ...

用法:
  ./zolver-dist/tools/deploy_and_run.sh build
    编译静态 binary（在源码仓库里执行，产出到 zolver-dist/bin/）

  ./zolver-dist/tools/deploy_and_run.sh run <logic> [选项...]
    后台运行 benchmark（nohup，终端断开不停止）

    示例:
      ./zolver-dist/tools/deploy_and_run.sh run lia,nia
      ./zolver-dist/tools/deploy_and_run.sh run lia,nia,lra,nra -j 200 -t 100
      ./zolver-dist/tools/deploy_and_run.sh run all -j 256 -t 100 --compare-with z3

  ./zolver-dist/tools/deploy_and_run.sh pack
    打包最新 benchmark 结果到 ./zolver-<hostname>-<run>.tar.gz（当前目录）

    常用选项（透传给 run_benchmark.py）:
      -j N         并行数
      -t SEC       超时秒数
      --max-files N   每个 logic 最多 N 个 case
      --compare-with z3/cvc5  交叉验证
EOF
        exit 1
        ;;
esac
