#!/bin/bash
# ============================================================================
# Xolver 极简部署脚本
#
# 默认目录结构（上传后保持这样）：
#   部署目录/
#   ├── xolver-dist/          <- 本脚本 + binary + Python 工具
#   │   ├── bin/xolver
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
#   ./xolver-dist/tools/deploy_and_run.sh build
#   ./xolver-dist/tools/deploy_and_run.sh run "lia,nia" -j 200 -t 100
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DIST_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BIN="${DIST_DIR}/bin/xolver"

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
        -DXOLVER_STATIC_BUILD=ON \
        -DXOLVER_ENABLE_CASESTATS=ON \
        -DXOLVER_BUILD_TESTS=OFF

    cmake --build . -j$(nproc)
    cd ..

    BIN_BUILT="$(pwd)/build_static/bin/xolver"
    [[ -f "$BIN_BUILT" ]] || err "Binary 未生成"
    file "$BIN_BUILT" | grep -q "statically linked" || err "不是静态链接"

    mkdir -p "${DIST_DIR}/bin"
    cp "$BIN_BUILT" "${DIST_DIR}/bin/xolver"
    log "编译完成: ${DIST_DIR}/bin/xolver ($(du -h ${DIST_DIR}/bin/xolver | cut -f1))"

    # scrambler (SMT-COMP) — 静态编译 + 复制，供 --scramble / SCRAMBLE=1 使用（竞赛会 scramble 输入）
    if [[ -d "${DIST_DIR}/tools/scrambler" ]]; then
        ( cd "${DIST_DIR}/tools/scrambler" && make >/dev/null 2>&1 && \
          g++ -D_GLIBCXX_USE_CXX11_ABI=0 -std=c++11 -static -O3 scrambler.o parser.o lexer.o -o scrambler 2>/dev/null ) || warn "scrambler 编译失败"
        if [[ -f "${DIST_DIR}/tools/scrambler/scrambler" ]]; then
            cp "${DIST_DIR}/tools/scrambler/scrambler" "${DIST_DIR}/bin/scrambler"
            log "scrambler: ${DIST_DIR}/bin/scrambler ($(file "${DIST_DIR}/bin/scrambler" | grep -o 'statically linked' || echo dynamic))"
        fi
    else
        warn "tools/scrambler 缺失，--scramble 不可用 (git clone https://github.com/SMT-COMP/scrambler.git tools/scrambler)"
    fi
}

# ---------------------------------------------------------------------------
# package: 把 xolver-dist/ 打包成 tar.gz，方便上传
# ---------------------------------------------------------------------------
cmd_package() {
    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build。"

    PKG="$(pwd)/xolver-dist.tar.gz"
    log "打包: ${BIN} + tools/ -> ${PKG}"

    TMPDIR=$(mktemp -d)
    trap "rm -rf ${TMPDIR}" EXIT

    mkdir -p "${TMPDIR}/xolver-dist/bin"
    cp "$BIN" "${TMPDIR}/xolver-dist/bin/xolver"
    chmod +x "${TMPDIR}/xolver-dist/bin/xolver"

    # scrambler (for --scramble / SCRAMBLE=1)
    if [[ -f "${DIST_DIR}/bin/scrambler" ]]; then
        cp "${DIST_DIR}/bin/scrambler" "${TMPDIR}/xolver-dist/bin/scrambler"
        chmod +x "${TMPDIR}/xolver-dist/bin/scrambler"
    else
        warn "未找到 ${DIST_DIR}/bin/scrambler（先 build），打包不含 scrambler"
    fi

    mkdir -p "${TMPDIR}/xolver-dist/tools"
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
            cp "$src" "${TMPDIR}/xolver-dist/tools/"
        fi
    done

    tar czf "$PKG" -C "$TMPDIR" xolver-dist

    log "打包完成: ${PKG} ($(du -h ${PKG} | cut -f1))"
    log "上传命令示例: scp ${PKG} user@server:/data/"
}

# ---------------------------------------------------------------------------
# run: 本地后台运行 benchmark
#   第一个非选项参数是 logic，其余透传给 run_benchmark.py
# ---------------------------------------------------------------------------
cmd_run() {
    shift  # 去掉 "run"

    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build，或把 xolver-dist 目录放完整。"
    [[ $# -gt 0 ]] || err "请指定逻辑，例如: ./xolver-dist/tools/deploy_and_run.sh run lia,nia"

    LOGIC="$1"
    shift

    # 解析 deploy_and_run 自己的开关（--both / --allon / --scramble / --scramble-seed N），
    # 其余参数透传给 run_benchmark.py。也兼容旧环境变量 (BOTH=1 / ALLON=1 / SCRAMBLE=1 / SCRAMBLE_SEED=n)。
    DO_BOTH=0;     [[ "${BOTH:-}"     == "1" ]] && DO_BOTH=1
    DO_ALLON=0;    [[ "${ALLON:-}"    == "1" ]] && DO_ALLON=1
    DO_SUBMIT=0;   [[ "${SUBMIT:-}"   == "1" ]] && DO_SUBMIT=1
    DO_SCRAMBLE=0; [[ "${SCRAMBLE:-}" == "1" ]] && DO_SCRAMBLE=1
    PASS_ARGS=()
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --both)          DO_BOTH=1; shift ;;
            --allon)         DO_ALLON=1; shift ;;
            --submit)        DO_SUBMIT=1; shift ;;
            --scramble)      DO_SCRAMBLE=1; shift ;;
            --scramble-seed) SCRAMBLE_SEED="$2"; shift 2 ;;
            *)               PASS_ARGS+=("$1"); shift ;;
        esac
    done
    set -- ${PASS_ARGS[@]+"${PASS_ARGS[@]}"}

    # --scramble 且未指定 seed：生成随机种子一次并 export（竞赛风格，每次不同；--both 的 OFF/ON
    # 两遍共享同一 scrambled 输入 -> oracle-cache 命中。想复现某次运行就传 --scramble-seed n）。
    if [[ "$DO_SCRAMBLE" == "1" && -z "${SCRAMBLE_SEED:-}" ]]; then
        export SCRAMBLE_SEED=$(( (RANDOM * 32768) + RANDOM + 1 ))
        log "scramble seed 未指定 -> 本次随机种子 $SCRAMBLE_SEED"
    fi

    # --both: 一条命令后台顺序跑 OFF 然后 ON；z3 oracle 仅跑一遍（共享 --oracle-cache）。
    # ON 默认 = --allon (bug-hunt, floors off)；若同时传 --submit，则 ON = --submit
    # (submission config, floors on → solved-count 是 CORRECT 计数, 适合按效果裁剪 flag)。
    if [[ "$DO_BOTH" == "1" ]]; then
        SELF="$(cd "$(dirname "$0")" && pwd)/$(basename "$0")"
        TAG="${LOGIC//,/_}"
        mkdir -p "$(pwd)/results"
        CACHE="$(pwd)/results/oracle-${TAG}.json"
        SEQLOG="$(pwd)/both-${TAG}-seq.log"
        SCRF=""; [[ "$DO_SCRAMBLE" == "1" ]] && SCRF="--scramble"
        ONFLAG="--allon"; [[ "$DO_SUBMIT" == "1" ]] && ONFLAG="--submit"
        log "--both: 后台顺序 OFF -> ON($ONFLAG), z3 oracle 仅跑一遍 ($CACHE)"
        log "  序列日志: $SEQLOG"
        nohup bash -c "unset BOTH ALLON SUBMIT SCRAMBLE; rm -f '$CACHE'; FG=1 '$SELF' run '$LOGIC' ${PASS_ARGS[*]} $SCRF --oracle-cache '$CACHE'; FG=1 '$SELF' run '$LOGIC' ${PASS_ARGS[*]} $SCRF $ONFLAG --oracle-cache '$CACHE'" > "$SEQLOG" 2>&1 &
        log "  PID=$!   查看: tail -f $SEQLOG"
        return 0
    fi

    # --allon: bug-hunt 预设 — 开所有优化开关，但关掉 soundness FLOORS
    # (COMB_SAT_FLOOR / PP_STRICT_VALIDATION / PP_VALIDATE_NONLINEAR_SAT /
    #  SAT_DEFER_EARLY_CONFLICT / NRA_UNSAT_CERT)，让假答案以 xolver!=z3 暴露。配合 --compare-with z3。
    if [[ "$DO_ALLON" == "1" ]]; then
        export XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 \
               XOLVER_COMB_SCALAR_BACKFILL=1 XOLVER_COMB_UFARG_ARRANGE=1 \
               XOLVER_LIA_CUTS=1 XOLVER_LIA_REPAIR=1 \
               XOLVER_LRA_BOUND_AXIOMS=1 XOLVER_LRA_PIVOT_HEUR=1 XOLVER_LRA_PROP=1 \
               XOLVER_NIA_REFUTE=1 XOLVER_NIA_GCD=1 XOLVER_NIA_ICP=1 \
               XOLVER_NIA_CDCAC=1 XOLVER_NIA_BV_CASCADE=1 \
               XOLVER_NRA_LAZARD_LIFT=1 XOLVER_NRA_LIBPOLY_PSC=1 \
               XOLVER_NRA_VARORDER=1 XOLVER_NRA_VARORDER_SIMPLEX=1 \
               XOLVER_NRA_HYBRID=1 XOLVER_NRA_PREELIM=1 XOLVER_NRA_LINEARIZE=1 \
               XOLVER_NRA_SUBTROPICAL=1 XOLVER_NRA_SIGN_REFUTE=1 \
               XOLVER_PP_REWRITE=1 XOLVER_PP_SOLVE_EQS=1 \
               XOLVER_PP_PG_CNF=1 XOLVER_PP_LET_ELIM=1 \
               XOLVER_SAT_LEMMA_MGMT=1 XOLVER_SAT_MIN=1 XOLVER_STRAT_PRESETS=1 \
               XOLVER_UF_DISEQ_WATCH=1 XOLVER_UF_FAST_CC=1
        log "--allon: optimizations ON (incl. NIA gcd/icp/cdcac/cascade + Lazard hybrid + NRA subtropical SAT-fast-path + PG-CNF/let-elim), soundness floors OFF (bug-hunt; false answers surface vs z3)"
    fi

    # --submit: SUBMISSION 预设 — 所有优化开关 + 全部 soundness FLOORS 都开 (= 实际参赛配置, 健全).
    # 用于参赛前 soundness 校验: 配合 --compare-with z3, xolver!=z3 (双方都确定) = 必须修的错误答案;
    # xolver=unknown 是健全的 (floor 兜底, 不算错). 与 --allon (floors off, 找 bug) 相反.
    # 注意: Lazard 混合 (XOLVER_NRA_HYBRID/PREELIM/LINEARIZE) 与 NRA subtropical SAT-fast-path
    # (XOLVER_NRA_SUBTROPICAL) 故意不在此预设里 — 它们尚未通过广 QF_NRA z3 差分 (default-path NRA
    # 改动的硬晋级门)。先在 --allon 里跑差分确认 0-unsound, 再提升进 --submit / 默认。subtropical 本身
    # 是 model-validate→else fall-through (invariant 1, 设计上健全), 但晋级前仍需广差分验证。
    if [[ "$DO_SUBMIT" == "1" ]]; then
        export XOLVER_COMB_CAREGRAPH=1 XOLVER_COMB_MODEL_BASED=1 \
               XOLVER_COMB_SCALAR_BACKFILL=1 XOLVER_COMB_UFARG_ARRANGE=1 \
               XOLVER_LIA_CUTS=1 XOLVER_LIA_REPAIR=1 \
               XOLVER_LRA_BOUND_AXIOMS=1 XOLVER_LRA_PIVOT_HEUR=1 XOLVER_LRA_PROP=1 \
               XOLVER_NIA_REFUTE=1 XOLVER_NIA_GCD=1 XOLVER_NIA_ICP=1 \
               XOLVER_NIA_CDCAC=1 XOLVER_NIA_BV_CASCADE=1 \
               XOLVER_NRA_LAZARD_LIFT=1 XOLVER_NRA_LIBPOLY_PSC=1 \
               XOLVER_NRA_VARORDER=1 XOLVER_NRA_VARORDER_SIMPLEX=1 \
               XOLVER_PP_REWRITE=1 XOLVER_PP_SOLVE_EQS=1 \
               XOLVER_PP_PG_CNF=1 XOLVER_PP_LET_ELIM=1 \
               XOLVER_SAT_LEMMA_MGMT=1 XOLVER_SAT_MIN=1 XOLVER_STRAT_PRESETS=1 \
               XOLVER_UF_DISEQ_WATCH=1 XOLVER_UF_FAST_CC=1 \
               XOLVER_PP_STRICT_VALIDATION=1 XOLVER_PP_VALIDATE_NONLINEAR_SAT=1 \
               XOLVER_SAT_DEFER_EARLY_CONFLICT=1 XOLVER_COMB_SAT_FLOOR=1 \
               XOLVER_NRA_UNSAT_CERT=1
        log "--submit: optimizations ON + soundness FLOORS ON (submission config; verify 0 wrong vs z3)"
    fi

    # --scramble: 用 SMT-COMP scrambler 扰动输入后再求解（solver 与 oracle 跑同一份 scrambled 文件）
    if [[ "$DO_SCRAMBLE" == "1" ]]; then
        SCR="${DIST_DIR}/bin/scrambler"
        [[ -f "$SCR" ]] || SCR="${DIST_DIR}/tools/scrambler/scrambler"
        set -- "$@" --scramble --scrambler "$SCR" --scramble-seed "$SCRAMBLE_SEED"
        log "--scramble: 输入经 scrambler 扰动 (seed $SCRAMBLE_SEED, $SCR)"
    fi

    # 默认 benchmark 路径: ./benchmark/non-incremental
    BENCH_DIR="$(pwd)/benchmark/non-incremental"
    if [[ ! -d "$BENCH_DIR" ]]; then
        warn "默认 benchmark 路径不存在: $BENCH_DIR"
        warn "请确保目录结构如下:"
        warn "  当前目录/"
        warn "  ├── xolver-dist/"
        warn "  └── benchmark/non-incremental/QF_*/"
    fi

    TIMESTAMP=$(date +%Y%m%d_%H%M%S)
    RUN_DIR="$(pwd)/results/run_${TIMESTAMP}"
    mkdir -p "$RUN_DIR"

    log "启动: logic=$LOGIC"
    log "binary: $BIN"
    log "benchmark: $BENCH_DIR"
    log "输出: $RUN_DIR"

    if [[ -n "${FG:-}" ]]; then
        # 前台模式 (FG=1)：阻塞至完成，便于把 OFF 与 ON 用 && 串成一条命令顺序运行
        log "前台运行 (FG=1, 阻塞至完成): $RUN_DIR/bench.log"
        python3 "${DIST_DIR}/tools/run_benchmark.py" \
            --solver "$BIN" \
            --logic "$LOGIC" \
            --benchmark-dir "$BENCH_DIR" \
            --dump-stats-dir "$RUN_DIR/stats" \
            --log-dir "$RUN_DIR/logs" \
            -o "$RUN_DIR" \
            "$@" \
            > "$RUN_DIR/bench.log" 2>&1
        rc=$?
        log "完成: $RUN_DIR (exit $rc)"
        return $rc
    fi

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
    OUT="$(pwd)/xolver-$(hostname)-$RUN_NAME.tar.gz"

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
Xolver 极简部署脚本

默认目录结构:
  部署目录/
  ├── xolver-dist/          <- 本脚本 + binary + 工具
  │   ├── bin/xolver
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
  ./xolver-dist/tools/deploy_and_run.sh build
    编译静态 binary（在源码仓库里执行，产出到 xolver-dist/bin/）

  ./xolver-dist/tools/deploy_and_run.sh run <logic> [选项...]
    后台运行 benchmark（nohup，终端断开不停止）

    示例:
      ./xolver-dist/tools/deploy_and_run.sh run lia,nia
      ./xolver-dist/tools/deploy_and_run.sh run nia -j 200 -t 30 --compare-with z3 --scramble --both

  ./xolver-dist/tools/deploy_and_run.sh pack
    打包最新 benchmark 结果到 ./xolver-<hostname>-<run>.tar.gz（当前目录）

    deploy_and_run 自己的开关:
      --both              一条命令后台顺序跑 OFF 再 ON；z3 oracle 仅跑一遍（共享缓存）
      --allon             开所有优化、关 soundness floors（bug-hunt，让假答案以 xolver!=z3 暴露）
      --scramble          先用 SMT-COMP scrambler 扰动输入再求解（solver 与 oracle 同一份）
      --scramble-seed N   指定 scramble 种子（默认每次随机，传 N 复现某次运行）
      （旧写法 BOTH=1 / ALLON=1 / SCRAMBLE=1 环境变量仍兼容）

    透传给 run_benchmark.py 的常用选项:
      -j N         并行数
      -t SEC       超时秒数
      --max-files N   每个 logic 最多 N 个 case
      --compare-with z3/cvc5  交叉验证
EOF
        exit 1
        ;;
esac
