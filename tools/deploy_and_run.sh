#!/bin/bash
# ============================================================================
# NLColver 极简部署脚本
#
# 默认目录结构（上传后保持这样）：
#   部署目录/
#   ├── nlcolver-dist/          <- 本脚本 + binary + Python 工具
#   │   ├── bin/nlcolver
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
#   ./nlcolver-dist/tools/deploy_and_run.sh build
#   ./nlcolver-dist/tools/deploy_and_run.sh run "lia,nia" -j 200 -t 100
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DIST_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
BIN="${DIST_DIR}/bin/nlcolver"

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
        -DNLCOLVER_STATIC_BUILD=ON \
        -DNLCOLVER_ENABLE_CASESTATS=ON \
        -DNLCOLVER_BUILD_TESTS=OFF

    cmake --build . -j$(nproc)
    cd ..

    BIN_BUILT="$(pwd)/build_static/bin/nlcolver"
    [[ -f "$BIN_BUILT" ]] || err "Binary 未生成"
    file "$BIN_BUILT" | grep -q "statically linked" || err "不是静态链接"

    mkdir -p "${DIST_DIR}/bin"
    cp "$BIN_BUILT" "${DIST_DIR}/bin/nlcolver"
    log "编译完成: ${DIST_DIR}/bin/nlcolver ($(du -h ${DIST_DIR}/bin/nlcolver | cut -f1))"
}

# ---------------------------------------------------------------------------
# package: 把 nlcolver-dist/ 打包成 tar.gz，方便上传
# ---------------------------------------------------------------------------
cmd_package() {
    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build。"

    PKG="$(pwd)/nlcolver-dist.tar.gz"
    log "打包: ${BIN} + tools/ -> ${PKG}"

    TMPDIR=$(mktemp -d)
    trap "rm -rf ${TMPDIR}" EXIT

    mkdir -p "${TMPDIR}/nlcolver-dist/bin"
    cp "$BIN" "${TMPDIR}/nlcolver-dist/bin/nlcolver"
    chmod +x "${TMPDIR}/nlcolver-dist/bin/nlcolver"

    mkdir -p "${TMPDIR}/nlcolver-dist/tools"
    cp "${SCRIPT_DIR}/deploy_and_run.sh" "${TMPDIR}/nlcolver-dist/tools/"
    cp "${SCRIPT_DIR}/run_benchmark.py" "${TMPDIR}/nlcolver-dist/tools/"
    cp "${SCRIPT_DIR}/analyze_benchmark.py" "${TMPDIR}/nlcolver-dist/tools/"

    tar czf "$PKG" -C "$TMPDIR" nlcolver-dist

    log "打包完成: ${PKG} ($(du -h ${PKG} | cut -f1))"
    log "上传命令示例: scp ${PKG} user@server:/data/"
}

# ---------------------------------------------------------------------------
# run: 本地后台运行 benchmark
#   第一个非选项参数是 logic，其余透传给 run_benchmark.py
# ---------------------------------------------------------------------------
cmd_run() {
    shift  # 去掉 "run"

    [[ -f "$BIN" ]] || err "找不到 binary: $BIN。请先 build，或把 nlcolver-dist 目录放完整。"
    [[ $# -gt 0 ]] || err "请指定逻辑，例如: ./nlcolver-dist/tools/deploy_and_run.sh run lia,nia"

    LOGIC="$1"
    shift

    # 默认 benchmark 路径: ./benchmark/non-incremental
    BENCH_DIR="$(pwd)/benchmark/non-incremental"
    if [[ ! -d "$BENCH_DIR" ]]; then
        warn "默认 benchmark 路径不存在: $BENCH_DIR"
        warn "请确保目录结构如下:"
        warn "  当前目录/"
        warn "  ├── nlcolver-dist/"
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
    *)
        cat << 'EOF'
NLColver 极简部署脚本

默认目录结构:
  部署目录/
  ├── nlcolver-dist/          <- 本脚本 + binary + 工具
  │   ├── bin/nlcolver
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
  ./nlcolver-dist/tools/deploy_and_run.sh build
    编译静态 binary（在源码仓库里执行，产出到 nlcolver-dist/bin/）

  ./nlcolver-dist/tools/deploy_and_run.sh run <logic> [选项...]
    后台运行 benchmark（nohup，终端断开不停止）

    示例:
      ./nlcolver-dist/tools/deploy_and_run.sh run lia,nia
      ./nlcolver-dist/tools/deploy_and_run.sh run lia,nia,lra,nra -j 200 -t 100
      ./nlcolver-dist/tools/deploy_and_run.sh run all -j 256 -t 100 --compare-with z3

    常用选项（透传给 run_benchmark.py）:
      -j N         并行数
      -t SEC       超时秒数
      --max-files N   每个 logic 最多 N 个 case
      --compare-with z3/cvc5  交叉验证
EOF
        exit 1
        ;;
esac
