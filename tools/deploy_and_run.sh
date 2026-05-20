#!/bin/bash
# ============================================================================
# NLColver 极简部署脚本
#
# 在哪里运行就在哪里跑。上传此脚本 + nlcolver binary 到服务器后直接执行。
#
# 用法:
#   ./deploy_and_run.sh build                    # 编译静态 binary
#   ./deploy_and_run.sh run "lia,nia" -j 128 -t 100
#   ./deploy_and_run.sh run "lia,nia,lra,nra" -j 256 -t 100 --compare-with z3
#   ./deploy_and_run.sh run all -j 128 -t 100    # 跑所有 logic
# ============================================================================

set -euo pipefail

# 自动探测 binary 路径（当前目录或 build_static/bin/）
if [[ -f "./nlcolver" ]]; then
    BIN="$(pwd)/nlcolver"
elif [[ -f "build_static/bin/nlcolver" ]]; then
    BIN="$(pwd)/build_static/bin/nlcolver"
else
    BIN=""
fi

GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

log()  { echo -e "${GREEN}[$(date +%H:%M:%S)]${NC} $*"; }
warn() { echo -e "${YELLOW}[$(date +%H:%M:%S)] WARNING${NC} $*"; }
err()  { echo -e "${RED}[$(date +%H:%M:%S)] ERROR${NC} $*"; exit 1; }

# ---------------------------------------------------------------------------
# build: 编译静态 binary
# ---------------------------------------------------------------------------
cmd_build() {
    log "=== 编译静态 binary ==="

    if [[ ! -f "third_party/cadical/configure" ]]; then
        log "初始化子模块..."
        git submodule update --init --recursive
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

    BIN="$(pwd)/build_static/bin/nlcolver"
    [[ -f "$BIN" ]] || err "Binary 未生成"
    file "$BIN" | grep -q "statically linked" || err "不是静态链接"
    log "编译完成: $BIN ($(du -h $BIN | cut -f1))"
}

# ---------------------------------------------------------------------------
# run: 本地后台运行 benchmark
#   第一个非选项参数是 logic，其余透传给 run_benchmark.py
# ---------------------------------------------------------------------------
cmd_run() {
    shift  # 去掉 "run"

    [[ -n "$BIN" && -f "$BIN" ]] || err "找不到 nlcolver binary。请先 ./deploy_and_run.sh build"
    [[ $# -gt 0 ]] || err "请指定逻辑，例如: ./deploy_and_run.sh run lia,nia"

    LOGIC="$1"
    shift

    TIMESTAMP=$(date +%Y%m%d_%H%M%S)
    RUN_DIR="run_${TIMESTAMP}"
    mkdir -p "$RUN_DIR"

    # 透传所有剩余参数给 run_benchmark.py
    EXTRA=("$@")

    log "启动: logic=$LOGIC"
    log "输出: $(pwd)/$RUN_DIR/"

    nohup python3 "$(dirname "$0")/run_benchmark.py" \
        --solver "$BIN" \
        --logic "$LOGIC" \
        --dump-stats-dir "$(pwd)/$RUN_DIR/stats" \
        --log-dir "$(pwd)/$RUN_DIR/logs" \
        -o "$(pwd)/$RUN_DIR" \
        "${EXTRA[@]}" \
        > "$(pwd)/$RUN_DIR/bench.log" 2>&1 &

    log "后台运行 PID=$!"
    log "查看日志: tail -f $(pwd)/$RUN_DIR/bench.log"
}

# ---------------------------------------------------------------------------
# 主入口
# ---------------------------------------------------------------------------
case "${1:-}" in
    build)
        cmd_build
        ;;
    run)
        cmd_run "$@"
        ;;
    *)
        cat << 'EOF'
NLColver 极简部署脚本 — 在哪里运行就在哪里跑

用法:
  ./deploy_and_run.sh build
    编译静态 binary（产出 build_static/bin/nlcolver）

  ./deploy_and_run.sh run <logic> [选项...]
    后台运行 benchmark（nohup，终端断开不停止）

    示例:
      ./deploy_and_run.sh run lia,nia
      ./deploy_and_run.sh run lia,nia,lra,nra -j 128 -t 100
      ./deploy_and_run.sh run all -j 256 -t 100
      ./deploy_and_run.sh run nia -j 128 -t 100 --compare-with z3
      ./deploy_and_run.sh run lra -j 64 -t 30 --max-files 50

    常用选项（透传给 run_benchmark.py）:
      -j N         并行数（默认 1）
      -t SEC       超时秒数（默认 30）
      --max-files N   每个 logic 最多跑 N 个文件
      --compare-with z3/cvc5  交叉验证
EOF
        exit 1
        ;;
esac
