#!/bin/bash
# deploy_one_panda.sh <panda_num>
# Kill prior, extract tarball, start xolver batch with NFS-shared z3/cvc5.
# SmartShard: caller exports TASKS_OVERRIDE + JOBS_OVERRIDE to override preset.
set -u
P="${1:?usage: $0 <panda_num>}"
DEPLOY_DIR="/pub/data/jiafq/xolver-runs"
TARBALL="$DEPLOY_DIR/xolver-dist.tar.gz"

[ -f "$TARBALL" ] || { echo "ERROR [$(hostname)]: $TARBALL not found"; exit 1; }
mkdir -p "$DEPLOY_DIR"

# 1. kill prior run + ALL orphaned child workers (xargs -P spawns survive pkill of parent)
pkill -u "$USER" -f "tools/run.sh"   2>/dev/null   # all run.sh (this panda only runs one batch)
pkill -u "$USER" -x  xolver          2>/dev/null   # orphan xolver workers
pkill -u "$USER" -x  z3              2>/dev/null   # orphan z3 workers
pkill -u "$USER" -x  cvc5            2>/dev/null   # orphan cvc5 workers (panda14)
sleep 2
# verify clean
RESIDUAL=$(pgrep -u "$USER" -x 'xolver|z3|cvc5' 2>/dev/null | wc -l)
if [ "$RESIDUAL" -gt 0 ]; then
    # 2nd round, harder
    pkill -9 -u "$USER" -x xolver 2>/dev/null
    pkill -9 -u "$USER" -x z3     2>/dev/null
    pkill -9 -u "$USER" -x cvc5   2>/dev/null
    sleep 1
fi

# 2. extract
cd "$DEPLOY_DIR" || exit 1
rm -rf xolver-dist
tar xzf "$TARBALL" || { echo "ERROR [$(hostname)]: extract failed"; exit 1; }
cd xolver-dist || exit 1

# 3. ENV: z3/cvc5 from NFS-shared ~/bin/  (all pandas same version)
#    Use `export` (not `env $ENV_ARGS …`) so values containing spaces — e.g.
#    TASKS_OVERRIDE="QF_LIA 1 1;QF_AX 1 1" — survive into the child shell
#    without word-splitting. The previous `env $ENV_ARGS` form unquoted-split
#    `TASKS_OVERRIDE=QF_LIA 1 1` into 3 tokens → env treated `1` as a command.
if [ -x "$HOME/bin/z3" ]; then
    export Z3="$HOME/bin/z3"
elif ! command -v z3 >/dev/null; then
    echo "ERROR [$(hostname)]: z3 missing"; exit 1
fi
if [ -x "$HOME/bin/cvc5" ]; then
    export CVC5="$HOME/bin/cvc5"
fi
if [ "$P" = "14" ] && [ ! -x "$HOME/bin/cvc5" ]; then
    echo "ERROR [$(hostname)]: panda14 needs ~/bin/cvc5"; exit 1
fi

# 4. SmartShard / batch overrides (forwarded from PowerShell ssh, already in env)
[ -n "${TASKS_OVERRIDE:-}"    ] && export TASKS_OVERRIDE
[ -n "${JOBS_OVERRIDE:-}"     ] && export JOBS_OVERRIDE
[ -n "${TIMEOUT:-}"           ] && export TIMEOUT
[ -n "${PROFILE:-}"           ] && export PROFILE
[ -n "${ORACLE_ONLY:-}"       ] && export ORACLE_ONLY
[ -n "${CANDFLAGS_VARIANT:-}" ] && export CANDFLAGS_VARIANT
# Oracle cache: if /tmp/oracle_cache.tsv exists (scp'd by deploy_pandas.ps1), tell run.sh to use it.
if [ -f "/tmp/oracle_cache.tsv" ]; then
    export ORACLE_CACHE_FILE=/tmp/oracle_cache.tsv
    echo "  oracle cache available: /tmp/oracle_cache.tsv ($(wc -l < /tmp/oracle_cache.tsv) entries)"
fi

# 5. start in background — bash inherits all exported vars
nohup bash tools/run.sh "$P" > "$DEPLOY_DIR/run_${P}.log" 2>&1 &
disown
sleep 2

# 6. verify
PID=$(pgrep -u "$USER" -f "tools/run.sh $P" | head -1)
if [ -n "$PID" ]; then
    echo "OK [$(hostname)] panda$P pid=$PID  tasks=${TASKS_OVERRIDE:-preset}  log=$DEPLOY_DIR/run_${P}.log"
else
    echo "ERROR [$(hostname)] panda$P FAILED to start:"
    tail -10 "$DEPLOY_DIR/run_${P}.log" 2>/dev/null
    exit 1
fi
