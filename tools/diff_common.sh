#!/usr/bin/env bash
# =============================================================================
# diff_common.sh — 差分跑批的共享底座(被 run.sh / run_differential.sh source)。
#
# 提供:
#   * RICH_HEADER          —— per-case 富 schema 的 CSV 表头(17 列,见 eval/oracle_schema.md)
#   * verdict_timed CMD...  —— 跑一条命令,回显 "VERDICT ELAPSED_MS"
#   * oracle_for_logic L    —— 设置 ORACLE_NAME/ORACLE_BIN/ORACLE_TLIMIT_MS(QF_DT/QF_UFDTNIA→cvc5,其余→z3)
#   * run_one_rich FILE     —— 跑 default + allon + oracle 三遍,回显一行富 CSV
#   * emit_node_sqlite ...  —— 把本节点的富 CSV 汇成 panda<N>_<ts>.sqlite(+ csv 镜像);python3 缺失则跳过
#
# 设计约束:
#   * 纯 bash + 一次可选 python3 后处理;panda 上无 sqlite3 CLI 依赖(用 python3 stdlib)。
#   * CANDFLAGS 的“内容”由各 caller 自己定义(本文件不碰),这里只消费 $CANDFLAGS。
#   * z3 / cvc5 二进制路径由 caller 经 Z3= / CVC5= 提供;cvc5 仅 offline harness 调用,
#     绝不编进 xolver 二进制(见 feedback_no_other_solver_strings)。
# =============================================================================

# 17 列,顺序与 eval/oracle_schema.md 的 diff_results 表 raw 列严格对齐。
# 派生 flag(is_decided_* 等)不在 CSV 里,由 diff_ingest.py 入库时算。
RICH_HEADER='key,division,file_path,file_size_bytes,declared_logic,xolver_default_verdict,xolver_default_time_ms,xolver_allon_verdict,xolver_allon_time_ms,oracle_solver,oracle_verdict,oracle_time_ms,panda_node,run_timestamp,xolver_git_tip,file_dir_prefix,file_name_stem'

# verdict_timed CMD...  -> "VERDICT ELAPSED_MS"
# VERDICT ∈ {sat,unsat,unknown,timeout,error};墙钟 timeout 走外层 `timeout`,内存走 ulimit -v。
verdict_timed() {
  local out rc t0 t1 ms v
  t0="$(date +%s%N 2>/dev/null || echo 0)"
  out="$( ulimit -v "$MEMCAP_KB" 2>/dev/null; timeout "$TIMEOUT" "$@" 2>/dev/null )"; rc=$?
  t1="$(date +%s%N 2>/dev/null || echo 0)"
  ms=$(( (t1 - t0) / 1000000 ))
  [ "$ms" -ge 0 ] 2>/dev/null || ms=0
  if [ "$rc" -eq 124 ]; then echo "timeout $ms"; return; fi
  v="$(printf '%s' "$out" | grep -Eoim1 'unsat|unknown|sat')"
  # grep -o 保留原大小写;统一成小写
  v="$(printf '%s' "${v:-error}" | tr 'A-Z' 'a-z')"
  echo "$v $ms"
}

# oracle_for_logic LOGIC  -> 设置全局 ORACLE_NAME / ORACLE_BIN / ORACLE_TLIMIT_MS
# Hole 1: QF_DT 与 QF_UFDTNIA(datatype-flavored)走 cvc5;z3 对这两类 structurally 不可靠。
oracle_for_logic() {
  case "$1" in
    QF_DT|QF_UFDTNIA)
      ORACLE_NAME=cvc5; ORACLE_BIN="$CVC5" ;;
    *)
      ORACLE_NAME=z3;   ORACLE_BIN="$Z3" ;;
  esac
  ORACLE_TLIMIT_MS=$(( TIMEOUT * 1000 ))
}

# 跑一遍 oracle(cvc5 额外传 --tlimit 做软超时,外层 timeout 仍兜底)
_oracle_verdict() {
  local f="$1"
  if [ "$ORACLE_NAME" = "cvc5" ]; then
    verdict_timed "$ORACLE_BIN" --tlimit="$ORACLE_TLIMIT_MS" "$f"
  else
    verdict_timed "$ORACLE_BIN" "$f"
  fi
}

# run_one_rich FILE -> 一行 17 列富 CSV(写到 stdout)
# 需要的环境变量:LOGIC XOLVER CANDFLAGS Z3 CVC5 TIMEOUT MEMCAP_KB
#                 ORACLE_NAME ORACLE_BIN ORACLE_TLIMIT_MS PANDA_NODE RUN_TS GIT_TIP
run_one_rich() {
  local f="$1" key rel d p1 p2 dir_prefix stem decl size
  key="$LOGIC/${f##*$LOGIC/}"
  rel="${key#"$LOGIC"/}"
  d="${rel%/*}"; [ "$d" = "$rel" ] && d=""          # 去掉文件名留目录;无目录则空
  IFS='/' read -r p1 p2 _ <<<"$d"                    # 取前 2 级目录
  if   [ -n "$p2" ]; then dir_prefix="$p1/$p2"
  elif [ -n "$p1" ]; then dir_prefix="$p1"
  else dir_prefix=""; fi
  stem="${f##*/}"; stem="${stem%.smt2}"
  decl="$(sed -n 's/.*set-logic[[:space:]]\{1,\}\([A-Za-z_0-9]\{1,\}\).*/\1/p' "$f" 2>/dev/null | head -1)"
  size="$(stat -c%s "$f" 2>/dev/null || echo 0)"

  local dv da ov dvv dvm avv avm ovv ovm
  dv="$(verdict_timed "$XOLVER" solve "$f")"
  da="$(verdict_timed env $CANDFLAGS "$XOLVER" solve "$f")"
  ov="$(_oracle_verdict "$f")"
  dvv="${dv% *}"; dvm="${dv##* }"
  avv="${da% *}"; avm="${da##* }"
  ovv="${ov% *}"; ovm="${ov##* }"

  printf '"%s",%s,"%s",%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,"%s","%s"\n' \
    "$key" "$LOGIC" "$f" "$size" "$decl" \
    "$dvv" "$dvm" "$avv" "$avm" \
    "$ORACLE_NAME" "$ovv" "$ovm" \
    "$PANDA_NODE" "$RUN_TS" "$GIT_TIP" "$dir_prefix" "$stem"
}

# emit_node_sqlite OUT_SQLITE OUT_CSV CSV1 [CSV2 ...]
# 把本节点产出的富 CSV 汇成一个 sqlite(派生 flag + 索引由 diff_ingest.py 算)+ 一个合并 csv 镜像。
# python3 缺失 → 只警告并跳过 sqlite(富 CSV 仍是 source of truth,master 端可集中入库)。
emit_node_sqlite() {
  local sq="$1" mirror="$2"; shift 2
  if ! command -v python3 >/dev/null 2>&1; then
    echo "    [sqlite] 跳过: 本机无 python3;富 CSV 已产出,master 端集中入库即可" >&2
    return 0
  fi
  local here; here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  python3 "$here/diff_ingest.py" --sqlite "$sq" --csv-mirror "$mirror" "$@" \
    && echo "    [sqlite] $sq  (+镜像 $mirror)" >&2 \
    || echo "    [sqlite] 入库失败(富 CSV 仍可用)" >&2
}
