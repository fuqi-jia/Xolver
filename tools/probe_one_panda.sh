#!/bin/bash
# probe_one_panda.sh — single-line CPU/mem/load probe for one panda
# output:  CPU=<int>%  LOAD1=<float>  NPROC=<int>  MEM_FREE_PCT=<int>  hostname=<host>
# CPU = current usage (100 - idle), 1-sec sample via /proc/stat diff

# 1. CPU usage via /proc/stat 1-sec diff
read _ u1 n1 s1 i1 w1 _ < <(grep -E '^cpu ' /proc/stat)
sleep 1
read _ u2 n2 s2 i2 w2 _ < <(grep -E '^cpu ' /proc/stat)
busy1=$((u1+n1+s1+w1)); total1=$((busy1+i1))
busy2=$((u2+n2+s2+w2)); total2=$((busy2+i2))
dbusy=$((busy2-busy1)); dtotal=$((total2-total1))
[ $dtotal -gt 0 ] && CPU=$((100*dbusy/dtotal)) || CPU=0

# 2. load1 + nproc
LOAD1=$(uptime | awk -F'load average:' '{split($2,a,","); gsub(/^ +/,"",a[1]); print a[1]}')
NPROC=$(nproc)

# 3. memory free pct
MEM_FREE_PCT=$(free | awk '/^Mem:/ {printf "%d", 100*$7/$2}')

printf "CPU=%d%% LOAD1=%s NPROC=%d MEM_FREE_PCT=%d%% hostname=%s\n" \
    "$CPU" "$LOAD1" "$NPROC" "$MEM_FREE_PCT" "$(hostname)"
