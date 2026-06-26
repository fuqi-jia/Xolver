# Panda Preset Profiles — quick reference

Use `.\tools\probe_pandas.ps1 -MaxCpuPct 10` first to see which pandas are idle, then pick the matching profile.

| Idle pandas | Profile | Dispatch command |
|---|---|---|
| 1-5, 6, 7, 8, 9, 10, 14 (all 11) | `default` | `.\tools\deploy_pandas.ps1 -Timeout 300` |
| 1-5, 8, 9, 14 (8; **6+7+10 busy** — common!) | `panda678_busy` | `.\tools\deploy_pandas.ps1 -Nodes 1,2,3,4,5,8,9,14 -Profile panda678_busy -Timeout 300` |
| 1-5, 8, 9, 10, 14 (9; **6+7 busy,10 up** — common!) | `panda67_busy` | `.\tools\deploy_pandas.ps1 -Nodes 1,2,3,4,5,8,9,10,14 -Profile panda67_busy -Timeout 300` |
| 1-5, **7**, 8, 9, 10, 14 (10; only **panda6 busy** ★ very common) | `panda6_busy` | `.\tools\deploy_pandas.ps1 -Nodes 1,2,3,4,5,7,8,9,10,14 -Profile panda6_busy -Timeout 300` |
| 1-5, 6, 8, 9, 10, 14 (10; only **panda7 busy**) | `panda7_busy` | `.\tools\deploy_pandas.ps1 -Nodes 1,2,3,4,5,6,8,9,10,14 -Profile panda7_busy -Timeout 300` |
| 1-5, 6, 7, 8, 9, 14 (10; only **panda10 busy**) | `panda10_busy` | `.\tools\deploy_pandas.ps1 -Nodes 1,2,3,4,5,6,7,8,9,14 -Profile panda10_busy -Timeout 300` |

---

## Profile: `default` (all 11 pandas available)

Standard allocation, balanced via runtime-weighted distribution (5min batch data):

| panda | -j | workload | est. wall |
|---|---|---|---|
| 1-5 | 220 | NIA 5-way | ~3.1h |
| 6 | 220 | LIA 1/3 + AX + UF | ~2.1h |
| 7 | 220 | NRA 1/2 + LIA 2/3 | ~3.5h |
| 8 | 220 | NRA 2/2 + LIA 3/3 | ~3.5h |
| 9 | 72 | smalls + LRA | ~3.3h |
| 10 | 200 | LIA + AX + UF | ~5.5h (long pole — known imbalance, see "default" variant below) |
| 14 | 64 | DT + UFDTNIA | ~2.2h |

**Issue:** panda10 = long pole if all 11 used (5.5h wall vs ~3.5 for others). Consider using `panda10_busy` profile even when panda10 is free to even out wall time.

---

## Profile: `panda678_busy` (8 pandas: 1-5, 8, 9, 14)

When panda 6, 7, 10 are all busy (common — these are popular for other users).

**panda8 absorbs panda 6+7+10 work** (NRA + LIA + AX + UF):

| panda | -j | workload | est. wall (300s) | est. wall (30s) |
|---|---|---|---|---|
| 1-5 | 220 | NIA 5-way | ~3.1h | ~5 min |
| 8 | 220 | NRA + LIA + AX + UF | ~6h (long pole) | ~25 min |
| 9 | 72 | smalls + LRA | ~3.3h | ~10 min |
| 14 | 64 | DT + UFDTNIA | ~2.2h | ~20 min |

**Max wall: ~6h at 300s** (panda8 is long pole, single-handedly carries all big non-NIA work). Acceptable for 30s bug check (~25 min total).

---

## Profile: `panda6_busy` (10 pandas: 1-5, 7, 8, 9, 10, 14)

When only panda6 is busy (very common — panda6 long-term occupied by other users).

| panda | -j | workload | est. wall |
|---|---|---|---|
| 1-5 | 220 | NIA 5-way | ~3.1h |
| 7 | 220 | NRA 1/2 + LIA 1/3 | ~3.5h |
| 8 | 220 | NRA 2/2 + LIA 2/3 | ~3.5h |
| 10 | 200 | LIA 3/3 + AX + UF | ~2.3h |
| 9 | 72 | smalls + LRA | ~3.3h |
| 14 | 64 | DT + UFDTNIA | ~2.2h |

**Max wall ~3.5h.** Clean balanced.

---

## Profile: `panda7_busy` (10 pandas: 1-5, 6, 8, 9, 10, 14)

When only panda7 is busy. panda8 absorbs panda7's NRA + LIA shards.

| panda | -j | workload |
|---|---|---|
| 1-5 | 220 | NIA 5-way |
| 6 | 220 | LIA 1/3 + AX + UF |
| 8 | 220 | NRA all + LIA 2/3 + LIA 3/3 |
| 9 | 72 | smalls + LRA |
| 10 | 200 | LIA + AX + UF (duplicate of panda6 work — TODO: dedupe) |
| 14 | 64 | DT + UFDTNIA |

**Known issue:** panda10 duplicate work. Re-balance for next refinement.

---

## Profile: `panda10_busy` (10 pandas: 1-5, 6, 7, 8, 9, 14)

When only panda10 is busy. panda6 absorbs panda10's LIA + AX + UF.

| panda | -j | workload |
|---|---|---|
| 1-5 | 220 | NIA 5-way |
| 6 | 220 | LIA + AX + UF (full, NOT 1/3) |
| 7 | 220 | NRA 1/2 |
| 8 | 220 | NRA 2/2 |
| 9 | 72 | smalls + LRA |
| 14 | 64 | DT + UFDTNIA |

This is the cleanest re-balance (was the proposal originally when only panda10 was out).

---

## Adding new profiles

When a NEW idle-set surfaces (e.g., panda 1+5 busy), add to `tools/run.sh` case `$PROFILE` block + here. Pattern:

1. Identify available pandas
2. Distribute by runtime weight (see 5min batch data in `results/2026-05-31/CATALOG.md`)
3. NIA (3458h) → split N-way across NIA-class pandas
4. NRA (922h) → split M-way across general pandas
5. LIA + UF (~1090h combined) → 1-2 NIA-class pandas
6. Smalls + LRA (~235h) → panda9 (low thread)
7. DT + UFDTNIA (~140h) → panda14 (lowest thread + cvc5 needed)

See `tools/run.sh` `case "$PROFILE" in` block for code.
