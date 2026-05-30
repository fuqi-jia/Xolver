# QF_UFNIA polyhedral-recovery target (Track C output)

Source: NOTES/oracle_QF_UFNIA_sample.json
Cases sampled: 31
Per-config timeout: 12s

## Detector-capability histogram

| bucket | count | meaning |
|---|---|---|
| already_solves | 14 | baseline returns oracle verdict |
| iface_recovers | 1 | needs XOLVER_NIA_IFACE_LIFECYCLE |
| uf_model_recovers | 0 | needs +XOLVER_EUF_UF_MODEL |
| track2b_recovers | 0 | needs +XOLVER_SIMPLEX_IMPLIED_EQ |
| unrecovered | 15 | none of above; further capability needed |
| wrong | 0 | sound regression — must be 0 |

## Per-case classification

| case | oracle | bucket | baseline | iface | uf_model | track2b |
|---|---|---|---|---|---|---|
| qf_AddSub_1043_values_0.smt2 | sat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AddSub_1164_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AddSub_1176_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AddSub_1202_values_0.smt2 | sat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AddSub_1295_values_0.smt2 | sat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AndOrXor_1006_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AddSub_1165_values_0.smt2 | unsat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AndOrXor_1230_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_1288_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_1294_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_151_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_1733_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_1829_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_1831_values_0.smt2 | unsat | already_solves | unsat | unsat | unsat | unsat |
| qf_AndOrXor_1844_values_0.smt2 | unsat | already_solves | unsat | unsat | unsat | unsat |
| qf_AndOrXor_1849_values_0.smt2 | unsat | already_solves | unsat | unsat | unsat | unsat |
| qf_AndOrXor_1885_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_2008_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_1900_values_0.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_2247_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_2113_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_2284_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_2265_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
| qf_AndOrXor_2663_values_65.smt2 | unsat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_273_values_7.smt2 | sat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AndOrXor_280_values_3.smt2 | sat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_290_values_7.smt2 | sat | unrecovered | unknown | timeout | timeout | timeout |
| qf_AndOrXor_523_values_0.smt2 | sat | unrecovered | unknown | unknown | unknown | unknown |
| qf_AndOrXor_709_values_0.smt2 | sat | iface_recovers | unknown | sat | sat | sat |
| qf_AndOrXor_732-2_values_0.smt2 | sat | already_solves | sat | sat | sat | sat |
