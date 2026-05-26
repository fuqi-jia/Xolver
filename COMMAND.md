  ./tools/deploy_and_run.sh build
  ./tools/deploy_and_run.sh package

  # panda3: UF family + difference logic + arrays  (~15,100)
  ./nlcolver-dist/tools/deploy_and_run.sh run
  uf,uflra,uflia,ufnia,ufnra,lira,nira,idl,rdl,ax,alia,auflia -j 200 -t 100 --compare-with z3

  # panda4: LIA  (13,306)
  ./nlcolver-dist/tools/deploy_and_run.sh run lia -j 200 -t 100 --compare-with z3

  # panda5: 实数族  (13,907)
  ./nlcolver-dist/tools/deploy_and_run.sh run nra,lra -j 200 -t 100 --compare-with z3

  # panda6: NIA 独占（25,452，unavoidable 大头）
  ./nlcolver-dist/tools/deploy_and_run.sh run nia -j 200 -t 100 --compare-with z3

  # ==========================================================================
  # 2-机方案（只剩 panda1 + panda7）— 缩短 timeout，重点查 bug（与 z3 对比找不一致）
  # 注意：新包目录已改名 zolver-dist（不是 nlcolver-dist）
  # ==========================================================================

  # panda1: NIA 独占（25,452，undecidable，最易出 soundness bug，且最常跑到 timeout）
  ./zolver-dist/tools/deploy_and_run.sh run nia -j 200 -t 30 --compare-with z3

  # panda7: 其余全部（可判定/快速逻辑 + UF/array 组合 + 差分逻辑，≈42,313）
  ./zolver-dist/tools/deploy_and_run.sh run lia,nra,lra,uf,uflra,uflia,ufnia,ufnra,lira,nira,idl,rdl,ax,alia,auflia -j 200 -t 30 --compare-with z3