# lower_chambers 第五批源码交付

新增三份局部完整源码；原始完整 task=false，batch target 仍为部分完成。D 两份最终 raw SHA 已复核匹配，所有前批源码冻结。未编译、formal_credit=0。

`P2OriginalStoredWQueryRounding.lean` 补的是实际 stored whole-box `wQueryLower`，不是先前 same-point cap loss。它明确识别 stored numerator 为 cap-(H0+H1+H2)，denominator 为 H2。cap error 为 r+3h/8，三个 prefix endpoints 再贡献<=3h，因此 numerator error<=r+27h/8；changed denominator 另付 Lambda*h/epsilon²。由实际 WBoxCheck 得到 stored numerator>=0、<=Lambda，最终 0<=idealQuery-storedQuery<=(r+27h/8)/epsilon+Lambda*h/epsilon²，全部源自 canonical actual mesh endpoints。

`P2ActualLowerFullModuliQueryCompilerLoss.lean` 在每条 retained prime source row 内保留所有 actualLowerSmallRoughModuli，而非任取一个 modulus。其 signed query loss 与生产 `physicalDensitySum` 的同 rho mean 精确相连；finite triangle inequality 得到 loss<=storedEnvelope*fullAbsoluteMeanNorm。总 norm 明确包含全部 primes 和全部 residual moduli 的 |actual rho(q)|/phi(q)；没有将它藏为一个未经证明的常数。transfer_trace 明确提醒：其 rough-tail O(v/omega) Euler bound 不等于 beta-attached physical absolute norm。本批遵守该边界，固定 normalized physical envelope 仍 OPEN。

`P2OriginalUniformMixedTentWChoice.lean` 将 actual mixed screened bank 的严格 point winner 转成实际 inherited-first mixedWinner，允许 winner 为独立 tent 或 W。每个 literal SourceForm 的 slopeNorm<=15/2、差 slopeNorm<=15 都由具体 slope 值证明，因此一个 common mesh threshold 统一所有 source rows/point/code，不再逐点假设 mesh-width。原始 rational baseline、canonical exponentCode、继承优先均保留。输入是 independently checked actual screened membership 与真实 point gap，不是 successful mixedWinner 等式。尚未由所有原 ideal tent points 构造 admissible bank membership/source factorization；lower_square 与 adopted_plan 正处理该 binding，故不能称全部 tent chambers 已闭合。

完整目标仍缺：ideal tent -> actual screened/source-licensed rows；beta-attached absolute norm/cancellation；ordinary nonlinear Fbar/fbar profiles和actual prime count传播；rank4/5 frozen-parent/cube-crossing wall coverage；完整 same-rho compiler convergence/hLower。这里只完成可供上述连接消费的具体必要引理，未发现新原稿数学缺口。

仅静态读原稿、源定义、手工证明及 raw hash identity；没有 Lean/lake、编译/修复、kernel replay、checker、CI、额度检查、Git/index 或看板改动。路径、raw SHA、安装/import map、原稿锚点和未闭合前提在 REGISTRY.json。
