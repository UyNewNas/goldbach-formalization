# P3.5 稿内续接审计

## 可以独立完成的一步

固定导数阶数 d，对**每一个实际 Fourier 模态先取测试变量的导数上确界，再合计模态**。这提供附录 A.5 在应用逐测试函数 Bessel 界前需要的一项实际输入。源是 period-64 的同一组 spectralTest 与 actualCoeff。R20 已有逐模、逐点的全阶一致证明，不需要重写这些证明。S22 做过共同测试点 q 的 Fourier 合计，其原报告第 45 行明确保留另一种取上确界的次序。

冻结文本为 UyNewNas/chen-imbalanced-semiprimes 在 a988cba584d803ae2856a0de50efb582f4f3dd6a 的 paper/release-20261106/en/analytic-appendix.tex；本地正文 Git blob 7cf3bbb16cd8924565eb439e474e0674f04631da、SHA-256 e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548。对应 705–717 行的固定箱 Fourier 分离与逐测试导数代价，757–776 行的 regular 权界和 level Cauchy，以及 1025–1028 行指明的外部 Pascadi Lemma D。

令规范化的实际逐模大小为

    S_d(ell,Y) = ∑ n ∈ Finset.range (d+1),
      sSup (Set.range (fun q : ℝ =>
        Y^n * ‖iteratedDeriv n (spectralTest ell Y) q‖))

可验收的声明应给出下列类型（数学签名，未编译）。

    ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ rho : ℝ, 0 ≤ rho → ∀ sigma : ℝ, |sigma| ≤ 1 →
      ∀ Y : ℝ, 0 < Y →
      Summable (fun ell : D4 → ℤ => ‖actualCoeff rho sigma ell‖ * S_d ell Y) ∧
      (∑' ell : D4 → ℤ, ‖actualCoeff rho sigma ell‖ * S_d ell Y)
        ≤ C * (1+rho)^(4*(d+3))

每个取上确界的实数集合非空（取 q=0）且有界（R20），因此 sSup 确实是常规实上确界。对 n≤d，由旧逐模界及 1≤1+|ell 0| 得到 S_d(ell,Y) ≤ (∑_{n≤d} testJetConstant n)(1+|ell 0|)^d。使用现有 actual_uniform_weighted_l1 的 Summable 与 actualW 上界。这样直接控制由模态决定测试函数的费用，一次支付最高阶。d=4 时 Fourier 上界是 (1+rho)^28；在证明最终外部调用需要几阶之前，应保留任意固定 d。全程没有外部定理证明。

## 可复用源与导入边界

Donor UyNewNas/goldbach-formalization 52098e403ac4b28c72ec5958fd738ae93d785ac5（本地 /workspace/scratch/e5a460f2108f/goldbach-p25）。

| 用途 | 精确路径、声明与证据 |
| --- | --- |
| 真正的导数公式和逐模一致界 | docs/source-only/20261102-resume-30r/full_modulus_test_support/Part3OriginalFullModulusTestJets.lean，Git blob d4ce9301a7c98f117937e614ca29577c09e98d19、SHA-256 cf4c4840f8bcdfa778848bb1ded656636dccf5e249e9f957092955a5f7b262dd。第 47–54 行 iteratedDeriv_tsupport_subset 与第 101–257 行 complexChi、nativePhase、迭代 Leibniz/伸缩公式、固定 cutoff jet 常数、spectralMode_jet_bound、spectralTest_jet_bound；第 261–325 行已写逐点 Fourier 合计。旧 REPORT/REGISTRY 将其列作未编译；未在此次检查的验收材料中找到本模块验收。 |
| 相位导数的三个小供应 | docs/source-only/20261102-resume-30m/exceptional_j_large_scale/Part3ActualExceptionalJLargeTransform.lean，blob 43fe6493d1a4c90a252ed163aa14572ebe9e44ad；33–34 行 modeFrequency、50–63 行 phase_hasDerivAt、136–142 行 modeFrequency_norm_le 可逐声明保留。不要移入该文件涉及外部谱函数的论证。 |
| R20 已知语法修订 | docs/source-only/20261112-resume/t03/abel-lift-next/TEST_JETS_SCOPE.patch，blob 4d8ccd525446ad28cde6a396b0d345e3b987ca9c，加入 ContDiff scope。 |
| 已有共同 q 与六尺度费用 | docs/source-only/20261102-resume-30s/S/s22_actual_spectral_energy/Part3OriginalUniformTestCutoffBudget.lean，blob 4ed252e2956690d46848cb14b4f8253a88050610。检查 normalizedTestJetMass_le、exists_original_six_testSeminorm_cutoff_constant、exists_original_six_test_and_tail_threshold。真实 rho=(2^j M)/N、非空 interval、共同 cutoff、(4(d+3)+2)η、六 tail 已有源码。d=4 的 30η 含额外 2η 截断费。其第 84–85 行明确量词次序。 |
| HEAD 可用本地依赖 | ImbalancedChen/Part3NativePeriod64Reconstruction.lean 已有 spectralMode、spectralTest、chi、chi_tsupport_subset、actualCoeff、e、norm_e；ImbalancedChen/Part3ActualWeightedSpectralBudget.lean 已有 actual_uniform_weighted_l1、actual_square_budget_absorbed；Part3ActualSampledFourierLattice 已在二者闭包内。由 HEAD 每个行首 project import 递归遍历，二个根的并集有 55 个不同项目模块（含根），全部在当前分支。使用 Mathlib.Analysis.Calculus.Deriv.Support 与 Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas；其余常规库由现有根导出。受理证据见当前 docs/part3-distribution/continuation-20261125/continuous-height/HISTORICAL_REUSE.json。 |
| 新声明的存在性检查 | 检查 donor 的 ImbalancedChen 与 docs/source-only 下 Lean 源。只发现 R20 的逐点证明，以及 S22 对所需 sup/Σ 先后次序的明确排除，未发现上述逐模上确界 Fourier 付款实现。这是限定检索结果。 |

R20 的文件级直接 imports 是 OriginalFullModulusSupport、ActualExceptionalJLargeTransform 以及上述两个 Mathlib 模块。其前者导入 OriginalTwoZFourierAssembly，后者导入 ActualExceptionalJLargeKernel 与 ActualExceptionalJPacketAdapter。用 Y04 历史 available_sources 映射遍历这整个文件得到 256 个不同项目节点（含未解析叶节点），其中 22 个在该选择映射无字节项。该数值只描述旧选择映射。推荐按现有源码声明提取相位与 jet 小段并保留 donor 映射、来源、名称与证明。所需数学不需要 OriginalData、物理 trace 和上述过宽 imports；这样独立于 Y04 的六缺源。若能找到已验收的同字节 jet 供应则直接导入使用。

## 实际谱函数的剩余接口

- Y04 的 docs/source-only/20261123-yellow-node-owners/y04_spectral_732/ImbalancedChen/Part3OriginalPrintedPrescribedRows.lean 第 143–155 行明确 Φ=spectralTest ell (chartY0 D k upper j N)。continuous 两支各有 /4；positive 另有 holWeight/2 与 nativeWeight*(M₁/4)，opposite 无 holomorphic 项。第 229 行 original_printed_six_spectrum 已有 signed 六次求和及逐模绝对可和源码；绝对可和本身不给一致 x^ε 费用。
- 正号定义源为 docs/source-only/20261112-resume/t04/positive-test-next/Part3ActualPrescribedPositiveJ.lean，第 16、25、80 行附近。regular_transform 提供实际连续 Schwartz 表示，fixed_regular_decay 先固定 ell,Y 才选 C。负号定义在同目录树 t04/bessel-next/Part3ActualOppositeBesselTransform.lean 第 19–23 行，为 8 cosh(πt) 乘 K 变换，随后必须保留打印行 /4。用 Y04 available_sources 遍历该负号源可到六个已知缺失项全部；直接导入原 def 所在整文件不能据此宣告已闭合。
- Pascadi, arXiv:2404.04239v3 的原文已有本地快照 docs/source-only/20261102-resume-30k/regular_continuous/references/pascadi-2404.04239v3.html，§3.3 (3.18)–(3.21)。外部输入按 dyadic compact support、各阶归一化导数界陈述。低界 (3.20) 写 t≠0，高界 (3.21) 对 |t|≥1，足够消费者 |t|≥max(1,2Y)。在 Y04 逐点消费者中，低界 t=0 需用对应连续表示延拓（对连续积分亦可另走 a.e. 版本）；外部规范中 J/K 的常数也须与 Y04 实际积分核比对。原文的声明没有把最小或充分 jet 阶数直接印成 4。该注册材料没有独立、统一物理族两支 transform 供应，不能靠引入目标等价假设补齐。现有 low/high shell、两独立累计能量、印刷 /π、(96)→(97) 均不需重做。
- 分类：上确界 Fourier 费用是可直接补足的稿内推导；同一外部测试类、归一化常数、t=0、有限阶依赖的映射是接口核对；Y04 原始行闭包缺字节是源码条件。此次检查没有给出冻结稿存在实质数学漏洞的证据。

本轮只读审计与这份交接记录。没有改 Lean、编译、运行内核或提交。


## 最小导入与闭包逐项核验

运行时只选下面两个项目入口，另显式引入 Mathlib.Analysis.Calculus.Deriv.Support、Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas；不要在精简的模块中保留旧文件对 PhysicalSupport、ExceptionalJLargeTransform 等父模块的 import/open。phase 三项放入原有命名空间可以保留 R20 原证明体。具体应复用 M 的 modeFrequency、phase_hasDerivAt、modeFrequency_norm_le；R20 的 private iteratedDeriv_tsupport_subset（47–54）以及 complexChi、nativePhase、complexChi_contDiff、nativePhase_contDiff、nativePhase_iteratedDeriv、spectralMode_iteratedDeriv、spectralTest_iteratedDeriv、private complexChi_tsupport、exists_cutoffJetBound、cutoffJetBound、cutoffJetBound_pos、cutoffJetBound_bound、testJetConstant、testJetConstant_pos、spectralMode_jet_bound、spectralTest_jet_bound（101–257）。R20 已写的共同 q Fourier tsum 第 261 行起无需另定义；新结果直接使用 existing actual_uniform_weighted_l1 及逐模界。

旁置文件 jet-supplier-closure.json 逐模块列出 55 个项目路径、Git blob、SHA-256 和直接 project imports。遍历起点为 Part3NativePeriod64Reconstruction 与 Part3ActualWeightedSpectralBudget；逐一读取当前 worktree、HEAD:路径、donor 工作树及 donor HEAD:路径，四者完全一致。此处证明源码身份与 import 可满足，不是新编译或重验收。
