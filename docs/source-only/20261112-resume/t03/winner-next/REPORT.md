# P1.4 原始 saved 第六层的实际准入、全盒见证和最终策略

本包给原档案的 632,104 行逐行建立实际入树条件。在每个获准的细闭盒上，整盒共用同一个获胜动作见证。最终全有序第三层、第五层并集和 R17 第六层的读数覆盖全部 87 个原始第八层域，包括没有 saved 行或旧第三层 owner 的域内点。八份 Lean 源已静态核读，尚无本包的远端内核验收。登记的模块、前像、原档案、原稿和安装变体均见同目录 REGISTRY.json。

## 原表的掩码和适用范围

原生产器在每个细化的 grid-400 六维行盒选定一个写入档案的掩码。它在中点依次考虑 32 至 63，通过门与残差条件且严格改善当前值时才替换，随后用所选掩码复核整行盒的门、上界和角点。扩展生产器调用相同的 certify，将结果保存到原 NPZ 的 cells 数组。源码使用原 11 个 int64 字段中的下标 7 和原有 selectedMask，直接复用既有数据、原始不同行索引和经过原档案谓词导出的许可。[选取和验行，41–97 行](E:/timot/Documents/FilesForGPT/Myath/tmp/publication-20261010/verification-renewal-v2/_runs/full-final/certify_sixth_prefix_concave_boxes.py) · [保存，72–105 行](E:/timot/Documents/FilesForGPT/Myath/tmp/publication-20261010/verification-renewal-v2/_runs/full-final/certify_sixth_prefix_expanded_cover.py)

令 Uᵢ 为该行给真实第五层的原上界，Mᵢ 为原存掩码的端点。原增益只在 Uᵢ(t)<Mᵢ(t) 激活。原独立报告记有 444,302 行带负差角点，故不能把原 632,104 个粗盒全部提升为处处准入。行盒半开归属和正差测试在算术点保留。相等时此行不更新，其他实际动作仍分别按原门判断。[原稿第 17–49、95–117、120–155 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/sixth-prefix-expanded-independent-audit.tex#L17) · [原独审第 33、43–48 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/verification/data/sixth-prefix-expanded-independent-audit.json#L33)

原 chronological policy 存的是当前最大指数。已有 entries 按确定次序从实际已准入且达到最大值的动作中取一个见证。与继承的第五层相等时保留第五层并输出 none；多个严格改善的动作同值时，一个确定的成功见证就实现原最大指数。如果见证为 saved，则原半开行盒的唯一性还给出行号恰为 i，掩码就是档案的 selectedMask i。本包没有把最终各组的并列选择归为原生产器的唯一跨组行动 ID，也没有把仅在中点选出的掩码称为整个粗盒内所有候选的唯一最大值。[原有限树与事先记录，13–44 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/actual-k-compilation-joint-audit.tex#L13)

## 算术准入和同一祖先

* P1OriginalSavedRowsActualAdmission.row_owner 从原网格、原有第三层保留余量与 t₃≥1/50 得到同一 N 的真实前三素数 owner。它同时适用于 d₀=原第四/第五数据和 d⁺=旧新第五并集。original_and_union_admission、ordered_admission 将原 licensed filter、d⁺ 的 protected filter 及最终 current(d⁺,ω,N,h) 的 saved i 接纳，逐个等价为 t 在原半开行盒内且 Uᵢ(t)<Mᵢ(t)。真第五用自己的祖先和本行导出的 raw_parent_upper；第三、五次奇数门及 full/selected square、量化余量都来自原门。条件为整数 N>1、正六元标签、Schedule e q 0、a≤1/100、4 width(n)<1/1600，最终读另取 ω≤a。
* P1OriginalSavedRowsFinalRead.original_raw_selection、original_and_union_selection 还给出正差域中有序原素数词在真实 raw 第五与两个 protected 第五树上达到第六层的 FirstExitValidSelection。selected_words 在既有的 Schedule e q a（其中 a≤1/800）下将最终实际 target-deleted admitted 精确读成原 primes N，cap=N、z 为原 cutoff N。不同定理的粗筛区间在此分别保留。
* P1OriginalSavedRowsRawWinner.actual_read 对原未舍入树直接比较实际第五及完成全部组的 currentSixthExponent。它能识别舍入后两端恰相等的真实未舍入提升。P1OriginalSixthWinnerBankRead.read_at_history 把原已冻结的 scalar 和 tag program 接回实际第三层 seed 与真正第五祖先。P1OriginalSavedRowsWinnerSchedule.three_actual_reads 在一个细闭盒分别给出原 raw、原历史 licensed、d⁺ protected 的整盒见证。盒内每个 N′>1、每个有该坐标的正六元词均使用同一行、同一第三层标签和相应程序的同一见证；三个策略各自保有自己的第五和第六指数。

## 最终策略与全部 87 域

* P1OriginalOrderedSixthCompleteWinner.actual_read 用完整 current 根在自己的前五、前六个素数上求值。在 lower 分支，所选动作通过原 Accepted，达到真正 rounded 端点；另一分支逐层使用 saved、11 项和 19 项所属的实际 stage，原始不舍入端点达到 after … 8。四个 nonsingleton 项均沿用已冻结的 R17 比较。两个分支都用当前第五而非原某个数值上界判定是否改变。对 N>1、六个正整数与 ω≤t₃，rough_root 将实际根读回 ω=0 的静态表；全部 87 个原域都满足 t₁<μ、t₃>1/100。此处只需要第三坐标达标。
* P1OriginalFull87FinalWinnerBoxes.fixed_on_full87 给每个原域内通过共同细网格检验的点一个闭盒、一个 mode、一个见证、一个仿射输出公式。该公式在未舍入分支可随点变化。对盒内每个相容的整数目标和六元词，晚取任意 ω≤1/100，还是同一个见证和公式，均与该词真实第五/第六读数相接。refines_saved 在同一个 m 把该检验投回前述三种 saved 读数。最终 d⁺ 结论没有 saved membership、旧 owner、strict trim 或第八层安全余量假设。
* P1OriginalFull87FinalWinnerBoxes.all_sources_exact 在未通过细盒检验的点及墙上也给出原有限 fallback bank B 加 R17 的实际布尔读数。后继前缀的第六祖先固定。长度 7、8 继续在其真实第六层做原 Rosser 检验；更深处分 selectedCap 为 none 或 some v，分别保持原六层或按原第八层 v 覆写。这里所有后继取同一 N、同一前六个标签。保存行上的未舍入原树亦有 raw_descendant，历史支持上的最终树有 physical_descendant。
* common_schedule 先选 n，再选 0<e≤1/64000、足够大的 q、a≤1/100，继而选足够细的 m，最后才代入 N 和 ω。whole_mesh 保证对每个误差 ε>0，一个 m₀ 同时控制归档行盒并集的遗漏体积和 87 个原域遗漏体积之和，对所有 m≥m₀ 成立。这里的量是普通 Lebesgue 体积；原稿中漏盒的素数权、sharp PP、带符号分布须各有自己的付款。精确 wall fallback 没有丢弃任何有限 N 的原子。[原编译边界及漏盒，第 70–102 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/actual-k-compilation-joint-audit.tex#L70) · [历史顺序与墙，第 103–146 行](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-current-upper-density-assembly-20261009.txt#L103)

## 节点裁定

3d4f8ba 已有原行动的量化 square 许可，b060e4d 已有共同余量及达到最大值的原行动，旧 boxed lookup 已有判定表的闭盒稳定性。它们各自的声明仍需要归档行的实际历史、相应程序的 seed 和真实 parent。本包补齐这些接合，另接最终双模式树、真实晚取 cutoff 和各域外墙的布尔后继。原 87 个数值 saving 和同系数支付沿用此前 R17 结果。建议将这一条“归档准入、整盒实际获胜见证、最终因果读数”送独审作 source-only 结项；整项 P1.4 的低模数 PP、素数权以及全依赖的内核检查仍分别登记。先前 .599 定理给两真实系数的高模数相等，不能由此推出任何单树系数的支撑归零，本包也不使用它作准入前提。
