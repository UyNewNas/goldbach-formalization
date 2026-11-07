# Q26 — H430 根来源与后代独立复核

**结论：Q13、Q14 下列局部源码范围 PASS；原始 H430 全链 HOLD。** 两个作者报告准确保留完整目标 OPEN。P10/P11 的既有局部 PASS 沿用 P/t25 的原范围，没有被重审成整链声称，也没有因本轮局部进展扩张。

review_complete=true；compiled=false；kernel_verified=false；formal_credit=0；finite_guards=UNEVALUATED；full_target=OPEN；ready_to_install=false。

审查者：/root/q26_review_h430。先读 Q/BRIEF、P 两组 REPORT/REGISTRY、P/t25 和 Q03 triage，再读原稿及实际依赖。完整逐行审阅 Q13 两源、Q14 三源及最终报告；只写本审查文件。未运行 Lean/lake、编译器、CI、数学有限 guard、数值 replay、Git；未修改作者或旧批次文件，未派生代理。

**冻结范围及 SHA256**

仓库根为 E:/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation。下表 Q 指 docs/source-only/20261102-resume-30q。

| 文件 | 审阅范围 | SHA256 |
| --- | --- | --- |
| Q/h430_root_license/Part5OriginalH430RootSourceDictionary.lean | 1–224，全部 | 8a868d9ebd0a15b5d0eabf8f50466645a3afc8c9a3606f7208bdfa7e3fd252d2 |
| Q/h430_root_license/Part5OriginalH430ClassicalTailBV.lean | 1–190，全部 | c235528f5f46b551e7422747b51053b7c08d571a684fd1b895c8b542da5fbea2 |
| Q/h430_descendants/Part5OriginalH430DescendantLimits.lean | 1–233，全部 | c2e801c844b1e5b445e6279df28fd23cccf38342e10ec696e954824a9822f469 |
| Q/h430_descendants/Part5OriginalH430ActiveKnotPullbacks.lean | 1–160，全部 | 595ee1c5550376f3cdfbdc8e983ac0531e3e97d74243eb3bf05a9d17ef42e46c |
| Q/h430_descendants/Part5OriginalH430BuchstabPhysicalBudget.lean | 1–389，全部 | 3035244dba603222d96c79e79bce017d7c6ccaba36b9322a7c352ab42a95a2a8 |
| Q/h430_root_license/REPORT.md | 全部 | 2672231816bcf26a7b08cd89e1046575ac6acc1df8773c6fec202bd0733aad27 |
| Q/h430_root_license/REGISTRY.json | 全部元数据 | 678522cad225c04a62e5c6e0dd0c761e4939d7641bca7b467db71f6ebcad0347 |
| Q/h430_descendants/REPORT.md | 全部 | 5a1febf688f1dde1cda780575708997726624d32d7f25805bb9e89970db841c0 |
| Q/h430_descendants/REGISTRY.json | 全部元数据 | 9e7b670a669b21cf4a7c66bb067648b4784e7621393133ea23ed0f2099698a08 |

Q13 的 41 次 path/hash/bytes pin、432 个登记声明行号引用均匹配，其中新声明为 32 个。Q14 的 46 次 pin 与 58 个新声明的完整 namespace/声明行号均匹配。声明位置核对是文本元数据检查，不表示重新验证全部复用证明或内核验收。五份新 Lean 的 admission/axiom/evaluation/unsafe token 扫描未命中。

基线证据已重新核对：

| 证据 | 已读范围 | SHA256 |
| --- | --- | --- |
| Q/BRIEF.md | 全部 | 727be2f0211dade53d575cef30e55cf57d61d3f858ea47b22ae996f15227046d |
| Q/q03_original_gap_triage/REPORT.md | 全部，重点任务 3–5 | 5dfb3069d4d021acad6d27bf36295adcef9e288388ad46ab1afbf15261b436cd |
| docs/source-only/20261102-resume-30p/reviews/t25_review_h430.md | 全部 | e289262c151ff9e6302b294b76846a2f958cbd7f1cfa1759f3dc9d45f95e01ca |
| ../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex | 275–297、795–895，重点 808–895 | ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd |
| 同 paper/source/modules/global-chen-lower-completion-20261010.txt | 175–289，重点 184–197、254–256、272–289 | 8597fd1dc01d3fc49e5b31d28afeab3cf48e88ae23908fb6777a1c23f5b360e5 |
| 同 paper/source/modules/distribution-coefficient-completion-20261010.txt | 69–139、227–244 | a6cfa86f625242527df3ba485a7e86867b84e289bca651c0e8b942be36f0fc69 |

**原稿语义与 P 基线**

1. physical lambda 决定 Q、残余 L、真实 alpha、cutoff 和 Theta；analytic ell_aux 只供应同一整数系数的 support/full/selected-square cover。原稿允许两者不同。classical complete level below half 是第三种来源条件；U3 的 t≥57/224 尾部走固定正 tau 下的半水平从下逼近。
2. O 的 sourceRoot_fullGates_iff 和 U3 tail 否定在其现有模型中成立：将外部 selected 根放入完整 slots 后，物理 fullGates 要求 2t≤1/2−tau。该失败保持为模型入口障碍；它没有证明原稿反例，也不否定已有 Member 范围内的 residual floor。
3. 原稿 857–877 要求只读前代、替代动作取最大、closed support minima、seed-only430、共同嵌套 refinement；norm12、root norm7/2、depth440、101^−440 和 (12^441−1)/11 保持原值。D5-bad 与 Gamma9–21 保持独立的 positive switched bases。
4. P10 已供每固定父状态的 moving-start 原子及 strip 误差；P11 已供两个根的 H430 correction 表权 L1 收敛。它们没有声称实际全后代或全部 441 代实现。原有正测度 root max(2,L/a)=2 分支及其 entries49/50 相邻 closed minimum 完整保留；本轮没有删除或改写该状态。

**Q13：限定 PASS**

RootSourceDictionary:26–40 从实际 root/coordinate 计算来源，U3 严格 t<e 为 enhanced，等号及其尾部为 classical，U4 原 band 全为 enhanced。它没有把算术 licence 填入新字段。

RootSourceDictionary:44–101 用既有完整 word、selectedWord、remainingWord 定义 coverGates。append/perform/realize 的转换保留物理 LocalDomain 与原 Program；证明时暂用 total=ell_aux 的记录只用于复用既有 gate 引理，输出节点仍是原物理节点。其新 square 仍由物理 residual 控制，未用 ell_aux 重新计算物理 alpha 或 cutoff。

RootSourceDictionary:103–164 从原 tent 证明 enhanced 根的 t<e、2t<v(t)、total=v(t)，再推真实 frozen 根及后代的 cover gates 和相同 total。这里 v(t)≤ell_aux 只是门的比较；不能据此把任意大 cover 当成合法 factorization 来源。:168–201 的具体 midpoint cover 在显式 hbuffer: frozen lambda<v(t) 下给 lambda<ell_aux<v(t) 及 2t<ell_aux。该 strict buffer 没有自动对所有冻结 mesh 端点成立；no-loss/equality/inherit 的共同策略仍 OPEN。:203–221 的 classical 后代结果是实际 total≤1/2−tau<1/2，尚未给每个后代的整数系数许可。

ClassicalTailBV:34–109 直接使用 K 的原 rowWeight/rowActive、半开 prime selector 和真实 clamped cutoff。从非零 Rosser 系数的实际支持推出完整 p*q≤N^(1/2−tau)、正性及 target coprimality；没有 p²≤Q 前提。共同 strict sieve product 的包含由原 primeWindow 和 target deletion 导出。

ClassicalTailBV:111–156 用生产 ChenPooledQuotientAP 的 gcd recovery/injectivity 汇总真实 signed AP 项；没有引入外层质数个数或未经证明的 multiplicity loss。固定 0<tau≤1/12 和 A>0 后，生产 BV 给一个 N 阈值，随后同时覆盖两个 sieve signs。该阈值没有被宣称对 tau→0 统一。

ClassicalTailBV:160–187 将新估计与真实 receiver/rowError 接上，逐项保留 true-li 与 literal-li 的 2/log2 常数差以及负的 centre-prime correction，符号核对正确。现已支付的是初始 U3-tail 的 true-li AP 分量；完整 rowError、标记族 main-term/Theta 归一化、adopted seed 和 H430 count licence 尚未由此得出。

复用链重点已追读：K SameQCountEntrance:27–121、PrimeCorrectionPayment:29–103；F root_coefficient_full_Q:41–60；J receiver_error_eq_sharp_prime_error:147–160；生产 ChenPooledQuotientAP:32–125、276–290；Part3PrimeAPDistribution:190–205；P2MarkedThetaLiNormalization:39–43。没有用带有失败 p²≤Q 入口的 classical box receiver冒充原尾部来源。

**Q14：限定 PASS**

DescendantLimits:25–145 在同一 Program 和同一物理追加坐标上，复用 O 的 root-loss 恒等式推 residual/query 收敛；query 归纳只要求 ideal Member，没有把 frozen Member 或两域相同当作前提。:147–222 从真实理想路径推出正 residual/ceiling，保留完整 marked word，得到真实 alpha 与 physicalWeight 极限。:226–230 精确保留 transport/W1-fixed/W2-fixed 的常值 query；该等式不自动供应这些动作的 admission。

ActiveKnotPullbacks:25–103 的五种 active query 具有正确的物理分子/正分母。特别 D7/D8 保持 (L−x−y)/x，未 clamp 到2。:105–157 从真实 residual 差得到 |numerator_ideal−numerator_frozen|≤|slope|·levelError，并把 closed comparison 变化定位到闭 strip，保留等号。这里尚无完整 W1/W2 admission 域定理、proper fibre 的母体质量趋零定理或全 closed-atom membership 稳定性；局部分母正性仍明确可见。

BuchstabPhysicalBudget:33–124 从字面 LocalDomain 推出有效端点：
a_plus=max(max(2,s−1), L/ceiling−1)，a_minus=max(s−1, L/ceiling−1)。
其中 lower 仍要求 s≥2，w≥1 给出新 square，ceiling 条件逐项保留。它仅等价 LocalDomain；下一真实 TypedNode 边还须 incomingAllowed、cellMember 和来源历史。PhysicalNode 候选本身不限制末端 TypedNode 的 upper/lower 标志。

BuchstabPhysicalBudget:129–220 将原 singleton 插入、绝对 Jacobian L/(w+1)² 和完整父 physicalWeight 结合，保留每个 closed FloorAtom。方向正确：upper Buchstab 用 tableAtomSet true，即 lower h；lower Buchstab 用 upper H。该 identity 是显式 w-pullback 密度的恒等式。

BuchstabPhysicalBudget:225–271 先证真正 absolute integral，再控积分差：
weightedAtomError ≤ 4|P−Q| + |Q|·|a(p)−a(q)|，
P/Q 是两父的完整 physicalWeight。可积性由 P 的 startAtomDensity_integrable 供应，strip 部分直接复用 P 的 startAbsoluteError_bounds，没有用 signed cancellation 代替 L1。:275–301 导出 production localBudget 对一个 Unit/zero-base Buchstab 动作、全部 closed atoms、任意给定 old nums 的精确特化和上界，没有把目标误差列为假设。

BuchstabPhysicalBudget:303–365 在每个固定 admitted ideal 物理父路径上得到 moving start、单动作预算及实际 LocalDomain-filtered w-pullback absolute error 的极限。正 ceiling 与 frozen residual 最终为正已正式接入。:370–386 的 lower budget 只覆盖理想 parent s>2；s=2 仍 OPEN，不能将该范围写成整个 s≥2 已解决。

该新增极限比较两个真正移动的端点；它没有声称连续参数到固定 1/50 网格的距离趋零。两父的 x=L/(w+1) 是不同物理映射：w-pullback L1 尚不是 same-native-x L1；完整 measure change-of-variables 与外层父族积分仍待供应。

**actualTheta、immutable localBudget 与共同阈值：HOLD**

Q14 是实质性的局部进展，但以下连接没有出现在最终五源中：

- 整个 ideal/frozen Program Member 的 native-coordinate symmetric difference；所有 typed/cell/history 过滤、W1/W2 门、lower s=2 与恒等/继承 strata，以及 active knot strips 的真实父质量。
- 连续 4/(word.prod*L) 到原 C(BN)/phi(B)/log(Q/B) 的 arithmetic Theta_Q 质量律和同一正标记族上的父积分。零质量 pieces 必须继续用绝对误差，不能通过除以 Theta 消去。
- immutable seed-only430 的真实 predecessor arrays、所有 fixed/feedback/switched bases、labels、multiplicities、scalars 与 localBudget 的身份。Q14 的系数包含完整父 physicalWeight，行总质量并非自动≤12；Unit/zero-base 特化尚不能作为原 normalized row 输入。
- 因而生产 RenewalFiniteErrorPropagationP5:239–253 的真实 hw/hmass/hlocal 尚未同时实例化。其 localBudget:29–33 仍要求实际 base 差及实际旧表值乘系数差的加权和。通用传播定理、M 的 Fin441×Primitive×FloorAtom 无权和、两根共同 n，以及逐父极限均不能代替该身份。
- 正确量词继续是 final reserve → 选正 delta 使 (7/2)·delta·(12^441−1)/11 小于 reserve → 一套共同 nested finite smooth refinement、tau/caps/正 cutoff → N threshold。Q13 的固定 tau BV 阈值符合其局部顺序；Q14 的每个连续父路径各自极限没有给出全 441 labels、全父族同一 refinement/阈值。
- 完整 enhanced same-rho buffered factorization、classical/descendant counts、adopted analytic seed、正切换叶，以及完整 root 的 continuous upperAmplitude 项仍未闭合。

现有 source-model 的 U3-tail 否定没有升级为原稿反例；同样，这些尚未构造的完整来源/质量/历史义务也不能被归为简单 namespace 问题。新增部分属 class2 局部省略推导已补源码，完整共同算术构造仍保留 class3 未完成风险，elaboration/API 为 class1 未验证。

**给 main.md 的建议**

当前 main.md:116 的 P 局部蓝叶保持原义；:117 的 descendant移动域、实际Theta与全部441代共同smooth realization 继续黄。可在 h34 下添加两个明确标注 source-only/uncompiled 的局部蓝叶：

- 原稿 enhanced/classical 根分流与独立 analytic-cover 门转换；真实 U3 classical-tail 初始 signed true-li AP 分量的同阈值 BV 供应。
- 同 Program 后代极限、active knot closed-strip 定位、带实际 ceiling/完整父权/Jacobian 的单 Buchstab w-pullback absolute L1 与局部预算。

完整 root count licence、native parent-Theta/normalized localBudget、immutable430 和共同 441 代实现继续黄。P5.6.eight_suppliers、完整 h34/hLower 及依赖它的 P6.3 不因本次变为完成；本组没有消除完整 hLower/hUpper 的终端前提。

**静态检查界限**

实际检查了上列新源的定义、符号、布尔方向、原子端点、母词/同 Q 语义、主要依赖 API，以及相关 Mathlib 的 division、floor、finite-product pooling、limits、indicator/integrability 和 integral API 源文本。所有检查均为只读源码/JSON/SHA256/行号核对。未执行任何 Lean 证明；M/O/P/K 等 intended-module 依赖仍存在未安装 source-only 路径。最终限定判定为：Q13/Q14 局部 SOURCE_REVIEW_PASS，完整 H430 链 HOLD。

