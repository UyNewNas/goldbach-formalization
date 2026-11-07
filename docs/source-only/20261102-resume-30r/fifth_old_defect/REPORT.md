# R04 / D02 — 原第五旧 Jensen/Taylor 分支的直接解析前置供应

**SOURCE ONLY；九份 Lean 均未编译；kernel_verified=false；formal_credit=0。D02 全目标仍 HOLD，`oldBranchDefectQ` 尚未收回。** 本轮提供原父 Jensen 的原始标量 floor 许可与全档 Q80 rounding 误差、Taylor 原十四项对数及实际 profile 导数界、实际有符号 Taylor kernel 到真实祖先 owner 积分的连接、原分支有限条件到真实 raw15+W 仿射结构等式的转换，以及实际仿射残差和完整 reciprocal-prime 权重的原导数界。没有证明完整原 stored old floor 的积分下界。

143 个新闭有限 bodies 均为 **UNEVALUATED**。已有数据、history、gates、stored-max、child-facts 等全部继承有限 bodies 同样未求值。没有运行 Lean/Lake/compiler、CI、finite guard、原数值程序或数值重放。只写本目录，没有修改旧文件、生产模块、作者 main.md 或 Git，也未派生子代理。

## 原稿与原程序优先核对

读取 R/BRIEF、DISPATCH，Q/fifth_parent 的 REPORT、REGISTRY、四源和独立 q23 review，并搜索生产、全部 source-only 及 ignored/hidden `.lake/proof-continuation/source-reviews/drafts`。Q 的全档包络及 F/G/H 的完整 64-child 分解、真正 owner 可积性、原索引组装全部复用，不在本轮重写。

原主稿 `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:367–375` 保留真实祖先，连续替换，禁止重复收益。`../goldbach-research/fifth-prefix-subdivision-refinement.tex:113–134` 的整父界为 `max(J_P,T_P,Σ_C B_C)`；原 `certify_fifth_prefix_subdivision.py:160–176` 的 `old` 则先取原 Jensen floor 与已有 Taylor override 的最大值，再与完整 child sum 取最大值。因此

```
oldBranchDefectZ(i) = max(0, storedOldQ80(i) - childSumZ(i))
```

是一笔固定的未授权旧分支差额，不能用 `e→0`、`q→∞` 或“一次 floor 小于一个 ulp”消去。Q 的 all-ArchiveIndex 包络仍然扣这笔差额和 R05 独立处理的实际 `indexedActualReserve64`。

旧 Jensen 与 subdivision 并非同一个对数表达式。原 `certify_fifth_prefix_jensen.py:70–74` 将 grid、lo、hi 各乘 32，再调用 `certify_fifth_prefix_adaptive.py:124–138` 的 `exact_term`。后者使用 `2(y+y^3/(3(1-y^2)))`；已有 child directed-log 使用四项加 `1/9` tail。对旧 parent floor 不能直接改用 child 的更强表达式后声称保存值已认证。

Taylor 的原依据是 `fifth-prefix-taylor-pilot.tex` 的 smooth-box、完整带权 G、`1/24` midpoint 及导数段，和 `certify_fifth_prefix_taylor_pilot.py:16–19,39–94`。原程序先检查所有原 raw v 的单一 affine branch、old winner 全盒 dominance、new>old、真实参数 `2≤s_old<s_new≤4` 及 seams，之后才求导。`certify_fifth_prefix_taylor_full.py:23–40` 只在这些检查通过且有改进时替换旧 floor。主稿与原程序支持完整旧分支许可的数学路线；本轮没有发现原稿反例或坏档案行。

## 本轮九份源码的实际供应

1. `P5OriginalParentJensenDirectedLog.lean` 证明旧 parent 的 `1/3` upper tail，并精确比较已有 `1/9` upper tail。二者差为

   `4*(y^5/15+y^7/35+y^9/63)/(1-y^2) ≥ 0`。

   保留被减去的 old log 及其 `-e` 系数，得到原 `parentDirectedQ≤Q_b(e)`，并给原 numerator `2Y(3C²−2Y²)` 的展开等式与向下 Q80 rounding 的 signed scalar 许可。这里不假设 rational minorant 为正，也不把两个 tail 混为同一源值。

2. `P5OriginalParentJensenRawFields.lean` 直接读取原 `FifthWireRow.grid/lo/vertexGapSum/ratioA/ratioB`，独立转写 32-fold rescaled `exact_term` 的 H/C/Z/D、rn/rd、ln/ld、dn/dd、完整 numerator/denominator 和整数 Q80 quotient。它没有读取 child d/A/B，也没有把 `storedAt.oldQ80` 定义成新公式。`ParentScalarFacts` 仅包含实际 rational range、原整数正分母、rational expression identity 和 exact floor equality；没有实积分下界或 saved-old licence。

3. `P5OriginalParentJensenArchiveScalars.lean` 在现有 block000…block142 上给上述 `ParentScalarFacts` 的闭源码，并按已有 `rows_toList_order/block_order` 聚合到每个原 `ArchiveIndex`。未重转写数据、排序、去重或替换 mask。实际移除每行 scalar facts 输入后，`each_original_parent_Jensen_floor_le_Q` 把原 Jensen integer floor 接到其自己的 `parentBQ/parentEQ`。`all_original_Jensen_rounding_loss` 支付的是

   `0 ≤ Σ(original unrounded rational − original Jensen floor) ≤ 292633/2^80`。

   **此定理与固定 `oldBranchDefectQ` 是不同命题。它没有把旧 Jensen floor 接到父盒积分，更未支付 Taylor override。** 143 bodies 的大整数/rational reduction、资源与真假都未通过本次元数据工作确认。

4. `P5OriginalTaylorLogBounds.lean` 证明原 `log_bounds(x,m=14)` 的精确上尾 `2z^29/[29(1-z²)]`，没有改成现有 `RationalLogCertificate` 的无 `1/29` 粗尾。actual upper-gap 导数为 `(4/29)z^30/(1-z²)²`。`original_midpoint_lower` 保留完整 weight 和 new-lower/old-upper 两个不同符号，直接给原 Gmid 的下界。

5. `P5OriginalTaylorProfileDerivatives.lean` 在实际 `firstF/firstSlope/firstCurvature` 上复用已有导数和凹性，证明原 pilot 的

   `m1=(a/(a−1)−logLower14(a−1))/a²`，
   `m2=2/[a²(a−1)]+1/[a(a−1)²]`。

   它证明 `|f'|≤m1`、`|f''|≤m2`，以及真实 `f(s_new)−f(s_old)`、`f'(s_new)−f'(s_old)` 的 mean-value 界。`original_derivative_cancellation` 保留原

   `min(m1*(Dn+Do), m1*T+m2*delta*Do)`，

   没有丢掉两导数之间的相消。这部分是实际 profile 的解析供应；完整 weighted G 的五个 diagonal second derivatives 及其原 rational `M[i]` 实例还未在本轮闭合。

6. `P5OriginalTaylorActualSignedKernel.lean` 定义的 G 使用原 `rawCandidate 0 raw t` 与真实 raw15+W `rawFourth t`，含完整 reciprocal-prime weight。`originalTaylorSignedKernel_eq_literal` 在原 Taylor `[2,4]` range（包括等于 2）证明它等于已有 **signed** `literalRawKernel 0 raw`，分别保留新旧各自 strict own-cube gate，没有改成 positive-part kernel。

   `originalTaylorSignedKernel_le_actual_owner` 和 `originalTaylorIntegral_le_actual_owner` 对任意实际源 index 与其实际 `licensedOwners`，使用 O 的真实 `originalRows4/originalAdmission4`，由已证 one-sided old15 majorant 接到同 owner 的真实 `rawOwnerKernel/rawOwnerIntegral`。可积性从已有 literal 与 actual-owner 定理导出，primitive fourth geometry 从 `originalAdmission4_geometry` 导出；没有外加可积性、祖先 cap equality 或目标积分下界。Taylor `[2,4]` range 在实际 owner 上仍是待实例化的原始几何条件，不能推及所有 nonsmooth archive 行。

7. `P5OriginalTaylorAffineBranchBinding.lean` 复用生产 `P1OriginalFifthCorrelatedRawBoxGates` 的 `Affine5`、原 tent planes、signed difference 的 coefficient-sign exact lower 与 closed raw box，不重复这些旧证明。新增 `activeSide` 精确保留原 ascending-first 顺序和闭端点；`active_tent_eq_plane` 从原 raw lower/upper 的有理端点条件推出 `v=A/C`。`BranchFacts` 只包含实际新旧 mask 的 active 结果、所选旧项属于十五个非空 masks 或 W，以及原相减后 affine dominance/strict-gain 条件。

   `original_old_eq_selected_affine` 从这些 primitive 有限条件证明完整真实 `rawFourth` 等于所选 affine，`original_signed_kernel_eq_affine` 接到原完整带权 signed Taylor integrand。结构等式不再是假设；仍未将 `rawFourth` 等同真实动态祖先。**本源尚未为任一个实际 archive 行供应 `BranchFacts`，没有新增闭 finite body，也没有声称消掉实际 smooth-row 的几何输入。** 原保存值绑定、整盒积分与 fixed defect 仍在下述边界内。

8. `P5OriginalTaylorAffineRatioDerivatives.lean` 在实际 `Affine5.eval` 与 `Function.update` 坐标曲线上，证明原参数 `(level−sum5)/t5` 的一二阶导数，继而证明 pilot 原 `D/E/T` 公式。前四个坐标为 `a_i/t5` 与二阶零；末坐标为 `(a_5−s)/t5` 与 `−2s'/t5`。原 A/C/W 的 residual coefficients 非正由表达式直接推出；末坐标的 `D=(sMax−a_5)/lower5` 和 `T=(|a_n5−a_o5|+delta)/lower5` 均保留原相关参数差，没有拿独立 numerator 极值替代。结论仍需父盒的 primitive argument-range/gap 输入；没有以坐标导数界本身为前提。

9. `P5OriginalTaylorWeightDerivatives.lean` 把原 `originalTaylorWeight` 的实际坐标曲线写成 `C/x` 或 `C/x²`，证明 `w_i=−p_i*w/t_i` 与 `w_ii=p_i(p_i+1)*w/t_i²`，其中末坐标 `p=2`、其余 `p=1`。原正 lower box 直接给 `w≤wmax`、`|w_i|≤wmax*k_i`、`|w_ii|≤wmax*q_i`，使用完整 reciprocal-prime 权重。**本文件没有把这些 factor bounds 直接命名为完整 G 的 Hessian，也没有声称已有五维 Taylor 积分。**

## 精确剩余边界

- **原父 Jensen integral licence 仍缺。** 143 scalar bodies 并不证明 stored `vertexGapSum` 等于原父 32 个 `frozenGap(sourcePicks raw)` 的 vertex sum，也不证明原 parent A/B 对整个父盒的 ratio licence。必须把这两种原几何事实和 whole-parent Jensen/积分接通；已有 64-child 证书不能直接充当此 parent 证明。
- **原 Taylor integral licence 仍缺。** `active` 与 old-dominance → 实际 affine 结构的转换已有第七源；实际 affine ratio 和完整 weight 的坐标一二阶导数及原 D/E/T、k/q/wmax 由第八九源供应。实际 smooth-row 的 `BranchFacts`、原 vertex argument range/gap 实例仍未供应。尚需组合真正 chain/product rule 与完整 weighted G 的 `M[i]` bounds、原五维 midpoint `Σ h_i²M_i/24` 及 boundary/seam treatment。已有 K/u7_sharp `P5OriginalSignedMidpoint.midpoint_bounds` 可精确复用其一维 `1/24` Peano 公式；本轮没有重新证明它，也没有把一维结果直接称为五维积分许可。
- **保存值 structural binding 仍缺。** G 的真实 72-block `new=max(stored old,complete64)` body 不证明 `stored old=max(original Jensen,original available Taylor)` 的来源等式。新 `originalParentJensenFloorQ` 与 `storedAt.oldQ80` 保持独立，尚无把任一 saved field 自动替换成已解析表达式的 theorem。
- **完整 old-branch 支付仍缺。** 本轮没有证明 `Σ oldBranchDefectQ=0`、`<epsilon` 或给未扣旧债的全档 floor→actual integral。没有增加一个以该目标为前提的 generic consumer。Q 的 `full_original_stored_floor_envelope` 及 R05 的 child reserve scope 维持原样。
- 所有源仍需必要的 exact-source import staging、elaboration、Lean API 与 kernel 验证。143 新 bodies 与继承 closed bodies 均 UNEVALUATED；raw SHA 只标识实际文件，不能证明数据真实性或闭命题已被执行。

困难分类：原 scalar/log/derivative 省略为 **(2) 可补的数学推导及源表达转换**，本轮填入上述窄部分。父盒几何→积分、Taylor 完整五维许可和旧保存值来源仍是未完成的 **(2) 形式化供应**，不能仅称安装问题。具体 Lean API、有限 reduction 和 staging 为 **(1)**。没有取得 **(3) 实质原稿数学缺口** 的证据；未把模型限制、未执行、未写完或强程序审计升级为原稿反例。

## 静态交付和复用

本轮只进行源码/原稿阅读、生成定理文本、文本结构与 declaration/import 检索、JSON 解析和 raw SHA256/字节数登记。源码生成只按 000…142 生成有限 body 及分支引用，未解析 raw archive payload，也未计算其任何 floor、gate、saving 或总量。恢复时核对了实际文件；一次中断留下的零字节 SignedKernel 已在本槽恢复完整。第七至九源没有增加闭 finite body；九份是本次最终静态交付边界，更进一步的完整 Jensen/Taylor 许可留给下一项实际工作。

精确新源、direct-import 映射、原程序/原稿 pins、被复用 declarations 和本轮 declaration 行号见 `REGISTRY.json`。Q07 的 REGISTRY 保留完整原143 typed+72 stored pins，本轮链接并 pin 该 registry，不重复另造数据清单。完整 Q 的 envelope、G/H 的 owner assembly、O 原第四 geometry 与旧 firstF calculus 均是复用。

导航建议只增窄叶“原 parent Jensen 标量 floor / 全档 rounding，Taylor 原 log14+profile/ratio/weight 导数、条件性仿射结构转换与 signed actual-owner 桥（source-only）”。主 D02、未扣债 original fifth floor→actual total integral、完整87、All22、两笔 reserves 和最终物理 rho 均不应因本轮改为已完成。
