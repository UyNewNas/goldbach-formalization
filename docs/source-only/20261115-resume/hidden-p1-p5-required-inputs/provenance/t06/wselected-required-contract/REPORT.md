# P5OriginalWSelectedAtomFamily：原源定位与实际接口

结论是 **旧实现存在，local exact locator 已解决**。缺项来自默认搜索忽略的 `.lake` 目录，不是已经证实的缺证明。原模块为 `ImbalancedChen.P5OriginalWSelectedAtomFamily`，namespace 为 `ImbalancedChen.P5Z.OriginalWSelectedAtomFamily`。

原冻结源位于：

`goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-LocalGlue-Phase8/frozen/8214b2f59ce68b5f4e2b4d4930eba0cbd420a57d6667cd18561ea140e3695619/P5OriginalWSelectedAtomFamily.lean`

该件为 **9001 B**，SHA256 **8214b2f59ce68b5f4e2b4d4930eba0cbd420a57d6667cd18561ea140e3695619**，按本地原字节计算的 Git blob 为 **45aaabd51c2479a82ba0cc7d617d452c3d13b183**。同目录 draft 与该 frozen 件同字节。此 blob 是内容身份，不冒称已经发布到某个远程 commit。

它不是按文件名猜出的替代品。原 UniformCutoff 的 `LocalGlue-Phase12/registry.json`（SHA `8475a62d…`）在 `exact_dependency_preimage_guards` 精确指定该 Phase8 SHA；原 cutoff 源为 `80344489…`，现有 `b6079159` repaired 版本为 `d8492698…`，import 与此消费者均保留。已存 cohort04 coefficient inventory `d13dec43…` 第 1933 行还独立记录这个同一 Phase8 frozen API。该来源链是原作者依赖固定记录；当前 P1/T05 AL 签的是直接 MiddleTensor 与 repaired cutoff，并未因此替未定位的完整传递依赖完成验收。

原标签完整保留：Phase8 `complete_module=true`、`ready_to_install=false`、`compiled=false`、`formal_credit=0`。本轮只给 ROOT 原字节归档候选；没有复制或安装 Lean 源，没有修改 import、旧 proof 或旧 freeze。

`API_EXTRACTS.md` 收录两个必需声明的完整原类型、原 namespace/open、finite-key/atom 定义值、26 个原对象定义摘录和 repaired cutoff 第 309–394 行实际消费者。这里没有新的定义或 lemma。

第一个精确接口是 `OriginalWSelectedAtomFamily.selected_W_family_common_threshold`（原第 95 行）。固定 n、eta>0、c>0、0<z≤1/128、z≤ellMax(n,eta)/512、0≤kappa0≤z 后，先给一个 N0，再任取 selectedWCells 中的 J、N≥N0 和 x≥c N^(1−kappa0)，同时得到：

```text
N^(1−2δ_J)     ≤ x^(1−3z)
N^(2−2δ_J)     ≤ x^(2−3z)
N^(2−39δ_J/16) ≤ x^(2−3z)
```

这是原有限银行的统一阈值。源码从 `ellMax≤cellDelta/2` 和 `z≤ellMax/512` 导出 `1024z≤cellDelta`，调用 Phase3 的既有幂余量定理，再以 `Finset.sup` 合并各 J 的 N0。没有按 N、mark、U 或误差符号重选阈值。

cutoff 第 359 行取 `c=1/(2*256^K)`，第 363–380 行从同一原 HB Group list 的 rank≤K、smooth trim 与分组互补窗口得到 x 的上述下界，第 386 行才在原 owner J 上消费统一付款。第 387–390 行用原 `selectedPolicy=wPolicy` 把 cellDelta 精确改写为同一 `delta wPolicy (ownerBox n N t) eta`。因此第 392 行所需的 hpay1–3 已由真实 chart 几何与固定银行提供，并非额外塞入一个目标估计。

第二个接口是 `OriginalWSelectedAtomFamily.active_W_mark_in_selected_atom`（原第 127 行）。前提保持原 jointNearCap ordinaryTuples、实际 selectedPolicy=wPolicy、实际 rowSupport、同一 `jointPresievedSigma(...,fullPrefix t*r)≠0`、固定 common-beta budget，以及明确的 local-x/A 窗口和上述三项付款。输出实际 WAtomKey、e,d、canonicalSlots 和原 occurrence map，使：

- owner 与 key 的 J 逐字相同，rough rank 等于 key 的有界 rank，实际 log tuple 位于同一 half-open fine cell；
- a,b,c 是 `atomGroups` 给出的同一三份 label 列表在实际 occurrence 上的乘积，只有 group 3 再乘原 beta 整数 e；
- `a*b*c=fullPrefix t*r`，且得到全部四条 `NumericGates N x U ... (z/2000)`。

本轮将该输出的 `∃ key ... NumericGates` 与 repaired cutoff 第 336–356 行作空白规整后的全文比较，结果相同。原 source 调 Phase7 `active_W_mark_fixed_four_M` 的加强冻结版本 `267c054f…`，消费 rough-rank、r=e*d 与 fine-cell 成员字段，再构造有限 key。另一冻结 `0911aad8…` 没有这些字段，不能为当前接口接线；没有选它。Phase5/6 也严格沿原 author guards 的 `afba3abd… / 6b5143dd…`，不是选择看起来较新的目录。

原对象规格有四个不能省略的区别。selectedWCells 是原 selectedCells 按实际 `boxPolicy(gridBox n J)=wPolicy` 过滤；不是任意兼容 W 类。原系数是 `OriginalJointPresievedCompiler.jointPresievedSigma`，其定义在 actual jointMarks 的同模数 fibre 上求原 rowCoefficient 和；不能默认为旧 all-prime native sigma。canonicalSlots 的参数仍是物理目标 N、cap=ceil(Z(atomOwner key,eta,N))、w=N^(nu0*epsilon²) 和同一 Z。独立 test HB words/groups 与系数标记 t 始终分开；不能把 t 当作 test tuple，也不能因为 singleton 根在另一条纯 cutoff 应用里使用 cap 2N，就把此 selected-W 分支的 N 改名成 2N。

padding/mesh 也都来自已有实际定义：`paddedOwnerCorner=B.hi+endpointPadding(wPolicy,B,eta)`；`roughMeshPrecision=ceil(((rankBound)+3)*(59/250)/ellMax)`，在 N 与 mark 之前固定。atomGroups 对原 `wGroups` 喂入这些整盒上端点与 HB query A，完成的是 whole-box endpoint W run。它允许依赖 N 和 A，正如原稿允许按 atom、T 与 HB length 变化；固定 key/N/A 后不依赖该盒中哪个算术 tuple 或误差符号。粗细网格边界没有因归档而被删去。

原稿对应关系固定在既有 `9731290e…` 文本：
`distribution-prime-product-completion-20261010.txt:25–49` 要求实际 test W 与同一 rho；第 72–117 行给原 trim、psi、HB chart 与 local x；第 119–149 行给同系数、固定有限 tensor/分组。原 `distribution-coefficient-completion-20261010.txt:171–184` 的 W 三容量与首次溢出算法按 endpoint 每 atom/HB length 运行；第 254–274 行规定 beta 只附 group 3、原局部余量及有限银行之后的共同阈值。Phase8 的数学步骤已有源码，不应重新实现为一个 conditional wrapper。

最小尚未进入当前公开源树的内部段为七源，均是原冻结字节：
 
| Phase | 模块尾名 | Bytes | SHA256 前缀 | 原 complete_module |
|---|---|---:|---|---|
| 2 | P5OriginalWWholeBoxRealRun | 10870 | `94bfdcb284bda457…` | false |
| 3 | P5OriginalWWholeBoxEndpointMonomials | 19345 | `c9254b88c1b1bc19…` | true |
| 4 | P5OriginalWCanonicalMeshEndpoint | 6810 | `3392052f78327192…` | false |
| 5 | P5OriginalWOwnerOccurrenceBinding | 9193 | `afba3abd7c510a11…` | false |
| 6 | P5OriginalWFixedMeshBudgets | 10796 | `6b5143dd5d3085df…` | false |
| 7 | P5OriginalWActiveMarkFixedMedium | 9302 | `267c054f1a780183…` | true |
| 8 | P5OriginalWSelectedAtomFamily | 9001 | `8214b2f59ce68b5f…` | true |

`LOCATOR_MANIFEST.json` 给七源的完整相对原路径、bytes、SHA256、blob、各原 registry hash、原标签和 import。Phase8 直接 import Phase7；该段逐步回接 Phase2–6。共有 11 个直接外部模块，连同原 guards 的另外四件，15 个边界源均在真正 bare mirror `goldbach-proof-github-sync-20261110.git` 的 `31cce275f72b0dd8d91366dcb47ac0ef8260652f` installed tree 找到；其 blob 与本地原 guard 字节全部相同。故这十五件应复用已有公开 pin。本轮对七个内部模块的 exact installed paths 及 `docs/source-only` 精确 basename 搜索没有命中；没有由 working repo 的 untracked 状态推断远端缺源。这个七源集合是相对于已确认边界的最小归档段，不是全递归闭包。

较早 Phase2/4/5/6 的原 registry 仍为 complete_module=false，描述当时尚待后继组合的数学接口；Phase3/7/8 给出了相应后继源码。不能把旧日志中的“当时缺”当成今天缺 code，也不能静默改掉这些历史标签。七件全都 ready=false、compiled=false；归档这批证据不授予安装或 kernel 信用。

还有明确的表达验收事项。Phase7/8 及 cutoff 使用短名 `jointPresievedSigma`，这些文件自身的 open 列表未显式打开其唯一定义 namespace `OriginalJointPresievedCompiler`。本包记录完全限定名与原定义；未运行 Lean，故这是待逐文件 namespace/implicit-generalization 检查的静态表达风险，不能伪称编译已失败或已通过，更不能以抽象函数替换真实系数来绕过。归档候选必须保持原字节；若后续确认需要补限定名，应另做有精确原像的表达修复审查。

真实未闭的上层输入也保留：Phase12 原登记明示一般独立 test `W_N(u)` 的实际 constructor/equality/support 与 htrim 绑定，所需 signed local M、辅助 SW、rough wall/face、collision/scalar/mean 和最终 PP 并未由本 atom 分类定理全部提供。该边界不取消已经签审的实际 singleton roughPrimeReserve 精确零项；也不能借该零项反向宣布一般 selected-W PP 已闭合。本轮没有发现需要新造“所求 W 前提”来补这两个具名接口的理由。

此新包只更新上一 `p1-validation-selection` 中 WSelected locator 尚未定位这一历史记录。原 `180097e0…` 与 `3a024532…` freeze 均未修改。全部工作限于本地源码/元数据读取和本目录证据文档；没有 Lean/Lake/LSP、项目 helper、额度、Git/GH 写、artifact 下载或新 proof。

