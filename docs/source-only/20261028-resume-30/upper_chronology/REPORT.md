# upper_chronology 源码交付

新增 `P4AOriginalCell0AffineChronology.lean`，245 行。未编译，正式验收信用为 0；文件文本闭合，分配的完整实际历史任务仍未全部完成。

这次消除了前任 slot16 单元必须另给完整 `CellGuard` 的证明义务。把 cell0 的原始 96 行全部解码：62 条旧子集 affine 行按原始 mask 顺序对应 `R - chosenOldPlane`，遗漏的 mask6 是精确恒等式；再从其余行推出严格顺序、激活、四个继承 cube 历史、W 与 descending winner、全部 full/selected-complement square 门槛、两端 residual。`literalRows_cellGuard` 因此从 literalRows 直接构造完整 CellGuard，不借用采样点、simplex 体积或最终结果。

`retainedLiteralCell0_slot16` 把这个结果接回真实的 all-eleven sixth ancestor 参数和先 seed7 后 cell0 的 slot16 定理。`literalRows_not_H3_first_failure` 则从同一 cell0 的 H3<D23 与 later H3 源码的 D23<H3 导出不相容，为后续29域的历史分离提供一个必要连接。这里 H3 first-failure 仅指原始比较历史，不冒称 Rosser 树的真实 first-exit。

原始 `HistoricalThirdCoarse.firstStop` 始终保留为 Prop；新增选中域要求其真实 coarse-label stop，并用已有 rank≤8 splice 身份保留早先 policy 决策。我们没有从 open affine 导航凭空推出离散 prime carrier，也没有从 `rawSixthEnvelope=R` 推出实际 cap 等于 R。`CurrentParentGuard` 和实际 prefix 的 firstStop/admission 仍需原父树供应。

静态审阅另以精确 Fraction 系数逐一比对了源码中62个 row index 与 gap-row 公式，全部相符。此为小型文本系数审阅，不是 Lean、证书 checker 或数值 replay。对 `fin_cases`/`decide` 的展开资源与 tactic/API 的可编译性未作运行判断，按用户分工交由编译专员处理。

未发现原稿新的数学缺口。尚欠真实 half-open carrier/等号墙分配、实际 parent guard、其余13 ascending cells及完整58/87 policy、same-rho密度/K衔接。精确源码与依赖 SHA、安装/import 对应和边界均在 REGISTRY.json。
