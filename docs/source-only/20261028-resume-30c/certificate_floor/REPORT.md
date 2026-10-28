# certificate_floor 第三批：H_B闭cell minimum及完整floor proxy

交付 `P2HistoricalDefectClosedProxy.lean` 和 `P2HistoricalFullFloorProxyChain.lean`，共455行完整source-only源码。没有编译、Lean/lake调用、大型checker、source producer、h迭代或数值积分回放，也未检查额度。第一、二批保持冻结；formal credit为0。

## 实际H_B对象与源数据

本轮直接使用实际 `bankLowerTable` 的200个原始h248整数。已定向读取原JSON：
`tmp/publication-20261010/verification-renewal-v2/data/expanded-w2-midpoint-table248-v1.json`，SHA256为 `a91c371b8c69398619ebee8b17598c163fbf8b6267fa0470ed6930e2097a98ed`。其 `fixed_point_denominator` 正是Q80的整数值，`grid_denominator=50`，`h_cell_lower_numerators` 的200个字符串与既有Lean `bankLowerNumerators` 逐token一致。该项是静态文字核对，没有运行原表生成算法；没有新增kernel-verified JSON parser的声称。

`rowHB` 定义为这些实际closed-cell值与精确 `[s_l,s_h]` 相交部分的minimum，再按原Q80解码。每个网格cell是闭区间
`[1+k/50, 1+(k+1)/50]`；精确start保留 `ceil((s_l-1)*50)-1`，stop保留 `floor((s_h-1)*50)`，并截到0…199。

## 本轮消去的义务

`exact_indices_iff_closed_meeting` 证明start/stop选择当且仅当真实两个闭区间相交，`exact_knot_both_cells` 明确证明singleton knot同时选中k−1和k。`exact_slice_subset_outward` 使用实际I80解码端点的outward包含关系，证明每个精确meeting cell也属于旧lookup slice；因此 `outward_min_le_exact_min` 给出正确方向 old minimum≤H_B。guard返回0的情况用实际bank非负性处理，不要求bank的分析licence。

`rowHB_zero_of_two_mem` 另外保留s=2时的preceding cell49；该实际bank项为0，故包含2的exact interval的H_B为0。strict crossing的saved输出上界则直接复用原producer guard零，不靠把真实crossing积分置零。

第二文件给出真实 `rowDefectRaw` 算式，复用actual log backend的真实logmass enclosure，并从原parent residual证明Q80舍入后的point分母严格为正。`actual_defect_credit_le_proxy` 保留向下I80舍入与最后max0，证明

\[
\frac{\operatorname{decode}_{Q80}(\mathrm{rowDefectCredit})}{4}
\le \frac{H_B M_B}{R_B}
\]

于positive分支成立；strict crossing分支使用同源lookup零和proxy零。该saved-output上界不需要实际Wu-h的endpoint licences。

若另外提供原本明确的 `BankEndpointLicences δ`，exact minimum所含最后meeting cell的right endpoint覆盖精确s_h；该项原licence加实际h反单调性给出 `H_B≤h(δ,s_h)`。`rowDefectProxy_le_actual` 再复用真实guarded-h logmass积分比较。这是有明确原bank前提的分析方向，不能当成已经证明200项端点licences。

最后加回第二批普通constant/chord max-proxy。定理 `checked_full_proxy_sandwich` 对同一17572个dependent Rows给出：

\[
\sum_r\frac{\operatorname{decode}_{Q80}(\mathrm{frozenSavedRow}(r).savedQ80)}4
\ \le\ \mathrm{selectedFullProxy}
\ \le\ \frac{\mathrm{selectedUnionIntegral}(\delta)}4.
\]

完整saved numerator的正defect credit保留在左侧。左侧要求原逐行 `fullSourceRowCheck=true` 来绑定frozen输出，右侧额外要求 `0<δ≤1/10` 与原实际bank licences。两边都没有使用整数total检查或total witness，Chen因子只除一次4。右侧依旧是第一批证明的同selected pair-union真实 ordinary+guarded Wu-h 积分；没有声称proxy是真实removed Y6 count的上界。

## 边界和状态

原稿1178–1189的closed-cell H_B、knot双格、outward最小值方向及单独defect proxy是本轮对应步骤；普通部分对应 `eq:current-floor-proxy`。未发现新增原稿数学错误。剩余均明确保留：

- 两份源码及冻结source-only依赖尚待编译、elaboration和kernel核验。
- 17572项source-output整数检查尚未执行；静态h-bank token一致不等于这些输出checks已经通过。
- 实际h248的200-bank endpoint licences尚待证明，本轮分析方向继续把它们列作原始局部输入。
- 独立320项Mercator/decimal interval的完整proxy总和 `<λ`、算术enhanced-family识别、same-mask count绑定、net gain与current c均未完成。

`REGISTRY.json` 固定两新模块、三份冻结source-only前置模块、146个生产传递依赖以及实际h248 JSON的原始SHA256和安装映射。`complete_module=true`、`local_step_complete=true`、`batch_target_source_complete=true` 表示本轮下一连接的文本已闭合；按原完整certificate口径 `task_complete=false`，且 `compiled=false`、`formal_credit=0`。
