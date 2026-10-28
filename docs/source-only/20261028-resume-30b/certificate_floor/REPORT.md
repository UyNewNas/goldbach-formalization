# certificate_floor 第二批：ordinary上代理与同mask实际积分

交付两个闭合源码提案，均未编译，formal credit为0；第一批文件保持冻结。没有执行Lean/lake、大checker、整数total回放或额度查询。

- `P2HistoricalOrdinaryProxyIntegral.lean`：精确端点与真实moment、ordinary proxy至真实同mask积分的比较。
- `P2HistoricalOrdinaryProxySourceUpper.lean`：实际历史sf/log及I80 directed arithmetic至该proxy的上界绑定，保留完整ordinary max和crossing分支。

## 本轮实际证明链

在每个原始dependent `Row` 上定义原稿的
`r_B=R(t_r,u_r)`、`R_B=R(t_l,u_l)`、`M_B`、`M_{R,B}`、`f_l=log(s_l-1)/s_l`、`f_h=log(s_h-1)/s_h`。constant与chord两式均直接以Chen-quarter单位定义。若精确lower query低于2，则ordinary proxy取0。

最终源码定理 `checked_selected_ordinary_proxy_sandwich` 给出：

\[
\sum_{r:\mathrm{Row}}\frac{\operatorname{decode}_{Q80}
 (\mathrm{frozenSaved}(r)-\mathrm{defectCredit}(r))}{4}
\ \le\ \mathrm{selectedOrdinaryProxy}
\ \le\ \frac{\int_{\mathrm{selectedPairRegion}}K_{\mathrm{ordinary}}}{4}
\ \le\ \frac{\int_{\mathrm{selectedPairRegion}}
 (K_{\mathrm{ordinary}}+K_{\mathrm{guarded}\ h,\delta})}{4}.
\]

左侧要求每行 `fullSourceRowCheck r=true`，仅用于同一原始row的整数输出相等；右侧要求实际Wu source的 `0<δ≤1/10`。该链不使用 `storedTotalCheck`、整数total定理、数值proxy总和上界或bank endpoint licence。没有把完整saved numerator的正defect credit无声删除：左侧明确减去该credit，所绑定的是ordinary分量。

## 消去的证明义务

`row_residual_moment_integral` 把原稿封闭式 `M_{R,B}` 识别为真实 `R/(tu)` 迭代积分。`row_chord_coefficients_nonneg` 则实际积分 `(R_B-R)/(tu)` 与 `(R-r_B)/(tu)`，得到两个chord系数非负。由此，`row_chord_endpoint_lows_le_proxy` 证明将两历史lower endpoints替换为精确端点值的方向正确。

`actual_factor_eq_logFactor` 复用真实normalized lower factor的初始log公式。当前父512网格已能证明全部upper query≤4，因此足够使用该公式；本轮没有假定尚待数据绑定的selected-positive tighter 9/4结论。positive constant的积分比较来自真实lower factor单调性，positive chord来自其在[2,∞)的凹性。对于crossing cell，proxy0只与真实ordinary密度非负比较，没有断言整个真实cell积分为0。

第二文件复用现有 `parent_ordinaryRanges`、`parent_plane0_not_accepted` 和原parent chord divisor正性，把literal两plane max还原为原始descending分支；实际 `actualSf_contract` 与 `actualLog_row_contract` 供应具体算法的端点语义。`ordinaryRectangleBase_decodeLo_le`、`ordinaryRectangleChord_decodeLo_le` 保留全部I80向下舍入。两个真实非负moment系数允许将历史sf lower endpoints上推到精确log端点。strict crossing则由实际factor在≤2时为0及原chord guard给出saved ordinary≤0，原max0使上代理0适用。没有新增sf/log licence、floor不等式或积分上界假设。

最后用第一批冻结的half-open `pairCell`、ownership与Fubini，把同17572行ordinary实际积分求和转成同一个二维selected union。实际guarded Wu-h的非负性由现有source域定理证明，故可再接到第一批的完整ordinary+Wu-h union。这里使用的二维pair mask与extra gross四维fiber union保持明确对应各自定义。

## 原稿方向与剩余边界

原稿1143–1209的 `eq:current-floor-proxy` 上界控制的是历史saved lower estimate。精确constant/chord自身仍然位于真实ordinary积分之下。原稿也明确说proxy不是真实removed Y6 count的上界；本轮证明保持该方向，未发现新增原稿数学错误。

本轮普通分量的 `actual_saved_ordinary_le_proxy` 及其同mask实际积分比较已完成源码文本。完整literal-floor certificate仍然OPEN：

- 两个新文件与第一批source-only依赖链尚待编译专员安装、elaboration及kernel核验；没有声称正式接受。
- 原17572逐行source-output checks尚未执行。源码定理中用于读取frozen rows的检查前提是精确整数等式，不是目标实数估计。
- 全proxy还需单独的defect上代理 `H_B M_B/R_B`，并证明其exact closed-cell minimum与old outward-rounded lookup的包含方向；尤其保留knot两侧closed cells。
- 完整proxy总和低于λ的320-term Mercator/decimal interval计算、positive mask的9/4数据绑定、arithmetic enhanced-family识别及最终gain/c没有在本轮证明。

`REGISTRY.json` 给出两个候选和全部source-only导入的精确路径、namespace、安装映射及SHA256，并重读固定146个本地传递依赖。`complete_module=true`、`local_step_complete=true` 指本轮源码文本闭合；`task_complete=false` 保留原完整certificate口径，`compiled=false`、`formal_credit=0`。
