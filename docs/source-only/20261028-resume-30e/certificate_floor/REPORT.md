# certificate_floor 第五批：原17572行真实source-output等式

交付 `P2HistoricalFullSourceRowWitness.lean`（145行）与REGISTRY。本轮未编译、未执行source engine、checker、replay或任何有限decision；formal credit为0。

## 前驱冻结与原source核对

已重新读取第四批独立review的最终freeze条目，并对两Lean/REGISTRY/REPORT重做raw SHA，均与最终冻结一致：Mercator `5c271c04058ca473fbea6203131c415cead819ef00ae80a262e3511f437d8008`，FiniteCertificate `dd3151cf52b88cfda0d2e793fe8e6f01238f2bce89788cf251ebe3ac9e3dcc68`。前批字节没有修改。

已核原稿1121–1141及1143–1209，并定向读取原ordinary/point/log/pair producer。原caller为 `author.Ordinary(16384)`，其构造确为 `SieveTable(g,8)`；pair调用保留 `False,False`，没有将P112 weighted-node、真log或ordinary-only估计替换进历史程序。

原payload JSON `corpus-renewal-paired-certificate-v2-20261010.json` 的raw SHA为 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`，与既有RowsBinder导入注记一致。原caller及四个backend source文件的raw SHA均在REGISTRY，所有文件只读取/哈希，没有运行。

## 本轮source连接

`actualSf_exact_source` 显示真实sf就是原16384、maximum8的Q80 point程序。`actualLog_exact_source` 显示先做原 `I80.point q`，再分别取原 `logPoint(lo).lo` 与 `logPoint(hi).hi`。`actual_source_directed_formula` 展开现有导入的完整source输出，保留全部I80 directed rounding、两个eligible plane的逐次max、ordinary max0及单独defect lookup/max0。

该展开式没有引用frozen payload，payload仍是既有独立literal数组。本轮没有通过把等式两边都定义成新candidate来消除绑定。

`original_frozen_strip_lengths` 是186个原literal strip长度与原firstU宽度相等的闭合decision提案，明确保留totalized getD的数据边界。`stripSourceCheck` 对一个既有t-strip的全部dependent u-index检查原 `fullSourceRowCheck`，该检查同时比较原t/u key及完整saved ordinary+defect numerator。

`original_strip_source_checks` 只对原 `Fin 186` 做fin_cases，然后为每个原strip留下 `decide +kernel` 的完整闭合有限体。它没有crop u域、没有新输出表，也没有以目标source等式作调用前提。`original_fullSourceRowCheck_true` 将这些strip witness组装到原17572个Row，`original_frozen_source_fields` 与 `original_frozen_full_components` 导出同一row的完整源字段和ordinary/defect分解。

## 复用第四批的数值路线

后续只消费已冻结的independent320 evaluator与其aggregate proof proposal，不再证明analytic log。源码连接为

\[
\sum_r \operatorname{decode}_{Q80}(\mathrm{frozenSaved}(r))/4
=\sum_r \operatorname{decode}_{Q80}(\mathrm{actualSourceOutput}(r))/4
\le\mathrm{selectedFullProxy}
\le\mathrm{selectedProxyUpper}<\lambda.
\]

`original_stored_sum_lt_lambda` 消去第四批传递定理中的逐行check调用前提；`decoded_stored_integer_sum_eq` 与 `original_stored_integer_sum_lt_lambda` 给出相同原selected stored整数和的Q80/4形式。没有pasted display total、storedTotalCheck或新λ上界假设。完整saved numerator的正defect credit没有删除。

这里控制的是原saved lower-estimator数值。它不把该proxy当作true removed Y6 count的上界，也不需要借用enhanced的analytic action licences来伪造这样的解释。与lower_functional的联系仅为原Row/query数据；已按其请求提供冻结D纯Mercator primitive路径/hash，不导入后来的peer最终结论，避免循环。

## 未执行边界

新增的strip长度和186个strip/source-output有限体全部未执行，第四批的query/divisor和aggregate两个decision同样未执行。因此本轮没有取得已接受的17572项相等或数值`<λ`结果。原SieveTable状态规模及重复query可能需要编译专员做保留真source公式的sharing或更细chunking；没有性能/编译成功声称。

尚待用户指定编译专员核验全source-only链，执行所有有限证明体。实际h248 endpoint/action licences、same-Q/same-mask算术family/count绑定、net gain与current c仍OPEN。

REGISTRY固定本候选、七份冻结source-only前驱、146个生产传递依赖及原raw source路径/SHA/安装映射。`complete_module=true`、`local_step_complete=true`、`batch_target_source_complete=true` 只表明本轮文本闭合；按原完整目标保持 `task_complete=false`、`compiled=false`、`formal_credit=0`。
