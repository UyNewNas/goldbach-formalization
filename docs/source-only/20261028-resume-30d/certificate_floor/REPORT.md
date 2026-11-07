# certificate_floor 第四批：320-term directed-log及有限full-proxy证书

本轮交付两份完整source-only源码，共413行，以及REGISTRY。未运行Lean/lake、checker、数值replay、原producer或任何`decide +kernel`求值，未查额度；第三批和更早交付保持冻结，formal credit为0。

## 原稿与实际producer

已核原稿1191–1209和原文件
`tmp/publication-20261010/verification-renewal-v2/data/corpus-renewal-paired-independent-v2-20261010.py`，原始SHA256为 `521ed8e9ff82a06f9f6b4feedb853b0d9ada32e063056ab12c96f1994c915f51`。producer的scale是10^80，Mercator项数是320；先取even partial sum，再把下一个正项加到upper endpoint。logq仅在q>3/2时乘4/5并加回log(5/4)。

本轮只处理full floor proxy的四类log query：`t_r/t_l`、`u_r/u_l`、positive cell的`s_l−1`与`s_h−1`。它们在原selected rows上均落在[1,3/2]，所以此用途下原logq循环的shift数为0。该性质以新的闭合finite rational guard证明提案给出；没有把extra-gross/fibre所需的nonzero-shift分支混入本任务。

## 精确Mercator余项和directed节点

`P2IndependentMercator320.lean` 用有限paired polynomial证明：若y≥0，则

\[
S_{2n}(y)\le\log(1+y)\le S_{2n}(y)+\frac{y^{2n+1}}{2n+1}.
\]

证明先得到finite derivative的几何恒等式
`S'_{2n}(y)(1+y)=1−y^(2n)`。因此 `log(1+y)−S_{2n}` 与 `y^(2n+1)/(2n+1)−(log(1+y)−S_{2n})` 都从0单调增加。这里实际证明了原next-term remainder，保留1/(2n+1)，没有用未经证明的sharp tail，也没有改用atanh backend。

同文件以10^80定义decimal outward floor/ceil，证明point、带符号四corner multiplication、positive division和整数division的real enclosure语义。`loop_contains` 跟随原始power/total状态和奇偶符号逐步证明；`alternating_even_eq` 将320步状态识别为160对alternating项；`mercator_contains` 再用真实next-term enclosure得到actual `Real.log` 包含。

## 实际selected rows上的有限full-proxy

`P2IndependentFullProxyFiniteCertificate.lean` 原样保持普通constant/chord的maximum、真实signed residual moment、第三批exact closed-cell H_B、positive residual分母、strict crossing零分支和quarter units。每个乘除节点都按原decimal scale向外舍入，signed intermediate不需要假定非负。

`rowProxyInterval_contains` 将这些节点组合成原Row的真实 `rowFullProxy` enclosure。原sf/log/source integer checks没有替代这个independent backend；实际bank H_B与完整proxy定义复用前批冻结对象。

本轮另外写出两个**闭合但完全未求值**的有限证明提案：

- `all_original_row_guards`：直接在原17572个dependent Rows上以`decide +kernel`证明四类query的有理范围和point interval的正分母guards。它不包含目标proxy不等式。
- `original_selected_upper_lt_lambda`：对完整定义的decimal rational interval evaluator之upper endpoints求和，直接以`decide +kernel`比较原λ=`466977/200000000`。它没有导入旧display total或pasted aggregate token，没有将sum<λ列为前提。

`selectedFullProxy_le_directed_upper`、`selectedFullProxy_lt_lambda` 与 `checked_full_saved_sum_lt_lambda` 给出上述有限比较一旦内核接受之后的语义传递。最后一个仅保留原始每行 `fullSourceRowCheck=true` 来识别frozen numerator；不使用storedTotalCheck，也不需要bank endpoint licence来证明saved estimator的proxy上界。

## 当前状态与未完成项

两个`decide +kernel` body是编译专员待处理的源码证明义务。本轮没有执行它们，因而没有取得已接受的`selectedProxyUpper<λ`数值结果，也没有性能或可直接编译通过的声称。320-term decimal evaluator的finite reduction可能需要编译专员做保留表达式和证明语义的chunking/caching。

实际17572 source-output equalities、h248端点analysis licences、算术family/same-mask count绑定、net gain和current c仍OPEN。本轮upper-proxy数值路线继续只控制saved lower estimates；不能推出true removed Y6 count的上界。

`REGISTRY.json` 固定两新模块、五份冻结source-only前置模块、第三批四件交付、146个生产传递依赖及原independent producer的raw SHA和安装映射。`complete_module=true`、`local_step_complete=true`、`batch_target_source_complete=true` 表示源码文本闭合；`task_complete=false`、`compiled=false`、`formal_credit=0` 保留原完整目标和未经内核接受的边界。
