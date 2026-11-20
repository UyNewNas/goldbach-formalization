# P5 literal-li 公共接口：原证明的最小可见性后像

本包只将既有 `literalScale_limit` 的 `private ` 修饰删除。没有新增定理或复制证明到另一条声明。后像是原模块完整源文件，供 ROOT 安装/编译；原 dirty worktree 和所有旧 freeze 保持未写。未运行 Lean/Lake/LSP/kernel、项目 helper 或 fixture；没有编译收据，formal/green credit 均为 0。本作者冻结不是独立审查或编译通过声明。

## 真实需求及边界

本人读取当前 `1_+_1.748_lean_proofs/main.md` 第472/484/488行：P5和P5.6仍黄，h34的U3+U4组合接口为蓝；所需的是给尚欠实际供应保留可调用的纯标量归一化接口，不是重做h34。读时main SHA为 `1cd7cd90ea69c4e91e0c515679bda0a56cc40c935a2fa5eeb8b731adc4dce5c6`；ROOT确认其与早期6b098...差异来自获授权的R4终态追加，非本任务写入。

原稿 `chen-imbalanced-semiprimes/paper/source/manuscript-body.tex:507–558` 保留同一rho的density `C_N/log N`及 `T≤X S_N+errors`；795–817保留 `4 li(N)`、physical N、同一Q、实际alpha且不复位为2。既有 `Part5OriginalH430W1PriceLower.thetaConversion_lower` 给出的基价是 `4*li₀(N)*C_N/N`，不是 `4*C_N/log N` 的精确恒等式。因此后续与density尺度比较需要 `li₀(N)*log N/N → 1`。本包只暴露该已有的 scalar bridge，不新增组合消费者。

PriceLower源身份仍为3498 B / SHA256 `09a535f1efe9685e4a99cc3860b83fd5e8d375850e28cca1d1025b06e0cf85ae`。ROOT提供的公开source60完整ref为 `68fa8ad820b16f94b960d55fd484a2f555a47278`，初始消息 `e68fa` 是误写；不移签价格，也不重证它。

## 有界去重与远端核对

本人已检索 continuation 和 github-sources 归档相关Lean文本中的 `literalScale_limit`、literalScale声明、literal/logarithmicIntegral归一化极限，另核相关P2/CurrentChen normalization表达。该范围内只找到原RootIntervalTheta的private声明及其209行内部调用。公共 `ImbalancedChen.tendsto_currentChen_trueLi_normalized` 是trueLi而非literalLi；公共 `P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add` 是准确常数平移；公共 `tendsto_literalLi_nat_atTop` 只给发散；公共 `uniform_trueTheta_relative_error` 给normalizer相对误差，均不能直接充当本标量首项公共声明。旧T08去重报告同样记录public_alias_found=false。

远端 GitHub code search 两条查询 `repo:UyNewNas/goldbach-formalization literalScale_limit`、`repo:UyNewNas/goldbach-formalization Tendsto logarithmicIntegral` 均返回total_count=0且incomplete_results=true，因此不据此断言全仓不存在。默认branch及旧topic-ref猜测path的404也不作不存在证据。

随后按ROOT提供实际source ref精确读取：`c5f3d76641429830e38093c384e90636fa1a3d18:docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/Part5OriginalH430RootIntervalTheta.lean:150–175` 返回blob `28ae6ccaa118cab66261be32d10058982f1c7a47`，确认仍为同一个private声明，定义与证明正文一致。另精确读取 `31cce275f72b0dd8d91366dcb47ac0ef8260652f:ImbalancedChen/CurrentChenTrueLiNormalization.lean:128–160` 返回blob `983c8e26799558adea0a1e632dc95447e611539a`，确认公共供应只为trueLi首项。`PUBLICATION_SOURCE_INDEX.json:793–803` 将原源定位到publication commit `50f7994e165c1f720e6b55f5669730f32f109a62`、同branch/path/blob/20929B/cc3ef5...。这是有界查重与精确定位，不宣称全import cone或全仓所有可能等价定理的完备证明。

## 精确 before/after

原路径：`goldbach-proof-continuation/docs/source-only/20261110-yellow-closure-10t/t07_h34_actual_counts/Part5OriginalH430RootIntervalTheta.lean`。

- before：20929 B，SHA256 `cc3ef5f1c7d692d1b062ffb0c2738bf9f43edd87ce98918900367ecec39e6833`。
- after：本目录 `Part5OriginalH430RootIntervalTheta.lean`，20921 B，SHA256 `b0580c827fa840432f04c617c1ea7db13fbbfeddecf38f3d945047d2646a08c6`。
- 唯一改变：158行、零基byte offset7409删除ASCII `private ` 八字节。其余字节逐字一致，保留7个imports、31条文本层def/theorem声明、原namespace、原声明头其余部分、完整原proof及内部209行调用。

```diff
-private theorem literalScale_limit : Tendsto literalScale atTop (𝓝 1) := by
+theorem literalScale_limit : Tendsto literalScale atTop (𝓝 1) := by
```

待编译后的预定公共名为 `ImbalancedChen.Part5OriginalH430RootIntervalTheta.literalScale_limit`，类型仍 `Tendsto literalScale atTop (𝓝 1)`，没有参数/额外前提。`literalScale (N : ℕ) := logarithmicIntegral N * Real.log N / (N : ℝ)` 原封不动。完整postimage按旧registry stage-as为 `ImbalancedChen/Part5OriginalH430RootIntervalTheta.lean`；ROOT须保持相应import解析环境，不能从旧private生成物继承新public名的编译证书。

原证明逐项保留：Nat目标上 `log N/N→0`；从公共trueLi首项极限扣除 `(2/Real.log 2)*(Real.log N/(N:ℝ))`；以公共准确平移恒等式识别literalScale。没有用 `_private` 生成名，没有把trueLi或trueLi+2/log2偷换成literalLi，没有新增PNT或积分证明。

旧reuse freeze本人复核SHA仍为 `257cba3dc5af5b6f007e56651d74c64985dc3569b60e7773c1834e76ded0a802`。旧独审 `PASS_EXACT_NARROW_SOURCE` 仅适用旧cc3ef5...预像，不移签此后像；新源必须独立审查与后续外部编译。

## 保留的h34供给缺口

该极限只有epsilon先于N的纯标量共同阈值；它对Nat成立，不引入d/Q/label依赖阈值，不更换physical N。没有新导出epsilon阈值定理或数值N0。

同rho实际density与signed Delta、actual selected-history/positive atlas到获准PP源族的实例、coprime与small-prime误差、全PP、relative own-Theta、整族聚合及全部标签/owner/实际alpha/Q绑定仍待。全Member proper/equality/inherit质量、ordinary append整份rejectedChild、W1/W2端点/repeat/selected异常、bank/base/seed许可、h34、原430/并列441共同realization及hLower/P5.6仍不因本接口暴露而完成。未添加这些目标形前提，未改变main颜色。

精确身份和检查结果见 `IDENTITY_AUDIT.json`；唯一源码diff见 `EXACT_CHANGE.diff`。
