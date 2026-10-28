# certificate_floor 第六批F：同mask fibre/floor与Δ8源endpoint连接

交付两份完整source-only文件，共313行，及REGISTRY。`local_step_complete=true`；完整F派发目标仍未闭合，`batch_target_complete=false`、`batch_target_source_complete=false`、`task_complete=false`。没有把目标缩成常数叶子后标完成。未编译、未运行checker/replay/有限decision，formal credit为0。

## 冻结与原稿

已重新读取E独立review并重核三件最终raw SHA：Lean `b280219d899be2eb8cca23348af8fdccd41e24783e06cd01ffca300adaa54b2a`，REGISTRY `ca37bbe842160f3a63eedee1ed17dc32f9872c4ea3d82198338824e46627ab67`，REPORT `e34b30e4698904d4b30be2b66da3eada0bb9fd3c7473fea124a9b7361fda41b8`。E和所有前批保持冻结。

原稿锚点是1000–1120的同17572 mask/extra fibre，1121–1217的完整saved floor与λ，1219–1307的Δ、两个Δ/8、R/B/current-c/slack，以及972–998的原baseline和两个旧reserve。

## 新增实际对象连接

`P2ActualSameMaskFloorFibreAccounting.lean` 使用E的原literal payload/source-output witness，定义原完整stored loss与其ordinary、positive defect两分量。`actual_stored_loss_components` 保留完整分解；`actual_ordinary_proxy_chain` 明确给出

\[
\mathrm{storedLoss}-\mathrm{defectLoss}
=\mathrm{ordinaryStoredLoss}
\le\mathrm{ordinaryProxy}
\le\mathrm{trueOrdinaryIntegral}/4.
\]

完整stored loss另由既有完整proxy及D原320-term evaluator得到 `<λ`。没有把它当作true removed count的上界，没有移除正defect后仍冒称完整numerator。

四维extra fibre与二维floor cell都读取同一原dependent Row。`same_row_cutoff` 保留原 `min(u_l,3(1−t_r−u_r)/13)`；`same_row_fibre_projects` 和其union版证明每个真实fibre点投影到同owner的floor pair cell。它没有把不同维数区域等同，也没有建立尚缺的历史算术parent字典。

实际extra gain直接复用 `P2SemanticGainSetIntegral.unionSemanticIntegral`：真实omega减half、原K/4权和三角w变量上端。既有四维Fubini、原constant extra-fibre certificate及safe g下界被复用；本轮没有再生成或执行数值证书。`actual_extra_eq_new_minus_old_half` 保留真正new−old半基线的差，不把同一个分量的两个替代估计相加。

于是新的实际局部源项

\[
\mathrm{actualIncrement}=
\mathrm{actualExtraFibreGain}+
(\mathrm{oldSavedPayment}-\mathrm{actualStoredLoss})
\]

严格大于原Δ=`37237/62500000`。这个不等式来自真实gain≥g与真实stored estimator `<λ`，没有把final gain作为前提。old payment在原baseline continuation和replacement中精确抵消；E0、E1旧crop各保留一次，没有重复/新增1/4或permutation factor。

对原savedL6构造的retained frozen endpoint，证明它高于原 `savedL6−4λ` 的literal endpoint。这里的whole savedL6仍是已有原历史端点；没有将它识别成corrected ordinary sixth、真实增强count或actual Chen mean。

## Δ8与current-c链

`P2ActualSameMaskDelta8Endpoint.lean` 使用已有 `P5OriginalCoefficientArithmetic` 的原Δ、baselineReserve、eachReserve和endpoint数值，证明原recovery=`37209/10^9`、每个extra reserve=`37237/500000000`、booked net=`111711/250000000=3Δ/4`。这些是小型精确代数，未重复任何17572-row或320-term有限数值提案。

`exists_positive_collar_net_room` 消费已有真实collar loss趋零定理，构造δ>0，使真实extra Buchstab gain损失≤一个Δ/8。对已经缩过的gain，源码只再减**剩余一个**Δ/8；如果再减两个会重复支付collar。两个原baseline reserves仍各保留一次。

`refinedSourceEndpoint` 将原baseline端点ledger加上上述实际局部fibre/loss源项。它严格超过原adopted reconstruction；原R/B/currentC/slack链由既有精确endpoint定理接上。原slack大于`49061/10^13=4.9061·10^-9`，`exists_positive_collar_currentC_endpoint_room` 在实际collar后保留这个源endpoint余量。

这不是D12/count定理：原 `P5OriginalCoefficientArithmetic` 本身明确只是rational endpoint reconstruction，尚未把baseline绑定到actual lower Chen mean。本轮也未将余下booked allowance伪装成已证明的compiler或算术wall成本。

## 完整F目标仍缺什么

- 真正历史positive-parent/PP family与同mask四维fibre的算术injection/ownership仍缺；projection到floor pair cell不供应该事实。internal K/PP没有被移出内部工作。
- lower_functional F明确使用n48 `SourceRow(term,ix,iy,iz,iw,method,floorQ)`，不是17572 paired `FullMask.Row`；它尚未导出逐17572 row至真实n48 parent/query字典。本轮没有按名称互认mask/parent。
- certificate_enhanced F的frozen-receiver Phi/Buchstab countstate不自动供应全部h248 endpoint licences或本任务parent/完整reserve支付；没有导入其后继finalgain结论。
- 本轮只支付真实连续collar的integral loss，不供应完整common finite approximation、arithmetic modulus-wall、compilation/smoothing费用界。continuous thin-wall volume没有冒充算术附着支付。
- baseline/adopted rational端点仍需actual同Q/同policy lower mean/count语义。h248解析/seed/184+64动作soundness、signed child correction、netgain/currentc作为实际算术结论仍OPEN。
- E源输出、D320-term aggregate以及既有extra-fibre finite checker bodies全部仍未执行；本轮没有新数值通过或内核接受声称。

REGISTRY固定两新候选、八份冻结source-only前驱和338个按精确import路径读取的生产source raw SHA/namespace，列出所有当前未解决的完整F义务。未发现可据此证明的新原稿数学错误；上述均为明确实现/语义绑定缺口。
