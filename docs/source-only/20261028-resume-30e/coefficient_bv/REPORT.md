# E：实际 ordinary 内盒的门消去与完整 q 三卷积

本交付为 source-only，未运行 Lean、lake、编译器或 checker，formal_credit=0。仅完成下面的窄步；原完整任务与 E 批完整目标均为 false。D 及更早批次未修改。

## 冻结源码

| 源码 | Raw SHA256 |
|---|---|
| P1ActualWGammaThirdBeta.lean | 86d4b57686ee69226b8f8c9c277b1f66310509f35455826a1008b702c57b7541 |
| P5ActualInnerMeshSeparatedGamma.lean | 72d901714e954dd054e2eb7037a2a948f6982227b92f0434f6e613ce8a02128b |

第一源为 9 个定理，第二源为 14 个定理。安装目标分别是 `ImbalancedChen/P1ActualWGammaThirdBeta.lean` 与 `ImbalancedChen/P5ActualInnerMeshSeparatedGamma.lean`。REGISTRY.json 记录实际直接 imports、原稿、独立供应源的 raw SHA 和继承安装清单；这里没有安装到 production。

D 冻结源 `P1ActualHighWWholeBoxNativeRegroup.lean` 的 SHA 仍为 `3b7bea263c59711712cf22ef93874113e7d91fa8cb7be9fe39d07f7d44b3beb4`，登记 SHA `eceedad57fa6729f9f898a15af4e38a515c046dc861958771ebf040096fd9fad`，报告 SHA `899c667281bbddd50567b494171549e4dfba1052e4fe7c154a59373f17f703fa`。

## 与原稿和独立对象的连接

已重读原稿 `manuscript-body.tex` 274–314 行的同 signed physical rho、完整模数、逐标签阶乘、β 唯一 small/rough 附着和固定整盒分组，以及 334–338 行的 medium / 合法低秩 BV / Brun 分工。原稿 SHA 为 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`。本交付不把四标记总模数当作 rank-one below-half BV 系数。

第二源直接消费 signed owner 的冻结 D 源 `P5All16FineMeshGateScalar.lean`（SHA `5b7584cc6c8557764f5836ed67fe2f18babb7d1090ef69fcb972d8ea64be910b`）。使用的是其独立定义的原 meshPrimeAlphabet / meshPrimeBox 及已证明的 `inner_mesh_box_original_gates`，没有增加“rho 在盒上常数”或“门一致”的目标假设。

证明链为：

1. 原 innerCells 的整盒门证书给出每个实际 tuple 的严格递降和原 `ordinaryRosserPrefixAdmissible false (N^ell)`。
2. Prime-factor dictionary 给出 `rawUpperGate (N^ell) ps.prod` 和真实 `μ(ps.prod)=(-1)^r`。重复素数未通过一个额外假设删去；严格递降在这条实际内盒分支中已经排除了它们。
3. `inner_list_actual_retained` 调用 production `ranked_word_product_retained` 的反向原树词典，证明每个内盒 tuple 的乘积确为实际保留 rough modulus。
4. `inner_list_actual_presieved_value` 调用独立原系数的 `presieved_coefficient_value` 和 `roughWeight_eq_moebius`，得到真实 `presievedCoefficient(e*ps.prod)=(-1)^r rawBetaWeight(e)`。原 residual level `N^ell` 与 common small level `B` 保持分离。
5. 原固定 endpoint `computedGroups` 只计算一次；`inner_signed_fixed_beta_three_groups` 在已消去门的真实原盒上作精确 Cartesian regroup。
6. `attachedGamma` 把按总 residual rank 固定的原 rawBetaWeight 仅附着第三组。实际 rough alphabet 给出 `w`-rough support，原 small 支持给出严格 `w`-small support，唯一 small/rough factorization 证明每个占据整数只有一个 e,d 来源。`attachedGamma_abs_le_one` 对所有整数成立，没有 `card(actualSmallRosserSupport)`。
7. 最终 `actual_ordinary_inner_source_three_convolution` 从独立实际系数的显示内盒线性型出发，输出三个分别只依赖 a、b、q3 的系数。测试仅为 `F(prefix*(a*b*q3))`，没有 rho 或门的 coupled product test。该等式对任意 F 成立，故同一 complete q 可用于原计数测试与精确 coprime-mean 测试。

这里的显示内盒线性型为 `sum_e (1/M_res) sum_ps presievedCoefficient(e*prod ps) F(prefix*(e*prod ps))`。它不是通过把独立原系数重新定义为候选张量而得到。外部 all16 marked coefficients 尚未由本源重构；这一点不隐藏在 F 中。

## 标量和旧 W4 的精确边界

第二源当前使用已有的 **总 slot 数阶乘** 归一化：每组 gamma 的分母为该组长度的 factorial；外标量字面保留 `(-1)^r K1! K2! K3! / M_res`。这给出合法精确恒等式与逐整数一界，但没有声称已经得到原稿更紧的逐标签 `M1 M2 M3/M_all` 标量预算。Marked multiplicities 不被重置；它们仍须由外部真实源字典与 signed owner 的标量消费统一恢复。

第一源为旧 W4 的独立算术附着接口：实际 fine word 的 normalized Mobius gamma、实际 small Rosser β、第三组唯一分解一界及精确 `q=e*(a*b*d)` 求和。其 `row4_right_rough_endpoints` 从 D 已证明的真实 row4 occurrence permutation 继承 rough 下端点。该源没有断言旧 compact W4 的 native rho 已等于这些独立 gamma，也没有把旧 coupled rho 测试传给 medium。

已读 E physical constructor（SHA `b677d48c44fb943caaa386e314bd9870a7429045959afb0ff653208f7417361c`）与 signed E 内项加显式 wall 重构源（SHA `7022118821da530bdcd66a0d83b820a9b246ae251b212fa27e45a229d8b082de`），两者均未作为 imports。没有把 NEW ordinary all16、旧 compact W4 和 E common-refined physical policy 按名字认作同一 rho。

## 下一必要连接与仍未完成的目标

- 把 signed E 的独立 `innerAtomLinear` / 实际 innerPairs，按总 rank、同 mesh word 和同 marked prefix，重构为本源显示的完整 Cartesian 内盒源。需要真实 canonical-word / fine-label 纤维与原 M_res 的双向精确词典，不能仅定义一个新 atlas。
- 对旧 compact W4 与 E common-refined 原策略证明自己的 literal causal gates 的整盒细分和真实源 map；普通 residual 上筛内盒的结论不能自动移植。
- 实现原逐标签 gamma 标量、完整 marked/small-beta 标量消费，并支付实际 wall / collision 余项。本源的第三组 β 一界可直接避免 small-support 计数损失，但不代替这些全局预算。
- 覆盖所有真实 winning branches，并接入各自 fixed whole-box 数值 monomial / capacity 和原 SW、medium / Brun primitive callers。当前精确有限恒等式本身不供应这些分析许可。

以上是明确的形式化连接缺口；本交付没有据此宣称发现原稿反例或取得完整估计。`local_step_complete=true`；`batch_target_source_complete=false`；`task_complete=false`；`compiled=false`；`formal_credit=0`。
