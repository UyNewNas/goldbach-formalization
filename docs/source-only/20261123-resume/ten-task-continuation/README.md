# 2026-11-23 稿内形式化续接

本包继续固定稿本 `paper/release-20261106/en` 内的实际对象形式化，接续 `47a617fd24a5076f3caa6440058a61c5e13aa75c`。当前稿本为 [chen-imbalanced-semiprimes@a988cba](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en)。生产源码基线仍为 `be3b6ef8f8459bf7ac2ba5a2f5e2cc9ed009cad8`；前轮 `900b3d4e` 与 `47a617fd` 的八份源码按已发表字节复用。

**交付状态：source-only。** 本轮没有执行 Lean、Lake、证明检查器、数值证书或 CI，完整传递闭包和内核验收仍待。新增源码不能据此增加绿色节点。原工程树仍为 **28 绿、242 蓝、29 黄、0 红**，颜色图例不计；H247 的 29 个分析端点是另一组义务，仍为 0/29。

本包含 **14 份新数学模块、9 份旧模块选版**，合计 23 份 Lean、4,336 行、237,531 字节。两组独立静态审查按最终源码逐项冻结；该审查层级与内核验收分别记录。

## 已接入的实际证明链

| 稿内部分 | 本包终端与解除的前提 | 保留范围 |
| --- | --- | --- |
| P4B 短头 medium | 四模块从实际完整模数余词核，经原频率积分、两组 HB 和全部实际 chart/补块恢复，接到 `mediumTotal` 及 `eventually_fixed_policy_RealB`。原子精度取 `A+54`，碰撞按原整纤维账支付一次。 | 余项明确保留长头、其余原词和未触及纤维。完整同一 `rho` 的 PP 与无条件 `hUpper` 仍待。 |
| U5 原 plateau 的短完整模数 | `P5OriginalU5PlateauPrimeBV` 在全原有序对族上，按各标签自身策略推前整数 `rho`，plateau 盒内共用根计划。用严格 primorial 的 gcd 和有序素数乘积单射恢复标签，取得 `abs rho ≤ 1` 并接原 prime BV 与投影下界。 | 只支付 `q ≤ floor(N^(9/20))`；盒外、长模数、prime/centre 费用及所有原 signed 余账保留。 |
| saving16 的 R17 第一角点 | `P2Saving16R17StrictFirstCorner.r17_strict_first_corner` 在原唯一一次网格选择上加任意正上限，给出严格 96 行、实际小因子、rank/trim/history 和两族整数平方。两笔旧计数始终使用同一 `k, beta, N0, Q, rho`。 | 第一角点之外、完整十四角、定量 signed PP 与数值端点许可证仍待。 |
| Wu 原窗口的一条严格上壁 | `uniform_indexed_upper_wall_error` 对任意实际旧槽 `p_j < V_j`，在所有动态框之前选共同阈值；域内损失为零，外漏至多 `epsilon/2 * Theta`，连同旧完整乘积内帽总误差至多 `epsilon * Theta`。 | 因子本身光滑，其余墙保持原 sharp mask。完整联合 smooth Family、其余墙、同一 `Q/rho` 的 PP 和 H247 均未由此闭合。 |
| P1 原 singleton 短头有符号单行 | 三模块复用两组付款的几何证明，处理 singleton 自己的真实 raised-action 分组与所有余词；任意精度的复 `signedError` 接到 source64 的 `HB scalar * occurrenceAtom`，以 `A+82` 支付真实单行恢复费用，给出 `eta H_N` 收据。 | 这是原 `products/free` 通道。长头、短头余词、完整模数后的 Fourier 尾以及外层 chart/HB、trim 和完整 PP 保留。 |
| h34 原 nonretained fixed rejected 历史账 | `Part5OriginalH430FixedRejectedWindows` 从实际 W1/W2 固定读取得到 child/common 截止方向，以真实首素因子半开窗给 rejected 全账分解；扣去窗口及 fresh 余账后，以原单次 431 加权预算付共同根壳，并按每根自己的正预算恢复原 R4 单位，接回原负四分之一。 | 正窗口、fresh rejected、非经典根及全 U4 等仍保留。431 是带 mark 的 zero-fresh LIST 预算，不是列表长度，也不表示 epsilon-small 或完整 h34。 |
| P3 稿面全纯规范与实际 Fourier 双行 | `printed_shell_eq` 与 `printed_cumulative_eq` 证明稿面 `1/(2 pi)` 全纯正型精确等于旧 `Gamma(k)` 二次型的两倍；`original_fourier_pair` 在同一实际 level 与 Fourier 模式的 `commonMBlock`、`nCarrier` 上供应旧 `hCumA/hCumB`。 | 原 Bessel test 的两条点态界、含复合标记的 ABL 去除、无穷极限、层/频率总恢复与完整物理 `7/32` 仍待。反号展开没有全纯项。 |

### U5 的原子子族与真实完整模数

plateau 保持 `p1` 对数坐标在 `[0.10,0.11)`、`p2` 在 `[0.12,0.13)`，使用原有序对筛选和原 `V=90621/160000`。共用根查询并不将原逐时决策换成新的策略。`paidModuli` 限制的是完整模数 `(p1*p2)*k`。实际附着中至多有两个不同 rough 素因子的子族，连同全部 small Rosser 因子，可由

\[
 0.11+0.13+\frac{34/125}{8}+2\frac{417}{5000}
 =\frac{551}{1250}<\frac9{20}
\]

进入这一完整模数支付区间。代码保留原完整及 selected-complement 平方过滤，并将 `original_account_partition` 接到原 `originalU5_causal_lower` / projected main 消费者。原 plateau 的正调和质量已有来源，本包复用其几何而没有重新证明。

### Wu 严格端点与重数

原窗口为 `[V_j/Delta,V_j)`。新因子在 `p_j=V_j` 等于一，因此该端点属于外漏；在 `p_j=V_j*(1+w)` 等于零。反向 membership 保留原 expanded label、原有序词、加强尾部和重复素槽。固定所选槽的整数 `p` 后，完整正乘积落在 `(0,N]` 中的 `p` 倍数里；每个乘积复用既有 `r^r` 标签纤维界。所得误差含离散端点项 `N/V_j`，由实际 moving box 的多项式下界统一支付，再接原 native `Theta` 预算。没有把乘积内帽的条带估计直接用于坐标墙。

### 全纯规范与连续谱的不同连接义务

取 `k=2j+2`，`printedCoeff` 使用实际斜线作用后的 q-展开，并乘稿面 `sqrt((k-1)!/(4*pi)^(k-1))`。旧逐项恒等式 `sieveCoeff_eq_scaled_R` 消除频率相关比例，余下比例的平方为 `4*pi*Gamma(k)`。因此稿面谱测度 `1/(2*pi)` 给出精确的两倍关系，覆盖两个观察 cusp、全部 `k-1 ≤ T` 的正偶权、各权完整 ONB，且常数先于 level、ONB、原行和高度选择。

连续谱仍需要在同一几何 cusp 框架下，将非零模的算术 Fourier 系数 `phi` 的临界延拓与现有 `nativeR` 识别。现有初始半平面的 Fourier 公式、逐行绝对界、零模延拓和 character-basis 的临界公式各有确定范围；尚未定位到能够直接连通这些对象的完整公共接口。因此本包没有把稿面的 `dt/pi` 与原含 `cosh` 的测度当作单纯常数变换，也没有任意定义一个新 `phi` 来消去该义务。

### 实际历史位置的有向窗口

对经典 U3 的每个原 `p`，令 `v` 为其共同根截止，`z` 为原位置在自身 `cellQ` 的截止。纯 retained 位置有 `v ≤ z`；含真实 W1/W2 fixed 且没有 fresh 的位置有 `z ≤ v`。令

\[
 W(l,h)=\sum_{l\le r<h}
 \operatorname{frozenCount}(N,pr,\operatorname{receiver}(N),r),
\]

其中求和使用实际 `primeWindow(p*N,l,h)`，保留原素性、互素和严格上端。位置差额分别是 `-W(v,z)` 与 `+W(z,v)`。原 `retainedRejected + nonretainedRejected` 等于 `L*rootShell + historyWindow + freshRejected`，`L` 是含 origin 的实际加权 LIST 预算，满足 `0 < L ≤ 431`。`actual_rejected_history_credit` 只支付扣除后面的两个显式余项之后的共同根壳。

`fixed_original_units_exact` 在每个根单独除以其正 `L`，将零追加素数位置的未加 mask 计数恢复成原 `originalReceiver.card`。`manuscript_signed_fixed_windows` 在原 presieve 假设下把这一精确等式用于 R4 的经典 U3 子和，保留原 O、E、其它 U3 和全部 U4，再乘原来的 `-1/4`。深度至多 430 的后代出现仍按每个原根单独归一化；未付的窗口和 fresh 余项继续显式列账。

## 依赖选版及避免重复

`ImbalancedChen/` 放本轮新模块；`selected-api/ImbalancedChen/` 放九个旧逻辑模块的最小选版。安装或将来验收本包时，每个逻辑模块只能选一份源码，按 `PUBLIC_SOURCE_MANIFEST.json` 的 `module_selection` 使用。历史包、生产源码、工具链和锁文件不改写。

| 旧逻辑模块 | 本包的必要选版 |
| --- | --- |
| `P4BOriginalShortMediumTripleReceiver` | 仅将 `boxed_le`、`feeConstant`、`free_difference` 的三处 `private` 移除；证明体不变，供原 atlas 与 singleton 复用。 |
| `P4AOrderedThirdSameCoefficient` | 新强版接任意正网格上限，旧公开入口用上限一投影；原签名保持。 |
| `P4AOrderedThirdCommonSchedule` | 向同一次选择传递网格上限，旧公开入口及结论保持。 |
| `P4AOriginalR17PaidIntegral` | 在同一原 R17 实例上保留全部旧输出并供应网格上限，旧入口保持。 |
| `P4BOriginalShortMediumTriplePayment` | 抽取母图无关的 `short_three_owner_lengths`，旧两组入口成为该证明的原实例；singleton 使用同一证明，旧公开签名保持。 |
| `P1OriginalSingletonMediumAdmissible` | 一行显式证明 `1 ≤ J0+1`，保留全部声明。 |
| `P1OriginalSingletonMediumRestoringBudget` | 三处显式使用真实 `lower_pos`、自然数非负性及既有 `dyadicConstant_pos`，保留全部声明。 |
| `P1OriginalSingletonMediumLiveRowInventory` | 一行显式证明 `1 ≤ N+2`，保留全部声明。 |
| `P4BOriginalMediumRestoringBudget` | 在真实 `pieces_cost` 中显式使用既有 `dyadicConstant_pos`，原恢复预算和全部声明不变。 |

其中 U02 和 U06 共用修正后的 `P4BOriginalMediumAtomFamily`（`review-r1`，blob `2a4dbb1d03b172bfac62536b6d28fa8bebcc438e`）、`P4BOriginalHighRankPostModulusRow`（`postmod_stage`，blob `4a3f59e34db49d9bec6bd5eb8b9be70064268074`）和 `PrimeProductsMellinExactMeanInsertion`（`rank2-dependency-audit/repairs`，blob `1d872b1bc4c1c176f2ff90a588b674d4887ecb2a`）。清单逐一记录本包源码和所有直接导入的路径、固定 ref、Git blob 与 SHA-256；该直接选版清单不声称已验收整个传递闭包。

## 范围与验收

原稿先固定 `k ≤ k_*`，每个原组有 `2j ≤ 6` 个 HB 坐标，所以 `m_HB ≤ 6k_*`。现有 all-rank Fourier、完整模数后的尾界和原 bank 恢复继续复用。独立 smooth 标签和移动 atlas 网格的重数仍要按原稿分别支付。旧记录中的增长维数目标不能代替当前固定族的真实缺口。

`PUBLIC_SOURCE_MANIFEST.json` 给出最终文件身份、直接导入和静态审查范围；`YELLOW_NODE_SCOPE.md` 给出 29 个黄色父节点的实际剩余职责。本轮只提供各条明示证明链，完整 `hLower`、`hUpper`、同一实例 PP 与主定理无条件总装没有由这些子结果自动获得。
