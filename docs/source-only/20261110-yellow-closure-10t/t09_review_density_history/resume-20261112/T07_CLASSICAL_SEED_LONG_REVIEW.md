# 经典 U3 上原 Γ9–21 长字的独立源码审查

T07 的七份冻结源码通过以下范围的静态审查。它们支付全部二十次原出现的小乘积计数，将未测 Γ9–21 收到二十个既有非单位积分，并把大乘积的真素数测试接回原夹持根及四轮收支。正式编译、内核和运行资源均未验证。

## 载体、参数及转换

原经典带为 $N^{57/224}\le p<N^{1/3}$。对真实 `LevelIndex N n .U3 τ p dep`，起点旧字为 `[p]`，每条边在右端追加，故每个实际父乘积 $d$ 保留 $p\mid d$。由 `rootQ` 冻结的 $\nu\le1/2-\tau$ 和 $T=\log_N d\ge57/224$，`actual_cubic_residual` 得到 $dR^3\le N^{1-1/112}$、$R=Q/d>1$、原 $\alpha>3$ 及固定正幂下界。对 $0<\kappa\le1/112$，$m\le R^{3-5r/11}$ 的整个尾商进入闭小区。每个原字 $r\le6$，因而包括 Γ20、Γ21 的真实单位项。

`all_parts` 按 $D m\le X=N^{1-\kappa}$ 和 $X<Dm$ 划分每个原先的 `roughNumbers`，粗糙下端为原序列倒数第二颗素数。加法素数测试是 $Dm<N$ 且 $N-Dm$ 为素数。未测载体保留等于 $N$ 的上端点。颜色字仍按原列表逐次求和，包括各出现两次的 112 和 122。每个未测小纤维至多 $X/(d\prod q_i)$，原标签倒数和至多 $5^r$，总界为 $20\cdot5^6 X/d$。此处保留 $1/d$，使任取 $B$ 的相对估计有意义。

`small_both_atoms` 用原 `Theta_lower` 与 `rawMainAtom_to_thetaAtom` 分别比较 $N/(d\log^2 N)$ 和它乘 `thetaConversion` 后的量。两端共用原 $Q,d$ 与 Richert 的 `logarithmicIntegral`（`liuLogarithmicIntegral 0`）。`all_marked_small_products` 对固定正 $\kappa,\varepsilon$ 先选 $T_0$，随后任取 $N\ge T_0,n,0\le\tau\le1/12,p,\mathrm{dep},B$，其中 $1/(n+1)\le11/384$ 且 $p$ 属原带。真测试小量、原 $K/4$ 乘转换后的未测小量各自至多 $\varepsilon\Theta_B$。$K=681/100$。证明直接累加各原子，允许空 $B$，没有除以子族质量。

## 实际积分与尚存的正的大乘积

`classical_inclusive_long_cost` 以 $\kappa=1/112$ 分割，单位的原档计数为 $\#\{\boldsymbol q:D\le N\}$，由同一小区中的 $m=1$ 给出。大区包含于原 `erase 1` 载体。逐位置用已有 `original_Gamma9_to_21_theta_upper`，其 $\alpha\ge2$ 与尺度前提由实际历史满足。两半预算之和给出整段未测量上界 $\sum_{l\in B}\mu_l (K/4)\theta_l\sum_{\rm occurrences}J_{\rm nonunit}(\alpha_l)+\varepsilon\Theta_B$。一般 $\alpha\ge2$ 下原单位曲面的处理仍独立。

`prime_tuple_reindex` 用正整数的规范非降素因子表，乘积给逆，保留相等尾素数、截点相等及外层字位置。`actual_large_prime_tuple` 在 $\kappa\le1/112$ 时给出 $5\le |A|\le\lfloor1/\mathrm{frozenLeafCutoffFloor}\rfloor$，每颗素数都达固定幂下界。这是五个素因子位置。相同素数、实际 HB 分组和独立尺度的许可还须在物理矩形上处理。

`actual_large_product_difference` 对任意固定 $\kappa,\varepsilon>0$ 把整个有向余额与只保留大区的余额之差控制到 $\varepsilon\Theta_B$。两块小量均非负且均至多这一上界，所以一个预算即足。`classical_seed_and_four_rounds_large` 对真实种子位置保留一般继承 Γ5、七项普通 AP、四轮前代和两项已有抵扣。`original_E_and_S_after_small_switches` 专用于夹持根，调用同 $p,Q$ 的旧 Γ5 付款。长字先按真实重复与中心收费，再用小区付款。固定 $0<\tau\le1/12,\kappa,\varepsilon>0$ 后对充分大偶数 $N$ 和所有合格 $n$，原 $5(\Theta_{\rm clamp}-\sum(E_p+S_p))$ 的右端为 `otherSeedTerms − longPrime + badPrice + allLarge true` 的原根和及一次 $\varepsilon\Theta_{\rm clamp}$。一般后代的 Γ5 仍在其余额内。

原夹持种子仍需处理大乘积真素数测试。直接接现有 `largeBalance` 的充分条件是同原标记及同物理质量的有向大区估计。若目标仅为种子上价，原稿亦允许对固定几何盒的正测试用上极限，结合未测积分上界和普通部分。这条路线需要整族保持标记的几何逼近、同物理系数的 PP 及与 Θ 的归一化，毋须逐个变化的 $X_N$ 证明差趋零。两条路线均未在本包支付全部正长字、H430 或 430+11。原完整黄色职责维持。

## 字节与原件

作者 REGISTRY 的 SHA256 为 `16bd58689250a01a0ea99445859ca7d719fa14609fac1234eb7627dbe404a13c`。七份新 Lean 含 46 条声明、13 条直接导入边和 7 个外部直接模块。已核 39 个不同来源路径的原始字节、SHA256 和 Git blob，包括八份原稿、既有单位及非单位供应、实际历史与归一化定义、原 Γ5 收据和作者报告。所有条目选用冻结原件。没有运行本地证明、有限检查、数值证书或 CI。
