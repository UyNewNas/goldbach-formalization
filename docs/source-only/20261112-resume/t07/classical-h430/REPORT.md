# 经典 U3 的实际根计数与 H430 表价

本包给出五份 SOURCE_ONLY Lean 源码。对固定的正余量 `0 < τ ≤ 1/12`、任意误差 `ε > 0`，取足够大的偶数 N。对所有满足 `1/(n+1) ≤ 11/384` 的冻结精度，原经典整段和原正宽夹持段各自满足

\[
  \sum_{p\in B}\left|C_p+E_p+S_p-\theta_p\right|\leq\varepsilon\,\Theta_B .
\]

`C_p` 是原接收集 `chenSiftedQuotientPrimeSource N p (N^a)` 的整数商个数。外层指定素数 p 同时是模数前缀，接收端的素数是 ℓ，接收整数为 q=(N−ℓ)/p。所有 p 共用原冻结的 \(Q=N^{\mathrm{frozenLevel}(n,1/2-\tau)}\)。\(\Theta_B=\sum_{p\in B}\theta_p\)，其中 \(\theta_p=4\operatorname{li}(N)C(pN)/(\varphi(p)\log(Q/p))\)。取 \(a=417/5000\)。两个 B 分别由原素数坐标 \(t=\log p/\log N\) 满足 \(57/224\le t<1/3\) 与 \(833/2500\le t<1/3\) 决定，还保留原筛选的 \(p\nmid N\)。

## 源码与付款

| 源码末名 | 可核对的结果 |
| --- | --- |
| ThetaPayment | `uniform_clamp_witness` 将原真素数区间的半层极限与每个真实冻结层逐项比较。固定正数 \(I=8\log(834/833)\) 满足 \((I/2)\mathcal H_N\le\Theta_{\rm clamp}\)，门槛对 n、τ 一致。这里 \(\mathcal H_N=C(N)N/\log^2N\)。`complete_classical_AP_le_clamp_theta` 将先前全经典 \(\sum_p|D_p|\ll_\tau N/\log^3N\) 用生产库的奇异级数正下界吸收到 \(\varepsilon\Theta_{\rm clamp}\)。这个 BV 门槛依赖先选的 τ，对 n 和 m 一致。 |
| PriceGeometry | `actual_classical_queries` 用 \(57/224\) 及原 1/50 闭格宽度证明 \(2\le s_p\le149/50\)，且实际一侧公共端点 \(s_p\le w_p\le3\)，对所有 m 有效。两种原普通上幅分别满足 \(A(s_p)=A(w_p)=1\)。`external_prime_outside_Wu_windows` 证明经典区 \(p^2>N^{1/2}\)。Wu 的每一个准入卷积因子窗要求 \(p<V_j\)、\((\prod_{l<j}V_l)V_j^2\le N^{1/2-\delta}\)、\(V_l\ge1\)，因此没有一个因子窗能包含该 p。 |
| OrdinaryMean | `classical_root_main_close` 对每个原 p 证明双侧 \(\left|M_p-\theta_p\right|\le\varepsilon\theta_p\)。使用 `ActualRosserInitialResidualSaving` 的原严格系数双侧紧集定理。实际筛目标为 M=pN，取 \(\beta=\log(Q/p)/\log M\in[11/768,1]\)、\(v=1/w_p\in[1/3,1/2]\)。紧集参数为 \((\beta,\beta v)\)，故原规范化系数为 \(4/\beta\)。真实冻结 Q 的有理幂与 \(p\nmid N\) 给出 \(\lceil Q/p\rceil=\lfloor Q/p\rfloor+1\)。该等式将两个库的逐除数 Rosser 系数及严格素数窗对齐。`li(N)`、\(C(pN)\)、\(\varphi(p)\)、\(\log(Q/p)\) 全部保留。这个门槛还对几何范围中的 τ 一致。 |
| Credits | `physical_marked_class` 把每个原有限 owner 类的实际 markedPhi 写成 \(\sum C_p\) 加真实最小素数壳，并识别原 Θ。`original_class_zero_theta_iff_empty` 证明单位正标记的零 Θ 类恰为空类。`original_classical_credit` 用已有逐系数首立方约简，同时保留真实全模数 \(p r\) 的有符号误差，证明两个非负余量的和对所有辅助 m 相同。 |
| H430Boundary | `actual_classical_and_clamp_distance` 给出上式的两个相对 L¹ 终端。`archived_classical_H430_gap` 在源参数读取已存 H430。`selected_classical_H430_gap` 对来源历史保留第 430 代真正选中格的 `requestValue`。`archive_clamp_charge_positive`、`selected_clamp_price_lower` 和 `actual_clamp_H430_gap` 给出原夹持区的严格正表价及带符号余额。 |

具体地，取 \(z_3=(Q/p)^{1/3}\)。\(E_p\) 在真实外层模数 p 的素数接收纤维上求和。每项为 \(\sum_{r\mid\gcd(P(pN,z_3),N-\ell)}\lambda_r^+ -1_{\gcd=1}\)。\(S_p\) 在 \(z_3\le q'<N^a\) 的首个素因子上求和，项为完整前缀 \(p q'\)、筛到 \(q'\) 的实际 frozenCount。二者均非负。此前源已证原幸存商上的局部 Rosser 余量为零。本包没有向幸存 q 复制一个外层 p 的整笔余量。实际字母、整数商、素数 ℓ、Rosser 除数 r 各保留其角色。

## 原稿的推导和精确未付项

原稿 `paper/source/manuscript-body.tex` 第 795–817 行在同一 Q 的正标记族上定义 \((A-H)\Theta\) 的上界。第 819–865 行用真实种子、四轮和先前代反馈形成 430 代闭格表，第 867–894 行再接公共误差及十一项。配套 `own-chen-table-insertion-chain-20261009.tex` 第 135–157、388–400 行明确准许经典分支使用完整模数 BV，并在同段提出 \(4\int(A-H)/(tL)\) 的上界。已付 BV、Θ 正常数以及本包双侧普通主项足以确定普通基线的确切大小。\(H\Theta\) 是另一个主阶要求。

对原经典整段，只要检验下面一个带方向的真实算术估计，就能判定这部分最终上界，误差可任意缩小。由前述 L¹ 估计，它与该部分原上界在渐近意义上等价。

\[
  \sum_{p\in B}H_{430}(s_p)\,\theta_p
     -\sum_{p\in B}(E_p+S_p)\ \le\ o(\Theta_B).
\]

对原夹持段的单独上界，第一项简化为 \(H_{430}(2)\Theta_B\)。原序列化数组的 49、50 两格均为 \(37052565421922458792801/2^{80}\)，闭节点取相邻最小值。因此这段表价至少为 \((37052565421922458792801/2^{80})4\log(834/833)\,\mathcal H_N\)。实际选中历史在同一夹持段也要求至少 \(1/50\) 的正增益，这个下界只用存入的第零代整数和逐代保留得到。两种读取的结论分别成立，全文不需要把两个 200 项数组预先等同。表价和金额的正性没有给出 \(E_p+S_p\) 的所需下界。单独夹持段的算式也没有排除其他区段在更粗的整段界里补偿它。

`PositiveGainActual.lean` 确有 Wu 旧改进函数的严格正下界。它的 `wuAdmissibleImprovements` 量化于 `wuSourceBox`。上面的 \(p^2>N^{1/2}\) 给出从该许可直接套到此处的算术障碍。冻结稿 `second-seed-stable-prefix-extension.tex` 第 48–55、103–125 行另给经典分布和正 switched 积的扩展路线，`generalized-one-step-double-sieve.tex` 第 68–81、107–153 行区分普通符号项和 switched 正项。本轮找到的既有形式源码与已付两侧普通主项均未提供该类真实非负余量所需的平均下界。把前代 h/H 的真实标记族计数作为输入，仍须沿原种子、Buchstab 和 W1/W2 的 switched 作用证明它；把目标根的 H430 计数当作该输入会构成循环。这里是尚待兑现的分析估计，现有结果没有证明该估计为假。

正质量见证只用于两组原素数总体。对随 N 变化的任一细格，非空仅保证严格正 Θ，不能据此把整池绝对误差换成该格自身的相对误差。空格的真实标记和计数正好为零。τ 可按原方案随所需精度先选，再求 N 的门槛；本包没有建立随 N 任意改变 τ 的 BV 常数。

P3 的增强段带标记普通 AP、正 switched 乘积的同一 \(\rho\) 许可及相应分布调用仍是独立输入。原 106 行、四轮种子、430 次非负转移和 11 层的实际前代计数及共同细化仍须原规则。所有原转移正质量至多 12，仅逐层受控误差可进入 \(\delta(12^{441}-1)/11\)。十一项根系数绝对值和为 \(7/2\)，U3 本项的系数是 \(-1/4\)。本包的 L¹ 门槛给出经典根普通部分，无权支付其他转移的误差或源增益。

五个安装模块均为未编译源。OrdinaryMean 采用 `install_overlay/` 中的同名文件。该版将 `rw` 后的 `rfl` 仅用于仍存在的目标，保留原声明及数学证明；最初提交独审的字节也已保存在目录顶层。具体选版、原稿和直接依赖的指纹见同目录 REGISTRY.json。本轮未运行 Lean、Lake、LSP、数值重放、guard 或 CI。
