# 经典 U3 固定族的真实计数与种子价格

七份冻结源码在固定夹持根上给出全部 Γ9–21 标记的精确几何字典、未测整数的上质量 $J$ 及种子原价的同归一化极限。对测试侧，已接到种子不等式右端的是实际几何计数。其正分布估计仍是独立前件。本次核对源码、原稿和原件指纹，未运行 Lean、守卫、数值或 CI。

## 同一整数的多个标签

原稿 ba6ec11d 的《global-positive-upper-completion-20261010.txt》§1 定义 $w_N(M)$ 为乘积等于 $M$ 的所有带标签素数组的权重之和，容许有限个带固定非负权重的几何族以及重复素因子。§7 的完全互素均值也对这些素数组求和。因此，一个整数由两个不同前缀产生时，两次都应进入普通计数和素数测试计数。

`original_count` 对 $N>1,0\le\tau\le1/12$ 把真实夹持根在 `rootQ` 上的有标记和逐项识别到 `marks N N`。外素数 $p$ 是完整乘积的首个指定槽，随后是原来严格递增的彩色素数列 $q$，再接原尾数 $m>0$ 的规范非降素因子列 $r$。尾素数下端是倒数第二颗 $q$，允许相等。`tuple_mem` 双向给出无目标掩码的固定窗、颜色、顺序及 $N^{1-\kappa}<M=p\prod q\prod r\le N$。`count_tuples` 所用注入把 $(p,q,m)$ 送到 $(p,q,r)$，以 $\prod r=m$ 恢复尾数。这里从未宣称仅从 $M$ 可恢复指定的 $p,q$。外层仍是逐次出现的原列表，112、122 各出现两次。测试侧要求 $M<N$ 且 $N-M$ 为素数，未测侧保留 $M=N$。整个对应无阶乘或除重系数。

先固定 $n,\tau$ 满足网格条件 $1/(n+1)\le 11/384$，根需要 $0<\tau\le1/12$。这样 $\nu=\mathrm{clampLevel}(n,\tau)$ 与 $\kappa\in(0,1/112]$ 均先于 $N$ 固定。在 $N^{833/2500}\le p<N^{1/3}$ 上，物理 $Q=N^\nu$、原查询为 2，且 $R=Q/p\ge N^{7/128}$。所有列坐标均至少 $N^{1/200}$。前缀乘积至多 $pR^3\le N^{1-1/112}$，故保留的大区必须 $m\ne1$。被标记的 $p$、至少三颗 $q$ 与非空尾列给出总秩至少五，完整乘积给出至多二百。不同固定秩、颜色和出现位置可作有限标签；全部阈值不要求对变化的几何族一致。

## 去掩码与未测整数上质量

`exact_target_mask` 只恢复 $p,q_i$ 与 $N$ 互素的原条件。删去的标记必投到与 $N$ 不互素的 $N^{1/200}$-粗整数。在同一颜色字上用 $(M,p,q_1,\ldots,q_s)$ 可恢复整个标记。原 `omega3_labels_card_le_outputs` 在这里给每个输出至多 $200^{s+1}\le200^7$ 种有序前缀。`complete_deletion_le` 与 `deletion_vanishes` 由此把原二十次出现的**未测**去掩码损失控制为 $20\cdot200^7(\log N/\log 2)N/N^{1/200}=o(N/\log N)$。测试侧只需正权包含 `original_le_geometry`，无需把这个普通质量估计当成带号分布误差。

`actual_untested_upper` 对每个固定合格 $\nu,\kappa$ 与任意 $\varepsilon>0$，在充分大 $N$ 上给出 $\mathrm{count}(\mathrm{false},1,N,\nu,\kappa)\le(J_\nu+\varepsilon)N/\log N$。每个原 $p$ 以自己的 $R,\alpha\ge2$ 调用非单位 Buchstab 上界。Γ9–15、Γ16–19 及 Γ20–21 分别复用原积分证书，末两项的保守价格可保留非负单位价格。对每次出现取 $\varepsilon/20$。原 $C=\sum_{j<13}\mathrm{switchedMass}(j)$ 不含已付 Γ5。原子乘 $\log N/N$ 后的系数为 $1/[p(\nu-\log_Np)]$，以原倒数素数测度的 $1/(p-1)$ 单向控制，最终得到 $J_\nu=CI_\nu/4$，其中 $I_\nu=\int_{833/2500}^{1/3}4\,dt/[t(\nu-t)]>0$。此处只用总的上质量；无随 $N$ 的未测量收敛前提。

## 真实 Θ 接点与未付项

`original_price_common_limit` 同时给普通上界与 $\mathrm{switchCost}\,\Theta/H_N\to K_{\mathrm{seed}}J_\nu$。其中 $\mathrm{switchCost}=(681/100)C/4$，$H_N=\mathcal C(N)N/\log^2N$，原 `thetaAtom` 使用 $4\,\mathrm{Richert418.logarithmicIntegral}(N)\mathcal C(pN)/[\varphi(p)\log(Q/p)]$。原 `actual_clamp_theta_limit` 给 $\Theta/H_N\to I_\nu$，这里未改变 li 中心。`paper_upper_price_fits` 取 $\delta=\varepsilon I_\nu/2>0$，以原全局 $K_0=8452171/1250000\le681/100$ 与 $J_\nu\ge0$ 得到最终的标量不等式 $(K_0J_\nu+\delta)H_N\le\mathrm{switchCost}\,\Theta+\varepsilon\Theta$。

`original_balance_at_sharp_family` 在原 $5(\Theta-\sum(E_p+S_p))$ 的上界中保留 `otherSeedTerms − longPrime + badPrice`、无掩码真测试 `count true` 和一次误差。将此测试替换为上述标量仍须在同一物理系数上实现 U*。原稿 §8 对完整乘积上墙用 $y=M/N$，在固定精度上构造全族光滑正外逼近，然后计算同系数精确互素均值和带号误差，最后放宽精度。现有双固定秩 `p5z_eventually_mixedMarkedFamily_upper_of_actual_rho` 需要真实权重、载体、许可、密度及带号 hPP。现有全秩 Family 容器也需要实际外权及导数控制。单靠 $J_\nu$、标量价格或不同上极限相减都不能生成这笔实际测试付款。原根 Γ5、其他普通项和反馈保持各自既有职责，全 H430、430+11 及整黄不升级。

核对 41 个不同原件路径，覆盖七份候选、五个外部直依赖、历史定理、原生计数源码、八份原稿及前包收据。新源 51 项声明、12 条直接导入边。作者 REGISTRY 的 SHA256 为 `70f6bd29f6b77d0144521c6601c900007a5d7184d5ac380a03e390aa959b106b`。仅选择此冻结七源；后续径向补件另册。
