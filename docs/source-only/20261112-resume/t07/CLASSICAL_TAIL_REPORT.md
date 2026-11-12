# 原 U3 经典区全部冻结根 AP 余项

在 $57/224\le t<1/3$ 的完整原 U3 区间，固定 $0<\tau\le1/12$ 和任意正整数 $J$。本组三源把实际冻结根余项（含完整有限均值平移及中心扣除）对全体指定素数的绝对和控制到

$$
\sum_{p\ {\rm in\ the\ classical\ U3\ band}}
 \big|D_p^{AP}(N,Q_p,z_p)\big|
 \le C_{J,\tau}\,\frac{N}{(\log N)^J}.
$$

阈值先于全部冻结水平精度 $n$ 和辅助查询精度 $m$。$Q_p$ 为原物理冻结水平，$z_p=(Q_p/p)^{1/s_c}$，$s_c$ 取原第 430 代闭格对应的公共右侧查询。包括结构性 $s_c=2$。原报告中全带的有符号根估计作为输入。[第一组三源](ROOT_SOURCE_REPORT.md) · [经典段独立来源与声明登记](CLASSICAL_TAIL_REGISTRY.json)

## 可直接复用的原结论

P5 的 eventually_tailSignedPrimeAP_log_saving 已将原始未冻结行的 true-li AP 分量总和接到经典 BV。其 receiver_atom_eq_trueLi 给出同一个完整模数 $k$ 上的逐项等式。生产库的 sum_chenPooledQuotientModuli 将大指定素数与小模数经真实乘积作单射汇总，适用于随 $p$ 改变的除数集。part3_chenQuotientPrimeAPError_pool_log_saving 允许取任意正的对数幂次。此处直接使用这些原声明。经典段之外的 P3 切换或增强分布另有假设。

## 冻结水平、真实模数和中心

1. 经典分支总水平从下方取 $1/2-\tau$。向下冻结保留 $Q_p\le N^{1/2-\tau}$。压低比较 cutoff 给出 $z_p\le N^a$；原 $p\ge N^a$。对每个非零原上 Rosser 系数，完整模数满足 $k=pr\le Q_p$，其小素数部分 $r$ 整除 $P_N(N^a)$。共同的严格小素数积与指定素数互素。即使两个 $p$ 落在不同闭格，$\gcd(k,P_N(N^a))$ 仍恢复唯一的 $r$，继而恢复 $p$。[真实冻结模数](Part5OriginalH430FrozenClassicalRootModuli.lean)
2. 对每个 $k$，将同一原普通上筛系数保持在有符号和内，从加法素数接收集的原中心恢复 true-li AP 分量。剩下的精确项为

   $$
   \frac{2}{\log 2\,\varphi(k)}-\#\{\ell\le N:\ \ell\ {\rm prime},\
                         \ell\mid N,\ \ell\equiv N\pmod{k}\}.
   $$

   由于 $k>0$，其绝对值在 $\log N\ge1$ 时至多 $(3/\log 2)\log N$。每个 $k$ 保留一个加权项，故全部中心代价至多 $(3/\log 2)\sqrt N\log N$，这可按同一 $J$ 收到 $N/\log^J N$。加上真 BV 得到上式，允许各 $p$ 的有符号和先取绝对值再求和。[整笔经典 AP 付款](Part5OriginalH430FrozenClassicalRootAP.lean)
3. 用已有的 keyAt 按原闭盒分组，每个 $p$ 归回其自己的 $Q_p,s_c$。original_U3_signed_split 从完整的有符号 U3 表达式分出经典段。original_U34_with_classical_root_AP_paid 将所有经典根余项换为一个 $C_{J,\tau}N/\log^J N$，保留增强段原 AP、两个标签实际普通主项、每个 $p$ 的整数除数盈余和原最小素数壳，不收取随盒数增长的误差。[插回原 U3 与 U4 总数](Part5OriginalH430U34PaidClassicalRoot.lean)

## 仍开放的原责任

- 这一付款在**根的经典普通上 Rosser 多项式**。即使在经典段，原闭格改进还要用真实盈余、最小素数壳和有符号误差抵消 $H_{430}\Theta$。递归中的标记多素数词需要处理多个前缀分解。
- 在 $t<57/224$ 的增强 U3 段及整个 U4 上，仍需原许可系数族的增强 AP 分布。U4 交叠的两个原始标签保持各自的 $-1/4$。
- 原 106 行、严格同 $\rho$ 的 PP、$1/50$ 种子、四轮前代反馈与整套 430+11 的实际计数闭格归纳仍开放。两包 11 月 10 日的限定复核保留其各自范围。[原五源限定审查](../t09/T07_PAIR_ROSSER_REVIEW.md) · [原八源限定审查](../t09/T07_SEED_PAIR_REVIEW.md)

三个声明文件仅作源码审查。没有启动本地 Lean、Lake、LSP、证书守卫、数值重演或远程 CI。尚无此包的 kernel 或传递公理回执。
