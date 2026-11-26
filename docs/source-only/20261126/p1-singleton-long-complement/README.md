# 实际 singleton 两长 occurrence 的完整补积连接

**状态：source-only；未执行 Lean，未取得 normal、kernel 或 owned 验收。**

本目录只新增 `P1OriginalSingletonLongComplement.lean` 一个 owner，字面 import 只有 `ImbalancedChen.P1OriginalSingletonLogNormalization`。它组合发布 C `545566753bae9464560a871bea87ea663f90aa53` 中的实际 two-long dictionary、log-normalization 和 PhysicalLevel，补齐从选中的实际 occurrence 到**整个补积块**的有限接口。没有改 canonical、旧 provider、runner 或既有验收身份。

源码为 **10,612 B**，SHA256：

`e332fddc14a70b6ff2f688a4c6c9ce8d0571e95077ead958c45d96bbdecdebc2`

## 新增的两个声明

### `actual_factor_whole_complement`

给定原 `fs ∈ factorTuples r n` 及某个真实 `p ∈ fs`，直接组合旧 API 得到：

\[
0<p,\quad p\mid n,\quad 0<n/p,\quad p(n/p)=n,
\]

以及 `Owns (owner (n / p)) (n / p)`、`owner (n / p) ∈ bank n`。因子的正性与上界来自 `actual_factor_bound`；整除来自 `factorTuples_spec` 和 `List.dvd_prod`；补积正性、精确乘积与右闭 dyadic owner 分别由原 Nat/owner 接口支付。

这里没有额外的整除、补积正性或补积块假设，也没有构造替代 block/bank。

### `eventually_actual_remaining_two_long_complements`

输入仍是原非零 chart、真实 HB tuple、该 tuple 的非零 `assignedWeight`，以及使用同一历史 \(Q\) 和原 \(\rho\) 的非零 remaining selector。原 dictionary 只调用一次；它选出的同一对不同**位置** \(i,k\) 原样返回，并保留：

- `List.ofFn bs = row.blocks`、`List.ofFn ns = row.factors`、完整整数 rectangle 和原 HB 权值；
- 原单母体 `rowRoles`、两 long 的 `.one`/`.logarithm` 角色、至多四个 short occurrence；
- 原 same-rho fixed-mode 恒等式，对所有 \(\xi\) 成立，仍有同一 `historicalModuli`、`rho`、物理 `N`、完整乘积和 exact coprime mean。

log-normalization 在**同一个实际 tuple**给出原完整整数 \(n=\texttt{row.factors.prod}\) 的 `scalarProfile ≠ 0`。对每个 \(a\in\{i,k\}\)，原 list roundtrip 和 rectangle 分别给出 `ns a ∈ row.factors`、`Owns (bs a) (ns a)`。补积块随后取为既有的

\[
c_a=\operatorname{owner}\!\left(\frac{n}{\mathrm{ns}(a)}\right).
\]

源码还证明了按索引删除一个 occurrence 的精确恒等式：

\[
\prod_{b\in\operatorname{univ}\setminus\{a\}}\mathrm{ns}(b)
=\frac{n}{\mathrm{ns}(a)}.
\]

这一步用 `Finset.mul_prod_erase` 和正整数除法；没有按数值去重。其他相同数值的 occurrence 和 unit 都保留。整个补积包含另一 long occurrence **及所有 short occurrence**。

最后直接调用既有 PhysicalLevel，在每个选定位置得到

\[
x_a=\operatorname{localScale}(\mathrm{bs}(a),c_a),\qquad
1<x_a,\quad x_a/2\le N\le x_a^{1+\kappa},
\]

并对同一
`historicalModuli levelB old fresh N cap w z`
中的每个 \(q\) 得到

\[
q<x_a^{1199/2000},\qquad
q\le\left\lfloor x_a^{1199/2000}\right\rfloor.
\]

原 \(q<N^{599/1000}\) 到局部指数的运输完全由已有 PhysicalLevel 支付。本目录不重证这一运输，也不把所需 scale/level 或误差估计作为前提。

## 参数与量词顺序

先固定

\[
0<\kappa,\qquad
\kappa\le\zeta/10000,\qquad
\zeta\le1/20000,\qquad
\kappa_0<\frac{\kappa}{4(1+\kappa)}.
\]

由此在证明内推出 \(0<\zeta\)、\(\kappa_0<1\) 以及 PhysicalLevel 所需的 \(\zeta\le1/400\)。`zeta ≤ 1/20000` 是已发布实际 dictionary/numeric supplier 的条件。

三个原 eventual 阈值取交集后，才量化 profile 参数 `kap < 1`、`B`、`K`、chart、row、历史 `levelB/old/fresh/cap/w/z` 与 `rho`；两个位置沿原 dictionary 先于 Fourier mode 选定。没有根据实际 tuple 或模数再选择参数以强迫局部界。

## 稿件与既有来源

固定稿件为仓库 `UyNewNas/chen-imbalanced-semiprimes` 的提交 `a988cba584d803ae2856a0de50efb582f4f3dd6a`，文件 `paper/release-20261106/en/coefficient-appendix.tex`，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`；缓存 **39,389 B**、SHA256 `267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`。

对应段落是 251–270 行的参数顺序，514–548 行的 HB、unit、保留 smooth chart 与完整乘积尺度，以及 621–630 行的 no-medium 两长与 exact coprime mean。稿件的 `sigma = zeta / 2000`、`kappa ≤ sigma / 200` 比这里所用的 `kappa ≤ zeta / 10000` 更强，允许在固定正余量之后先把 `zeta` 取得足够小。

`SOURCE_REVIEW.json` 保存两个新声明的精确 UTF-8 statement/proof 区间和 SHA，12 份使用到的源码、3 份原来源审查的 C Git pins，以及固定 Lean 4.33.0-rc1 / Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 的相关 API 文件指纹。PhysicalLevel 的字节还与发布 A `1576fac11ccf44b4fc6e652fc76e8c2f71655f58` 相同。

去重核对仅覆盖这些精确 API 及相邻 `P4BOriginalHighRankMotherScale`。后者已有 whole-quotient `owner`，但其 live profile 是 P4 两母体；此处复用 canonical factor/owner 与 singleton PhysicalLevel，没有迁入那条母体链或复制其 scale 证明。这里不作全历史库不存在其他工作的断言。

## 静态审查与保留边界

独立只读审查核对了两个声明的数学合同、完整补积、索引删除、量词顺序、原 kernel/mean 和实际 Lean API 签名，未发现具体阻断。该结论不等于 elaboration 或 Lean 验收。未执行 Lean、云任务、Git stage/commit；本目录没有添加 runner 或验收脚本。

局部界只附于给定实际 tuple。没有声称 \(x_i=x_k\)，没有声称任一 \(x_a\) 在整张 rectangle 或整个 fibre 上固定，也没有把某个点的 `scalarProfile ≠ 0` 提升为整张 rectangle 或聚合系数非零。原 fixed-mode 有限恒等式可以同时保留，但将局部界用于最终求和仍需后续真实的 carrier/预算装配。

实际 short-product/endpoint 预算、P2/Brun row 的对应和 roughness 误差、Fourier 重构及最终 remaining Atlas 求和仍未支付。本目录仅一个新 source-only owner；将来导入时须沿用旧 dictionary 已登记的互补 provider postimages，避免同时导入未迁移旧 provider 与其提取出的 generic owners。完整传递源码闭包与编译信用均未在此宣称。
