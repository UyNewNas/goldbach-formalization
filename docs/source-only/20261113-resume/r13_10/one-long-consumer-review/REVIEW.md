# 最终 singleton 单长槽 E5 源码审查

**限定结论**　`original_one_long_two_channels` 对最终 singleton 图中 `firstMedium = none` 且恰有一个长位置的子和给出两种原模数系数的统一估计。它量化固定的 $0<\kappa<1,\ \omega>0,\ 0<\zeta\le 1/20000,\ K\ge2$ 和 $A\in\mathbb N$，随后选取一个 $N_0\ge2$。对每个满足 $P.N\ge N_0,\ P.\omega=\omega$ 和原系数高度条件的 $P$，两种子和分别至多 $P.N/(\log P.N)^A$。常数可取 1。阈值先于 $P$、母图、块、位置和短列。审查范围为四份新 Lean 源文，未编译、未核验 kernel，formal credit 为 0。

## 从原子和到已有有限 E5

1. `sourceChannel_singletons` 依原 `chartBank (2*N) 1` 枚举单标签，再使用已冻结的逐图 `source_to_actual_rectangles`。 `physicalChannel_dictionary` 在核内删除零权，保存 $P.S,P.\rho$ 的计数和均值。`freeChannel_dictionary` 保留完整模数 `products P` 及所有记录合成的 `free P q`。同一个 $J_0(\omega)!$ 在 $N$ 以前固定并涵盖两种模数系数。
2. `selected_long_position` 使用列表索引上的唯一性，即使不同位置有相同数值也分别计数。其余至多五个位置分别满足短阈值。原严格 rough 条件删除所有 $p\le z$，包括 $p=z$。`actual_count_mean_dictionary` 恢复原 $mn\equiv N\bmod q$ 与 $\mathbf1_{(mn,q)=1}/\varphi(q)$，原实数值的 Möbius 截断仍在各短位置上。
3. `occurrenceAtom_short_fibres` 先依原 profile 支撑截取 $mn\le2N$。长元的闭上端是 $\min(2U,\lfloor 2N/m\rfloor)$，包括空纤维。`longFibre_eq_actual_profileError` 把每条有序短列及其原复系数接到旧 `profileError`。同列位置值给出乘积 $m$，其区间、权和 profile 在全体 $q$ 之前固定。长 $\mu$ 由实际 $R$ 的统一增长及 $(2R)^{1/3}<R^{1/3+\zeta/4}$ 逐项归零。其余角色是原 one/log。归一化使用完整整数的原组对数。
4. `actual_fibre_finite` 使用旧 `actual_chart_one_long_finite` 的完整有限声明。令移动剩余为 $N$，$J=0,\ D=\lfloor N^{599/1000}\rfloor$，短积集合为单元素、单位系数，外乘原短列系数，宽度参数为 1。幅值和导数同时使用已冻结的实际全轴 $C^1$ 界，$B=6$ 对应指数 73。B1/B2、完整模数上的精确互素密度与除数矩均由旧定理证明体支付。

## 统一恢复

- `active_chart_geometry` 由原非零实 profile 与 $\psi$ 支撑给出 $N^{1-\kappa}/2\le R\le4N$。固定 $K$ 后，`roughF_mono` 在实际区间把 $f(2^{6K+3}R)$ 放大到 $f(4\cdot2^{6K+3}N)$。`roughF_upper` 在 $[N,N^2]$ 给出 $\bar z=N^{2/(\log\log N)^3}$。原素数集合仍由图内实际截断定义。
- 有限 E5 对任一 Brun 层数有效。取所有活图共用的 $j_N=\lfloor(\log\log N)^2\rfloor$，以旧 Mertens 引理取 $H=2\log\log N$。于是 $Y=\bar z^{2j_N+1}=N^{o(1)}$ 且 $\epsilon=H^{2j_N+1}/(2j_N+1)!$ 具有任意固定对数精度。费用可在 $A+100$ 阶支付。这里改变的是有限 Brun 层数的选取，原精确 discrepancy 和 rough 集合都由前一段的恒等式给定。
- 活块上每个可能的短元不超过 $4N$，五个角色的绝对值保守地合计至多 $L^5$，$L=1+\log(8N+8)$。有序短列总数 $S\le(4N)^{15\zeta}$，原活块所有纤维总宽至多 $2N$。因此每个块的预算由 $10YDS+4\epsilon N$ 乘 $2 C_{\rm prof}R_\rho L^{78}(1+\log D)^4$ 给出。
- 每个母标签至多 $G^6$ 个块，每阶实际 HB 标量至多 3，三个阶合计至多 9，母标签数至多 $G$，其中 $G=\lfloor\log_2(8N)\rfloor+4\ll L$。总对数幂为 $73+5+4+7=89$，最终保守上取 100。令 $\theta=599/1000+15\zeta\le0.59975$。几何余量允许额外 $1/10$ 的幂。`eventually_full_restoration_payment` 实际调用旧 `eventually_one_long_E5_budget`，该引理可取 $\delta=(1-\theta)/2$，吸收 $Y\le N^\delta$ 并保留 $\theta+\delta<1$，同时独立支付 $N\epsilon$ 项的对数费用。最终分别恢复两种原模数通道。

原稿正文第 328–340 行及配套 `distribution-prime-product-completion-20261010.txt` §§6–8 使用严格 rough、有符号短元和精确互素均值的直接 Brun 估计。静审发现的改动属于表达与有限和的显式重排，数学假设与原稿适用范围相符。本文给出的 source-only 判定只覆盖所列单长分支。两个历史差、其余中段算术分支及完整 whole PP 仍待证明。

## 冻结与定位

作者清单 SHA-256 为 `e7bebd73b4007bae07b072965fa926c77f9f756d059640e41c0073e750d4686d`，冻结回执 SHA-256 为 `521e0130a88f679ea363ef29b797f07339121470c157dcb94a7aa5a03d206b6a`。四份 Lean 共 60,164 字节，有 66 个定义或定理。七条清单内容、清单本身及冻结回执的字节数、SHA-256、Git blob SHA-1 已静态校对。复用的四个基础源与原基础审查清单 `035c1602` 对应。原声明及证明体保留在已发布包中。

作者依赖说明的 `upstream_recheck` 报其当时未能重读两条历史路径。独立复核通过 Windows 扩展长度绝对路径在原位置打开 `P5GroupedOccurrenceLogShift.lean`、`P5AllWordAmbientOccurrenceBound.lean`，两者的三项指纹均与冻结定位一致。`P5SmoothChartHBDyadicPartition.lean` 同样可从本地原路径静读，SHA-256 为 `75526601e62d131bf00f850725ee2ad9de2b34a0bd5baa57ab3147893ad69bec`。依赖表内 59 个带本地路径的指纹对象（含重复定位）及额外这条 scalar 指纹均已核对。后续的导入、elaboration、kernel、完整类型及公理检查仍待远端验证。

