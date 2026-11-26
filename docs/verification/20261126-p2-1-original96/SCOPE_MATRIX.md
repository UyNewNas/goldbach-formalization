# P2.1 原查询与有理区间执行器范围矩阵

本矩阵把看板 P2.1 第三个子项中的“原可执行 producer”落实到稿内实际调用的整数操作和函数查询。按下列域核对，当前三个新增模块补上了作者的 96 项对数和 P160 直接四角除法。其余表内操作均有已验收定义或可从已验收的线性解码等式直接导出。全节点结论仍取决于文末列出的联合核验结果。本文件记录源码审阅，不签发编译、内核或看板验收。[11 月 4 日原看板第 65–68 行及 E1/E2 第 264–273 行](https://chatgpt.com/library?file_id=libfile_ab188d198fc481919635b50e2d5dd79c&account_id=personal)

## 作者的 P160 区间

冻结稿为 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。数值附录第 94–120 行规定定向舍入及 paired-cell 对数的精度。作者源文件 `verification/data/corpus-renewal-paired-certificate-v2-20261010.py` 的 Git blob 是 `ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce`。第 13–16 行定义尺度和整除，第 24–48 行定义区间，第 50–61 行定义对数，第 140–144、160–170 行给出调用。下表取 $P=2^{160}$、$W=2^{224}$。对原区间 $X=(l,h)$，两整数按 $l/P,h/P$ 解码，构造断言要求 $l ≤ h$。[冻结稿](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L94-L120) · [固定作者原程序](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/corpus-renewal-paired-certificate-v2-20261010.py#L13-L61)

| 作者操作与输入 | 两端的精确对应 | 已有证据及核验边界 |
|---|---|---|
| `Interval(q)`，第 25–28 行，任意有理 $q=n/d$，$d>0$ | 返回 $(⌊nP/d⌋,⌈nP/d⌉)$。旧 P160 的 `ofReal_int_div_source n d hd` 将构造器两端等同于 `n*P160/d` 与 `up (n*P160) d`，其中 `up a b = -((-a)/b)`。 | 旧 140 中 `ActualThirdOriginalRoundedNewOperations.lean` 第 16–18、43–60 行给出精确整数等式和 `ofReal_sound`。任意规范有理数用整数分子和其正分母实例化。该旧文件来源于另一 P160 计算，这里按逐操作定义和共同尺度对应到 paired 程序。 |
| `raw=True`，第 25–28 行，本程序传入有序整数对 | `IV.mk l h` 两投影按定义等于 `l,h`。 `Encloses` 解码为 `value l ≤ x ∧ x ≤ value h`。 | 旧 `ActualThirdOriginalRoundedNewOperations.lean` 第 10–14 行及 `ActualThirdOriginalFixedpointClippedChord.lean` 第 11–13 行。可用 `rfl` 检查投影。原程序在构造处执行顺序断言，Lean 的载体允许任意整数对，比较执行结果时保留该输入域。 |
| `__add__`、`__radd__`，第 29–32 行 | 对有序整数对返回 $(l+l',h+h')$，无舍入。逐端使用 `value_add` 后就是解码端点相加。非区间实参先走 `Interval(q)`。 | 旧文件 `ActualThirdOriginalFixedpointClippedChord.lean` 第 47–48 行导出 `ImbalancedChen.OriginalThirdClippedChordSourceOnly.value_add`。旧 `P2DirectedLogRounding.Enclosure.add_contains` 给出有理区间包含。旧 140 中这两处分别给线性恒等式和语义。另有 `ActualThirdOriginalPositive256Log.lean` 中的 `add` 与 `P4AOriginalExecutableLog32.lean` 中的 `addIV`，这两个文件均未列入该 140 清单。联合契约可直接以字面整数对证明此行，无需导入它们。 |
| `__neg__`，第 33 行 | 返回 $(-h,-l)$，包含原有真值的相反数。由 `value_zero`、`value_sub` 可得 `value (-i) = -value i`。 | 旧 `ActualThirdOriginalFixedpointClippedChord.lean` 第 31、50–51 行及 `P2DirectedLogRounding.Enclosure.neg_contains`。后者针对有理 `Enclosure`。建议联合契约对字面 P160 整数对和 `Encloses` 实例化，明确交换左右端点。 |
| `__sub__`，第 34–36 行 | 加上相反数后，两端为 $(l-h',h-l')$。 | 旧 `ActualThirdOriginalRoundedNewOperations.lean` 第 20、64 行的 `sub` 和 `sub_sound`。整数等式使用 `sub_eq_add_neg`。两个实参数各自由其输入区间包含即可。 |
| `__mul__`、`__rmul__`，第 37–41 行 | 对四个带符号端点乘积取最小值及最大值，按 $P$ 逐端向下、向上整除。旧 `fourLo`、`fourHi`、`mul`、`up` 直接给出相同整数式。 | 旧 `ActualThirdOriginalRoundedNewOperations.lean` 第 16、22–28、112 行的定义及 `mul_sound`。允许任意符号，包括跨零区间。新的 96 项循环中 `positiveMul` 只负责工作尺度的非负奇次幂运算。 |
| `__truediv__`，第 42–47 行 | $Y=(l',h')$ 满足 $0<l'≤h'$。下端取四个 $⌊nP/v⌋$ 的最小值，上端取四个 $⌈nP/v⌉$ 的最大值，其中 $n ∈ \{l,h\}$、$v ∈ \{l',h'\}$。 | 新 `P2OriginalP160DirectDivision.directDiv_eq_round160` 给出解码后两端与精确有理区间除法最后一次 160 位舍入的等式。`directDiv_contains` 使用两个 `Encloses` 和 $0<l'$，容许有符号分子。契约中的 $2/3$ 验证作者的上端比先舍入倒数再乘的 `divide` 少一个整数单位。[直接除法契约](../../../verification/part2/original96/P160DivisionContract.lean) |
| `log_interval(q)`，第 50–61 行，$1≤q≤2$ | 按 $W$ 定向执行 96 次旧幂累加及新幂更新，末端下界截取，上界加入原 `TAIL`，再以 $2^{64}$ 缩放。`tail_eq_one`、`remainder_le_tail` 给出该单位对现有对数余项的支付。 | 新 `P2OriginalLog96Series.lean`、`P2OriginalLog96.lean`。命名空间 `ImbalancedChen.Certificates.P2OriginalLog96` 内的 `logInterval_eq_source` 比较递归和逐操作的原形 fold。`certificate_valid` 与 `logInterval_contains` 在指定域证明返回两整数解码后包含 `Real.log q`。边界 $q=1$ 返回 `(0,1)`。[公开契约](../../../verification/part2/original96/PublicContract.lean) |
| `record()`，第 48 行 | 输出 `str(F(lo,P))`、`str(F(hi,P))`；数学对象仍为上述两个有理端点。 | 源码对应终点在精确有理数值。Python 字符串格式和缓存行为没有额外稿内估计。 |

表中旧文件均可在验收源码提交 `1de0453bee55bf1128be422787216937b8fda9c9` 查看。只有明确列入旧清单的 owner 才计入原验收。直接除法沿用旧 `IV`、`Encloses`、`up`、`P160` 和 `Enclosure.divisionBounds`，另外提供二字段转换 `toEnclosure`。上述对照不要求把 Python 类、解释器或序列化程序形式化。[旧 owner 清单](../20261125-p2-1/TARGETS.json) · [旧 P160 线性解码](https://github.com/UyNewNas/goldbach-formalization/blob/1de0453bee55bf1128be422787216937b8fda9c9/ImbalancedChen/ActualThirdOriginalFixedpointClippedChord.lean#L31-L51) · [旧 P160 整数算术](https://github.com/UyNewNas/goldbach-formalization/blob/1de0453bee55bf1128be422787216937b8fda9c9/ImbalancedChen/ActualThirdOriginalRoundedNewOperations.lean#L10-L64)

## 五个已经验收的查询根

| 查询和原参数 | 已验结果与域 |
|---|---|
| P112 原尖锐表，网格 16384、终点 12、公开尺度 P160 | `OriginalU2All40CheckedTable20261024wSourceOnly.literalBlocks_read_eq_original` 证明整份 40 块 reader 与原有限整数递推相等。`P0All40PublicQuery.query_eq_original_all` 与 `public_query_encloses_all` 覆盖所有有理点，含 $q≤2$、格点、插值及 $q>12$ 终端分支。`query_range_encloses_all` 覆盖任意有理端点之间的实数。外部历史字节对照单独记录到初始四列与 Block01。看板和稿件未指定须匹配的另外一份全表序列化文件。 |
| 同一公开表的有理点、区间适配器 | `OriginalU2RationalQueryPublicAPIP0SourceOnly.pointQuery_sound` 与 `rangeQuery_sound` 给出闭域 $[2,12]$ 的实函数包络。其整数表示适配器 `pointQuery_int_div` 要求分子非负、分母为正；上一根的 `query_integer_encloses_all` 允许任意有符号分子和正分母。 |
| 历史 Q80 paired `Ordinary(16384).f` 以及其原 32 项对数 | `P2HistoricBackendTypeAdapters.sourceSf_delegation`、`sourceSf_lo_exact`、`sourceSf_hi_exact`、`sourceSf_contains_actual` 对所有有理数绑定 `sf 16384 8`。`sourceLogI_lo_exact/hi_exact` 绑定原 Q80 的 `logI`，`sourceLogI_contains` 保留初始舍入下端严格为正的条件，`sourceLogI_ratio_contains` 适用于 $0<l≤r$ 的正比值。 |
| 原 compact Q80 表，网格 16384、终点 12 | `P2OriginalCompactQ80TableSourceOnly.point12_contains_actual` 覆盖任意整数分子和正整数分母，`sf12_contains_actual` 覆盖所有有理 $q$。终点 8、终点 12 的两个原查询分别接受核验。 |
| 四前缀实际 Buchstab 闭区间 | `P5Z.AutomaticBuchstabIntervals.actual_interval_bounds` 给出 $m>0$、$1≤l≤s≤u≤8$ 的确定性有理上下界，包括单点和格结点。原生行的参数窗口 $2≤l≤u≤8$ 在该域内。它支持稿中 $\omega((1-S)/z)$ 的区间界。若某笔费用指定作者 Q80/4096 或独立 N48/8192 表的整数，应在该消费者处给出该整数的证据。看板未单列两套历史表对任意查询整数均相等的要求。 |

具体模块、26 个具名目标、140 个 owner 的验收及其版本见原结果。数值附录第 122–175 行规定延迟函数和弦积分方向，第 425–445 行规定四前缀 switched 核与分区；原看板的 P2.1 第三个子项记录公共接口与原执行器的剩余责任。E2 第 268–273 行说明旧 Q80 数学版本验收未含 `qpow/box/Repr/decision-instance` 的 VM 实现。原程序在稿内所需的数值返回和有向包络可以按上述具体接口核对。[原五根验收](../20261126-p2-1/P21_STATUS.md) · [查询生产器分工](../20261125-p2-1/PRODUCER_BINDINGS.md) · [稿件对应与原生 Buchstab 范围](../20261125-p2-1/MANUSCRIPT_SCOPE.md)

## 整节点验收判断

在以上稿件、原查询输入域和 11 月 4 日看板定义下，本次审阅没有定位到其他需要新算法或新解析定理的 P2.1 义务。整节点的最小收尾是把以下证据绑定到同一源码和工具链环境。

1. 保留旧五根的既有验收。本次 P2 作业 `aacffde21ac8418e88d591bd7769bfc5` 已验证 3 个新增 owner 的严格编译记录：前两个沿用 attempt-001 的相同源码记录，直接除法在 attempt-002 新编译；随后三个 owner 均新执行 stock kernel replay 与 owned 审计，并完成两份公开契约；20,290 个实际对数输入的两端整数均与原程序一致。作业末尾单次 stdout 传回完整归档时超过传输预算。原始证据的分块取回与校验由独立执行记录记载，本矩阵不把单次归档传输记为成功。
2. 在可复用的旧 140 个对象及其原生依赖环境中联合导入旧五根、新 `P2OriginalLog96` 和新 `P2OriginalP160DirectDivision`。前者已传递导入 `P2OriginalLog96Series`。联合探针引用上表关键目标，核对原五根可用、三个新 owner、真实 `IV/Encloses` 及 `Real.log` 类型在同一环境兼容。已有对象按源码、对象、工具链与依赖绑定复用。
3. `P160RemainingContract.lean` 中的十条全称实例覆盖 `IV.mk` 的两个整数投影、任意规范有理数的精确 P160 构造和包含、字面加法和取负的包含、减法和乘法的端点定义及包含。最后一条把 `logInterval q` 的两个整数装入 `IV.mk`，直接调用 `logInterval_contains` 推出 `Encloses`。将此文件与联合探针一起按同一对象集执行，并保存退出码。[P160 其余操作契约](../../../verification/part2/original96/P160RemainingContract.lean)

上述收尾实际通过后，可以按此明示范围接受 P2.1。单项的编译成功或本矩阵均不能替代联合回执。P2.4 的自适应 compact 分割树及各叶 charge，P2.7 的 same-mask 全行、各 strip 核算与总收益，P2.9 的 17,572 行实际积分许可，以及 P5.3 的 U7 saved-total、P5.4 的 U10/U11 策略和费用，分别留在其消费节点。全 P2 及主定理的状态另行验收。[原分工](../20261125-p2-1/MANUSCRIPT_SCOPE.md) · [原看板与子项](https://chatgpt.com/library?file_id=libfile_ab188d198fc481919635b50e2d5dd79c&account_id=personal)
