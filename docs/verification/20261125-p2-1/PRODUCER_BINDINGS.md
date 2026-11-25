# P2.1 查询的生产器与证明

本批源码固定为 `8703e635b499907a655180bf97373ffb3fbbaf2a`，涵盖五个核验根、140 个项目模块和 26 个具名定理目标。前两根共用一个 P112 生产器；第五根复用 P2.4 的原 compact Q80/M12 数学查询。手稿固定为 20261106 英文发布稿 `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`。[核验目标](TARGETS.json)

| 核验根与参数 | Lean 中可核验的对应关系 |
| --- | --- |
| `All40PublicQueryAllBranches`，网格 $n=16384$，终点 $M=12$，内部 P112、公开 P160 | `literalBlocks_all40_checked` 对 40 个各含 4096 次更新的具体块逐块给出检查等式。初始段为索引 0–32768，更新段为 32769–196608。`literalBlocks_update_semantics` 给出每一步的原弦递推等式，`literalBlocks_read_eq_original` 给出整个 `assembledRead literalBlocks = originalFinalNodes`。`literalBlocks_query_eq_original` 对整数分子分母给出两端读取等式，`P0All40PublicQuery.query_eq_original_all` 进而对每个有理数把这两端与 `originalQueryLo160/Hi160` 的整数返回值逐一相等。`public_query_encloses_all` 给出按 $2^{160}$ 解码后的真值界。覆盖 $q\le2$ 零支、紧段内结点与插值、$q>12$ 终端下筛下界和上筛上界；P112 输出精确乘 $2^{48}$。[原查询说明][sharp] · [具体块与递推][blocks] · [全分支公共等式与界][all] |
| `P0RationalQueryPublicAPI`，同一生产器的有理区间接口 | `pointQuery` 将原公开两端解码为 `IV`。`pointQuery_int_div` 对非负分子和正分母给出整数读取形式。`rangeQuery_sound`、`rangeQuery_rational_bounds` 对 $2\le l\le h\le12$ 给出整段真值界。前一根的 `query_integer_encloses_all` 接受任意有符号分子和正分母，`query_range_encloses_all` 允许任意有理端点及其中的实数，证明用的是真实下筛函数单调性。[有理区间 API][iv] · [具体表点查与区间查][all] |
| `P2HistoricBackendTypeAdapters`，paired `Ordinary(16384).f`，$M=8$，$Q=2^{80}$ | `sourceSf_delegation`、`sourceSf_lo_exact/hi_exact` 将返回整数绑定至 `sf 16384 8` 的 `point`。`state` 按索引递增更新四个整数，`trapLo/Hi` 保留内外两层舍入，`point` 依次处理零、终端、结点或插值再除以查询参数。`sf_contains_actual` 对此递推归纳，`sourceSf_contains_actual` 暴露全有理数的界。`sourceLogI_lo_exact/hi_exact` 对应 `logI` 的整数输出，含初始 Q80 舍入、二进制范围约化、32 个奇数次项和分母含 65 的尾界。`sourceLogI_contains` 的前提是舍入后的下端点为正；`sourceLogI_contains_of_one_le` 供 $q\ge1$ 调用。这里的精确性来自 Lean 定义与归纳。历史 Python 的对应依据是冻结源码的逐运算对照；单行保存值还需 `fullSourceRowCheck`，总计另需相应检查。[作者筛表][pytable] · [作者对数][pylog] · [paired 参数][paired] · [整数递推][historic] · [对数解释][log] · [接口][adapter] · [保存行调用][binder] |
| `P5ZU1011AutomaticBuchstabIntervals`，$m>0$，有理数 $1\le l\le u\le8$ | `node m k` 在 $k\le m$ 初始化为 $(1,1)$，随后用前一结点和延迟结点作有理矩形积分，传播 $s\omega(s)$ 的界。`generated_check` 从 `node_step` 和 `generated_valid` 证明生成表通过原有理递推检查，调用者无需交付数组或通过凭据。记 $x_k=1+k/m$、结点上下界为 $L_k,U_k$。格界为 $\max(0,L_k/x_{k+1})$、$U_{k+1}/x_k$；对 $k<7m$ 中与 $[l,u]$ 闭相交的格取最小下界、最大上界。`actual_interval_bounds` 对每个 $s\in[l,u]$ 包住真实 Buchstab 函数。该定理的返回值类型为有理数；历史 Q80/4096 或独立 P112/8192 数组的整数身份需各自举证。[稿内延迟方程][delay] · [生成表与检查等式][nodes] · [格界][cells] · [相交规则与区间定理][omega] · [两种历史网格][meshes] |
| `P2OriginalCompactQ80Table`，原 compact `SieveTable(16384,12)`，$Q=2^{80}$ | $I_{3,c}$ 使用终点 12 的原 Q80 梯形表。`point12_contains_actual` 针对具体 `point 16384 12 a b`，允许任意整数分子及正分母；`sf12_contains_actual` 针对每个有理 $q$，证明 `sf 16384 12 q` 包住实际下筛函数。涵盖零支、表内结点与插值、$q>12$ 终端分支，调用者无需提交状态有效性或真值包络。该文件从 P2.4 逐字节复用，为本批新增的唯一模块，SHA-256 为 `e9f37ac098bb46dc8befa0211d7c39ac8a0907ef675b9ebca824ffa58d49e66a`。[稿内紧域项][compact] · [本批全域点界][compact-sound] · [来源记录][compact-intake] |

## 与 P2.4 共用的源码

历史对数所依赖的 `P2DirectedLogRounding.lean` 采用 P2.4 的递归证明修复，SHA-256 为 `9dbfd25cc94f8aae9fbb163bda717c84845d3b04296193211ed902a39cccceb0`。此版本保留直接导入与 22 个定理陈述，按新源码核验。[共享修复记录][directed-intake]

紧域计算的增量数组与求值器继续由 P2.4 核验。该分支的 `sourceState_eq_historical`、`sourceTable_eq_historical`、`point_eq_historical` 逐层绑定求值器和历史 Q80/M12 的 Lean 定义，`tableArray_lookup_historical` 绑定增量数组的索引读取。P2.4 还负责自适应树、叶序与逐叶整数费用、逐叶积分和归档总和。第五根的结论止于表中所列点查。[状态与点读等式][compact-read] · [数组读取等式][compact-array] · [P2.4 验收分工][p24]

## 看板结论与验收界限

P2.1 看板明确点名原 P112 尖锐查询表、完整紧段查询与实际表执行。1106 稿把四前缀的 switched 核写为真实 $\omega((1-S)/z)$，并以既定分割、选择和逐行账目完成具体数值比较。看板与这些稿段均未单列“对任意查询重现作者 Q80/4096 的全部 $\omega$ 整数”作为 P2.1 的独立要求。自动根提供指定窗口的真实函数区间；如 P2.7 等消费节点引用某一保存整数、floor 或费用，仍需在该行证明所用端点足以支付，或绑定相应历史整数。该结论限于上述窗口和接口。[原看板清单第 65–68 行][board] · [四前缀核与分割][switch] · [作者与独立检查][meshes]

五根在本批固定源码上的正常编译、内核回放、公开类型及所属声明的传递公理审计均待取得回执。早一轮正常编译针对 `a06d5f2a7e`；修复后的续编任务排队记录只说明已安排验证。单次编译成功只能记为编译回执。Lean 读取等式所指对象是文中列出的具体 Lean 定义；历史 Python 运行和外部序列化文件字节的身份由各自的溯源或比较记录支持。当前整项状态以独立验收记录为准。[核验目标](TARGETS.json) · [可复用证据](REUSED_EVIDENCE.json)

[sharp]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/numerical-third-compact-source-review-20261010.txt#L144-L154
[compact]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L198-L233
[delay]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L122-L175
[switch]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L425-L445
[meshes]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/sharp-248-four-min48-independent-review-20261008.tex#L40-L49
[paired]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/corpus-renewal-paired-certificate-v2-20261010.txt#L85-L97
[pytable]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/certify_extended_prefix.py#L51-L116
[pylog]: https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/certify_conservative_chen.py
[blocks]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/Certificates/OriginalNodeArraysV1/All40CheckedTable.lean#L765-L842
[all]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/Certificates/OriginalNodeArraysV1/All40PublicQueryAllBranches.lean#L11-L61
[iv]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P0RationalQueryPublicAPI.lean#L25-L125
[historic]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P2HistoricSieveTableSemantics.lean#L64-L132
[log]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P2HistoricLogPointInterpreter.lean#L7-L24
[adapter]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P2HistoricBackendTypeAdapters.lean#L25-L115
[binder]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P2HistoricalSavedFloorFullBinder.lean#L44-L149
[nodes]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P5ZU1011AutomaticBuchstabNodes.lean#L20-L82
[cells]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P5ZU1011AutomaticBuchstabCells.lean#L19-L20
[omega]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P5ZU1011AutomaticBuchstabIntervals.lean#L48-L130
[compact-read]: https://github.com/UyNewNas/goldbach-formalization/blob/67e0791e62db299690d29f19440bcf579e5e1492/ImbalancedChen/P2OriginalCompactQ80Encloser.lean#L89-L107
[compact-array]: https://github.com/UyNewNas/goldbach-formalization/blob/67e0791e62db299690d29f19440bcf579e5e1492/ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean#L73-L101
[compact-sound]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/ImbalancedChen/P2OriginalCompactQ80Table.lean#L127-L178
[p24]: https://github.com/UyNewNas/goldbach-formalization/blob/67e0791e62db299690d29f19440bcf579e5e1492/docs/superpowers/plans/2026-11-25-p24-original-compact.md#L3-L20
[board]: https://chatgpt.com/library?file_id=libfile_ab188d198fc481919635b50e2d5dd79c&account_id=personal
[compact-intake]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/docs/verification/20261125-p2-1/COMPACT_PROVIDER_REUSE.json
[directed-intake]: https://github.com/UyNewNas/goldbach-formalization/blob/8703e635b499907a655180bf97373ffb3fbbaf2a/docs/verification/20261125-p2-1/SHARED_REPAIR_REUSE.json
