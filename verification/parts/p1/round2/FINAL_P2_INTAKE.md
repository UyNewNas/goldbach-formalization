# P1 最终 P2 增量接收记录：E0 前 64 行

## 1. 结论、时间与固定来源

**P2 已新增原始 E0 行 `[4,64)` 的 60 项实际四重积分认证，并与旧
Prefix4 合成前 64 行的有限积分和。P1/P2 的历史、坐标和选盒接口没有改变；
本次没有取得实际历史 parent、原始 prime-box 并域或 stored-cap 表的绑定实例。**
这是一份只读生产者证据接收记录，不是 P1 重编译、整合验收或完整构造完成声明。
依据为固定新头的 [ROUND3_HANDOFF][handoff]、[收据][receipt] 和三个新生产源。

父会话在 `2026-10-12 13:09:49 UTC` 观察到分支更新。本次实际固定 SHA 读取
始于 `2026-10-12 13:10:49 UTC`，结束于 `2026-10-12 13:14:33 UTC`。
GitHub 返回新发布提交时间为 `2026-10-12T12:59:20Z`。
旧 [UPSTREAM_INTAKE.md](UPSTREAM_INTAKE.md) 的 12:05 历史快照保持原文。

| 身份 | 完整 SHA / 来源 |
| --- | --- |
| P2 分支 | `chatgpt/chen-p2-certificates` |
| 比较旧头 | [`076473720210ee602e6e9735902e16bb6c5f1398`](https://github.com/UyNewNas/goldbach-formalization/commit/076473720210ee602e6e9735902e16bb6c5f1398) |
| 本次读取的新发布头 | [`e6d6d57323cc358cef060fb243ec386c13cb662d`](https://github.com/UyNewNas/goldbach-formalization/commit/e6d6d57323cc358cef060fb243ec386c13cb662d) |
| 新增数学源码提交 | [`f0c00f9ccce98e04af439321a92eb9fd0dd26203`](https://github.com/UyNewNas/goldbach-formalization/commit/f0c00f9ccce98e04af439321a92eb9fd0dd26203) |
| 旧九模块数学源码提交 | `6acf61cc28f227a9154363f2347c386ec01dffb0` |
| 共同证明基线，未替换 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 冻结手稿，未替换 | `ba6ec11d800eccc54406490631895e174de85766` |
| 冻结手稿 body blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |

[旧头到新头比较][compare] 返回 ahead 2、behind 0、67 个变更文件。
其中新增三个生产模块；已有文件只改 P2 的生成器、专项 workflow、
`CertificateAudit.lean` 和 `check.sh`。旧九生产模块、既有接口、共同 map
和依赖声明没有出现在变更表。[数学源码到发布头比较][binding-compare]
只返回三个元数据文件：本轮 handoff、PUBLICATION 和 receipt；生产源码没有改变。
这不构成新的 Part 0 基线单，也不授权把发布头当作 P1 证明基线。

## 2. Prefix4 的实质进展及准确范围

`PairedV2Prefix4` 本身没有重写。新增 `PairedV2Batch4To64Data` 存储原始
ordinal 4 至 63 的采用数据；`PairedV2Batch4To64` 校验证书并连接真实积分；
`PairedV2Prefix64` 复用旧四行和新六十行的界，以 `Fin.append` 拼接。
新增批次中 `rowOrdinal i = 4 + i.val`；累计 `rowOrdinal i = i.val`。
第 64 行没有计入认证数量。[源码][prefix64] 另用 63 个相邻整数键严格不等式
证明实际 `rowIndices` 单射，而非仅假设 ordinal 不同就代表格子不同。

| 实际积分和 | 原始行范围 | 精确下界 | 精确上界 |
| --- | --- | --- | --- |
| 旧 `Prefix4.integral` | `[0,4)` | `12676565261567/10^20` | `12676572571081/10^20` |
| 新 `Batch4To64.integral` | `[4,64)` | `190579962282066/10^20` | `190580072663307/10^20` |
| 累计 `Prefix64.integral` | `[0,64)` | `203256527543633/10^20` | `203256645234388/10^20` |

关键新接口位于命名空间 `ImbalancedChen.Certificates.PairedV2`：

- `Batch4To64.certificate_inputs`：证书参数等于实际采用行的固定外层坐标和 cutoff。
- `Batch4To64.rowIntegral_eq_certificate`、`rowIntegral_bounds`、`integral_bounds`：真实逐行积分及六十项和的上下界。
- `Prefix64.source_ranges_disjoint`、`source_ordinal_coverage`：两段 ordinal 恰好覆盖 `[0,64)`。
- `Prefix64.rowIndices_injective`、`prefix_batch_indices_disjoint`：实际网格索引无重复。
- `Prefix64.integral_eq_parts`：`Prefix64.integral = Prefix4.integral + Batch4To64.integral`，证明复用 `Fin.sum_univ_add`。
- `Prefix64.integral_semantics`、`integral_bounds`：从真实坐标定义的 64 项四重积分和及其累计上下界。

以上完整编译器关键类型见 [key-theorem-types.txt][key-types]。
累计和已经包括旧首格及整个 Prefix4；不得再加一次旧四行或首格收益。
这些有限索引不重计结论尚不是几何并域互不相交、strict Ico prime-box 身份或
完整 mask 积分身份；源码注释、handoff 和 receipt 的 scope 均明确保留这个区别。

## 3. 数据字段、坐标和端点

原始七字段顺序仍为
`group,t_index,u_index,exact_Z,discarded_floor_Q80,extra_lower_Q160,extra_upper_Q160`。
采用源仍是原 CRLF 文件，SHA256
`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`，
Git blob `49499697cca96de5f7b779e95077874ce5f9d119`。
新 `[4,64)` LF 七字段流 SHA256 为
`86c9f08228f08e98a9f1467fc353f1f01bdb5878e0d01e8a678debc664c661ab`；
累计 `[0,64)` 流为
`f89caa496a9672c1dc9285a22f1e010008a0d6ea6e9ff850fb09747586afaaf9`。
本 intake 没有重读全部 17,572 行原 JSON；这些采用流身份由发布 handoff/receipt
给出，三个取回生产源的完整 Git blob 和 SHA256 已独立核对。[数据与范围][handoff]

| 项目 | 新头实际约定 | 对 P1 的影响 |
| --- | --- | --- |
| 历史 mesh | `Fin d → Fin (m+1)`；分母 `m+1`；坐标逐项左闭右开 | 与 P1 原网格一致，无替换为 `m` 或修改端点。 |
| 历史存储 | `history.reverse.getD i.val 0`；第五层处理坐标严格递减 | 保留反向存储字典和真实排序，数值解码不得隐含重排。 |
| paired fibre 坐标 | `(t,u,z,w)`；`tl<t<tr`、`ul<u<ur`、`a<w<z<Z` | 这是连续开纤维的坐标；仍需与实际素数 tuple/历史 carrier 证明身份。 |
| cutoff | `Z = min(ul, 3*(1-tr-ur)/13)`，冻结在外层格子端点 | `exact_Z` 是纤维 cutoff，不是历史 cap，也不应在内点重算。 |
| 归一化 | 正号核 `K/(80*t*u*z^2*w)` | `K/80` 已含 `1/20` 与 Chen 的 `1/4`，只用一次；这里的固定核常数不代表完整上界 K 已认证。 |
| 原数值来源 | Q160 端点保留来源身份；新 bounds 由实际 checker 推出 | receipt 明确 `original_Q160_enclosures_used_as_proof_premises = false`。 |
| discarded floor | 本新增批全部原 Q80 floor 为零 | 不能由此推出全部 saved-floor estimator 或完整历史误差账。 |

[P1 接口][interface] 的 Git blob 仍是
`ad46c9e1bc9ef11692b7650fbb5372e8f4174706`，与旧快照完全相同。
它仍要求离散素数边界质量先由 P1 控制，再在连续积分侧使用零测边界等式。
新 batch 包含 `uUpper=h` 的原始行 4、9、15、23、32、43、55；P2 按已证开纤维
端点约定接收这些行，没有把它们跳过。该连续结论不能直接充当实际离散边界支付。
`p ∤ N`、严格素数排序、原始上截断及唯一盒归属仍须由实际 carrier 字典保留。

## 4. 历史 old/new 和任意存储有理 cap 的兼容性

未变的 [PART1_INTERFACE][interface] 继续要求两个独立的严格 own-cube
指示函数，积分差方向为 **new minus old**；它成为 upper saving 的符号须由
实际树恒等式供应。普通 fifth parent 的两个 old 门不足以取代历史祖先门，
第五 own-cube 仍不得加入 candidate enumeration，未选中处仍要回退。
新三个 paired 模块没有提供这些历史 joint-cell/parent 身份。

**兼容性判断：P2 没有提出与 P1 stored-cap permit 冲突的新字段约定，
但也没有交付它的实际表实例。** P1 的已验证
[StoredHistoricalBoxPermit 接口](permit/KEY_THEOREM_TYPES.md) 接受任何通过
严格 whole-box 检查的存储有理 `cap`，不要求等于 midpoint。调用方仍须给出固定于
`N` 之前的 `J`、`I j`、`old j`、`nu j`、`cap j`，并证明 `old j` 是真实有效历史
祖先值，包括 fallback。新的七字段 paired 行不是这一五字段历史许可表：
`exact_Z` 与 cap 语义不同；`rowIndices` 单射不能替代 `old j = D.old5 j`
之类的身份，更不能由通过某个任意较小 old 的检查取得真实 parent license。

本次取回的三个新生产源没有引用 `storedBoxCapCheck`、`storedMeshCapCheck`
或 `HistoricalPrefixCapData`。因此只确认协议可衔接，未声称 P2 已采用、实例化或
确认 P1 新 permit。P2 接口仍保留“proposed interface / 未代表其他会话已确认”的
措辞；本记录不替 P2 更改确认状态。

## 5. P2 生产者验证范围与本次只读核对

固定 [producer receipt][receipt] 的状态为
`PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT`，其实际取回字节 SHA256 是
`e4eb7548bde3b578109f05a42840b6e5ec2076991bc11fbf69fcc4f6fde8a29a`。
本次核对了它与 PUBLICATION 的同源绑定、三个完整生产源、六个生产门原日志及
[axiom-counts.json][axiom-counts]。三个日志均有相应 `FRONTEND_OK`，
`trustLevel=0`、strict/warningAsError；三个 checker 日志均有请求模块的
`replaying` 行，其退出码在绑定收据中均为 0。所有六个取回日志的完整内容哈希
与 receipt 归档清单相符。

| 新生产模块 | producer strict / replay | 所属声明数 | 源 SHA256 | `.olean` SHA256 |
| --- | --- | ---: | --- | --- |
| `PairedV2Batch4To64Data` | `0 / 0` | 72 | `4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c` | `61b3d3eeef416c6293ebdba0b5b1ac89a1d0d44e99be316f6139c2d51d60b259` |
| `PairedV2Batch4To64` | `0 / 0` | 207 | `c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4` | `6beb6f075f9d8539026bdd18716d9f3e6175a7253ec04244f7b1f8bf80637562` |
| `PairedV2Prefix64` | `0 / 0` | 121 | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` | `43adce492a503e2fc3bae8ab1d5f1e2586f17f20307bb1bc78258a2810436bca` |

P2 的联合 audit 编译退出 0，覆盖旧九加新三共十二模块、709 个声明；新增
`72+207+121=400` 条，旧 309 条编译器记录被生产者重新枚举并逐条比较为不变。
统计包含 private/generated，标准传递公理仅 `propext`、`Classical.choice`、
`Quot.sound`，所属 unsafe/新 axiom 声明计数为 0。旧九模块 compile/replay
复用第二轮确切源码回执，不能计作本轮十二次新编译/重放。

本 intake 没有重新执行 Lean、checker、P2 接收校验器或 CI，也没有逐条重新
审计全部 709 个声明；审计统计来自已发布 receipt/counts。一次指定 audit log
尾段的读取返回空内容，原请求和返回已保留；未将其当作成功读取整个审计日志。
P2 回执明确没有 full lake build、fresh imported-closure replay、完整历史 mask、
hLower 或 hUpper 供应。生产者保留的失败/中断尝试不计入最终成功门。

PUBLICATION 在发布时将新头 CI 标为 `NOT_YET_TRIGGERED_FOR_BINDING_COMMIT`。
本次没有查询或触发后续 Actions run，因此不推断当前远端 CI 成败，也不移用旧头
CI 成功。P2 producer 结果不替代 P1 本轮 permit 回执或 Part 0 的整合门。

## 6. P1 与后续 Parts 仍需补齐的输入

| 接收方 | 可接收的新结果 | 仍未闭合 |
| --- | --- | --- |
| P1 / P5 | E0 新六十项与累计六十四项实际积分界；确切 append 和网格索引不重计 | 与实际配对修正、真实采用区域、历史 parent、素数计数及 `pairedLocalIntegral` 的身份。 |
| P1 / P2 | 原 mesh、处理坐标、端点、own-cube 分离约定保持一致 | adopted `J/I/old/nu/cap` 表、历史祖先绑定、有限合法性实例、实际支持与 fallback。 |
| P1 / P5 | 开纤维几何和连续积分供给 | 原 Ico 唯一归属、离散边界支付、共同历史并域和截断/旧 floor/保留项的完整有符号误差账。 |
| P4 | A 旧 coarse-chart 结果保持原范围 | 本轮没有扩大 A 或完整上界 K 证书。 |
| P0 | 两个固定 P2 SHA 和生产者范围证据 | 在整合后的完整 SHA 上接收、导入及运行统一 root 门。 |

剩余未认证 E0 原始区间是 `[64,6091)`；E1 为 `[6091,17572)`。
saved-floor 的真实语义、完整 mask/历史构造、K/c、最终 hLower/hUpper 均未由本次
更新关闭。独立报告的完整继承 fifth 源码仍为 **SOURCE_PENDING**；新增 paired
积分认证不是该候选，也不是 P1 普通父树 lower-fourth restoration 的替代品。

## 7. 原始元数据与源身份

原 GitHub connector 返回、固定文件内容、六个门日志和有限核对结果均存于
`/workspace/scratch/127408f63891/p1-round2-final-p2-intake/`。
`compare.json`、`proof_to_publication_compare.response.json` 保存两个限定比较；
`head_commit.json` 与 `base_commit.json` 保存提交消息和时间；
`fetched-identities.json` 记录完整文件的 URL、字节数、Git blob 和 SHA256；
`read_checks.json` 区分实际取回日志、producer exit codes 与未执行的接收门。
该 scratch 元数据不修改任何生产或已验证 permit 文件。

| 已读取固定来源 | Git blob SHA1 | 内容 SHA256 |
| --- | --- | --- |
| [ROUND3_HANDOFF.md](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/docs/part2/ROUND3_HANDOFF.md) | `82533e1c06b660f60cb8758c71007595edb253f4` | `7d3918431650a32f70a88e5601c4eaf047ecf2a2120c3e43b0b8fa1c2dc87bb3` |
| [PART1_INTERFACE.md](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/docs/part2/PART1_INTERFACE.md) | `ad46c9e1bc9ef11692b7650fbb5372e8f4174706` | `f495da9492dc742b8deb608694bd1ddf85b2ca27a3d9d249ac1b0e45b3dabf47` |
| [round3/PUBLICATION.json](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/PUBLICATION.json) | `6b9e778262fc80f8868958342a510d7a149c4faf` | `8f35b8ab538bb78d514d522b707ac0287d23d12b3fc64e67d7199c5ef4343243` |
| [batch4-to64/receipt.json](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/batch4-to64/receipt.json) | `fc1b4061f4b6dfbd9e5ac8476cdfd4eac431e516` | `e4eb7548bde3b578109f05a42840b6e5ec2076991bc11fbf69fcc4f6fde8a29a` |
| [PairedV2Batch4To64Data.lean](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean) | `dd3ae42f58bb3a11ae22bf9619e5e30caf630596` | `4cf955fd381af6b405daa00dba827aada4f174eedda152ccd5de7b15cdaa5b0c` |
| [PairedV2Batch4To64.lean](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/ImbalancedChen/Certificates/PairedV2Batch4To64.lean) | `a6f77ee5f56dce46a9a559d8f3cb60d70c0b6a53` | `c8f78bbb79fc111aaad09ac49f0685bc51d37e67171418290cab9cd8b7724cb4` |
| [PairedV2Prefix64.lean](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/ImbalancedChen/Certificates/PairedV2Prefix64.lean) | `b06442f1dea7c84c298f0d15c60322d50b2a3863` | `11b0d1bf69c25abf05256eb0e6d52b2c743d37b47650a15ba6da90e2a453d7da` |
| [key-theorem-types.txt](https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/batch4-to64/key-theorem-types.txt) | `957daf62a47485a387740e4fc3ae56a1c4d53251` | `9e9f3867c7416525e3158c14323714cbd8403cce59d7863b06ed49808896163b` |

[compare]: https://github.com/UyNewNas/goldbach-formalization/compare/076473720210ee602e6e9735902e16bb6c5f1398...e6d6d57323cc358cef060fb243ec386c13cb662d
[binding-compare]: https://github.com/UyNewNas/goldbach-formalization/compare/f0c00f9ccce98e04af439321a92eb9fd0dd26203...e6d6d57323cc358cef060fb243ec386c13cb662d
[handoff]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/docs/part2/ROUND3_HANDOFF.md
[receipt]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/batch4-to64/receipt.json
[interface]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/docs/part2/PART1_INTERFACE.md
[prefix64]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/ImbalancedChen/Certificates/PairedV2Prefix64.lean
[key-types]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/batch4-to64/key-theorem-types.txt
[axiom-counts]: https://github.com/UyNewNas/goldbach-formalization/blob/e6d6d57323cc358cef060fb243ec386c13cb662d/verification/part2/round3/batch4-to64/axiom-counts.json
