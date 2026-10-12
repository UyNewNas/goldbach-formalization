# Part 1 round 3：继承第五层实际 saving 与真实积分

**已完成可验证里程碑。** 四个生产模块连同历史回归 probe 和新完整声明审计，共通过 6 次严格原前端编译、6 次原 checker；审计 100 个声明，传递公理仅为 `Classical.choice`, `Quot.sound`, `propext`。准确执行范围与证据见 [VERIFICATION.md](VERIFICATION.md)。

## 固定来源

| 引用 | 完整身份 |
| --- | --- |
| 共同数学基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 手稿 commit | `ba6ec11d800eccc54406490631895e174de85766` |
| 手稿正文 blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| 本轮源码所基于的交付父提交 | `744316efd1887f21c91dd4b63c218fa27704c931` |
| P1 分支 | `chatgpt/chen-p1-history` |
| 已观察的 P0 integration | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 已观察的 P2 交接头 | `101bb2291cd51f9717544ce477122fdd44eda44d` |

未收到替换共同数学基线的 Part 0 完整基线单；观察到新的文档或 integration 头不改变冻结手稿。初始来源核对见 [UPSTREAM_INTAKE.md](UPSTREAM_INTAKE.md)，当前五个固定引用和 P0 新接收状态见 [FINAL_HEAD_RECHECK.json](FINAL_HEAD_RECHECK.json) 与 [FINAL_P0_INTAKE.md](FINAL_P0_INTAKE.md)。

## 本轮闭合的链

1. `HistoricalUpperFiveCellGeometry` 将实际第三 cap 的 rank-four frontier 在同一 Ico owner 内识别为历史共同区域：根第一门、有效第三祖先门、严格下降顺序；保留完整 parent validity、`p∤N`、严格端点和唯一归属。
2. `ActualHistoricalFifthCellIntegral` 将实际第五 tuple correction 精确分解到选中共同格，再分别保留 new / inherited-old own-cube residual，证明每格及固定有限族到真实 Lebesgue 积分的极限。
3. `ActualHistoricalFifthSavingIntegral` 补上 literal `actualHistoricalFifthSaving` 的实际列表/tuple reindex，并把实际 `upperFourth - upperFifth` policy 密度差接入同一归一化积分。
4. `HistoricalFifthCutoffInvariance` 证明固定同一 residual/enumeration cap 时，提高外层 cutoff 至任意 `z ≥ N^b` 的归一化 saving 不变；在两个独立最终覆盖条件下，给出 moving cutoff 的真实积分极限。

选盒数据在 `N` 之前固定。第三、第四、第五有效 old 包含逐层未选中回退。`D.levelCheck` 是有限有理数 level 比较；最终 `K/c`、数值积分界或分布估计没有被放入合法性假设。实际历史 old 与通用 stored-cap permit 的整盒平方/envelope 条件仍须按采用表绑定。

[KEY_THEOREM_TYPES.md](KEY_THEOREM_TYPES.md) 给出 15 个关键定理的完整 Lean 类型及已验证源码位置身份；[INTERFACE_AND_OPEN_INPUTS.md](INTERFACE_AND_OPEN_INPUTS.md) 给出字段、坐标、历史投影、归一化和接收条件。

## 边界、截断与回退

选中 owner 外的 actual residual 差在归一化前精确为零。公开的完整 cutoff 恒等式保留 `log N / singularSeries N`，固定同一个 cap；不要求 `cap ≥ z`。积分极限另外要求 `cap(N) ≥ N^b` 最终成立，且数据与网格固定。

真实离散 prime 的边界质量通过逐点 ramp 估计乘非负实际权重后求和控制；连续零测结论用于连续积分及 ramp 极限。[MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md) 记录准确供应链和初始静态审查时的源码身份；[BRIDGE_STATIC_REVIEW.md](BRIDGE_STATIC_REVIEW.md) 记录两个新桥接模块的独立静态复核。静态审查与实际编译回执分开保存。

本轮不供应不足 cap、`z < N^b`、裸 floor、移动网格或完整采用构造的有效数值边界账。cap 不需要覆盖商水平 `N^lambda / P`，但改变 residual cap 不能直接使用外层 cutoff 不变性。

## 旧成果与独立缺失来源

普通 lower-fourth 真积分与历史有限接口已在 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 验证：6 次严格原前端、6 次原 checker、150 个声明。它已被 P0 接收；普通 lower density 极限的 `2*b ≤ old` 与选盒合法性条件仍按其原类型保留。

stored-cap permit 的独立验证保存在 [round2/permit](../round2/permit/HANDOFF.md)：3 次严格原前端、3 次原 checker、36 个声明，其中 14 项为生产声明、22 项为 probe。P0 `d0366ce64272e81faf6166a8a90050f56b328d38` 已通过归档证据复用接收并导入 permit；此处读取消费者回执，没有重跑该复用检查。这些旧验证没有被重记为本轮次数。

先前 reported inherited-fifth 独立候选仍为 **SOURCE_PENDING**：有界核对未取得其完整 SHA、源码与真实日志。本轮验证的是仓库中明确认领的源码；没有替该未取得来源补造验证。旧 round2 候选/停止状态原样保留，本 round3 当前源码回执为上述四个生产模块的新验收记录。

## 接收 Part 与未闭合输入

| 接收 Part | 交付 | 尚未闭合 |
| --- | --- | --- |
| Part 0 | 四个历史生产模块、对 d036 固定根的未应用导入补丁、当前源码回执 | 四个历史模块的公共根集成与规范门；公共手稿映射更新 |
| Part 2 | 完整数据/坐标/历史 old/双 own-cube/积分接口 | 实际采用的 cells/caps；有效 old 逐行绑定；有限 level 和整盒许可检查；共同区域数值证书 |
| Part 3 | 实际 parent、第五候选、自然数 product、同 cap cutoff 接口 | P1 尚须补齐完整采用 policy 的支持及因子分解所需结构，并绑定真实 selected subproduct 许可 |
| Part 4 | 旧 lower-fourth 里程碑、继承第五 saving 和第四减第五实际密度差积分 | P1 尚须补齐其余历史积分与完整采用上/下组合；之后接入 Part 2 数值证书与 Part 4 same-weight 密度界 |
| Part 5 | 原 `p∤N` carrier、严格端点、实际有限组合和固定族边界趋零 | 同一实际系数的分布估计、全局边界/截断账、最终 counting 输入 |

P2 的 paired E0 `[0,64)` 认证不是上述历史采用表，`exact_Z` 也不是历史 cap。本轮完成指定历史积分/截断里程碑，尚未完成整个 Part 1 或最终 `K/c`。

P1 仍负责全部采用层的完整组合公式、下游支持及因子分解所需的历史许可结构，以及完整构造的截断、回退和边界账。Part 2 供应实际固定数据及有限合法性证书；上表列的是接入条件，没有将尚未完成的 P1 证明转交给接收 Part。

Part 0 接收时须使用本轮完整交付树中的四个历史生产模块。Geometry、CellIntegral 已在 P1 父头 `744316efd1887f21c91dd4b63c218fa27704c931` 中存在，当前 P0 头只保存了旧候选快照与身份回执，尚未作生产接收；仅取本轮增量不会自动带入完整文件。旧 `StoredHistoricalBoxPermit` 已在 P0 新头接收。文本导入补丁适用性和接收后真实根构建是两个独立检查。
