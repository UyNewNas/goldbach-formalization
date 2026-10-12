# P1 第二轮：上游增量核对与接收边界

本记录固定已经实际读回的上游信息，记录时间为 **2026-10-12 12:05:30 UTC**。
它不是本轮新 P1 数学模块的编译或验收回执；结构化事实与来源见
[upstream-intake.json](upstream-intake.json)。

## 1. 结论与核对范围

用户另行报告的“继承前层选择、仅过单模块编译的第五层积分候选”，
本次仍未找到对应的实际源码、完整提交和编译回执，状态为 **SOURCE_PENDING**。
普通父树 fifth integral、P1 有限历史恒等式和 P2 的四格纤维积分均不冒充该候选。

本次从 P1 已发布交接中的固定快照出发，只检查相关分支的后续提交、
P0/2/5 当前交接与 P0 的 P1 接收记录，没有重扫全仓递归树或全部 PR 历史。
范围内没有新候选，不等于断言未发布或不可访问的工作不存在。

共同证明基线仍为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`；
手稿仍为 `ba6ec11d800eccc54406490631895e174de85766`，
主体 blob 仍为 `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`。
没有读到替换该数学基线的 P0 新基线单。

## 2. 实际观测到的完整分支头

| 分支 | 本次观测完整 SHA | 相对前次固定快照 |
| --- | --- | --- |
| P1 `chatgpt/chen-p1-history` | `7f894bfb57b7aa561360e335c6d610b7c30614e0` | 相对 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 仅 1 个 workflow 提交 |
| P0 `chatgpt/chen-p0-integration` | `cce2334906f068fda2f58c400646366f2aa2d417` | 相对 `80aca6710c83b5160f4c5fdd05d180e507990e95` 仅 1 个 workflow 提交 |
| P0 `chatgpt/chen-p0-validation-r2` | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` | 未变 |
| P2 `chatgpt/chen-p2-certificates` | `076473720210ee602e6e9735902e16bb6c5f1398` | 相对 `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` 前进 3 个提交，比较返回 113 个变更文件 |
| P5 `chatgpt/chen-p5-lower` | `bf54caeb5e708474cacefac13a171d307b4c64f2` | 相对 `a03a57265a49d542e6fac8ba72094dd673e5ed7d` 前进 2 个提交，比较返回 132 个变更文件 |
| `codex/variable-envelope-boxes` | `1a80c1bcce67886f699d097fc37fd245cd3620bf` | 仍为原证明基线 |

这些是本次只读观测的固定身份，不保证分支未来不再前进。
[机器记录](upstream-intake.json) 保留比较的完整 base/head 和来源 URL。

### P1 外部 CI 150/90 分钟调整

外部提交 [`7f894bfb57b7aa561360e335c6d610b7c30614e0`](https://github.com/UyNewNas/goldbach-formalization/commit/7f894bfb57b7aa561360e335c6d610b7c30614e0)
只修改 `.github/workflows/lean.yml`：

- `jobs.lean.timeout-minutes` 从 **45** 改为 **150**；
- “Build the full project”步骤新增 `timeout-minutes: 90`。

`LEAN_NUM_THREADS = 2`、build 条件和命令没有变化。
P1 数学源码与已验证提交 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 相同。
该外部 workflow 改动应保留；它不属于本轮 P1 数学证明改动，也不是新的数学基线。
当前 workflow 的实际 Git blob 为 `f174e81f181dbc8c57a78be87b6d0e124f25915a`。
P0 的本次分支增量也是同样的 workflow 超时调整。

## 3. P0 旧接收身份与 P1 后来验证的身份不同

P0 当前
[P1_FIXED_INTAKE.md](https://github.com/UyNewNas/goldbach-formalization/blob/cce2334906f068fda2f58c400646366f2aa2d417/verification/parts/p0/round2/closeout-context/p1/P1_FIXED_INTAKE.md)
仍只接收 `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` 这一源码检查点。
它记录的历史模块 SHA256 是
`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`，
部分运行观测与“编译器确认类型为 0”的描述属于当时阶段。

P0 当前 [ROUND2_VERIFICATION](https://github.com/UyNewNas/goldbach-formalization/blob/cce2334906f068fda2f58c400646366f2aa2d417/docs/PART0_ROUND2_VERIFICATION.md)
也保留该历史身份，明确未找到独立 inherited-fifth 积分源码。
自前次 P0 快照后的唯一提交只改 workflow，因此没有新增对 P1
`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 的接收记录。

P1 后来的 [已发布 VERIFICATION.json](https://github.com/UyNewNas/goldbach-formalization/blob/b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f/verification/parts/p1/VERIFICATION.json)
有独立的当前源码绑定：六目标 strict 官方 frontend 编译、六次原版
`leanchecker`、五个定义模块的 **150** 条完整声明审计。
其实际 receipt SHA256 为
`2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1`；
归档 SHA256 为
`c56fc707d40ad255fd2d9c8b6c94dc7442c9c62b7238d833188b18cdf10f601d`。
当前历史模块源 SHA256 为
`b6ef2c6febc61e28ddf5bbeb5c02fd665e5266833df4cd1b5b2640481cb6e6f3`。

上述是已发布的前轮验证事实，本次没有重新执行这些门。
P0 的旧 intake 不能替代对后续源码的接收，也不能被解释成否定已发布的新验证。
本记录不声称 P0 已经接收 `b09d...`，或已经应用公共根导入补丁。
官方 `Lean.Elab.runFrontend`、`trustLevel = 0` 与标准
`lake build` 的执行身份仍分别记录。

## 4. P2 新增的实际可用输入

P2 的本次交接元数据提交为 `076473720210ee602e6e9735902e16bb6c5f1398`，
绑定的实际证明源码提交为 **`6acf61cc28f227a9154363f2347c386ec01dffb0`**。
详见 [ROUND2_HANDOFF](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/docs/part2/ROUND2_HANDOFF.md)、
[PART1_INTERFACE](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/docs/part2/PART1_INTERFACE.md) 和
[Prefix4 实际回执](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/verification/part2/round2/prefix4/receipt.json)。

新增的三模块位于 `ImbalancedChen/Certificates/`：

| 模块 | 实际 Git blob | 新声明数 | 发布回执的编译 / 原版重放 |
| --- | --- | ---: | --- |
| `PairedV2Geometry.lean` | `f7bb75a4a2c1b4debc41a334df30d64bf81647f5` | 10 | 退出 0 / 退出 0 |
| `PairedV2Prefix4Data.lean` | `3bfedf4c0c6222adb6afa747b2a4c394de841bc5` | 11 | 退出 0 / 退出 0 |
| `PairedV2Prefix4.lean` | `40dfff1c63af27d15da9f22e88b4b11e96369672` | 35 | 退出 0 / 退出 0 |

读取到的源码 blob 和 UTF-8 字节数与 receipt 的三份源码身份一致。
联合审计覆盖九个生产模块、**309** 条声明；旧六模块的
253 条声明使用确切同源码的 P0 编译/重放验收，新三模块贡献 56 条。
传递公理并集为 `Classical.choice`、`Quot.sound`、`propext`。
本 P1 intake 只读取该发布证据，没有重新执行 P2 的验证，也没有宣告
全项目构建、完整历史 mask 或最终 K/c 已通过。

### 实际纤维、几何与有限积分和

数据坐标保持 `(t,u,z,w)`，外层端点固定，实际开纤维为

```text
tl < t < tr, ul < u < ur, a < w < z < Z,
Z = min(ul, (3/13)*(1-tr-ur)).
```

该 cutoff 在外层端点冻结，不能在任意内点重新计算。
`E0Geometry` 不含积分收益假设；它检查实际采用网格、严格非空、
cutoff、外层端点和 E0 残量门。已证
`ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_argument`
给出整个开纤维上的

```text
a < w < z < u < h < t < d,
7/3 <= (1-t-u-z-w)/z.
```

末格允许 `uUpper = h`、`tUpper = d`，也允许 `Z = uLower`；
`a = Z` 和零外层宽度被排除。E0 残量门不用于给 E1 重新贴标签。

`Prefix4.integral` 是原始行 0、1、2、3 的实际积分有限和，
全部来自 E0。`certificate_inputs`、`rowIntegral_eq_certificate`
和 `integral_semantics` 将每行参数接到真实四重积分。
`integral_bounds` 认证的区间是

```text
12676565261567 / 100000000000000000000
  <= Prefix4.integral <=
12676572571081 / 100000000000000000000.
```

**四格和已经包含原先认证的首格，不再加一次首格收益。**
积分系数为 `K/80 = K*(1/20)*(1/4)`，quarter 已在其中，不能再次乘除。
这一 B 局部修正也不等同于 P1 的普通父树 lower-fourth restoration；
撤回的 `12/5` 增量不重加。

### P1 仍需提供的连接

最新 P2 契约继续要求实际历史 joint-cell/区域/策略/算术所有权字典。
若从迭代积分有限和进入并域积分，还需相应的 Fubini、覆盖、不重计
和边界身份。实际父限制、历史整盒许可及 A 粗双图的物理域换元、
同一 rho 识别也仍缺失。连续零测边界不能跳过离散素数边界支付。

P2 的 Prefix4 回执明确写明：完整 mask、算术 parent license、其余
17,572 行及 E1 和误差总账并未由这个切片认证。其有限几何条件没有
引入最终 gain、K/c 或期望积分界作为许可前提。

另有版本同步事项：P2 当前文档仍把接口称作尚无另一 P1 会话确认的
提议，而我方 `b09d...` 交接已记录接受此前发布的语义契约。
本记录固定这个差异及新版来源，不代替 P2 写入确认，也不声称出现了新的双方验收。

## 5. P5：S1Carrier 的独立有限接口

P5 新检查点为 `bf54caeb5e708474cacefac13a171d307b4c64f2`，
见 [S1Carrier 交接](https://github.com/UyNewNas/goldbach-formalization/blob/bf54caeb5e708474cacefac13a171d307b4c64f2/docs/CHEN_P5_S1CARRIER_HANDOFF.md) 和
[实际回执](https://github.com/UyNewNas/goldbach-formalization/blob/bf54caeb5e708474cacefac13a171d307b4c64f2/verification/parts/p5/round3/s1carrier/receipt.json)。
被验证的是固定 goldbach 依赖
`MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier`，其源码 SHA256 为

```text
757bdcea11195c48ed5814f95a70737326853e68bfaa093711a4f6161e1a896a
```

发布回执记录：严格官方 frontend、原版 checker 及完整定义模块
公理审计均退出 0；全部 **36** 条声明包含 private/generated，
其中公开源码定理 17 条。证明源码保持依赖固定版本原字节。
这是发布的生产者证据，本次 P1 没有重跑它。

可复用的接口是实际有限 S1 载体、筛和、主和及标准素数 AP 余项身份，
保留严格端点、目标删素数 `p ∤ N` 和实际差值载体。
它没有供应历史第五层真实积分，也没有供应完整 Chen 均值。

`CurrentChenInitialMean` 仍是未编译验收的第一项候选，
系数为 `(33/4) * Real.log 3`，不等于采用 L1，也不闭合
全十一项均值或 `hLower`。P5 将 `LiLiuGoldbachS1LowerRosser`
列为下一个小供应节点，回执明确该节点尚未启动。
P1 不在本次 intake 中扩大执行该供应链。

## 6. 本轮 P1 新供应的定位与待取得项

本轮新模块的定位是：在明确、可检查的条件下，供应独立的
**历史 joint-cell 构造与实际素数和到真实积分的连接**。
这不是另造一个全局 policy-density 结果来替代尚未取得的独立候选，
也不把该候选记录成已经重写、导入或验收。

继续保持数据固定在 N 之前、处理顺序与反向存储历史的字典、
`p ∤ N`、严格端点、唯一盒归属，以及旧/新 own-cube 指示函数分别处理。
先控制实际算术边界质量，再使用连续零测结论。
最终 K/c 不进入有限合法性假设。

本文件不声称本轮新 P1 证明已编译；后续实际同源码的编译、原版重放、
完整声明审计及接收范围应另给回执。独立 inherited-fifth 候选的
完整 SHA/补丁、真实文件名、依赖和原始编译记录仍待取得。

## 7. 固定来源索引

以下 Git blob 均来自本次实际读回的文件响应；完整提交、路径、URL、
UTF-8 字节数和选取的回执字段保存在 [upstream-intake.json](upstream-intake.json)。
没有复制完整仓库、对象二进制或大证据归档。

| 来源 ID | 固定文件 | Git blob SHA1 |
| --- | --- | --- |
| p1_previous_handoff | [verification/parts/p1/HANDOFF.md](https://github.com/UyNewNas/goldbach-formalization/blob/b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f/verification/parts/p1/HANDOFF.md) | `ded2d4f763502fdfe2f2ed4b6e0320345e2db576` |
| p1_published_verification | [verification/parts/p1/VERIFICATION.json](https://github.com/UyNewNas/goldbach-formalization/blob/b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f/verification/parts/p1/VERIFICATION.json) | `fa799e99c42cff79421fe59c0412e0707bf0b0fb` |
| p1_current_workflow | [.github/workflows/lean.yml](https://github.com/UyNewNas/goldbach-formalization/blob/7f894bfb57b7aa561360e335c6d610b7c30614e0/.github/workflows/lean.yml) | `f174e81f181dbc8c57a78be87b6d0e124f25915a` |
| p0_interfaces_latest | [docs/CHEN_175_BASELINE_INTERFACES.md](https://github.com/UyNewNas/goldbach-formalization/blob/cce2334906f068fda2f58c400646366f2aa2d417/docs/CHEN_175_BASELINE_INTERFACES.md) | `fd97c85489ce1613245a65e0c9f21736bc8cb7dc` |
| p0_verification_latest | [docs/PART0_ROUND2_VERIFICATION.md](https://github.com/UyNewNas/goldbach-formalization/blob/cce2334906f068fda2f58c400646366f2aa2d417/docs/PART0_ROUND2_VERIFICATION.md) | `fcbc8b6d5745d92de53a7a066d745e1e911f3b9f` |
| p0_p1_fixed_intake | [verification/parts/p0/round2/closeout-context/p1/P1_FIXED_INTAKE.md](https://github.com/UyNewNas/goldbach-formalization/blob/cce2334906f068fda2f58c400646366f2aa2d417/verification/parts/p0/round2/closeout-context/p1/P1_FIXED_INTAKE.md) | `cabe5ba7143b0fc0f4f47b564814a22f2d9e5c7b` |
| p2_interface_latest | [docs/part2/PART1_INTERFACE.md](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/docs/part2/PART1_INTERFACE.md) | `ad46c9e1bc9ef11692b7650fbb5372e8f4174706` |
| p2_round2_handoff | [docs/part2/ROUND2_HANDOFF.md](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/docs/part2/ROUND2_HANDOFF.md) | `a3bf5c624477049379efd4419870c2e0b948e6c4` |
| p2_geometry | [ImbalancedChen/Certificates/PairedV2Geometry.lean](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/ImbalancedChen/Certificates/PairedV2Geometry.lean) | `f7bb75a4a2c1b4debc41a334df30d64bf81647f5` |
| p2_prefix4_data | [ImbalancedChen/Certificates/PairedV2Prefix4Data.lean](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/ImbalancedChen/Certificates/PairedV2Prefix4Data.lean) | `3bfedf4c0c6222adb6afa747b2a4c394de841bc5` |
| p2_prefix4 | [ImbalancedChen/Certificates/PairedV2Prefix4.lean](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/ImbalancedChen/Certificates/PairedV2Prefix4.lean) | `40dfff1c63af27d15da9f22e88b4b11e96369672` |
| p2_prefix4_receipt | [verification/part2/round2/prefix4/receipt.json](https://github.com/UyNewNas/goldbach-formalization/blob/076473720210ee602e6e9735902e16bb6c5f1398/verification/part2/round2/prefix4/receipt.json) | `c11ce176846530953f2a968e30e9da3b3f24dfa8` |
| p5_s1_handoff | [docs/CHEN_P5_S1CARRIER_HANDOFF.md](https://github.com/UyNewNas/goldbach-formalization/blob/bf54caeb5e708474cacefac13a171d307b4c64f2/docs/CHEN_P5_S1CARRIER_HANDOFF.md) | `dbda7bc4bf741a19407081d4a6e58d42561197e9` |
| p5_s1_receipt | [verification/parts/p5/round3/s1carrier/receipt.json](https://github.com/UyNewNas/goldbach-formalization/blob/bf54caeb5e708474cacefac13a171d307b4c64f2/verification/parts/p5/round3/s1carrier/receipt.json) | `a42cb22e923ee78785e60a17c4e19f93752d44e8` |

