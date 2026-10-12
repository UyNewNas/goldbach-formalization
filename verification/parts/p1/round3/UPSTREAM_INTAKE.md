# P1 round 3：固定上游与实际 CI 增量接收

## 结论与范围

**P0 尚无新的分支提交；没有取得对 stored-cap permit 的新增接收，也没有取得独立 reported fifth 候选的源码或同源验证回执。P2 唯一新增提交为文档更新。P1 上轮完整提交的实际根 CI 已成功，但它没有覆盖本轮拟恢复的历史第五层 leaves。**

本次有界只读核对在 **2026-10-12 17:49:14–17:51:58 UTC**（北京时间 **2026-10-13 01:49:14–01:51:58**）完成。起点为上轮 [FINAL_P0_INTAKE.md](../round2/FINAL_P0_INTAKE.md) 和 [FINAL_P2_INTAKE.md](../round2/FINAL_P2_INTAKE.md)。只读取四个已知分支、P2 唯一变化的固定交接、两个 exact-SHA run 的有关元数据，以及 P1 一个完整原始 core job log。未启动编译、checker、CI、Codex 或外部消息；未下载 Actions cache、artifact 或二进制对象。此 intake 不替代本轮实际编译回执。

## 1. 实际固定头

| 分支 | 本次实际完整 SHA | 相对上轮结果 |
| --- | --- | --- |
| `chatgpt/chen-p0-integration` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 未变 |
| `chatgpt/chen-p0-validation-r2` | `6d1e5c4710a66f68fd101d0b40b5514bbbba4919` | 未变 |
| `chatgpt/chen-p2-certificates` | `101bb2291cd51f9717544ce477122fdd44eda44d` | 相对 e6d6 新增一个文档提交 |
| `chatgpt/chen-p1-history` | `744316efd1887f21c91dd4b63c218fa27704c931` | 与本轮接收头相同 |

共同数学基线仍为 `1a80c1bcce67886f699d097fc37fd245cd3620bf`，冻结手稿仍为 `ba6ec11d800eccc54406490631895e174de85766`，body blob 仍为 `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`。本次没有新 Part 0 基线单，也没有自行将集成头替换为数学基线。

初次请求误用了不存在的 `chatgpt/chen-p0-validation`，API 返回 404；随后从上轮固定记录取回正确名称 `chatgpt/chen-p0-validation-r2` 并成功核对。一个直接 job URL 也被 connector 拒绝，后改用同 run 的 jobs endpoint 成功读取。这两次错误均记录于原始响应，未解释成上游状态变化。

## 2. P0 接收与 reported fifth

P0 两个 ref 均未移动，因此上轮固定接收事实仍保持：

- P0 integration 已接收 `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` 的四个生产模块：普通 lower-fourth frontier、实际 cell sum、真实 own-cube 积分、历史 cap 数据接口；140 个生产所属声明。该旧生产者完整 150 声明回执包括另 10 个 Probe 声明。
- 本轮没有新的 P0 提交导入 `StoredHistoricalBoxPermit`。其实际验证仍使用 P1 上轮三目标、36 声明的独立回执，不能改称 P0 已接收。
- P0 的两份历史 joint-cell `.lean.txt` 归档仍是已取得但未编译的本轮候选快照。它们不等于此前另行报告“仅过单模块编译”的独立 inherited-fifth 候选。
- 独立 reported fifth 继续为有界 **SOURCE_PENDING**。本次未取得原提交、实际文件、对象和原始同源编译记录，也未重新搜索全仓库、全部 PR 或其他会话；不据此断言候选不存在。

P0 在 28fd 的已有根 CI 成功和具体范围详见上轮 [FINAL_P0_INTAKE.md](../round2/FINAL_P0_INTAKE.md)。此次没有重复下载其旧日志或重新验收旧对象。

## 3. P2：只补录成功 CI 和一处宽度笔误

[P2 两头 compare][p2-compare] 实际返回 ahead 1、behind 0、total commits 1，**完整变更表只有 `docs/part2/ROUND3_HANDOFF.md` 一项**。新提交时间为 `2026-10-12T13:14:49Z`，唯一父提交为 `e6d6d57323cc358cef060fb243ec386c13cb662d`。新增数学源码身份仍为 `f0c00f9ccce98e04af439321a92eb9fd0dd26203`。

[新交接][p2-handoff] 只增加以下内容：

1. 补录 e6d6 上的 Part 2 专项 CI 成功。生产者交接称 12 个模块的 build、strict、replay 全部成功，709 条完整声明记录与其本地记录逐条一致，180 个验证输入文件字节未变。
2. 将旧 Prefix4 区间宽度的文字笔误由 `7319514/10^20` 改为 `7309514/10^20`。旧上下界、机器账和生产证明均未改。精确相减也有 `12676572571081 - 12676565261567 = 7309514`。

本次实际读取的 [run 38252572597][p2-run] 为 `completed / success`，绑定的完整 head SHA 是 **e6d6**，不是新文档头 101bb。创建时间 `12:59:31Z`，完成更新 `13:08:31Z`。[job 114822365913][p2-job] 的逐步骤元数据确实给出：

| 步骤 | 实际状态 | 时间 UTC |
| --- | --- | --- |
| Explicit Part 2 build and strict individual elaboration | completed / success | 13:01:59–13:05:58 |
| Replay every new module with the bundled kernel checker | completed / success | 13:05:58–13:07:42 |
| Inventory all Part 2 declarations and their transitive axioms | completed / success | 13:07:42–13:08:25 |
| Record required verification outcomes | completed / success | 13:08:25 |

709 条记录逐条相同是**生产者交接的记录**；本次没有再次下载该 job 全日志、逐条比较或运行 P2 接收器。此次只独立确认 exact-SHA run/job/step 成功，以及完整单文件 compare。因新提交只变该交接，旧 12 个生产源、P1 接口、验证输入和所有其他路径均在这个增量中保持原 Git 内容。

累计认证范围仍为 E0 原始 `[0,64)`。累计积分界仍是

\[
203256527543633/10^{20}
\;\leq\; \mathrm{Prefix64.integral}
\;\leq\;203256645234388/10^{20}.
\]

它已含旧 Prefix4，不能重复加一次。有限行/网格索引不重计尚不等于实际 prime-box 并域身份。新提交没有提供 `storedMeshCapCheck` 的采用表、有效历史 old 的绑定、fallback 实例、第五层 parent 或离散边界支付；`exact_Z` 仍为 paired fibre cutoff，不是历史 cap。P1/P2 的 `m+1` 网格、逆序历史存储、原处理坐标、严格 Ico 归属和 old/new own-cube 分离约定均保持上轮范围。

## 4. P1 744316 的实际根 CI：成功与未覆盖范围

本次实际读回 [P1 core run 38255617449][p1-run] 和其 [job 114832792410][p1-job]，head SHA 均为 `744316efd1887f21c91dd4b63c218fa27704c931`。Run 创建于 `13:25:41Z`，最后更新于 `14:07:52Z`，状态为 `completed / success`。同 SHA 的 [Variable envelope run 38255617510][p1-ve] 也为 `completed / success`，更新于 `13:28:07Z`。

**此次不仅读取元数据，还完整取回了 P1 core job 原始文本日志。** 其中明确记录 `project_commit=744316efd1887f21c91dd4b63c218fa27704c931`，三门结果为：

| 实际执行门 | 原日志结果 | wall 秒数 |
| --- | --- | ---: |
| stock full project build | `Build completed successfully (9776 jobs)`，exit 0 | 1969 |
| bundled `leanchecker --verbose ImbalancedChen` | `stage=leanchecker ... exit_code=0` | 367 |
| root/transitive axiom audit | `audited 4867 declaration(s) under 'ImbalancedChen'`；允许三标准公理，exit 0 | 27 |

原日志也有最终 `build=success`、`leanchecker=success`、`axiom-audit=success`。这是真实已有远端执行的接收，不是本轮新运行，不能把 9776 jobs 解释为 9776 个新生产定理，也不称之为本轮独立重放所有 imported closure。

**根 CI 没有给新增 leaves 提供同源目标验证。** 完整日志中，以下五个模块名的出现次数均为 0：

```text
ImbalancedChen.HistoricalUpperFiveCellGeometry
ImbalancedChen.ActualHistoricalFifthCellIntegral
ImbalancedChen.StoredHistoricalBoxPermit
ImbalancedChen.HistoricalPrefixCertificate
ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral
```

P1 744316 保留旧公共根；新 P1 leaves 的导入补丁没有在此分支应用。该 run 的实际命令针对默认根目标，而许可、lower-fourth 和历史候选的逐模块证明证据必须按各自明确回执接收。**此根成功不能将历史 fifth 候选从 UNCOMPILED 升级，也不能替代独立 permit 的 3 + 3 + 36 验证。**

对本轮恢复供应链有用的只读观察：原日志确实包含 `MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergPrimeDivisorGrowth` 和 `...LiuSelbergDenominatorAsymptotic` 的成功 Built 标记，后者在 `13:36:34Z` 显示 2.7 秒；末尾还有同一 744316 key 的实际 Lake cache 保存成功行。这说明旧固定源码在该远端环境有成功供应构建，**没有产生本地可复用对象的字节身份、下载链或本轮完成条目**。不据此将本地缺失依赖标为完成，也不探索 cache 下载。

本 run 的 [artifact 元数据][p1-artifacts] 为 `lean-verification-38255617449-1`，ID `11751819059`，60,429 bytes，digest `sha256:dd2a06c5658de5d660bffd92a7c7f160aa6dbae1b89011e4e9a33c8f2c719bf9`。工作流上传目录明确为 stage verification logs。此次未下载该 artifact，没有从它取得供应二进制。

## 5. 同源记录与本轮交接

本次机器可读记录见 [upstream-intake.json](upstream-intake.json)。完整 connector 响应的规范化副本及原始 P1 job 文本存于 scratch 辅助目录 `/workspace/scratch/127408f63891/p1-round3-upstream-intake/`；GitHub 的固定提交和 run/job 链接是持续引用身份。

| 内容 | 字节数 | SHA256 |
| --- | ---: | --- |
| 完整 P1 core job log，含工具返回 BOM | 719,448 | `21a930e6de18772198367440ed7b00386e3e09491822f53ec58f7cf4e3b91208` |
| 本次规范化 API 响应 `responses.json` | 108,638 | `fe67a8a7f8e8268a0b873b594f422f0aee24e89ccb029fe076cd38a213946c22` |
| 101bb 固定 P2 `ROUND3_HANDOFF.md` | 17,868 | `97072db87ed7b10008141a18b53eed7e580a5fe8df0cd8d4f72ced42376ebdc5` |

P2 新交接全文按 UTF-8 重算 Git blob 为 `56156ad0fe6499303884e5457e8d68aa655a292d`，与 compare 返回的实际 blob 一致。其余未变化的旧固定交接未重复读取或重写。

本轮接收建议：继续从 P1 744316 的已封存本地检查点恢复历史 fifth 所需最小供应闭包；保留原 strict、原版 checker 和全声明审计门。P2 的 E0 积分范围、P0 的旧四模块接收、permit 的独立三目标回执分别按实际身份复用。采用 cap 表、真实有效祖先、完整 retained saving 到 tuple correction 身份、支持/因子分解、截断和有符号边界误差仍是各自尚未闭合的输入。

[p2-compare]: https://github.com/UyNewNas/goldbach-formalization/compare/e6d6d57323cc358cef060fb243ec386c13cb662d...101bb2291cd51f9717544ce477122fdd44eda44d
[p2-handoff]: https://github.com/UyNewNas/goldbach-formalization/blob/101bb2291cd51f9717544ce477122fdd44eda44d/docs/part2/ROUND3_HANDOFF.md
[p2-run]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38252572597
[p2-job]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38252572597/job/114822365913
[p1-run]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38255617449
[p1-job]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38255617449/job/114832792410
[p1-ve]: https://github.com/UyNewNas/goldbach-formalization/actions/runs/38255617510
[p1-artifacts]: https://api.github.com/repos/UyNewNas/goldbach-formalization/actions/runs/38255617449/artifacts
