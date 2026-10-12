# Part 1 round 3：Part 0 发布前增量接收

**Part 0 已接收 stored-cap permit；本轮历史第五层的生产验收仍须使用本轮新回执。** 初始 [UPSTREAM_INTAKE.md](UPSTREAM_INTAKE.md) 记录的是 17:49–17:51 UTC 的旧头观察，本文件补录 2026-10-12 19:10 UTC 后实际读到的固定增量，不改写旧观察记录。

## 固定身份和完整范围

| 项目 | 完整身份 |
| --- | --- |
| 原 P0 integration | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 新 P0 integration | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 新提交的唯一直接父提交 | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 新根 Git blob | `d4a92f3f3ff889260b0fc22fd095aff9e1e4796b` |
| 新根 SHA-256 | `d6a0af92c0827bc2f1ae30a12f895f46f8048049fdca694e89fc3678e202f449` |
| 共同数学基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 冻结手稿 | `ba6ec11d800eccc54406490631895e174de85766` |

此次读取五个已知 ref，完整响应保存在 [FINAL_HEAD_RECHECK.json](FINAL_HEAD_RECHECK.json)。P0 validation-r2 仍为 `6d1e5c4710a66f68fd101d0b40b5514bbbba4919`，P2 仍为 `101bb2291cd51f9717544ce477122fdd44eda44d`，P1 当时仍为 `744316efd1887f21c91dd4b63c218fa27704c931`，来源分支 `codex/variable-envelope-boxes` 仍指向共同数学基线。没有自行以集成头替换数学基线。

两头 compare 到达 300 文件上限。随后读取同一固定提交的完整分页，得到 **444 个文件：438 新增、6 修改**。新增生产源码恰为 permit 和三个 P2 Prefix64 模块；其他新增文件为接收说明、审计入口和证据。六个修改文件为根、核心 workflow、README、PROOF_STATUS、P2 generator 和 P0 `check_batch.sh`。完整清单中没有 manuscript map、外部复用说明、工具链或依赖 pin 变化；新接收说明仍明确使用原完整数学基线。

## Permit 已进入 P0 根

P0 新根新增：

```lean
import ImbalancedChen.StoredHistoricalBoxPermit
import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Batch4To64
import ImbalancedChen.Certificates.PairedV2Prefix64
```

P0 的 `REUSE_RECEIPT.json` 状态为 `PASS_ARCHIVED_EVIDENCE_REUSE`，固定生产者来源为 P1 `744316efd1887f21c91dd4b63c218fa27704c931`，接收 permit 的 **14 个生产所属声明**，另列 22 个 probe 声明。接收源 SHA-256 为 `50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d`，与 P1 已验证文件相同。

本次读取了消费者回执、说明和实际根文件，核对新增 permit 源的 Git blob。没有再次运行 P0 消费者、Lean 或 checker，也没有把读回的消费者结果计作本轮新验证次数。

## 第五层旧检查点与本轮验证分开

P0 保存的 geometry/cell 仍是 `.lean.txt` 候选快照，候选回执状态为 `PASS_EVIDENCE_IDENTITY_ONLY_TARGETS_UNCOMPILED`。它绑定的 geometry SHA 为 `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b`，cell SHA 为 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`，对应 P1 旧 round 2 停止检查点；新根没有导入这两份生产模块。

P0 旧候选身份接收不覆盖本地 round 3 后续严格编译。反过来，本轮新回执也不改写 P0 固定提交里当时的旧状态。独立 reported inherited-fifth 候选继续为 **SOURCE_PENDING**；这个有界增量没有提供该独立候选的源码或同源单模块成功记录。

## 当前导入提案

对新 P0 根使用 [PART0_D036_HISTORY_IMPORT.patch](PART0_D036_HISTORY_IMPORT.patch)，只新增本轮四个历史生产模块的导入。Permit 已在根内，不重复增加。其真实 `git apply --check` 返回 0，原根快照字节保持不变；完整命令、根与补丁身份见 [PART0_D036_IMPORT_CHECK.json](PART0_D036_IMPORT_CHECK.json)。公共根没有在 P1 分支上修改。

旧 [PART0_28FD_HISTORY_IMPORT.patch](PART0_28FD_HISTORY_IMPORT.patch) 和旧适用性记录保留为针对 28fd 的历史提案。它们不能代称对当前 d036 根的适用性检查。

Part 0 需按本轮完整交付树接收四个历史生产文件。Geometry 和 CellIntegral 已存在于 P1 父头 744316；其中 CellIntegral 本轮没有源码变动，仅 cherry-pick 本轮新增差异不能自动把这两个尚未进入 P0 生产树的父头文件带入。导入补丁的文本适用性也不能替代接收后的真实根构建、原 checker 和完整类型门。

此次没有查询或触发 d036 的 CI。源码中新增构建/类型门配置，只能说明拟执行范围，不能据此宣称新根 CI 已通过。

原始 ref、compare、固定提交分页、完整变更清单、消费者回执和实际读取文件保存在本轮证据目录 `p1-round3-final-upstream/`，并纳入本轮文本证据归档。
