# SupportData 单源 API 修复与失败配置保留

此入口只把 `P1OriginalSingletonSupportData` 的两个已确认 API 表达修复安装到 P1 member。四条 theorem 的 statement、imports 和数学合同不变。它不运行 Lean、Lake、normal 或 kernel，也不新增或转绑任何验收信用。

原失败来自 `e70bd4994a95f45cc2c75b6bae2213bcb2f99d91` 的 `job_983e2536dff8403eaca6af9528df7fce`：direct-import readiness 成功，SupportData normal exit 1，`accepted_owners=[]`。完整 11 份失败证据的路径、长度及 SHA256 固定在 [REPAIR_MANIFEST.json](REPAIR_MANIFEST.json)。

## 固定修复

| 对象 | 字节数 | SHA256 |
| --- | ---: | --- |
| SupportData 原像 | 3671 | `648340835401b53b8c19939b8874c0bbaa3be74975840d302752d092e109d298` |
| SupportData 修复后 | 3769 | `7b8225f32fe7ae0b23ceaf6bc8bfec0cadf90997e9f0237c5ab5884de4f4c8b7` |
| apply_source_repair.py | 24467 | `1174703554d9522be7e3e14c4204ddb54b7c9c44bc341eb8c5f9b07de8bc0f57` |
| REPAIR_MANIFEST.json | 15425 | `d2be5661d83a06bed3eb0a03bb0ecb8fbed02b1353c1b51419fa6ff4ab4c36c2` |

原字节区间 `[2377,2541)` 改为显式给出同一凸组合不等式的 expected type，再调用 `convexOn_exp.2`；区间 `[3270,3328)` 用 `le_add_of_nonneg_left (Nat.cast_nonneg N)` 支付同一 `2 ≤ N + 2`。运行时用这两个精确 splice 重建完整 postimage。

## A、B 两次发布

发布 **A** 包含修复后的 SupportData、本目录及其他独立 source-only 交付。A 的完整 360 源中只有 SupportData 发生变化；原 current-corrections runner、manifest、additive installer 和静态入口保持原字节。此目录不保存 A 的自引用 SHA；执行时 `--source-commit` 必须给 A 的完整 40 位 SHA，脚本会核对自身执行字节和 A 中的固定 manifest。

从 A 取得本脚本后，在原 P1 环境依次执行。以下 `<A>` 与脚本路径由发布者填入，不从当前 dirty checkout 推定：

```bash
python3 -B /path/to/A/apply_source_repair.py --source-commit <A> --check
python3 -B /path/to/A/apply_source_repair.py --source-commit <A> --apply
```

`--check` 只读：不创建 attempt、receipt、archive，不安装源码，不改 artifact。它会报告唯一已知 setup 是否等待保留迁移。`--apply` 使用原 lane 0 serializer 与 lane 核验，并通过原 `h.install_sources` 执行单源 exact preimage → postimage，保留原源码备份；已是 postimage 时仅允许在所有目标仍 fresh 的状态下 noop。

发布 **B** 再把既有 current-corrections 的 `SOURCE_ANCHOR`、manifest source anchor、Support row/origin 及相应静态绑定明确锚到 A。该工作由原入口负责人完成。之后仍仅按原 first3 顺序验收 SupportData、PrimeChartHBWitnesses、CutoffData，保留原 supplier receipts。A 的单源安装不能代替 B 的来源重锚，也不能通过旧 additive installer 覆盖已有源码。

## 唯一失败 setup 的保留迁移

实际 21 项 artifact 检查只有以下路径存在；其他 20 项必须 absent：

`/workspace/blue-member-build/.lake/build/ir/ImbalancedChen/P1OriginalSingletonSupportData.setup.json`

该文件固定为 6416546 B、SHA256 `44d2df67689a5385662b6801c1241c0ed179316c603114c13c176dee3612a2b6`。在固定 normal exit-1 证据全部匹配后，脚本只允许此文件进入本次 attempt 的私有 `failed-artifacts/`：独占创建 0600 副本，flush/fsync 全字节并复核指纹，fsync 目录及元数据，再核原文件 dev/inode/size/mtime 和完整字节，最后只移除这一活跃路径。setup 正文始终留在 P1，不进入 stdout。

迁移后重新读取真实的完整 artifact 集合，调用原 `require_fresh_owner`；没有过滤或伪造集合来绕过 fresh gate。若活跃 setup 已 absent，必须存在同一 A、固定 manifest/job 下完整且指纹匹配的先前私有 archive。未知 artifact、任一指纹不同或不完整 archive 都 HOLD，不自动清理或重试。后续失败也保留 archive、源码备份和原失败证据。

## 保全与静态边界

运行时核对发布图 360 源、实际 first3 闭包 130 源及 active ∪ targets 共 148 模块；只改变一个 SupportData 源，其他 359 个发布源和 129 个 live 源保持一致。9 个活跃已接受 supplier、118 个固定 dependency、原 receipts、runtime/config 及所有其他 artifact 均有前后绑定。原 `h.install_sources`、guard、serializer 和验收接口不改。

原仓库 dirty 保护的准确范围是 **HEAD/status 前后相等**；脚本没有写入原 `REPO` 的代码路径。完整执行证据保存在 `/workspace/p1-complete-proof/20261126-p15-support-data-api-repair-v1/<A>/runs/attempt-xxxxx/`，stdout 只输出有界状态与指纹。

[STATIC_REVIEW.json](STATIC_REVIEW.json) 记录实际完成的本地字节/AST 检查及独立只读审查。未 import 或运行 updater/driver，未执行 Lean、Lake 或云任务；修复后的 Lean 源仍待原入口验收。
