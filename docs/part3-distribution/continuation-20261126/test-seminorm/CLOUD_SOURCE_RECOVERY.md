# P3.5 六份登记源码的云工作区检索状态

**P1、P2 的只读文件名清点已提交，17:02 UTC 最后一次复查时均在队列中。** 备用编译器因保留任务数量上限拒绝提交。六份登记文件在这些当前工作区是否存在仍待核实。

## 已有检索范围

`5285d4f5d8c40eddf92c108b492c909de8b43cef` 的 `continuous-height/CLOUD_SOURCE_RECOVERY.json` 记录的是 P3 工作区内的 Git 对象检查，包括 `/workspace/goldbach-p3` 的 27,462 个对象和 `/workspace/goldbach-formalization` 的 6 个对象。其 README 明确记载当时 P1、P2 都有运行和排队任务，未查其文件或对象。P3.4 对恢复后的 P3 工作区和可见 worktree 的检索，以及历史 Git 和归档的检查，均有单独收据。当前 P3 工作区的检查由协调代理完成。 [P3.5 历史记录](https://github.com/UyNewNas/goldbach-formalization/blob/5285d4f5d8c40eddf92c108b492c909de8b43cef/docs/part3-distribution/continuation-20261125/continuous-height/README.md) · [P3.4 已有云端检查](https://github.com/UyNewNas/goldbach-formalization/blob/f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e/docs/part3-distribution/p34-20261125/SOURCE_RECOVERY_RESTORED_P3.md)

## 2026-11-25 UTC 的三项预检

| 工具环境 | `compiler_info` 和 `system_info` 的结果 | 工作区检查任务 |
| --- | --- | --- |
| P1 Private Compiler · 32GB · 6b053c6d | 已读。首次见 1 个运行、11 个排队。16:36:32 复查仍有 1 个运行、10 个排队，活动任务为 `job_a82c490d9f634f92bae162a54bf16fd0`。 | 未提交。 |
| Cloud Compile Private 8e1da5a7（P2） | 已读。首次和 16:36:33 复查均为 1 个运行、5 个排队。活动任务为 `0e75fdae4cbf4a0c853856c1c5eb2704`。 | 未提交。 |
| Cloud Compile（备用） | 已读。16:35:15 的状态报 0 个运行、0 个排队。 | 请求在 `/workspace` 以 1 个 CPU 线程、128 MB、45 秒上限运行只读检查。工具返回 `INVALID_ARGUMENT`，原文是 `retained-job limit reached; ask owner to archive jobs`。任务未创建，没有任务 ID。 |

备用环境拟执行的命令只匹配以下六个精确 `.lean` basename，跳过 `.git`、`.lake/packages` 和 `node_modules`，不追随目录符号链接。对候选常规文件比较长度与 SHA-256，并记录 `/workspace` 及其直系 Git worktree 的当前 HEAD、分支和 tracked 状态，关闭 Git 可选写锁。

- `Part3NativeCuspAllowedRowRightAction.lean`
- `Part3NativeAllCuspEisenstein.lean`
- `Part3NativeAllCuspEisensteinSpatialConvergence.lean`
- `Part3OriginalCharacterPairDilation.lean`
- `Part3NativeAllCuspFrameCovariance.lean`
- `Part3CharacterPairDivisorAmplitude.lean`

首次预检期间没有执行文件清点。预检未做编译、Git 历史对象扫描或云端写入。

## 16:51 UTC 后续提交

较早未提交记录保留于上。16:50 重新确认容量后，P1 与 P2 各提交一次当前文件清点，均为 1 个 CPU 线程、128 MB、45 秒运行上限。任务命令保留 `.lake/proof-continuation/source-reviews/drafts`，跳过 `.git`、`node_modules`、`.lake/packages` 和生成构建目录。备用编译器保持原状态。

| 环境 | 重新检查的队列 | 新清点任务 | 提交响应 |
| --- | --- | --- | --- |
| P1 | 16:50:35，1 个运行、9 个排队，队列上限 16 | `job_165cb6b9d7bb4921a0bae72a04d33732` | 16:51:31，已排队 |
| P2 | 16:50:30，1 个运行、3 个排队，队列上限 8 | `53e14470214e497a90db4f45c79a23e1` | 16:51:25，已排队，响应返回队列位置 6 |

文件名清点记录每个同名候选的路径、长度、SHA-256 和登记哈希匹配状态。直系 Git worktree 只读取 HEAD；当 worktree 不超过 8 个时另读取 tracked 状态。两个任务均未检查历史 Git 对象、归档或 P3 工作区。表中为提交时状态，实际读取结果见后续终态记录。


## 最后一次只读状态及续查

| 环境 | 查询时刻（UTC） | 状态 | 输出 | 上次看到的队列位置 |
| --- | --- | --- | --- | --- |
| P1 | 17:02:38.983 | `queued`，`started_at=null` | `output_bytes=0` | 17:01:29.521，第 10 |
| P2 | 17:02:40.281 | `queued`，`started_at=null` | `log_bytes=0` | 17:01:30.797，第 6 |

两项任务保留在队列中。当前证据覆盖工具预检、提交回执与任务排队状态。P1/P2 的工作区文件、候选字节与 HEAD 清单仍待实际读取。备用环境的保留任务限制仍在，当前文件同样待核实。P3 工具与既有 Git 历史、归档结果不计入这两项当前工作区清点。

下一轮可通过以下对应工具复查同一任务。

| 环境 | 复查状态 | 读取输出 |
| --- | --- | --- |
| P1 | `mcp__codex_apps__p1_private_compiler___32gb___6b053c6d__p1_private_compiler_32gb_6b053c6d_get_task({task_id:"job_165cb6b9d7bb4921a0bae72a04d33732"})` | `mcp__codex_apps__p1_private_compiler___32gb___6b053c6d__p1_private_compiler_32gb_6b053c6d_read_task_output({task_id:"job_165cb6b9d7bb4921a0bae72a04d33732",offset:0,limit:4000})` |
| P2 | `mcp__codex_apps__cloud_compile_private_8e1da5a7_get_task({task_id:"53e14470214e497a90db4f45c79a23e1"})` | `mcp__codex_apps__cloud_compile_private_8e1da5a7_read_task_output({task_id:"53e14470214e497a90db4f45c79a23e1",offset:0,limit:65536})` |

任务终止后按返回的 `next_offset` 读至 `eof`。第一行记录已遍历目录、文件、同名候选、登记字节匹配和读取错误，第二行记录直系 worktree。只有实际输出才能确认命中或有界未命中。

## 17:08 UTC 发布前更新

P1 任务 `job_165cb6b9d7bb4921a0bae72a04d33732` 已成功结束。其文件清点完成时刻为 17:06:21.372114 UTC：在上述限定范围内遍历 15,040 个目录和 144,311 个文件，六个精确 basename 的候选列表为空，读取错误列表为空。完整输出 1,714 字节，`eof=true`、`output_truncated=false`。任务元数据、实际清点输出和直系 worktree 记录保存在 [P1_SOURCE_RECOVERY.json](P1_SOURCE_RECOVERY.json)。这只确认当前文件名检查的有界未命中；不重查旧 Git 对象或归档。

同次发布前查询中，P2 `53e14470214e497a90db4f45c79a23e1` 仍为 `queued`，`started_at=null`、输出 0 字节。它保留在队列中，下一轮优先读取同一任务，不重复提交。备用环境仍未完成工作区读取。

P1 的 `read_task_output` 请求 `limit=65536` 返回 `INVALID_ARGUMENT`；改用 `limit=4000` 后完整读取以上输出。上面的 P1 续查示例已采用 4000。
