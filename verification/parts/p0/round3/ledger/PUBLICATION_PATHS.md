# 发布路径与待复制原始日志

台账最终位置：`verification/parts/p0/round3/ledger/`。

各 intake 证据链接使用 `../intake/<原 intake 目录>/`；CCE 原始 artifact 使用 `../prior-ci/cce-core/`。P2 已在生产验证目录的 gate/log/type 文件直接引用 `verification/part2/round2/prefix4/`，不重复复制。

已核对 39 个外部引用文件在发布树中存在且哈希一致；另有 3 个直接引用文件需要复制，清单如下。此清单不修改源分支或发布树。

| 原始文件 | 发布仓库目标 | SHA256 |
| --- | --- | --- |
| `/workspace/scratch/535d89efd063/p0-round3/p1-intake/evidence/runtime/logs/closure-attempt-01/closure/verification.parts.p1.Part1HistoryAudit.log` | `verification/parts/p0/round3/intake/p1-intake/evidence/runtime/logs/closure-attempt-01/closure/verification.parts.p1.Part1HistoryAudit.log` | `e4044b13c07e66e84051650f799b3fda9774959e5fa9c0a69f2dfbeda2f87d47` |
| `/workspace/scratch/535d89efd063/p0-round3/p1-intake/evidence/runtime/logs/closure-attempt-02/closure/verification.parts.p1.LevelCheckProbe.log` | `verification/parts/p0/round3/intake/p1-intake/evidence/runtime/logs/closure-attempt-02/closure/verification.parts.p1.LevelCheckProbe.log` | `80c4bd7996cc34601276d6d12c36cd713284d9e5901e27923f85b435347d042a` |
| `/workspace/scratch/535d89efd063/p0-round3/p2-p4-intake/p2/fixed/verification/part2/round2/prefix4/receipt.json` | `verification/parts/p0/round3/intake/p2-p4-intake/p2/fixed/verification/part2/round2/prefix4/receipt.json` | `a7eda6ca5d823aaa31e5ebce320f0fca802ab123cdd99a21ef0d7d692c677ca1` |

机器可执行复制清单见 [COPY_MISSING_FILES.json](COPY_MISSING_FILES.json)。完整复制 ledger-candidate 目录即提供所有内部源码、历史台账与历史日志；不要省略其 history/ 子目录。
