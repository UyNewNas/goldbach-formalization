# 文件引用与复核范围

本目录是 P0 对固定后续交接 `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9` 的外部接收材料，没有进入冻结集成 `d0366ce64272e81faf6166a8a90050f56b328d38`。

| 引用 | 本目录中的实际位置或固定来源 |
| --- | --- |
| 原交接的 `HANDOFF.md`、`SOURCE_TYPES.md`、`receipt.json`、`strict-compile*` 等 | `fixed-source/verification/parts/p3/prime-ap-distribution/`；该目录 18 个文件均为 f3 固定 Git 原字节 |
| 原 `inventory-evidence.tar.xz.b64` | 同上；解码字节另存本目录 `inventory-evidence.tar.xz` |
| 原归档的 6 个成员 | `archive-evidence/`；全部成员与原 manifest 逐项一致 |
| 项目源和工具链／依赖文件副本 | `fixed-source/`，只复制 `FIXED_FILES.json` 实际列出的 24 项；不是整个仓库副本 |
| 独立取得的固定 goldbach 源 | `upstream-fixed-source/`，6 个文件，完整 pin 为 `09b97db5764ade1246bfb77206baa1b124760958`；`upstream-api/` 保留每个 API 原始响应 |
| 独立源码供应审查 | `supplier-scope-review/`；其 `project-fixed-source/` 另有 3 个从 f3 固定 Git 读取的项目定义源 |
| `D036_LEDGER_ALIGNMENT.json` 引用的冻结台账 | git `d0366ce64272e81faf6166a8a90050f56b328d38:verification/parts/p0/round4/ledger/MODULE_LEDGER_CANDIDATE.json`；仅比较，并未覆盖该固定文件 |
| 旧直接前置模块的原 core 证据 | git `d0366ce64272e81faf6166a8a90050f56b328d38:verification/parts/p0/round4/ledger/previous-ci/core-artifact.zip`，其真实运行源为 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` |
| 旧 artifact 在当前 workspace 的已恢复副本 | `/workspace/scratch/535d89efd063/p0-round4/previous-28fd630/core-artifact.zip`；本次比对了它与上行固定 Git 载荷的完整字节；没有复制整份旧 artifact 到本目录 |
| 原证据中的 `/workspace/scratch/127408f63891/...` 与 `/workspace/scratch/e8f85e58ac36/...` | 生产者原始命令、source/object 路径与运行时身份；这些是历史路径，不表示当前消费者可访问这些对象或运行时 |

`verify_late_intake.py` 是消费者的离线源／证据一致性检查程序，只执行固定 Git 的 `show`、`ls-tree`、`diff-tree` 与本地字节检查。当前路径下可复核：

```bash
cd /workspace/scratch/535d89efd063
python3 p0-round4/late-intake/p3-f3ad8cbe/verify_late_intake.py
```

这个入口依赖同 workspace 已恢复的固定 Git 对象和旧 artifact；运行会重新生成本目录机器回执中的检查时间。它不会启动 Lean、Lake、Elan、leanchecker 或 CI，也不会改变任何仓库文件或 refs。生产者的 `diagnose_imports.py` 和归档 `frontend-driver/lakefile.lean` 只用于证据阅读，没有被消费者执行。

`OUTPUT_MANIFEST.json` 覆盖本目录实际交付的文件，排除自身。原证据引用而未复制到这里的整仓库、包对象闭包和旧 artifact 仍按上述固定来源解析，不能称为已经完整打包或已在本消费者运行环境可用。
