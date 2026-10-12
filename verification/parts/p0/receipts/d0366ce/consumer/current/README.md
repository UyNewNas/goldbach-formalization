# 实际核心原件的离线消费入口

本目录的 `consume_core_artifact.py` 是实际成功消费同一个原始核心 artifact 的版本，SHA-256 为 `5d697e55919c1e8a35053fbfb662605839ddba9319266b3ed97bc9a497c20e18`。它只读取固定 Git 源、原始 ZIP 和原始 GitHub 元数据；不运行 Lean、Lake、leanchecker、CI 或网络，不产生新的证明验证结果。

本次实际第二次消费已完成，结果为 `PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE`，3956 项检查通过。输出保存在 [core/verified](../../core/verified/)。第一次消费者错误及旧脚本仍保存在 [core/first-consumer-attempt](../../core/first-consumer-attempt/) 和 [原脚本及修复补丁](../actual-core-scope-correction/)。上级 `consumer/README.md` 及原 preparation 文件保留编写时的身份与状态；新的执行入口是本目录。

## 在别的会话复核原件

在包含此回执的仓库根执行以下命令。`--repo` 指向本地可读取固定提交 `d0366ce64272e81faf6166a8a90050f56b328d38` 的 Git 仓库；程序通过 `git show` 读取该完整 SHA 的源与继承证据，不把当前文档分支的 HEAD 当成已验证源码。输出目录由 `mktemp` 创建，位于仓库之外，不覆盖任何已封存回执。

```bash
P0_GIT_REPO="$(pwd)"
P0_RECEIPT_DIR="$P0_GIT_REPO/verification/parts/p0/receipts/d0366ce"
P0_RECEIPT_OUTPUT="$(mktemp -d /tmp/chen-p0-d0366ce-receipt.XXXXXX)"
python3 "$P0_RECEIPT_DIR/consumer/current/consume_core_artifact.py" \
  --repo "$P0_GIT_REPO" \
  --artifact-zip "$P0_RECEIPT_DIR/core/original/core-artifact.zip" \
  --run-json "$P0_RECEIPT_DIR/core/original/run.json" \
  --jobs-json "$P0_RECEIPT_DIR/core/original/jobs.json" \
  --artifacts-json "$P0_RECEIPT_DIR/core/original/artifacts.json" \
  --output "$P0_RECEIPT_OUTPUT"
```

缺失证据保持 `PENDING`；已经绑定的实际 CI 失败不会被缺 ZIP 或缺 Git 对象降成未知。命令仅供复核；为编写本页没有重新运行消费者或证明检查。新输出中的时间戳与路径属于调用者的复核过程，不能覆盖实际 CI 时间或原始 producer 记录。

## 必须保留的范围

- 核心 CI 源码为上述完整 d036 SHA，run `38289734671`、job `114946653833`、attempt 1。它的六个门都已实际成功。
- 23 个接收组件按固定源码导入图可达性检查；本批四模块仍要求根直接导入及显式 target。20 个组件具有本轮对象快照；另外三个保留旧 producer 记录与当前根重放标记，当前对象散列不补造。
- 每轮 before/after 完整相等；跨轮 267 个对象 map 相同，274 个源码条目中只有共同 272 个相同。两轮完整源码 map 各含两个专属 audit/exporter 路径，不能声称整体相等。请连同 [SNAPSHOT_SCOPE_CLARIFICATION.json](../../core/SNAPSHOT_SCOPE_CLARIFICATION.json) 阅读原成功输出。
- 1005 个类型为 393 继承、198 本次 Round3、414 本次 Round4；1000 个 `pp.all` 与 5 个旧 Buchstab 默认完整打印。主桥、VE 和额外上游 Rosser 分列。
- `hLower_hUpper_discharged=false`，最终无附加分析输入的定理仍待真实供应。离线消费成功不关闭这些数学输入。
