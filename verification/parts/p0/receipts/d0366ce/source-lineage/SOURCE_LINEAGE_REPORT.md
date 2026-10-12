# d036 的实际父链核对

**结论：符合用户指定祖先关系。** `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` 是集成 `d0366ce64272e81faf6166a8a90050f56b328d38` 的第 8 代父链祖先；共同证明基线 `1a80c1bcce67886f699d097fc37fd245cd3620bf` 是第 9 代。文档提交的直接父节点正是共同证明基线。

9 条实际父边已逐项读取，这段链中每个子节点都只有表中列出的一个父节点，没有未闭合边。3 个节点使用本地 `git cat-file -p` 原始 commit 字节，并按 Git commit 对象格式重算 SHA-1；其余 7 个本地缺失节点使用固定 SHA 的 GitHub Git-commit GET 原始元数据。所有原件和摘要都保留在本目录。

## 逐节点身份

| Commit SHA | Tree SHA | 原始／API 返回的父 SHA | 证据 |
| --- | --- | --- | --- |
| `d0366ce64272e81faf6166a8a90050f56b328d38` | `e2ab22b96f76c8969386296558c626c62a581700` | `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | 本地原始 commit，已重算 SHA-1 |
| `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` | `0c72ea1ceff699e58a728cf0ae5714609d55b617` | `cce2334906f068fda2f58c400646366f2aa2d417` | 本地原始 commit，已重算 SHA-1 |
| `cce2334906f068fda2f58c400646366f2aa2d417` | `0ce5014595c7468f87f5f5d8c7083a3c5c8f5155` | `80aca6710c83b5160f4c5fdd05d180e507990e95` | 固定 GitHub Git-commit API |
| `80aca6710c83b5160f4c5fdd05d180e507990e95` | `dd01bf7710f0ba0a9ddadb01ff0f608c5bb2607c` | `278f949444748a30b5165ff47bfa283ab0bad0d8` | 固定 GitHub Git-commit API |
| `278f949444748a30b5165ff47bfa283ab0bad0d8` | `9723353ffbda12028cdd9e64e36ccb3ac8fbd4b5` | `5e31713690daba5ff926da61875a99171718fd1d` | 固定 GitHub Git-commit API |
| `5e31713690daba5ff926da61875a99171718fd1d` | `77250593d254d680daf97a5d8930ee6f04949597` | `c9f407efe66240c08c2e8a678330ba7b98b74db5` | 固定 GitHub Git-commit API |
| `c9f407efe66240c08c2e8a678330ba7b98b74db5` | `c818607f1ffda6246cf1d03dd9a5dbb557c94be3` | `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` | 固定 GitHub Git-commit API |
| `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` | `298589f8e0d13cbdfbfc828c46c9545a6f09cb46` | `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` | 固定 GitHub Git-commit API |
| `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` | `d6c087c8c8ba025aebfb72a3ec43e80f4e056308` | `1a80c1bcce67886f699d097fc37fd245cd3620bf` | 固定 GitHub Git-commit API |
| `1a80c1bcce67886f699d097fc37fd245cd3620bf` | `1fd54b8b4d5fd89abc767ee7e8d814453453b29c` | `08d6e1385f747f8a0e45e77689f7c714653ac8f4` | 本地原始 commit，已重算 SHA-1 |

## 浅克隆观察应如何解释

`LOCAL_GIT_ANCESTRY_OBSERVATION.json` 的原字节副本保留为 `ORIGINAL_LOCAL_GIT_ANCESTRY_OBSERVATION.json`。其中本地 repository 明确为 shallow，`git log` 在 `28fd630…` 停止，`merge-base` 对共同基线返回 1，对本地缺失的文档对象返回 128。这些返回值属于本地不完整历史的观察，不等同于实际非祖先关系。

直接读取 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的原始 commit 对象可见 `parent cce2334906f068fda2f58c400646366f2aa2d417`，因此浅克隆遍历隐藏的父边确实存在。继续沿固定元数据逐边读取即可到达文档提交与共同证明基线。没有通过改写 `.git/shallow`、重建仓库或改 refs 来改变原观察。

## 证据边界

固定 API 返回的 SHA、tree 和 parent 已核对，但没有取得这 7 个远端节点的原始 Git 字节，因此不声称对它们重算了 commit SHA-1。API 的 unsigned／signature 状态原样保留，不宣称完成签名验证。共同基线以前的历史不在本次遍历范围；基线原始对象里可见的更早父指针仍保留在表中。

此回执只确认源代码历史，不增加任何 Lean 编译、内核重放、公理审计或最终定理验证状态。没有启动或轮询 CI，没有执行 Lean/Lake/Elan/leanchecker，没有触碰健康构建或集成分支。

## 可复核文件

- `SOURCE_LINEAGE_RECEIPT.json`：完整 SHA/tree/parents、9 条已闭合父边与机器结论。
- `SOURCE_LINEAGE_CHECKS.json`：本消费者 75 项证据核对。
- `local-raw/`：3 个本地原始 commit 对象。
- `github-api/`：7 个固定 Git-commit API 原始响应封装。
- `github-metadata/`：上述 API 返回的原 JSON 内容字节。
- `verify_source_lineage.py`：只使用这些已保存文件的离线复核程序，不执行 Git、网络、Lean 或 CI。
- `OUTPUT_MANIFEST.json`：实际交付文件的字节数和 SHA-256，排除自身。
