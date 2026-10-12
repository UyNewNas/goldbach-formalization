# 引用路径的解析范围

本台账的 `original_record_scope` 定位本包内两份原始 Round 3 JSON 及类型格式纠正表。**复制原始 JSON 不会改变其内部相对路径的原基目录。** `OUTPUT_MANIFEST.json` 所列文件是本次选定的交付内容；它不表示所有旧证据、运行时或依赖对象都已复制到新台账。

固定历史提交为 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`。下表中的仓库路径均从仓库根开始：

| 引用所在位置／原路径 | 实际解析位置 |
| --- | --- |
| 本轮新生成记录中的 `snapshot-sources/`、`input-receipts/`、`previous-ci/`、`original-evidence/` 及本轮类型 JSON 文件名 | 本轮 `verification/parts/p0/round4/ledger/` 下对应文件；仅按本包清单判断是否已复制 |
| 新台账里继承的 validation / toolchain 字段中的 `history/round2/ledger-delivery/...` | 固定历史提交的 `verification/parts/p0/round3/ledger/history/round2/ledger-delivery/...` |
| 新台账 `toolchain.protected_config[*].snapshot.path` 中的 `protected-config/...` | 固定历史提交的 `verification/parts/p0/round3/ledger/protected-config/...` |
| 继承的 `../intake/...` | 固定历史提交的 `verification/parts/p0/round3/intake/...` |
| 继承的 `../../../../part2/round2/prefix4/gates/...` | 固定历史提交的 `verification/part2/round2/prefix4/gates/...` |
| 复制到 `original-evidence/round3-module-ledger.json` 的原始文件内部引用 | 保持其原目录 `verification/parts/p0/round3/ledger/`；不能相对 `original-evidence/` 或本轮目录重新解释 |
| 继续读取 `history/round2/ledger-delivery/module-ledger.json` 后，其内部相对引用 | 按该历史文档自身原目录／记录约定解析；不能一律套用外层 Round 3 或 Round 4 目录 |

此次发布前只做了路径说明复核：上述四组继承路径在新模块台账中共有 **44 个不同引用**，均可从固定 `28fd630…` 读取；读取字节与原条目的 SHA256、字节数相符。没有重新执行 3,422 条整理检查、Lean 或 CI。

三个保护配置也可直接读固定历史提交的仓库根 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`；不能把这些仓库根路径当成本包内文件名。示例：

```bash
git show 28fd630ef7cc38eba86beb6c0ba123336b5d05f2:verification/parts/p0/round3/ledger/protected-config/lean-toolchain
git show 28fd630ef7cc38eba86beb6c0ba123336b5d05f2:verification/parts/p0/round3/ledger/history/round2/ledger-delivery/module-ledger.json
```

`input-receipts/` 中保留的生产者绝对路径、archive member 名和原相对路径是历史 provenance；应连同该记录的固定 SHA、归档身份和哈希读取。它们不保证对应旧工作目录今天仍存在，也不保证相应二进制嵌入本包。原始运行对象只记录哈希而未嵌入时，继续保持这一限制。

本轮新集成 SHA 的门在候选台账中仍为待执行；固定历史提交的成功不自动覆盖本轮新提交。
