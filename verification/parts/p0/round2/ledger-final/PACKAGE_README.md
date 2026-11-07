# 冻结台账交接包

完整冻结输出保存在 `complete-ledger.tar.gz.b64`。其中包含原始 `module-ledger.json` 的全部字段和输入目录内全部文件；没有重写 JSON、删去类型或丢弃证据。归档内统一以相对目录 `ledger-delivery/` 为根，不含外部绝对路径的归档成员。

三份主要 Markdown 已直接提供。`ledger-index.json` 是精简导航索引，并非完整台账替代品；完整类型及证据仍可从归档还原。Lean 源副本只留在完整归档原有目录内，没有复制到仓库默认生产根。

## 精确身份

- 原始 `module-ledger.json` SHA256：`fbc89d287e58d693b09bb1b53cbe1b4468992754389ec6c1863031e8a2aa8e73`
- `package-manifest.json` SHA256：`fd927acf5a4c8c36fff8cbb9da7329a8e11f1f70e9b56ece98f3917f267d318f`
- 解码后 gzip SHA256：`b761a757c7d4dda8a27f869743570d9dc91ad479f9d282ee2e9df88dcf1457d5`
- base64 文本 SHA256：`5bc04596aee532b4497f696602c9b348fe58782635382e379d19283c145914c3`
- 完整输入：106 个文件，9608589 字节。

`package-manifest.json` 列出每个原始相对路径、字节数、SHA256 和还原权限，以及直接可读文件/索引的哈希。`SHA256SUMS` 包含交接包所有其他文件的校验值。

## 还原

使用 Python 3.9 或更新版本的标准库。在本交接包目录中运行：

```bash
sha256sum -c SHA256SUMS
python3 unpack_ledger.py --destination /chosen/restore-directory
```

脚本先核对 manifest、base64 和 gzip 哈希，再按清单校验并还原每个文件到 `/chosen/restore-directory/ledger-delivery/`。它拒绝覆盖已有同名目录，拒绝链接及越界归档成员。原始完整台账为 `ledger-delivery/module-ledger.json`。

## 可复现与验证边界

归档按路径排序，规范化 tar 时间/所有者和权限，gzip 不写当前时间或来源文件名。相同输入内容、执行位、归档根目录名及 Python/zlib 实现产生相同归档。打包时前后重新核对输入清单；源目录变化则拒绝发布。

本工具只封装已冻结结果。它不运行 Lean、Lake、内核重放、公理审计或 Actions，不提升台账中的任何验证状态。
