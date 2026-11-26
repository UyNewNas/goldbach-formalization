# 三项条件性 metadata：只读消费者结论

本报告没有执行远端任务，没有扩大 draft02 的 13 项白名单，也没有删除任何原件。第一阶段保全任务 `f4ea526437424a519930753257d6e725` 已成功；随后释放动作被自动审批拦截，没有创建释放任务，完整拒绝理由尚未恢复。现行后续是独立 verification-only，不能将未来可能释放的字节计作当前空闲空间。

## 逐项结论

| 原件 | 字节数 | 当前能证实的事实 | 尚未证实的条件 |
|---|---:|---|---|
| `.lake/p24-cache-migration/attempt-001/ORIGINAL_DONOR_RECORDS.json` | 16,227,671 | 已读原 checks、audit、exporter、migration 工具源码，没有该文件名或目录的硬编码读取 | 当前 qualified snapshot 的完整 `files` 集、当前有效 receipt 的 `artifacts` 是否引用它；旧保全包是否已包含其完整字节 |
| 同目录 `MIGRATION.json` | 4,134,853 | 同上；原 `migrate_winner9_private_snapshot.py` 实际读 `.lake/p2-private/records.json`、`baseline-cache.json` 和显式 `fresh_receipt`，写 `schema2-migration.json`，不是这两个指定文件的固定消费者 | 同上；不能用不同 migration 工具没有硬编码路径来证明所有历史消费者不存在 |
| `.lake/p24-audit-export/source6e-full324-preflight-001/manifest.json` | 11,997,843 | 精确原字节已在旧持久 XZ 中保全，旧跨 job 重建实际成功；普通 `rebuild_original_export.rebuild` 从 bundle 读 manifest，不读该松散原路径 | 历史 stage1/stage2 的输入冻结仍读松散路径；当前 native/receipt/显式 export extras 的物理依赖尚未排除 |

三项合计 32,360,367 字节。它们目前仍应保留；本报告没有给出释放许可。

## 为什么“原代码没有这个文件名”不够

固定 b55 的 `winner9_external_snapshot.py`：

- 构造函数直接取 `self.files = value["files"]`（约第 113 行）。结构验证要求绝对路径、有效 hash 和大小，但不把所有文件限制到某一个 cache 子目录。
- `verify()`（约第 193–201 行）逐个读取 `self.files` 中的物理文件并校验大小、SHA。
- `binding()` 只返回 snapshot 路径/摘要、context signature、模块集和搜索路径，**不包含完整物理文件表**。因此当前 receipt 中只有 native binding 的情况下，不能据它认定这三项不在被核验集合中。

原 exporter 的 `validate_receipt` 还逐项冻结 receipt 的任意 `artifacts` 条目（约第 194–199 行）。这些物理路径由 receipt 提供，也不需要源码出现文件名。最终 `--extra-evidence` 是第三个可显式加入原件的入口。

原 exporter 的自动补充扫描限于 `.lake/p2-private`（约第 388–403 行）。本报告三项的 `.lake/p24-cache-migration` / `.lake/p24-audit-export` 都在该自动扫描范围外；这只能排除**该自动入口**，不能排除上述三个动态入口。

## 旧 manifest 的精确保全链

固定旧 `stage1_preserve.py` 第 12、34 行把原 manifest 的完整 bytes 保存为 `metadata/original-export-manifest.json`。旧 `rebuild_original_export.py::rebuild` 第 23–24 行从 bundle 获取并核对：

```text
bytes = 11997843
sha256 = 7a99f246b4c8bc54bc55ce3497de1445a270d76a34ce6af0a2e1b8e1f5e1e934
```

同一函数第 40 行仅对明确的 qualified-native 分区读取 `record['origin']`；其他所有原包成员来自持久 bundle 的 `members/...`。它重建原 `all.tar.gz` 时使用原 package 函数，并检查整包及全部成员。

实际成功回执 `/tmp/p24-export-retention-recovery-20261126/stage2-actual/stage2-rebuild-verification.json`，SHA `7675714e3ff393ef3ca50c652722fe0bca8e97f9acc0aa34c124e60a0dcfbed8`，确认：

- 持久 XZ：28,798,608 字节，SHA `059f665f7dd471a5f19a8ec7fcce4302deb3ab0ba170b2a34bd1db214e94ad49`。
- 原 gzip：581,735,403 字节，SHA `3fae348f45b7bab70e3fb11f5c8f68ff26ff5b03892ff44d9046bad1e8b94463`。
- 全部 13,856 个成员、4,302,650,543 字节都核过；其中 1,752 项 qualified native 保留原物理来源和逐项 SHA。

该实际回执足以确认 manifest 已保全，**不**足以确认两个 migration JSON 已保全。后者需要旧 `manifest['files']` 的精确 origin/大小/SHA 对照；当前本地只有 aggregate receipt，没有完整旧 origin 索引。

## 已识别的松散 manifest 消费者

普通 `rebuild()` 不依赖松散原件；以下历史函数仍依赖：

- 旧 `retention_common.py::current_inputs` 第 131–136 行直接 `digest(MANIFEST)` / `stat()`。
- 旧 stage1 在第 12 行直接读它。
- 旧 `stage2_verify_and_release.py` 第 73、96 行在其历史 gzip 释放前后直接校验该原路径。

上述已验证历史源码保持原样。若未来另有明确授权处理松散 manifest，兼容契约必须是：**调用任何需要原路径的历史程序之前，先从现有持久 XZ 提取原 manifest，校验 11,997,843 字节及 7a99…，通过独占安装恢复该原路径；已有文件不覆盖。** 普通 `rebuild()` 本身不必恢复原路径。该契约目前仅是恢复接口分析，没有实现新删除动作，也不改变已有回执承诺。

## 还缺的最小只读证据

若 root 需要继续分类，只需读取并输出小型报告，不必重新编译或导出大包：

1. 当前 SHA 固定 `EXTERNAL_SNAPSHOT.json` 的完整 `files` 对这三个绝对路径及实际 inode/解析别名的命中。
2. 当前被原 selection 选中的 receipt `artifacts` 对三路径的命中；保守地列出仍在历史 receipt 中的命中。
3. 旧 export manifest / bundle 索引中两份 migration 文件的精确 origin、大小、SHA；找不到即明确“未保全于该包”，不推断。
4. 当前及计划最终原 CLI 的 `--extra-evidence` 列表。

这四项目前未通过新的 P2 任务取证，本报告不会补造结果。无论结果如何，已被拦截的释放动作不因这份只读分析而获得批准。

## 固定源码依据

所有下列副本仅在 primary `/tmp` 读写，原生产文件未动：

| 固定原文件 | 本地副本 | SHA256 |
|---|---|---|
| b55 checks | `original-run-winner9-private-checks.py` | `164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac` |
| b55 migration | `original-migrate-winner9-private-snapshot.py` | `3a78c17ff965d12710e7fff943ab6bce5fc74d418d87d9f7f9d40373f912f44b` |
| b55 external snapshot | `original-winner9-external-snapshot.py` | `a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf` |
| 原 exporter | `/tmp/p24-export-retention-recovery-20261126/original-exporter-test.py` | `fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645` |
| 原 audit | `/tmp/p24-nine-source-promotion-20261126/original-run_winner9_private_audit.py` | `571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5` |
