# 最终原 CLI 导出到独立 tmpfs 的保全设计

这是只读设计，没有运行最终 exporter、创建最终包、删除原件或授予验收 credit。它只使用新输出目录，不涉及被审批拦截的旧 metadata 释放动作。

## 原 CLI 确实支持的接口

原 `export_winner9_private_evidence.py`（SHA `fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645`）第 232–243 行允许显式 `--output-dir`，并要求输出目录此前不存在。因此可以由原 CLI 在一次受控 job 内写入 `/tmp/<新的唯一目录>`，保持工作目录、全部原 source/object/native/receipt 检查和 full324 目标集合不变。

原 `--split` 仅支持 `all`、`group`、`module`（第 233 行）；没有 `--manifest-only`。最终必须由原 CLI 完整选择 ordered324 对应的全部模块，验证全部有效 receipt，并保留 `duplicate_owned_declarations == {}` 等原结果。不得以先前 selection-only 小报告替代最终 CLI。

## 分组并不会释放全局 raw evidence

成本依据在原代码中明确可见：

- `Evidence.add_path` 把整个文件读成 bytes；`add_bytes` 把它存入 `self.files[name]['data']`（第 75–98 行）。
- `main` 只创建一个全局 `Evidence()`（第 255 行）。所有模块 audit/source/type 和 native 文本先汇入这个对象。
- 分组发生在第 432–443 行；第 446 行每个 package 都使用**同一个** Evidence。没有每组创建、清空或释放原 bytes 的路径。
- `package()` 流式写 gzip/tar，但其输入 bytes 在全局对象中仍存活；`PACKAGE_MANIFEST` 和 file-index 序列化也需要额外内存。

所以 `--split group/module` 只改变包集合与每个包的成员，不保证降低全局 raw-bytes 内存峰值。它还可能让共同依赖成员出现在多个包中，增加总压缩输出；不能把按 module 分组当作无条件的内存修复。

旧 49 selected 的实际 raw payload 已达 4,302,650,543 字节，export job peak 约 5.12GB。这只能作旧批次的实测参考。加入 A 的实际三份完整 audit 文件 485,251,971 字节和其余模块后，必须先按**当前完整 selection 的唯一成员集合**估算 raw bytes、原解析临时对象、索引/manifest 和压缩输出。不能外推 full324 必然低于 13,107MiB。

## 一次原导出 + 同 job 持久保全

建议保留以下阶段界面，未来若实施须先另行审阅资源估算和脚本：

1. 在原锁下记录当前 HEAD、完整 current registry、ordered324 source/object、原工具、runtime、qualified native 前置绑定；确认全部 324 模块有当前有效原 gate/audit 依据。原 A/B/W 或 owned 尚未齐时不执行最终导出。
2. 子进程调用**原 CLI 原字节**，只指定一个全新 `/tmp` 输出目录以及原支持的 split 选项。stdout 保存小型原摘要；全部原包与完整 outer manifest 仍实际生成。
3. 等 exporter 子进程真实 exit0，复核原 manifest 的全 scope/duplicates/所有原成员索引。子进程退出后其全局 Evidence 内存已释放；tmpfs 生成的 gzip 仍计入 job memory。
4. 同 job 中流式检查每个完整原 gzip/tar：包长度与 SHA、完整 tar 字节指纹、每个 regular member 的名字/大小/SHA、无重复/异常路径、PACKAGE_MANIFEST 与 outer manifest 一致。
5. 在 `/workspace` 新独立目录生成固实 XZ，保存所有非 qualified-native 成员的**原 bytes**，所有生成 metadata/索引、完整 outer manifest、原 package 函数及工具源码、compression/runtime recipe、每个 package 的完整 tar 指纹、原 gzip 指纹/大小/文件名/排序/头信息。只有精确限定在已 qualified physical inventory 且逐项 SHA 验证的 native 分区可以保留引用，其他任何文件都必须保存原 bytes。
6. XZ 写入前按测得大小和必要 control files 留足原 32MiB `/workspace` reserve；写后 fsync、完整读回、逐成员/索引验证。保全完成和回执 durable 之前，不能声称临时导出已成为可恢复的交付物。
7. 全 canonical/runtime/native/source/registry 前后比较并保存实际 free/memory、全部阶段状态。没有删除旧源、对象、原 audit logs 或既有归档；此流程不对被拦截的释放操作作任何替代执行。

不能把临时 gzip 文件路径长期展示为仍可下载的文件。持久交付必须明确指向保全包和恢复步骤；若用户需要完整原 gzip，需先完成下面的独立重建并按实际可用载体交付。

## 独立 job 的精确重建要求

由一个新的 job，从持久 XZ 和完全冻结的 qualified-native 分区重建原 Evidence：逐项恢复原 name、origin、role、bytes 和 SHA；保留原 selected-records、created_utc、worktree、warnings/rejected、模块分组和所有 flags，不能重跑 main 后用新时间冒充同一 manifest。

每个 gzip 应由**原 `package()`** 对同一模块集合和排序成员运行。`gzip.GzipFile(fileobj=raw, mtime=0)` 未显式传 `filename=''`，头部可能从 `raw.name` 获取 basename。因此临时重建目录可以不同，但包的 basename（如 `all.tar.gz`、`common.tar.gz`）及 Python/gzip/tarfile/zlib 运行时必须按原 recipe 保留并校验。仅说“mtime=0，排序相同”不足以保证整 gzip 同 SHA。

重建完成后，检查每个原包完整 bytes/SHA、完整 tar 指纹和每个成员，外层 manifest 原 bytes/SHA 也逐字一致；随后再次核 qualified-native、所有持久保全物和 canonical 状态。独立重建是交付完整性的证据，不替代原 CLI 本身的有效 receipt 选择，也不新增 compile/kernel/owned/P2 credit。

## 资源与失败边界

`/tmp` 与 `/workspace` 虽是不同文件系统，根 tmpfs 消耗仍计入 job 内存限额。原 CLI 运行时的峰值至少同时包含全局 evidence bytes、解析/metadata 临时内存，以及已写出的 tmpfs gzip。后续保全可在 exporter 退出后进行，以避免人为叠加两套巨大 Python 数据结构；保持流式处理，不把完整 4GB tar 再读成第二份 bytes。

若预算预估不能证明合理余量，或实际任一阶段失败，就只记录失败与仍存的完整工件；不能缩小 scope、删除原类型、放宽原 checker、把不完整包叫作最终输出，或提高原资源限额。现有证据不足以断言 full324 此设计一定 fit；它只是原 CLI 支持且不触及旧文件删除的候选存储路径。

该原 exporter 的 `full_p2_complete` / `full_winner9_family_claimed` 字段保持其原值，不为本轮目的修改。最终 P2.4 边界仍须由原指定数学端点及完整 current gate/audit/export 记录共同说明。
