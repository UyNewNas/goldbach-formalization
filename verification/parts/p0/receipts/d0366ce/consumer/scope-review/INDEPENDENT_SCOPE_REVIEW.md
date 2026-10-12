# 实际 core 消费者导入范围修正：独立复核

## 结论

**未发现需要阻止本次接收的验证门放宽或真实性缺陷。** 修正处理的是旧消费者对历史模块的一条过强范围要求；实际固定根已经通过传递导入包含这些模块。新消费者仍要求本批四个新增模块被根直接导入、在固定 workflow 的显式 `lake build` 命令中逐个列出，并保留原有六门和完整类型、源码、公理检查。

实际第二次消费的 PASS 绑定同一真实 CI artifact，没有重跑或替换 CI；第一次失败目录和原消费者完整保留。这里进行了 69 项静态／原始归档／固定源码交叉核对，没有执行任何一版消费者，也没有运行 Lean、CI、构建环境或网络操作。

## 固定输入身份

| 输入 | 身份 |
| --- | --- |
| 集成源码 | `d0366ce64272e81faf6166a8a90050f56b328d38` |
| 原消费者 SHA-256 | `925ebb6e12e1693635ca56dfbf58fc548e5ee350897079a95b0bf11b63b6ed63` |
| 修正消费者 SHA-256 | `5d697e55919c1e8a35053fbfb662605839ddba9319266b3ed97bc9a497c20e18` |
| 实际 run／job／attempt | `38289734671`／`114946653833`／`1` |
| 实际 artifact ID | `11767708658` |
| 实际 artifact 字节／SHA-256 | 543994；`4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8` |
| 原失败目录 | `../actual-d0366-consumed/` |
| 实际成功目录 | `../actual-d0366-consumed-attempt2/` |
| 原差异补丁 | `../consumer-corrections/ACTUAL_IMPORT_SCOPE_FIX.patch` |

补丁与这两版实际文件的完整 unified diff 相同。AST 对比显示，28 个函数／方法中只有 `Consumer.check_root_and_fixed_inputs` 和 `Consumer.merge_and_write` 的函数体变化；其他 26 个函数／方法，以及这两个函数体以外的全部代码和常量均未变。

旧 `self.require` 中只删除了一条“23 个接收模块都必须直接在根 import”的要求。新增四条要求分别核对：23 个模块在固定根源图中可达；本批四模块仍直接 import；缺失新对象快照的接收模块恰好为固定旧三模块；这些缺项不与本轮新打印类型的模块相交。六门判定、实际元数据失败处理、固定 SHA／tree、完整导出器预期范围与公理检查逻辑均保留。

## 三个历史模块为何应核对根可达性

独立读取 `d036` 固定源码并处理 Lean 注释／字符串后，根项目源图有 276 个模块；三个历史模块不是根直接 import，但有以下真实路径。下表中的 `Certificates.*` 均在 `ImbalancedChen` 下。

| 历史接收模块 | 固定源导入路径 |
| --- | --- |
| `PairedCertificateChecker` | 根 → `PairedV2` → `PairedV2Data` → `PairedCertificateChecker` |
| `PairedFibreIntegral` | 根 → `PairedV2` → `PairedV2Data` → `PairedCertificateChecker` → `PairedFibreIntegral` |
| `RationalLogCertificate` | 根 → `PairedV2` → `PairedV2Data` → `PairedCertificateChecker` → `RationalLogCertificate` |

原始 `leanchecker.log` 确实有这三个模块各自的 `replaying ...` 标记，并有全部 23 个接收模块的标记。补充直接读取原日志得到 276 个唯一项目模块重放标记。根成员关系因此应按传递导入理解，不能因为根没有直接列出历史基础模块就判定实际 CI 无效。

原失败发生在消费者检查 `PairedCertificateChecker` 根直接导入时：172 项已过、1 项失败、消费者 exit 1。它是 `EvidenceFailure`，不是 Lean 报错；原目录中真实 Lean 诊断数为 0。修正没有删除或覆盖这个失败记录。

## 新对象字段留空准确，旧生产者证明保留

固定导出器从根、最终入口和本轮指定模块作为种子，只增加这些种子的直接项目 import。它不是递归采集所有导入对象的程序。实际两轮各采集 267 个生产模块对象集合；三个历史接收模块不在这个范围内。

| 模块 | 当前运行对象摘要 | 保留的原生产者对象 SHA-256 | 保留的完整旧类型数 |
| --- | --- | --- | ---: |
| `PairedCertificateChecker` | `null` | `46d84fd7f1625e3f55b20048ea52ae5835720b22f0b50ceee255b8175563f78c` | 58 |
| `PairedFibreIntegral` | `null` | `d974979205e82a178755d8b2bdde4c3aca7da742dde60a563bb80ef6314aa3ba` | 13 |
| `RationalLogCertificate` | `null` | `4797bc0a53a1062592f29d0176efc6a9fb4c819ddf727ffbd43fe77504eaac3b` | 47 |

这三个模块的原 `source`、`compiled_object_sha256`、严格编译／原装内核重放／所属声明公理审计的 `validation` 字段与固定接收台账相同；118 个旧类型的实际类型文本和旧来源也没有被改写。新增的当前运行字段明确为 `NOT_IN_FIXED_EXPORTER_SNAPSHOT_SCOPE` 和 `null`，并保留真实本轮 root replay 标记。

这既没有把旧生产者对象 hash 当成本轮对象 hash，也没有虚构内核重放时刻的 hash。原有 stock root replay 日志本身只提供模块标记。**三个源也不在导出器的 274 项运行时 source snapshot 中；它们的 `current_integration_source_sha256` 来自固定 `d036` Git 源与旧供应者源的一致性核对，不能称为新运行时 before/after 源采样。**

在全部 276 个项目可达模块中，另有 6 个 VariableEnvelope 模块同样不在本导出器的 267 对象采集范围；因此全部未采集项目模块是 9 个。旧三模块只是其中属于 23 个接收组件的子集。不能把 267 个摘要描述成整个项目传递闭包或所有外部依赖的 hash 清单。

## 六门、新增四模块、实际完整类型和公理

以下结果直接从同一原始 ZIP 的 timing/outcome/log 和对应实际 job steps 交叉核对：

| 门 | 实际秒数 | exit／outcome |
| --- | ---: | --- |
| 完整项目 build | 2640 | 0／success |
| 四个显式新增 target | 4 | 0／success |
| 原装 root leanchecker | 457 | 0／success |
| 根传递公理审计 | 29 | 0／success |
| Round3 完整类型导出 | 186 | 0／success |
| Round4 完整类型导出 | 187 | 0／success |

四个新增目标在固定 `.github/workflows/lean.yml` 中的实际命令明确为 `StoredHistoricalBoxPermit`、`PairedV2Batch4To64Data`、`PairedV2Batch4To64`、`PairedV2Prefix64`；四者在根中均直接 import。显式 target step 在完整 build 后复用已完成的对象，未强制重复编译，这是固定 workflow 原有行为。

实际 Round3 的 198 个、Round4 的 414 个完整类型，与各自原始 stdout 的 `P0_ROUND*_DECL` JSON 逐条相同；模块清点、唯一声明数、类型无省略标记、公理 allowlist 和 receipt 中的载荷 hash 一致。固定 Audit 源仍启用 `pp.all`，按 defining module 清点并拒绝 `isUnsafe`、新 axiom 和禁止的传递 axiom。

实际根审计记录 **5872 个声明**，allowlist 恰好为 `propext`、`Classical.choice`、`Quot.sound`。393 个继承旧记录保留原实际类型及 provenance；612 个本轮新打印类型保留原始编译器记录。合并清点为 **1005 个唯一类型：1000 个完整 pp.all、5 个旧 Buchstab 的默认完整 Meta.ppExpr**。最终条件式桥另列，没有混入 1005。

## 输入快照的范围说明已单独澄清

每轮完整 `inputs_before` 与本轮 `inputs_after` 相等；两轮的 267 个 `production_olean_parts` map 也相等。两轮各有 274 个 source 条目，其中 272 个共同条目的 hash 相同；Round3 独有其 Audit 与 exporter 脚本两个路径，Round4 独有对应的两个路径，因而两轮整个 source map 不相等。

原 `equality_checked_within_and_between_exports=true` 字段需要按这个范围阅读。P0 root 已另存 `../SNAPSHOT_SCOPE_CLARIFICATION.json` 作精确解释，SHA-256：

```text
f58cfdaa5224d8e2ef5123a5d7ff63ed0c2b92eb812e8263a572bb4874bdf9a7
```

它与实际 source map 差集、对象 map 和重放模块名单相符，并且保留了原成功目录与消费者字节。最终规范报告应引用这份解释，明确“20／23 个接收模块有本轮对象快照”，不将一般说明扩写成全依赖 hash 已核验。

**最终桥仍明确含 hLower 和 hUpper，K、c 的真实解析供应仍未闭合。** 消费者的 PASS 表示这次集成的规定门和证据接收通过，没有把这些数学输入判定为已证。

## 本复核文件

- `REVIEW_RECEIPT.json`：独立机器结论、实际原件身份、门结果与范围限制。
- `REVIEW_CHECKS.json`：69 项本复核核对；不属于重跑消费者或 Lean。
- `AST_SCOPE.json`：唯一删除的要求、四条新增要求、26 个未变函数／方法。
- `ROOT_REACHABILITY_AND_NULL_SCOPE.json`：全部接收组件路径、三个 null 的旧绑定、9 个未采集项目模块和 source 差集。
- `SUPPLEMENTAL_SCOPE_READBACK.json`：276 个实际唯一项目重放标记以及单独范围澄清文件的读取身份。

全部新文件只写在 `consumer-scope-review/`；未改变已封存父链、原失败、原成功、补丁或两版消费者。
