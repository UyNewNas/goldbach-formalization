# 既有 normal 成功模块的补充审核计划

## 交付结论

本包仅准备审核输入与原驱动的参数化版，没有启动 Lean、Lake、leanchecker 或云任务。
计划源码基线为 `8813fd28ee920da2f31f48e8253b73ecc27eec9a`。

- lane 0：batch1 额外 8 个 + batch2 16 个，共 24 个；其中 SwitchedOscillation 与它依赖的 SixteenOscillation 在同一 lane。
- lane 1：44 个 CompleteSeedBlock、44 个 SeedArchiveCheck、SeedArchiveChecks、CompleteSeedData，共 90 个。
- 24 个项目闭包 477 项，Seed90 闭包 92 项，总计 568 项；两个 lane 只共享 `ImbalancedChen.P2Winner9CompleteSeedTypes`。所有活动均读取既有产物。
- 两组目标与全部项目依赖，均与各自原 normal 的 Git 源码快照逐字节一致。878 接线包替换的两个旧模块以及 8813fd28 新修补的五个模块，均不在这些闭包中。
- 此前完整审核的 13 个目标明确排除；当前计划不能记为已通过，也不表示 P1 完成或全 11026 行 selected_checked 完成。

## 文件与原始日志绑定

`AUDIT_PLAN.json` 包含每个目标的原源码 SHA、原源码 Git blob、原 normal 日志、完整项目闭包和全部 568 个依赖源码 SHA。
`SOURCE_AND_NORMAL_INDEX.json` 是便于只读查阅的逐模块索引。
`RECEIPT_REUSE_INDEX.json` 保留 13 个既有完整审核目标及两个实际收据 SHA，并记录旧证据搜索范围和不能复用的理由。

| 原 cloud normal 日志（相对于 /workspace/p1-complete-proof/20261124-resume） | SHA-256 | 原源码快照 |
|---|---|---|
| batch1-normal/normal.log | `0ec7114556bc15852f80ad789482e831ddb5ef6c144385545e01ca39688014f5` | `d726bbee66b53d2ae5bf8fc21cbb144d6d8ea3cb` |
| batch2-parallel-normal/lane-0/normal.log | `ce48b44f8333bb4ae84af8c084b484c8a594cf44f736534574c9c737089e9f4d` | `103823711909b89ac9143f73352647e7a1061dc8` |
| batch2-parallel-normal/lane-1/normal.log | `5c973992b523544cdcfa00e57374405a3fd591fd5fa3ce4f1bbadb9a579efe48` | `103823711909b89ac9143f73352647e7a1061dc8` |

Built 必须从这些完整原始日志读取；`✔`、`⚠`、`ℹ` 均表示成功。原 COMMAND.json 的 built_modules 曾漏掉带警告的成功模块，驱动不使用该不完整列表。整个批次退出 1 不否定其中明确 Built 的目标。

## 旧收据去重

读取了当前 Git 树 `docs/verification/20261123-blue-compilation` 下 106 份 VALIDATION_RESULTS / 原 103 失败集 completion 收据，覆盖父任务指定的 member-repair-batch 系列。24 个目标没有对应完整收据命中。Seed90 命中旧 Block00..42 的 43 个完整收据，但旧源码 SHA 全部不同，因此不能冲销当前版本的审核。没有将 metadata-only 的 263 项清单当作证明信用。

另对当前 P2 的九份 VERIFICATION_RESULTS / SUMMARY / KERNEL_REPLAY / FINAL_TRIAL / EXPORT_SUMMARY 类收据作定向检索。SelectedRowRealJacobian 还找到 73d7e839 同源的旧 named kernel 与 23 个公开定理审计；这不是完整环境所属声明审计，且没有绑定当前全部依赖/六文件的收据。P2 后来的 62 owned 收据对应 16ee27bd 版本，不能冒充当前 73d7e839 的完整收据。当前 114 项中可直接完整复用数为 0；这不否定以上部分历史证据。

不能把“325 + 114”直接当作新增独立模块数：Seed 的 43 个条目是已有模块的新源码版本。本包不更新任何全局完成计数。

## 驱动保持与新增参数

`run_parallel_acceptance_multibatch.py` 沿用现有 `parallel-resume/run_parallel_acceptance.py` 的源码加五产物快照、named leanchecker、完整环境所属声明类型/公理审计和前后 `lake --no-build`。沿用 `accepted-batch102-two/PublicAudit.lean` 的完整正文，仅替换 import 和目标 modules 数组，并核对模板 SHA。模板仍包含 private/generated 声明、禁止 unsafe/axiom 声明、只允许标准公理、检查打印不省略。

新增部分只处理计划输入：多批日志的 SHA 与完整 Built 集合、每个目标源 SHA、项目依赖源码 SHA、计划与模板 SHA。它不调用任何 normal build。回执目录必须不存在；已有审核回执不会被覆盖。

默认直接运行会在两个原 serializer lane 内并行审核。为满足 lane 0 先执行五项修补的现有排程，可先仅准备输入，再在已持有相应 serializer 的两个 worker 中分别运行：

```bash
python3 /path/to/run_parallel_acceptance_multibatch.py --plan /path/to/AUDIT_PLAN.json --prepare-only
python3 /path/to/run_parallel_acceptance_multibatch.py --plan /workspace/p1-complete-proof/20261124-resume/batch1-batch2-normal-supplement-acceptance/AUDIT_PLAN.json --lane 0
python3 /path/to/run_parallel_acceptance_multibatch.py --plan /workspace/p1-complete-proof/20261124-resume/batch1-batch2-normal-supplement-acceptance/AUDIT_PLAN.json --lane 1
```

后两条是各自 worker 的命令，不能在未采用现有 serializer 的外部并发启动。lane 0 命令放在那五项修补步骤之后；lane 1 可直接审核 Seed90。若外层 worker 编排两个 `--lane`，它负责汇总退出状态；每个 lane 仍独立写 VALIDATION_RESULTS.json。无参数分 lane 的默认运行方式会写 PARALLEL_RESULT.json。

通过 `--receipt-root` 可以选择另一个全新回执目录，之后两 lane 必须指定同一路径。无须修改计划的源与日志绑定。

## 本地准备核对

已检查 Python 语法；对下载的 batch1 原始 normal.log 解析得到完整 21 个 Built，包含先前漏掉的 8 个警告成功；三种成功符号的解析均通过。已本地执行一次 `--prepare-only`，生成 24 / 90 两份 lane 输入，与计划完全一致。没有执行任何编译或审核。

8813fd28 的五项源码是 WeightedSourceReduction、VariableFourthEligibilityPartition、InitialSeedInventory、SixteenArithmeticProducts、SixteenWalls；与当前两个审核闭包交集为空。

## batch1_extra8


| 模块（ImbalancedChen. 前缀省略） | 原 normal 源码 SHA-256 |
|---|---|
| P4BSmoothPrimeEulerFlowBudget | `69435be4c298bb652d4474df098f66ed425070a4cd3e593cdd52177fbad057cf` |
| P2Winner9SelectedRowRealJacobian | `73d7e8390ecfa3cd614086bd636639df9104374d6d0fef14289068156e56f3d2` |
| P2EnhancedLowerPhysicalNode | `684c094498f4c8cb7d806f75e65c41fad03358bbe7ace3ff3bc8e820fcd3c9c1` |
| P5ZU1011OriginalSixteenOscillation | `ecb53528dcf832c7b7f1dcd11855195e562d8dcf8dcee4e004e766c5a5fa1bb0` |
| P1OriginalFourthIntegerGapSemantics | `b50df1ca66ad5a6633445f4bf765bca8367c60086eb42b55d01ebecd300e51aa` |
| ActualThirdOriginalPositive256LogRange32IntegerGuard | `c7f15768cc27d4753ae7773aeeac143b7e920d0f89c2f3f53c5a393ebcdc7b6c` |
| ActualThirdOriginalSymmetricMassCeil | `bd566cf1fd948e92a5a18eb6b9c6c9127081ff898fe53ca54c07a1c370fb40c5` |
| P1OriginalThirdGammaValueStability | `3d19f70667d777c8babf460f1690f286212ce987088db7f8baffcf0a68f27e38` |

## batch2_extra16


| 模块（ImbalancedChen. 前缀省略） | 原 normal 源码 SHA-256 |
|---|---|
| ActualThirdOriginalLiteralTentSelectorGuardBridge | `99a43763f875bfb731b99f11dc274fac92c8727b41041a61f3699093719dd10e` |
| ActualUpperPolicyDensity | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` |
| P1AffineCertifiedMesh | `2b1741aa7db395b49f2e8293a9a1472147c65d81cd3eacaf9f491c06ac79ffcb` |
| Certificates.P2HistoricJTableInterpreter | `d81f8e29f54c6f7ff0cb44b43b951a77ac4049aba86aefa88e83f79ae1fcbc75` |
| P1OriginalFourthUniformSmallRemainder | `616d55caaa6c7b51a283e121e604a766ac55b4a559d1d96ebc87d752844516fc` |
| P1OriginalThirdGammaMeshSectionBridge | `31eea8f6d764328293632928f486e43d2ea404ee53a877328910d2ea3b8ee896` |
| P2HistoricSieveTableSemantics | `f4e52f0cddd969afc05d0ee40eb681d05a303da5f41160bd931190d7fb905d87` |
| P2Winner9LedgerCore | `6e7d69c2f429fc4d174d608255be3726718ecae945878cdfc38f15482549ab82` |
| P2OriginalFourteenUniformResidual | `9cdf0add386e409b987e87472cda654e9caf6bc954f0e1b925bd565cb3418b33` |
| P4AClosedCutTreePositionalChargeBinding | `240b6dc74cdb6a61f7fad021d73bb8ee0b302e27022b16cf81cfdac38ebf7567` |
| P4AOriginalNewFifthArchiveReader | `59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6` |
| P4AOriginalSecondPhysicalIntegral | `3cf502f95a982da6c5134e349a73424f1e85ff167ead156effde9f6890f6636a` |
| P4AUpperTaggedBetaAttachment | `f941f530391d7c00948ba56b67c59024f1325db1489de1871c99da4a5392baee` |
| P5OriginalH3Cell00StrictOldPlanes | `c2e95d705df8f45c54719854a85199172854de6a79da22a32d264107b7c53451` |
| P5ZU1011OriginalSwitchedOscillation | `7c4cad4198bc258a94716fa9ee959018be1dc862f885a7b4db2212608bcb1c00` |
| Part3ActualWGapInitialization | `3f95d17e97eb59c612e60accf5f858a4b72ae0c803fe6e23ec868f746ccfa2f7` |

## 校验值

- `AUDIT_PLAN.json`: `b0cc5077081c2048001cf48bdf5e792f81be377060bcebbbddb05fc7648e3934`
- `run_parallel_acceptance_multibatch.py`: `e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1`
- `RECEIPT_REUSE_INDEX.json`: `c1c85addb4f6cb9353eb55d1fc1cb8082fdbbb57427ff6dd7f25243506782d41`
- `SOURCE_AND_NORMAL_INDEX.json`: `2b958081b9b8b03c51e80210ef2c5aeb85366e186bf1bca100c745ba9b93f81b`
- `PREPARATION_VERIFICATION.json`: `44e8660e4aa37e2a857d4fa4cc08eae0dc042adac1adcf27896b3a0626cdf7a7`
