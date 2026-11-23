首批十个依赖模块检查了 254 条显式公开源码声明，包括五个 U7 模块的 69 条、连续筛模块的 15 条和四个 Member 支撑模块的 170 条。后续完整入口与新增支撑模块按批次另行记录。U7 源码对应 1106 版手稿的第七积分原三角域，边界为 `59/250 ≤ t ≤ 1/3`、`t ≤ u ≤ (1-t)/2`，分段接缝为 `u=(1-t)/3`。手稿固定到 `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en`。

原构建在行积分的连续性组合处达到 4,000,000 heartbeat 上限，两处积分字典改写还保留了函数应用形式。修补显式给出配对映射、映射到正象限的证明与 `ContinuousOn.comp'` 的函数参数，并在分支改写前用 `change` 展开定义相等的条件表达式。复用了原来的全部定义、数字常数与 30 个公开声明。源码的状态注释指向本目录。

| 检查 | 实际结果 |
| --- | --- |
| 标准 Lake 模块编译 | 退出码 0 |
| 指定模块的独立 kernel replay | 退出码 0 |
| 30 个公开声明的完整类型与传递公理 | 退出码 0 |
| 公理集合 | `propext`、`Classical.choice`、`Quot.sound` |
| 独立源码复核 | 两处证明修补无问题记录 |

使用 Lean `4.33.0-rc1`、Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 与 goldbach `09b97db5764ade1246bfb77206baa1b124760958`。源编译保留 `-t0 -j2 -M12288`、`maxRecDepth=100000` 和 `maxHeartbeats=4000000`。复核覆盖指定模块及其现有导入环境。

本次验证工程为 `/workspace/blue-p6-build`，基础依赖选自已登记的 `R02_SOURCE_SELECTION.json`。Omega 模块使用本目录登记的生产源码后像。以下命令通过仓库现有 T01 `ci_runtime_guard.py` 创建的工具链包装执行。

```sh
lake build ImbalancedChen.P5U7OriginalOmegaIntegral:olean
lake env leanchecker -v ImbalancedChen.P5U7OriginalOmegaIntegral
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/OmegaAudit.lean
```

源码选版、实际编译器命令、五项产物摘要、检查退出码与日志摘要见 [OMEGA_RESULTS.json](OMEGA_RESULTS.json) 和 [OMEGA_SOURCE_SELECTION.json](OMEGA_SOURCE_SELECTION.json)。检查驱动见 [OmegaAudit.lean](OmegaAudit.lean)。

另外两个支撑模块各修补一处证明中的 API 用法。Buchstab 的有限差分证明使用当前 Mathlib 的 `abs_add_le`。Fubini 证明先用 `dsimp only [B]` 展开局部矩形集合，再改写乘积测度。两处修补保留原声明、定义、常量与假设。源码状态注释已更新。

以下命令在同一工程与 guard 下实际执行成功。两个模块均通过独立 kernel replay，27 个公开声明的完整类型与传递公理检查也通过，观察到的公理仍只有 `propext`、`Classical.choice` 和 `Quot.sound`。独立源码复核无问题记录。

```sh
lake build ImbalancedChen.P5U7OriginalBuchstabLipschitz:olean ImbalancedChen.P5U7OriginalOmegaFubini:olean
lake env leanchecker -v ImbalancedChen.P5U7OriginalBuchstabLipschitz
lake env leanchecker -v ImbalancedChen.P5U7OriginalOmegaFubini
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/OmegaSupportAudit.lean
```

这两个模块的结果与产物摘要见 [SUPPORT_RESULTS.json](SUPPORT_RESULTS.json)，选版见 [LIPSCHITZ_SOURCE_SELECTION.json](LIPSCHITZ_SOURCE_SELECTION.json) 和 [FUBINI_SOURCE_SELECTION.json](FUBINI_SOURCE_SELECTION.json)，检查驱动见 [OmegaSupportAudit.lean](OmegaSupportAudit.lean)。上述记录按实际执行的模块与命令分别保存。

连续筛模块 `P2ContinuousSieveRational` 的三个证明补充了振幅 `A` 的定义展开、乘法与除法的结合归一化，以及 `sub_div` 归一化。15 个公开声明及三个定义保持原样。它是首带有理包围与保守尾界的支撑模块；其余表格递推和最终数值积分的验收另行记录。本轮未发现实质数学缺口。

该模块在同一 P6 工程和 guard 下完成以下三项检查，退出码均为 0。类型与公理检查的标准输入逐字保存在 [P2ContinuousSieveAudit.lean](P2ContinuousSieveAudit.lean)，公理名称的宇宙参数只在汇总时归一化，原始输出完整保留。

```sh
lake build +ImbalancedChen.P2ContinuousSieveRational:olean
lake env leanchecker --verbose ImbalancedChen.P2ContinuousSieveRational
lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 --stdin < /workspace/goldbach-formalization/docs/verification/20261123-blue-compilation/P2ContinuousSieveAudit.lean
```

结果、15 个完整类型与传递公理、五项产物及实际编译器命令见 [P2_CONTINUOUS_SIEVE_RESULTS.json](P2_CONTINUOUS_SIEVE_RESULTS.json)，选版见 [P2_CONTINUOUS_SIEVE_SOURCE_SELECTION.json](P2_CONTINUOUS_SIEVE_SOURCE_SELECTION.json)。源码及五项产物在 kernel replay 和声明检查前后保持一致，公理集合仍限于上述三项。原失败与成功日志均保存在本目录。

U7 的 `P5U7OriginalKernelOscillation` 与 `P5U7OriginalRationalCellBounds` 分别检查 2 个和 10 个公开声明。前者适配固定 Mathlib 的绝对值三角不等式与同加项 API，后者显式搬运 `Rat.cast_le` 并归一化 `132/59` 的转换；原闭三角、接缝、常量及所有声明保持不变。标准构建、一次枚举两模块的独立 kernel replay、12 个完整类型与传递公理检查均退出 0，源码和十项产物前后稳定。结果见 [U7_CELL_OSCILLATION_RESULTS.json](U7_CELL_OSCILLATION_RESULTS.json)，选版见 [振荡界](U7_KERNEL_OSCILLATION_SOURCE_SELECTION.json) 和 [有理网格界](U7_RATIONAL_CELL_SOURCE_SELECTION.json)，驱动见 [U7CellOscillationAudit.lean](U7CellOscillationAudit.lean)。

Member 工程使用同一组 Lean、Mathlib、goldbach 固定版本，基础项目选源来自 `R03_SOURCE_SELECTION.json`，并使用其独立的现有 `-t0 -j2 -M12288` guard。以下两条标准构建命令均退出 0，三个模块也分别通过独立 kernel replay。

```sh
lake build ImbalancedChen.CurrentChenUpsilon1011JointSource:olean ImbalancedChen.CurrentP5MarkedElevenWitnessSource:olean
lake build ImbalancedChen.P5OriginalActionMassBound:olean
```

`CurrentChenUpsilon1011JointSource` 完整复用既有提交 `86d2a123d08befe29c69454637fa9aa1d2614441` 中的源码，补全有限和筛选表达的归一化。`CurrentP5MarkedElevenWitnessSource` 在 `subst` 前将投影等式定义展开为 `j = i`，并更新状态注释。两模块的 34 个公开声明均通过完整类型与传递公理检查；结果与原始日志见 [member-current/RESULTS.json](member-current/RESULTS.json)，选版见 [member-current/SOURCE_SELECTION.json](member-current/SOURCE_SELECTION.json)，驱动见 [CurrentSourceAudit.lean](member-current/CurrentSourceAudit.lean)。

`P5OriginalActionMassBound` 的七处证明修补使用 `setIntegral_const`、显式 `Fin 2` 坐标序链和集合参数，保持 109 个公开声明及全部定义、常量、假设不变。109 个完整类型与传递公理检查通过；结果见 [ACTION_MASS_RESULTS.json](ACTION_MASS_RESULTS.json)，选版见 [ACTION_MASS_SOURCE_SELECTION.json](ACTION_MASS_SOURCE_SELECTION.json)，驱动见 [ActionMassAudit.lean](ActionMassAudit.lean)。原阶段记录证明源码及四项输出 `.olean`、`.ilean`、`.c`、setup 在检查前后稳定；`.trace` 另记为全部检查后的独立当前快照，没有跨阶段比较。结果解析器只修正了标准公理名称的宇宙参数归一化，没有重跑成功的 Lean 命令。

上述三个 Member 模块的公理集合也仅包含 `propext`、`Classical.choice` 和 `Quot.sound`。原始日志保留 Lean 的输出空白格式。各入口的最终验收与单个依赖模块的检查分别记录。

Member 的 `Part5OriginalUpsilon5CausalDictionary` 另检查 27 个公开声明。其积分被积函数等式复用既有提交 `085ef205771858c7115d092766b3ffcf7ab86d55` 的 `congrArg` 证明，避免 lambda 应用下的改写匹配失败。27 个声明、11 个定义及全部常量和假设保持不变。标准构建、独立 kernel replay 和全部声明的完整类型/传递公理检查均退出 0，源码与五项产物跨阶段稳定，公理仍仅上述三项。结果与原始日志见 [causal-dictionary/VALIDATION_RESULTS.json](causal-dictionary/VALIDATION_RESULTS.json)，选源与手稿对应关系见 [REPAIR_RECEIPT.json](causal-dictionary/REPAIR_RECEIPT.json)。四个 Member 支撑模块的基础选源与生产源码覆盖见 [MEMBER_SOURCE_OVERRIDES.json](MEMBER_SOURCE_OVERRIDES.json)。

本轮生成 C 辅助文件的缓存复用修正另存于 [cache-reuse](cache-reuse/README.md)，包含遗漏原因、实际恢复范围、原始身份和标准 Lake 前后检查。

`P2EnhancedPrefixMaskDefect` 随后用显式 `_root_.not_imp` 解决命名歧义，保留原声明、定义和假设。标准模块构建、独立 kernel replay 与 12 条显式公开声明的完整类型/传递公理检查均退出 0；源码和五项产物跨阶段稳定，公理仍只有标准三项。结果与原始日志见 [prefix-mask/VALIDATION_RESULTS.json](prefix-mask/VALIDATION_RESULTS.json)。

Member 工程还复用基线已验证的 `P4BSmoothGateUpperStep` 生产源码，覆盖 R03 中的旧 API 版本。原验证记录位于 `docs/verification/20261123-local-pilot`，本轮保留其精确源码，不重复其已有证明验收、不计新增蓝色节点。来源与 staging 覆盖见 [EXISTING_REUSE_RECEIPT.json](existing-green-suppliers/EXISTING_REUSE_RECEIPT.json) 及 [MEMBER_SOURCE_OVERRIDES.json](MEMBER_SOURCE_OVERRIDES.json)。物理对象的当前资格单独核对。

原第七积分价格入口 `P6OriginalSeventhMeshPrice` 已通过完整标准构建。其 R02 入口源码保持原始 SHA，使用 112 个项目源码、411 个 native 源码及 15 项已登记证明修补。入口与本批九个新增支撑模块均通过指定模块 kernel replay；按 Lean 的定义模块元数据枚举的 223 条声明全部完成完整类型和传递公理检查，包括 private、结构字段及自动生成声明，公理仅标准三项。十个源码与五十项主要产物在检查前后稳定。

入口绑定见 [SEVENTH_ROOT_ACCEPTANCE.json](SEVENTH_ROOT_ACCEPTANCE.json)，完整批次见 [p6-seventh/BATCH_SUMMARY.json](p6-seventh/BATCH_SUMMARY.json)，实际命令、类型、公理、构建尝试及精确选源均保存在该子目录。本批九处源码修补由独立复核确认保持原声明、定义、常量和假设，见 [INDEPENDENT_REVIEW.json](p6-seventh/INDEPENDENT_REVIEW.json)。该入口在隔离的精确选源工程验证，原始入口文件及全部证明修补均可按记录定位。

原第八积分价格入口 `P6OriginalEighthMeshPrice` 也已通过完整标准构建。四个支撑模块和入口共五个模块通过指定模块 kernel replay，按定义模块元数据枚举的 172 条完整声明均通过类型和传递公理检查，公理仍为标准三项。五个源码与二十五项主要产物跨阶段稳定。原 `417/5000` 至 `1/3` 的积分域和 `log(2-3t)/(t*(1-t))` 对象保持不变。

本批适配了集合可测性 API、有理数转换、函数应用展开和已有分母非负证明。入口本身只增加一行 `dsimp only`；冻结 R02 原图保持不变，单独的入口后像按记录安装到隔离工程，主仓没有新增同名 canonical 入口。源码覆盖及安装路径见 [EIGHTH_ROOT_ACCEPTANCE.json](EIGHTH_ROOT_ACCEPTANCE.json) 和 [VERIFIED_P6_SOURCE_OVERRIDES.json](VERIFIED_P6_SOURCE_OVERRIDES.json)。完整结果见 [p6-eighth/BATCH_SUMMARY.json](p6-eighth/BATCH_SUMMARY.json)，独立源码复核见 [INDEPENDENT_REVIEW.json](p6-eighth/INDEPENDENT_REVIEW.json)。跨工程 native 现成产物的资格与复用摘要也保存在该批次目录；复用数量不计新增定理或看板节点。

Member 的 `P2HistoricLogRangeReduction` 复用既有提交 `085ef205771858c7115d092766b3ffcf7ab86d55` 的六处证明修补，显式处理整数/有理数转换、floor/ceil 与 `2^80` 位长为 81 的 kernel 计算。30 条显式公开源码声明、八个定义和全部常量、假设保持不变。标准构建、指定模块 kernel replay 及实际 `Certificates` 命名空间下的完整类型/传递公理检查均退出 0，仅标准三公理；源码和五项产物跨阶段稳定。结果见 [historic-log-range/VALIDATION_RESULTS.json](historic-log-range/VALIDATION_RESULTS.json)，源码复核见 [INDEPENDENT_REVIEW.json](historic-log-range/INDEPENDENT_REVIEW.json)。

原第九积分价格入口 `P6OriginalNinthMeshPrice` 已通过完整标准构建，R02 入口源码逐字保持。十四个支撑源码后像与入口共十五模块通过指定模块 kernel replay，全部 301 条定义模块声明（含 private 和生成声明）完成完整类型和传递公理检查，仅标准三公理，源码和七十五项主要产物跨阶段稳定。独立复核覆盖十四个源码后像、200 条显式源码声明及手稿对应关系，未发现后像问题，见 [NINTH_ROOT_ACCEPTANCE.json](NINTH_ROOT_ACCEPTANCE.json)、[批次结果](p6-ninth/BATCH_SUMMARY.json) 和 [源码复核](p6-ninth/INDEPENDENT_REVIEW.json)。

第九批有两项明确例外。`CurrentP5CausalCellEventualAssembly` 六处声明头将 `Finset.univ` 显式转换为原意的完整有限指标集合；旧语法不能 elaboration，因此不声称旧、新源码已生成相同 kernel 类型。`CurrentChenP5U9UniformTaylorTail` 原内部等式的算术值应为 `336/125`，原公开结论使用较宽的 `672/125` 预算；修补仅将内部错误等式改为不等式并使用原尾项非负，公开预算、假设、定义保持不变。这是可补齐的内部算术与余量推导，详见 [TAYLOR_INTERNAL_SLACK_REVIEW.json](p6-ninth/TAYLOR_INTERNAL_SLACK_REVIEW.json)。两次检查脚本自身失败的记录保留，最终检查采用缓存模块名、完整环境常量枚举和实际定义模块归属，不声称失败的 ModuleData 索引检查通过。

原零标记积分成本入口 `P6OriginalZeroMarkedIntegralCost` 与 `P6OriginalMarkedIntegralPrices` 无需源码修补，均与冻结 R02 选源完全一致。标准构建、两个指定模块 kernel replay 和全部 42 条定义模块声明的完整类型／传递公理检查通过，仅标准三公理，源码及十项主要产物跨阶段稳定，见 [ZERO_ROOT_ACCEPTANCE.json](ZERO_ROOT_ACCEPTANCE.json) 和 [批次结果](p6-zero/BATCH_SUMMARY.json)。

上述四个 P6 入口最后通过同一次 `lake --no-build build` 检查，退出 0，新增源码编译调用为 0。208 个项目源码和 810 个 native 源码的最终选版与产物绑定见 [FOUR_ROOT_ACCEPTANCE.json](p6-four-roots/FOUR_ROOT_ACCEPTANCE.json)。全部项目均有 `.olean`、`.ilean`、生成 C 和 trace；复用的 `ChenLogLevelGeometry` 未安装原生产者的辅助 setup 文件，其标准 Lake 重放及四入口最终检查均已通过，辅助文件例外单列记录。34 项生产源码覆盖见 [VERIFIED_P6_SOURCE_OVERRIDES.json](VERIFIED_P6_SOURCE_OVERRIDES.json)，冻结文件保持原样，阶段专有入口按安装路径恢复。

Member 的 `P2SavedFloorSemantics` 从已有正性假设显式推出相同分母为正；`P2GuardedReciprocalRounding` 删除已闭合目标后的多余 tactic，并补充 `one_mul` 归一化。两个标准模块构建、两次指定模块 kernel replay 和实际定义模块归属下的全部 94 个公开导出（45、49，包含生成导出）均通过，仅标准三公理，源码及十项主要产物跨阶段稳定。原 60 条显式公开源码接口、定义、常量和假设保持不变，见 [VALIDATION_RESULTS.json](member-api-pair/VALIDATION_RESULTS.json) 与 [独立源码复核](member-api-pair/INDEPENDENT_REVIEW.json)。

`P2DirectedLogRounding` 主源码同时对齐 R03 已选用的既有 `86d2a123` 后像，仅两处乘法消去 API 名称变化；Member 选源未改变，未重复已有验证、不计新增证明或节点。精确来源见 [DIRECTED_LOG_EXISTING_SOURCE_REUSE.json](existing-green-suppliers/DIRECTED_LOG_EXISTING_SOURCE_REUSE.json)。

Member 的两个 native 模块原来调用未选入的 `roughCount_uniform_buchstab_fixed`。旧供应器只覆盖上界 100，调用者需要任意预先固定的 `M`；本轮从上游已发表 `9d4c3a40` 的 Abel、Bands、Uniform 源码复用最小依赖的 18 个声明块（11 public、7 private，其中已含六个旧 private helper），组成单独扩展。全部声明头与证明正文逐字节一致，两个调用模块仅增加 import，原 4333／4282 字节完整保留。旧供应器、四项外部供应者、native 基线 `09b97db5` 和其它 pins 保持不变。

扩展及 `Omega3XBuchstabUniform`、`NonunitRoughUniform` 的标准构建、指定三模块 kernel replay、全部 51 条定义模块声明的完整类型／传递公理检查均通过，仅标准三公理；三个源码和十五项主要产物稳定。最后标准 Lake stock 退出 0，源码编译调用为 0。可移植源码安装表见 [SOURCE_INSTALL.json](member-native-generic-m/SOURCE_INSTALL.json)，本地验收见 [ACCEPTANCE_SUMMARY.json](member-native-generic-m/local/ACCEPTANCE_SUMMARY.json)，来源与原量词顺序见 [SOURCE_REUSE.md](member-native-generic-m/published-source-candidate/SOURCE_REUSE.md)。历史 4151 项验收仅作为来源记录，单项历史 receipt 的 payload 未公开，本轮验收使用实际重新编译与复核的当前产物。

`CurrentChenP5SelectedMaskTransport` 的五处有限和与 dependent tuple 证明完整复用 `86d2a123`，保留原选定 mask、标签重数、第二素数 cutoff 及正第六项 buffer。标准构建、kernel replay 和全部 48 个实际公开导出检查通过，原 32 条显式公开源码声明、定义、常量与假设保持，见 [验收结果](member-mask-transport/VALIDATION_RESULTS.json) 与 [独立复核](member-mask-transport/INDEPENDENT_REVIEW.json)。

Member 第三修补批覆盖 `P2HistoricQ80DefectLookup`、`P2TableActionSoundness`、`Part5OriginalUpsilon5CausalSplit` 和 `P5OriginalSignedMidpoint`：四个标准构建、四次指定模块 kernel replay、全部 259 个实际公开导出（186、33、33、7）的完整类型／公理检查通过，仅标准三公理，源码及二十项主要产物稳定。HistoricQ80 十处证明逐段复用已有 `ab19e4c4` 后像，原 200 项 bank 数据和混合换行字节保持；其它修补为 API、cast、函数展开，原 signed midpoint 的 `1/24` 保持。SignedMidpoint 主仓 canonical 文件仍不存在，后像及显式安装路径保存在本批目录。原声明头、定义、常量、假设均保留，见 [验收结果](member-repair-batch3/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch3/INDEPENDENT_REVIEW.json)。

`P5OrderedFactorTupleRectangleReindex` 的有限分支在独立的 70 项项目源码、456 项 native 源码选版中完成标准构建。19 个变更／新增模块通过指定模块 kernel replay；70 个项目模块的全部 1742 个公开导出完成类型／传递公理检查，仅标准三公理。后续用完整环境常量枚举与定义模块归属核对名称集，恰与既有 1742 项审计相等，无遗漏、额外名称或归属差异，没有重跑已成功的证明检查。精确选版、全部源码后像、较小验收记录与独立复核保存在 [reindex-isolated](reindex-isolated/README.md)。

该分支将既有同名同正文 `completeProduct` 搬至共享 leaf，并缩窄原目标的导入；目标自身六处证明替换块包含七项 API 适配效果。声明语法有两项单列例外：将 `Group` 的五个 scalar 字段加括号，以免解析为函数字段；用局部记号将原 bare `R` 指向既有 dyadic `R`。原目标声明与数学假设保持。安装必须使用 [SOURCE_INSTALL.json](reindex-isolated/SOURCE_INSTALL.json) 的隔离选版；旧宽依赖 parent 与其未编译的 reexport 提案均未整合到主源码，也不能与新 leaf 同装后声称宽闭包通过。这一有限分支验收不代表 `RetainedAnalyticReserves` 完整闭包完成。

Member 第六修补批的 `P2MarkedThetaLiNormalization` 与 `Part3ActualCompactInitialSupport` 通过两次标准构建、两次指定模块 kernel replay，以及全部 27 个公开导出的完整类型／公理检查，仅标准三公理。12 条原定理声明、定义、Theta 的统一阈值与零质量族条件、rank 4 的原 `5τ` 预算保持，源码和十项主要产物稳定，见 [验收结果](member-repair-batch6/VALIDATION_RESULTS.json) 与 [独立复核](member-repair-batch6/INDEPENDENT_REVIEW.json)。本批初始暂存器将 absolute 路径拼接为 Member 路径，实际未同步主仓；已验证的相同后像随后在核对主仓原 baseline 后同步，真实时点及旧 metadata 的失效范围保存在 [MAIN_SYNC_PATH_CORRECTION.json](member-repair-batch6/MAIN_SYNC_PATH_CORRECTION.json)，没有为此重跑已通过的验证。

Member 第二修补批覆盖 physical normalization、actual Buchstab transfer、U11 LastPair、marked tuple common refinement 和 collision floor 五个模块。五个标准构建、五次指定模块 kernel replay 和全部 140 个公开导出的完整类型／公理检查通过，仅标准三公理，源码及二十五项主要产物稳定，原声明头、定义、数字与假设保持。LastPair 首版真实失败的源码和 exit 1 日志完整归档，只有最终 `a6d9a86f` 后像通过；原有限 carrier、筛选、标签重数不变。见 [验收结果](member-repair-batch2/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch2/INDEPENDENT_REVIEW.json)。physical／actual 两模块的主仓 canonical 路径仍不存在，仅按明确安装路径发布已验后像。

第四批 `P2OriginalLowerAffineTieSelector` 的 `scan_ge_member` 用具名等式后 `subst`，避免 `rfl` 消去后引用已不存在的名字；18 个公开源码声明、定义、数字及假设保持。标准构建、指定模块 kernel replay 与全部 74 个公开导出的类型／公理检查通过，源码和五项主要产物稳定，仅标准三公理。该模块也保留为隔离安装后像，见 [验收结果](member-repair-batch4/VALIDATION_RESULTS.json)、[独立复核](member-repair-batch4/INDEPENDENT_REVIEW.json) 及统一 [源码覆盖表](MEMBER_SOURCE_OVERRIDES.json)。

Member 已完成缓存窗口的精简证据保存在 [member-cache-window](member-cache-window/README.md)：实际复用 T01 八组、Prototype 九组项目产物和一组 P6 native 产物；已存在的 18 组 T01、23 组 Prototype native 保持，64 组 T01 因实际依赖对象不同未采用。原聚合控制器在活动 Lean 自然退出后受控停止，exit 241 属于操作停点，停点前后 1242 项成功产物保持。Prototype 首次 stock 的 exit 3 后，只对两项工作 trace 采用真实生产者原始字节，并先补齐四个缺失 C／hash 辅助文件；旧 trace 已备份，没有修改 depHash 或生成伪 trace。最终对应 stock 均为 0，Member 源码编译调用为 0。该目录仅整理已完成回执、原始摘要与小脚本，未重跑构建或资格检查，不计新增定理或看板节点。

Member 第八批 `ActualFrozenSlotCoefficientRegrouping` 完整复用已发表 `c45e845b` 的 `8f609edc` 源码，保留原系数、阶乘恢复、ordered slot／product fibres 的标签重数和全部假设。标准构建、指定模块 kernel replay 及全部 19 个实际公开导出的完整类型／公理检查通过，仅标准三公理，源码和五项主要产物稳定，见 [验收结果](member-repair-batch8/VALIDATION_RESULTS.json) 及 [独立复核](member-repair-batch8/INDEPENDENT_REVIEW.json)。旧静态头表的两项 let-valued 结论仅记录了前缀；原表保持不动，新增 [完整 12 条源码声明头比较](member-repair-batch8/PUBLIC_HEADERS_COMPLETE.json) 与不可变发布补充清单。实际 elaborated 完整类型与 kernel 检查一直完整，未因元数据补正重跑验证。

Member 第七批 `P2EnhancedSortedDwellMerge` 通过标准构建、指定模块 kernel replay 与全部 14 个公开导出的完整类型／公理检查，仅标准三公理，源码和五项主要产物稳定。`cast_insertNth` 原声明无法推断 dependent family，现显式标注原常值自然数／实数 family；原 `q`、`v`、索引和 cast equality 意图保持，旧未 elaboration 的声明不声称已有相同 kernel 类型。其余修补为 β 展开、现有 `Fin.comp_cons` 和长度 API，原定义、标签、置换、Q／B 与常量保持。独立复核按顶层 `:=` 比较完整源码声明头，避免嵌套参数 `α :=` 截断，见 [验收结果](member-repair-batch7/VALIDATION_RESULTS.json) 与 [独立复核](member-repair-batch7/INDEPENDENT_REVIEW.json)。

Member 的 Renewal／Rational 两模块先将已不存在的 Mathlib imports 分别改为当前固定版本的 `Mathlib.Data.Fin.VecNotation` 和内置 `Lean.Elab.Tactic.Omega`，随后修补实际暴露的证明 API：有限和、序不等式方向、Fin 11 向量展开，以及原小 seed 的 kernel 决定过程与乘法消去名称。两个标准构建、两个指定模块 kernel replay 和全部 120 个实际公开导出（63、57）的完整类型／公理检查通过，仅标准三公理，源码及十项主要产物稳定。原完整声明头、定义、数值和假设保持；原 obsolete-import 失败、Renewal 四次失败和 Rational 一次失败的源码及日志均保留，没有把 import-only 中间版本记为通过。见 [验收结果](member-import-repair/VALIDATION_RESULTS.json) 和 [独立复核](member-import-repair/INDEPENDENT_REVIEW.json)。

Member 第十批 P4B 三模块全部通过标准构建、指定模块 kernel replay 与 71 个公开导出的完整类型／公理检查，仅标准三公理，源码及十五项主要产物稳定。`P4BSourceCutoffTransport` 复用增量远端 `6f4dd677` 的完整源码，`P4BLogGateOuterRamp` 复用已发表完整后像，均仅另加中性验证记录注释；`P4BLabelledPairDictionary` 两个证明逐字节复用 `48db`，保留当前 `Part3DistributionTargets` family、imports 和五个定义。Cutoff 原 header 中的 lambda binder 补充 `m : ℕ`，仍为原自然数 carrier 与实数 cutoff 比较；这是旧未 elaboration 声明的类型消歧例外，不声称旧 kernel 类型已存在。ordered bad、no2、相同 signed coefficient 与 outer approximation 的边界付款假设保持，见 [验收结果](member-repair-batch10/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch10/INDEPENDENT_REVIEW.json)。

Member 第九批 P1 三模块通过标准构建、指定模块 kernel replay 和全部 118 个公开导出的完整类型／公理检查，仅标准三公理，源码及十五项主要产物稳定。NearOne 与 Fallback 复用已发表修补；NearOne 的主仓同名源码为不同版本，原件保持，已验 `5697` 后像仅作为精确选源的安装覆盖发布，不将本批验收套用于不同主仓源码。Wall 的四处 projection 加入原 `Fin 4 → ℝ` 连续线性映射类型注解，使原 `(1,1,1,2)` 权重形式可 elaboration，并导入已存在的 log-product 供应者。该定义正文的语法例外明确单列；原 log 自然数乘积、uniform width／N0 在 omega／cap 之前的量词顺序及数学假设保持。见 [验收结果](member-repair-batch9/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch9/INDEPENDENT_REVIEW.json)，实际旧失败和后续修补记录完整保留。

Member 第十一批 Overlap／Multiplicity 两模块通过标准构建、指定模块 kernel replay 和全部 33 个公开导出的完整类型／公理检查，仅标准三公理，源码及十项主要产物稳定。Overlap 只把绝对值下的自然数分母非负显式给出，signed coefficient 仍可任意取符号；Multiplicity 只展开原补映射等式后使用原算术证明。原 labelled carrier、product fibre、重复素数、weighted sum、`rank^rank`、截断及量词保持。见 [验收结果](member-repair-batch11/VALIDATION_RESULTS.json) 与 [独立复核](member-repair-batch11/INDEPENDENT_REVIEW.json)。原批次 bookkeeping 对 Overlap 误记已添加中性验证注释，实际该源码保留旧历史注释；[发布补充清单](member-repair-batch11/PUBLICATION_ADDENDUM.json) 明确更正该字段，已验源码和原记录保持不动。

第十二批 `P4BSublinearCutoffMass` 在首次标准编译前复用远端 `bc9ac33a` 的完整既有修补，非注释差异仅把同加项 API 改为 `add_le_add hsum (le_refl (1 : ℝ))`。原声明、定义、数值、cutoff 与 sublinear 条件保持。标准构建、指定模块 kernel replay 和全部 10 个公开导出检查通过，仅标准三公理，源码和五项主要产物稳定，见 [验收结果](member-repair-batch12/VALIDATION_RESULTS.json) 及 [root 独立复核](member-repair-batch12/INDEPENDENT_REVIEW.json)。该源码原先没有当前对象，也没有本地失败或验收记录，本批不制造旧失败、不以候选 CI 代替当前验证。一次增量远端核对仅发现一个分支变化，现成 SourceCutoff／Sublinear 修补因此直接复用；八个当前选源交集和其它旧 support copies 的界限见 [增量来源审计](remote-reuse-incremental/AUDIT.json)。

十个 Member 入口第二次聚合构建启动时，项目源码覆盖为本目录登记的 34 个后像、一个 P6 共享后像和一个既有绿色供应者，共 36 项；native 的两个 import 覆盖与一个扩展另行登记。完整生产源码组合可从 [MEMBER_SOURCE_OVERRIDES.json](MEMBER_SOURCE_OVERRIDES.json) 定位。统一入口重试继续执行，单个依赖模块的成功检查不等于十入口全部通过。

第二轮新增第十五批 `P2SimultaneousTableIteration` 通过标准构建、指定模块 kernel replay 和全部 126 个公开导出的完整类型／公理检查，仅标准三公理，源码及五项主要产物稳定。原 `fullOrdinaryBank` 两个构造器的 Prop 资格证明显式展开为 `50 ≤ i.val+50`，原 `Fin 200` 索引 `i.val+50`、150 项 Upper 后接 150 项 Lower 的全部数据与次序不变；这是定义内部证明子项的 elaboration 例外，不声称原未 elaboration 定义已有相同 kernel 值或 raw body 不变。其余修补为长度、原网格常量和 Bool 化简，未增加 W1/W2 许可或正 seed／完整正表结论。原 154 秒失败中的 `sorry` 来自 elaboration 恢复，源码无字面 `sorry`，最终 126 项公理检查无 `sorryAx`。见 [验收结果](member-repair-batch15/VALIDATION_RESULTS.json) 与 [独立复核](member-repair-batch15/INDEPENDENT_REVIEW.json)。旧 static 计数漏掉 `inductive Action`，完整源码声明命令应为 41，补充见 [metadata clarification](member-repair-batch15/INDEPENDENT_METADATA_CLARIFICATION.json)；实际 126 项环境导出审计一直包含其构造器及 recursors。

第十七批 `P2HistoricQ80OrdinaryEstimatorSoundness` 的五处变化限定于四个证明：同加项 API、函数 β 展开和显式使用既有 `ordinaryA_pos`。全部原声明、七个定义、数据、row bank、cutoffs、chord／max 与 actual-h 许可保持。标准构建、指定模块 kernel replay 和全部 54 个公开导出的完整类型／公理检查通过，仅标准三公理，源码及五项主要产物稳定，见 [验收结果](member-repair-batch17/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch17/INDEPENDENT_REVIEW.json)。原 155 秒失败记录完整保留，没有重跑已经成功的检查。

第二轮启动时已提交源码与 36 项项目覆盖的逐项比较见 [ATTEMPT2_COMMITTED_SOURCE_ASSEMBLY_CHECK.json](ATTEMPT2_COMMITTED_SOURCE_ASSEMBLY_CHECK.json)，其 recipe commit 明确固定于 `31169d69`；后续通过的修补按批次追加。补充的 [只读复用核查](reuse-observations-iteration2/PUBLICATION_FILES.json) 确认当前缺失 native 对象没有漏用 P6 现成对象。四个已知修补提交另提供十份精确 preimage 匹配的源码候选，原始逐项索引均记录没有 `.olean`，不构成已有对象或资格。该核查没有执行新的 Lean、stock、资格检查或安装。

本目录前版根据伴随消息，将这十份源码误写为已有编译对象；原始 `a60103db` 索引始终正确且未改动。现以 [明确更正记录](reuse-observations-iteration2/OLEAN_PRESENCE_MESSAGE_CLARIFICATION.json) 修正说明，没有基于错误消息接受任何旧对象或计验证 credit。随后四个实际新失败命中现成源码的复用记录仍然有效。

第十四批 Receiver／Adaptive 两模块通过标准构建、指定模块 kernel replay 及全部 74 个公开导出的完整类型／公理检查，仅标准三公理，源码和十项主要产物稳定。Receiver 两处 sandwich 显式给出原 `s`、`t`，Adaptive 的原 tag-0 分支仅补 `ite_true` 化简；原 frozen receiver、函数 family、标签和量词保持。Receiver 主仓 canonical 路径仍缺席，仅发布明确安装的已验后像。见 [验收结果](member-repair-batch14/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch14/INDEPENDENT_REVIEW.json)。

第十六批 Rho／Incoming 两模块通过同样三项检查，全部 116 个公开导出仅标准三公理，源码和十项主要产物稳定。Rho 只补原 True 条件化简，保留相同 rho 与商。Incoming 将原 reserved-token binder `prefix` 及其同一引用写成 `«prefix»`，保留相同 Lean.Name、类型、数据 term 与 `(b,false)` padding；原未解析定义不能声称已有相同 kernel 类型或 raw definition 字节。另一处证明仅从原 `s<2` 得到 `s≠2`。原物理先前 prefix 的因果性和精确 `s=2` 边界保持，见 [验收结果](member-repair-batch16/VALIDATION_RESULTS.json) 与 [独立复核](member-repair-batch16/INDEPENDENT_REVIEW.json)。两批独立复核先冻结稳定源码／日志／产物摘要，FINAL 完成后只补相同 hash 链，没有重复源码或 Lean 检查。

第十三批 Floor／LogPoint／ChildMass 三模块通过标准构建、三个指定模块 kernel replay 和全部 255 个公开导出的完整类型／公理检查（47、132、76），仅标准三公理，源码及十五项主要产物稳定。Floor 仅展开原 let／函数应用；LogPoint 七处证明逐字复用已发表 `d33a86e4`，另一处只展开当前 R03 的 `oddLoop`，保留当前 core、imports、算法与 guards。ChildMass 保留原 N、固定 `L>0`、70／36、标签重数与 D5 positive-cost 排除；首次尚有 pointwise smul 类型与多余 `ring` 两处 API 错误，原失败归档后最终 `3efe` 后像通过，Floor／LogPoint 已成功检查没有重跑。ChildMass 主仓 canonical 路径仍不存在，仅发布明确安装后像。

完整结果见 [验收记录](member-repair-batch13/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch13/INDEPENDENT_REVIEW.json)。LogPoint 旧静态表受到注释内假声明及 let-result 截断影响，原记录保持，新 [完整 27 条声明头比较](member-repair-batch13/LOG_POINT_FULL_HEADERS_REVIEW.json) 与 [发布补充](member-repair-batch13/PUBLICATION_ADDENDUM.json) 给出修正；实际 132 项环境导出的完整类型／公理记录一直完整，没有因此重跑 Lean。

第十八批 `P2SeedOmegaQuotientUnitCarrierExact` 仅在两处 `Nat.div_self` 显式提供既有正性，原 mask、receiver 和最后两项 cutoff 保持。标准构建、指定模块 kernel replay 及全部 10 个公开导出的完整类型／公理检查通过，仅标准三公理；源码和五项主要产物稳定，见 [验收结果](member-repair-batch18/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch18/INDEPENDENT_REVIEW.json)。

第十九批三个模块共 113 个公开导出全部通过相同三项检查，源码及十五项主要产物稳定，仅标准三公理。`P1OriginalCoarseContinuationCells` 逐字复用既有 `3c94` 后像；`P4BLabelledOuterPushforward` 和 `P4BPhysicalShellMass` 逐字复用既有 `48db` 后像，包括历史注释。原 imports、完整声明头、定义、数值及假设保持，见 [验收结果](member-repair-batch19/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch19/INDEPENDENT_REVIEW.json)。这里复用的是可靠源码，当前对象通过本批实际检查接受。

第二十批只有 `P2EnhancedOrderedReciprocalBudget` 一个模块，共 14 个公开导出；`Nat.cast_prod` 的证明 API 修补保留原 Γ7–21 各有序位置和原 `22*H^6` 总预算。三项检查通过，仅标准三公理，源码及五项主要产物稳定，见 [验收结果](member-repair-batch20/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch20/INDEPENDENT_REVIEW.json)。BoundaryUnion 属于下一批。

第二十一批 `P4BOuterRampBoundaryUnion`、`P1ActualUpperClosedParameterUniformity`、`P1HistoricalFourthFullCellIntegral` 共 59 个公开导出通过三项检查，仅标准三公理，源码及十五项主要产物稳定。BoundaryUnion 仅移植既有四个证明体，保留当前 `ActualUpperCountingInputs` import；Uniformity 显式取出已有不等式，FullCellIntegral 使用原 `Pi.sub_def` 与 β 展开。原完整声明、定义和假设保持，见 [验收结果](member-repair-batch21/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch21/INDEPENDENT_REVIEW.json)。

第二十二批 `P5zMarkedPrimeFamilyCorrections` 与 `P2TwentyOneUnsiftedArithmeticSource` 共 44 个公开导出通过三项检查，仅标准三公理，源码及十项主要产物稳定。五个证明的代数、阈值与条件化简修补保留任意 M/J、signed rho、Γ7–21 重数、unit tail 及原严格 cutoffs。后者主仓 canonical 文件不存在，已验源码只按明确安装路径发布，见 [验收结果](member-repair-batch22/VALIDATION_RESULTS.json)、[独立复核](member-repair-batch22/INDEPENDENT_REVIEW.json) 和 [源码覆盖表](MEMBER_SOURCE_OVERRIDES.json)。

第二十三批 `ActualPrimeSlotSquarefreeSymmetry` 与 `Part3ActualCompactAllRankSupport` 共 25 个公开导出通过三项检查，仅标准三公理，源码及十项主要产物稳定。修补限定于零列表分支、局部名字、`List.Sublist` 及 Bool／if 化简，原声明、定义、重数与 support 保持。CompactAllRankSupport 首个候选的真实失败单独归档，最终 `25fcb4b7` 后像通过；已成功的 Squarefree 检查未重复运行。见 [验收结果](member-repair-batch23/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch23/INDEPENDENT_REVIEW.json)。

上述十八至二十三批合计十二个模块、265 个实际公开导出，按 `SOURCE_SELECTION` 的真实模块映射发布。单模块的成功不代替旧十入口的最终验收。当前阶段目标已改为完整 P1；后续执行范围与完整端点合同见 [P1 计划](../../superpowers/plans/2026-11-23-p1-complete-formal-proof.md)。其余已验工作保留，未验证的修改不计完成。

完整 P1 前置的第三十八批 `P1HistoricalFourthFullCellLimit` 与 `P1OriginalCoarseFourthCellIntegral` 共 34 个实际公开导出，通过标准构建、指定模块 kernel replay 和完整类型／传递公理检查，仅标准三公理，源码及十项主要产物稳定。修补为同一 `Fin 4` 坐标的显式化及原 `Pi.sub_def`／β 展开；完整声明头、定义、原积分域和假设保持，见 [验收结果](member-repair-batch38/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch38/INDEPENDENT_REVIEW.json)。

第三十九批 `P2OriginalFourthCapProducerInterface` 是完整 P1 历史链的必要供应者，完整复用已发表 `48db3d60` 的原始文件，包括历史注释。144 个公开导出的三项检查通过，仅标准三公理，源码和五项主要产物稳定，见 [验收结果](member-repair-batch39/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch39/INDEPENDENT_REVIEW.json)。其 `oldComponent_vector` 把原命名歧义 `B(t2)` 写为 `VariableEnvelope.B(t2)`：这是原第三分量的 `153/256-3*t2/8`，旧同名自然数函数导致旧声明不能 elaboration。此声明头例外明确记录，不声称旧声明已有相同 kernel 类型；其余完整声明头、全部定义和物理分量保持。

第四十四批 `Part3ActualAttachedRoughFrontier` 也出现在完整 P1 的真实闭包中。7 个公开导出的三项检查通过，仅标准三公理，源码和五项主要产物稳定。两条声明将原上下文已强制为自然数的存在量 `a k` 显式标为 `ℕ`；原因子分解、frontier、support、量词次序和 `q≠0` 保持，三个证明体逐字不变。旧声明未 elaboration，亦不声称旧 kernel 类型已存在，见 [验收结果](member-repair-batch44/VALIDATION_RESULTS.json) 和 [独立复核](member-repair-batch44/INDEPENDENT_REVIEW.json)。

旧 R03 的五模块 P1 前置链已完成：第四十一批 `P1OriginalCoarseFourthCellLimit`、四十二批 `P1OriginalFourthSmallPrimeStratification`、四十三批 `P1OriginalFourthSmallBinWeightedMass`、四十五批 `P1OriginalFourthMovingPrimeIntervalBound`、四十六批 `P1ActualMovingPrimeIntervalEnvelope`。五批共 112 个实际公开导出（28、51、14、14、5），全部标准构建、指定模块 kernel replay 和完整类型／公理检查通过，仅标准三公理，源码及二十五项主要产物稳定；独立复核均已完成。

前四个模块分别修补空集积分 API／β 展开、原 Nat/Fin 坐标显式化、同一有限和标量分配，以及原不等式的标量改写。完整声明头、定义、bin endpoints、常量、假设和 K 的独立量词保持。最后的 Envelope 与原选源逐字一致，直接复用其唯一成功的顶层 normal invocation，无源码修改或重复编译。四十五批原静态证明标签的已知误写由原发布前补充记录更正，原定理名与声明未改。逐批结果及独立复核见 [41](member-repair-batch41/VALIDATION_RESULTS.json)、[42](member-repair-batch42/VALIDATION_RESULTS.json)、[43](member-repair-batch43/VALIDATION_RESULTS.json)、[45](member-repair-batch45/VALIDATION_RESULTS.json)、[46](member-repair-batch46/VALIDATION_RESULTS.json)；每个目录同时保存 `INDEPENDENT_REVIEW.json`。这使旧二十模块 P1 子集对象齐备，仍不等于完整 P1 的最终证明闭合。

现代 P1 实际闭包还用到以下既有 Member 修补。本次完成独立复核并发布原验收记录，没有重跑成功的 Lean 检查。八批共十个模块、350 个实际公开导出，全部标准构建、指定模块 kernel replay 和完整类型／公理检查通过，仅标准三公理，源码及五十项主要产物稳定。

| 批次／验收结果 | 模块 | 公开导出 | 修补范围 |
| --- | --- | ---: | --- |
| [25](member-repair-batch25/VALIDATION_RESULTS.json) | `CurrentChenP5CausalRhoFactorization`、`P2EnhancedNativeLowerAtomSupport` | 32 | 原 signed Fubini alias 展开、`nodup_reverse` API |
| [26](member-repair-batch26/VALIDATION_RESULTS.json) | `Part5UpperTableLookup` | 31 | 原 `Set.indicator` 展开 |
| [27](member-repair-batch27/VALIDATION_RESULTS.json) | `P2LowerCapPlanIntegerRetention` | 76 | 原字段 token 引用、`mem_cons_self` API |
| [30](member-repair-batch30/VALIDATION_RESULTS.json) | `ActualPrimeMultiLabelNormalization` | 22 | 显式传入原 tuple carrier 和被积函数 |
| [31](member-repair-batch31/VALIDATION_RESULTS.json) | `CurrentChenP5OriginalU5CausalFinite`、`P2HistoricalBankLogWeights` | 97 | 原 cutoff／rho 展开、分式消去和已有 interval endpoint 显式化 |
| [32](member-repair-batch32/VALIDATION_RESULTS.json) | `P5ZU11MeasurableEnvelope` | 47 | 原 witness 重组、Bool／if 与 measurable API |
| [33](member-repair-batch33/VALIDATION_RESULTS.json) | `P4BActualPairOuterRamp` | 21 | 原 ramp 定义展开、具名参数 |
| [36](member-repair-batch36/VALIDATION_RESULTS.json) | `P4BWeightedHyperbolaSlotDecay` | 24 | 原有限和、倒数、非负与代数证明 API |

各目录保存 `INDEPENDENT_REVIEW.json` 和不可变发布清单。原完整声明、数学假设、数据、数值和定义保持；二十七批仅把 reserved-token 字段 `Frame.prefix` 及同名引用写作 `«prefix»`，相同 Lean.Name、类型与数据 term 不变，旧未解析语法不声称已有相同 kernel 值。三十一批配对验收的 `P2HistoricalBankLogWeights` canonical 文件仍未创建，其源码作为明确安装后像保存；验收不外推到不同源版本，也不把这些共享供应者计作完整 P1 终点。

完整 P1 的第一轮实际共享构建新增以下五批验收，共十四个模块、564 个定义模块声明，其中公开 542、private 22。每批均已完成标准构建、指定模块 kernel replay、按定义模块枚举全部声明的完整类型／宇宙参数／传递公理检查，公理仅标准三项，源码和七十项主要产物跨阶段稳定。独立复核及原命令、真实退出码、完整 AST 和源版本均在各批目录，没有为包装重跑成功的 source 或 kernel 检查。

| 批次／验收结果 | 范围 | 全部 owned／public／private |
| --- | --- | ---: |
| [47](member-repair-batch47/VALIDATION_RESULTS.json) | `P4AOriginalFull87GammaApproximation` | 8／8／0 |
| [48](member-repair-batch48/VALIDATION_RESULTS.json) | 四个原 P1 policy／cap／variable-fourth 前置、三个 literal 源、Descending15、Slot19 与 Slot9 | 451／430／21 |
| [49](member-repair-batch49/VALIDATION_RESULTS.json) | `P2OriginalFourteenCausalHistoryMesh` | 31／30／1 |
| [50](member-repair-batch50/VALIDATION_RESULTS.json) | `P1OriginalCoarseFifthResidualDictionary` | 32／32／0 |
| [51](member-repair-batch51/VALIDATION_RESULTS.json) | `P1HistoricalFifthJointIntegralSign` | 42／42／0 |

这些修补保留原声明头、定义、几何、数据、常量、假设与量词。Gamma 显式消费原 `v_eq_min`，并在证明内部限定实数 `VariableEnvelope.B`；四个 P1 前置限定已有 Θ 常量、计算原封闭 Bool 反例、显式给出原 profile 参数或解码完整原 firstStop guard。三个 literal 源调整条件化简与 witness 解构的次序；Descending15 使用原严格序传递正性；Slot19 展开原 mask138，Slot9 使用原正数倒数比较。Fourteen 限定原 R 并显式构造原有限标签会员；最终源保留真实 preimage 的混合行尾，早期规范化行尾的草稿未被编译或接受。ResidualDictionary 仅在两处补 `rfl`；FifthJointIntegralSign 使用原 dependent union、old/new own-cube gate 和同一 overlap 定义。

Gamma 第一次 public-only 审计与随后完整 owned 补充均保存，补充确认该模块 owned 恰为原八个 public，无 private；原成功编译与 kernel 没有重复。Gamma、三个 literal 模块和 Fourteen 的主仓 canonical 文件仍不存在，已验源码按明确安装路径作为后像发布。其余九个 canonical 文件与实际已验后像一致。当前这些是完整 P1 的必要前置验收；三个新的 P1 raw／structure／ancestor 输出候选及完整现代端点仍须继续验证，不能把本表视作整个 P1 完成。

随后第五十二批 `P1OriginalFourthPackedTableDecoder` 和 `P4AOriginalHistoricalFifthSelectedSlotBridge` 两模块通过同样三项检查及独立复核，155 个 owned 声明（151 public、4 private）仅标准三公理，源码及十项主要产物稳定，见 [验收结果](member-repair-batch52/VALIDATION_RESULTS.json)。Decoder 仅显式展开原 mask 的有限集会员并删除已经关闭的 impossible branch；它是原 17-byte ABI 的结构引理，没有以此声称整表解析或几何检查完成。SelectedSlot 原样复用已发表 `232c18b5` 的完整修补文件，保留历史注释及原参数、积分和 gate。

第五十四批九个实际依赖也全部通过标准构建、指定模块 kernel replay、完整 owned 类型／宇宙参数／公理检查及独立复核，共 175 个声明（169 public、6 private），仅标准三公理，源码及四十五项主要产物稳定，见 [验收结果](member-repair-batch54/VALIDATION_RESULTS.json)。实际模块清单以该目录 `SOURCE_SELECTION.json` 为准；修补限定于 zero-tag、lambda、列表长度、原补域、互不相交标签的 filter、函数加法及已有代数的表达。CanonicalSwitched 只开启原测度 `∞` 所需的 ENNReal notation scope；旧未 elaboration 语法不声称已有相同 kernel 类型。FirstIntegralSeries 的级数包围证明通过不代表其另列的精确数值端点已经完成。Disjoint 和 Series 的首版真实失败归档，最终仅重跑失败的两模块，其余七个成功的 source／kernel 检查保留。

本批 ReverseAdmission 和 OwnCubeCapPayment 仍只发布 stage 安装后像，主仓未创建同名 canonical 文件。RoughAuxiliarySW 直接复用 Prototype 已验源码 `659bc`，但四个实际项目导入对象不同，旧物件不能采用；当前 Member 因此完成自己的必要正常编译与 kernel，没有重复写其已有证明。各批 `INDEPENDENT_REVIEW.json`、完整原日志与发布清单均已保存。

少数旧 `pointer_inserted_this_overlay` 字段实际只记录 owner-stager 是否插入注释，未计入候选作者预先加入的中性指针。新增 [字段语义补充](P1_POINTER_FIELD_SEMANTICS_CLARIFICATION.json) 明确这三处，旧源码、验证与冻结记录均未改动；后续批次分开记录实际 overlay 与 stager 两个动作。

第五十三批六个依赖完成标准构建、指定模块 kernel replay、完整 owned 类型／宇宙参数／公理检查及独立复核，107 个声明（102 public、5 private）仅标准三公理，源码及三十项主要产物稳定，见 [验收结果](member-repair-batch53/VALIDATION_RESULTS.json) 和 [独立最终链](member-repair-batch53/INDEPENDENT_REVIEW.json)。范围为第四 reciprocal-bin regrouping／integral sign、AboveMu third admission、SmallAttachment support、CoarseUpper residual uniformity 与 ThirdGamma first-coordinate rise。修补使用原有限和、端点不等式、history-log 供应者、Fin 坐标及原同侧加法；统一 N0 仍先于 omega、cap、weight、state。SmallAttachment 仅一个 existential header 显式标注原 `a k : ℕ`，旧模板误写为两个 headers 已在独审记录澄清；随后一次 proof simp 补 `1+1=2` 单列，旧未解析 header 不声称已有相同 kernel 类型。两项实际失败的首版及 v2 均归档，其余四个已成功的 source／kernel 未重复。

第五十五批 `P4AOriginalSixthLaterLiteral` 通过正常编译、指定模块 kernel replay 及全部 80 个 owned 声明检查，其中 public 14、private 66，包含新增的 19 个 typed private tables 与生成声明。源码和五项主要产物稳定，公理仅标准三项，见 [验收结果](member-repair-batch55/VALIDATION_RESULTS.json) 和 [非作者复核](member-repair-batch55/INDEPENDENT_REVIEW.json)。八个原有限表定义的实现表示确有变化：将原十九份表分开定型，公有 lookup 使用同序 Fin19 向量，解决原 elaboration 预算及有限模式覆盖问题；原编译资源选项未提高。152 项 lookup RHS、1155 行／8085 个系数、行次序、多重及 R17 charts15–18=3 均保持，原 public headers 不变。原未 elaboration 的函数不声称已有相同 kernel 值或 raw body。

该表原完整 AST／宇宙参数／公理审计已接受全部 80 项；其中十九个 private equation 的 pretty 展示碰到默认 5000-step 上限。只对这十九项补充完整 pretty，逐项确认其 AST、宇宙参数与原记录相同，另外 61 项和全部原公理检查复用，原成功 source／kernel 没有重跑。原截断展示及约 40MB 的完整 raw 审计均留档，最终导出已合并补充。后续新审计显式提高展示步数，项目源码的 heartbeat 预算保持原值。

至此首轮实际构建遇到的 32 个失败依赖均已有相应正常编译、kernel 与 owned 验收，共 1081 个声明（978 public、103 private）。这不替代完整现代 P1 的最终端点：当前继续构建实际 All22 源、三个新输出及固定参数汇合入口，未把依赖验收当作完整 P1 完成。

项目看板最近读取仍返回 HTTP 401，完整蓝色节点到模块的对应清单尚未取得。四个已确认 P6 入口的验收完成，尚不能声称全部蓝色节点完成；看板访问不阻塞依据固定手稿和现有源码继续完整 P1。

第六十三批 `Data.P5SubdivisionStoredBlock071` 已通过正常编译、指定模块 kernel replay、完整 owned 类型／宇宙参数／传递公理检查及非作者最终复核，5 个声明（4 public、1 private）仅使用标准三公理，包含生成的公开 proof 声明。源码及五项主要产物跨阶段稳定，见 [验收结果](member-repair-batch63/VALIDATION_RESULTS.json) 和 [最终复核](member-repair-batch63/INDEPENDENT_REVIEW.json)。原正常编译在索引证明的 kernel 阶段内存超限；修补先用一个私有闭合证明校核 `rows.toList.map sourceIndex` 的顺序索引，再通过 `getElem?` 推回原来的全部有限索引命题。1817 行 literal 数据、字段、顺序、两个原公开声明及 `rows_size` 的 `rfl` 均保持，源进程的原 12 GiB 预算不变。三个检查分别实际退出 0，未为发布重跑。

第六十七批 `Data.P5SubdivisionStoredBlock070` 复用同一证明模板，也通过三项检查及非作者最终复核，5 个 owned 声明（4 public、1 private）仅标准三公理，源码及五项主要产物稳定，见 [验收结果](member-repair-batch67/VALIDATION_RESULTS.json) 和 [最终复核](member-repair-batch67/INDEPENDENT_REVIEW.json)。该块原失败是 4000000-heartbeat 的 `whnf` 超时，修补保持 4096 行数据、原偏移 286720、完整原声明及预算；没有把超时记为数据反例或内存失败。

这两份源码仍作为明确安装后像发布，主仓没有新建同名 canonical 文件。这里只验收两个档案块的原始索引事实；其它块、全部父子最大值检查和完整 P1 端点仍须各自取得实际验收。

第五十七批 `P1FiniteAffineDecisionProgram` 和 `P1OriginalHistoricalRetainedModulusLevel` 完成正常编译、指定模块 kernel replay、完整 owned 审计及非作者最终复核，255 个声明（228 public、27 private）仅标准三公理，源码及十项主要产物稳定，见 [结果](member-repair-batch57/VALIDATION_RESULTS.json) 和 [复核](member-repair-batch57/INDEPENDENT_REVIEW.json)。修补仅处理同侧加法、相同命题的 Decidable 实例及原有限最大值参数，并在两处调用补传原 ceiling check 已提供的第四层界；所有完整声明与定义保持。FiniteAffine 仍作为安装后像发布。

第六十二批四个供应者通过同样验收，共 78 个声明（75 public、3 private），源码及二十项主要产物稳定，见 [结果](member-repair-batch62/VALIDATION_RESULTS.json) 和 [非作者复核](member-repair-batch62/INDEPENDENT_REVIEW.json)。范围为 literal fifth、physical savings reserve、smooth common compact support 与 first derivative budget。两项定义恢复例外明确保留：`rawFourth` 的 Real 参数恢复使用既有 `VariableEnvelope.B`；四项原连续线性映射补齐同一类型信息，Derivative 完整文件原样复用已发表 `48db3d60` 后像。旧定义未 elaboration，不声称旧 kernel 值已经相同。原公式、常量、两策略／2eta／presieve 项及其余完整声明与定义保持。

[调度语义补充](validation-lane-correction/LANE_SEMANTICS_ADDENDUM.json) 说明：原 `compiler.lock` 约束源码编译，独立 `leanchecker` 未自行取锁，早期有短时验证重叠；原真实通过结果和日志均保留。新的独立 lane 锁覆盖整条 normal／kernel／audit 调度，并与原编译锁分离。互斥 fixture 和过渡代码见 [发布复核](validation-lane-correction/PUBLICATION_REVIEW.json)。没有将原两条源码 guard 外推为早期整条验证链始终独占两个 lane 或 24 GiB 总硬上限，也没有为此重跑已经成功的 Lean 检查。


现代 P1 的第二轮实际失败修补新增五组最终验收，共 24 个供应模块、773 个 owned 声明（737 public、36 private）。每组均完成原正常编译、指定模块 kernel replay、完整 owned 类型／AST／宇宙参数／传递公理检查和非作者最终复核，仅标准三公理，源码及 120 项主要产物跨阶段稳定。已成功的 source 与 kernel 检查没有为发布重复。

| 批次／结果 | 模块数 | owned／public／private |
| --- | ---: | ---: |
| [58](member-repair-batch58/VALIDATION_RESULTS.json) | 6 | 329／310／19 |
| [60](member-repair-batch60/VALIDATION_RESULTS.json) | 7 | 128／122／6 |
| [61](member-repair-batch61/VALIDATION_RESULTS.json) | 3 | 83／80／3 |
| [64](member-repair-batch64/VALIDATION_RESULTS.json) | 4 | 71／70／1 |
| [65](member-repair-batch65/VALIDATION_RESULTS.json) | 4 | 162／155／7 |

范围为原 variable-fourth/fifth、历史单元所有权与 literal affine rows、splice／singleton 传输、实际 winner support 与 rough Euler、原 finite-bin 与两类 tail、supported strip／rough-square，以及 P1 必需的 lower-cell／Entry3 前置。各批 `FINAL_REVIEW.json` 保存最终源绑定、实际失败的修订沿革和完整声明范围。Descending 的仿射编译器及 12960 项封闭有理坐标校核已实际通过，后续 H3／Remaining 是否可复用及通过仍须另验。

两个声明表达例外明确保留：WinnerAttached 的存在量 `a k` 显式定为原上下文所需的 `ℕ`，旧未解析模板不声称已有同一 kernel 类型；FiniteBin 的两个辅助有限和将 summand 写成 `(main + error)`，修正原模板被解析为 `(∑ main) + error` 的作用域。后者的最终 occupied-prime 质量上界、常量、K 的量词次序与其它最终声明保持；不是全部原辅助声明头逐字不变。LowerFinite 的 `roughProduct` 与 `«universe»` 保留原模块、定义体和归属，没有迁移到其它供应者。

58、61、64、65 的旧发布清单在 finalizer 尚未输出时记录了空 `finalizer.log`，随后辅助 stdout 写入完整 `FINAL_RELEASE.json`。四个包各自保存不可变 `LATE_FINALIZER_LOG_BINDING.json`，精确绑定实际 stdout 与 FINAL 的逐字同一性；原清单、实际日志及验证证据保持。仅该辅助条目使用显式晚绑定，所有其它原条目仍逐个核哈希，不将旧清单误称为当前全部匹配。60 的原清单全部匹配。这项包装补充没有重跑 Lean，也不增加数学前提。

这些结果仍是完整 P1 的真实供应链验收。H3、Remaining、SixthLater、其余原始数据与最终四个 P1 出口继续按实际编译结果推进；本表不宣称完整 P1 或看板全部蓝色节点已经完成。


第六十八至七十二批完成 `Data.P5SubdivisionStoredBlock000` 至 `049` 的实际验收，共 50 个模块、204800 行原数据、250 个 owned 声明（200 public、50 private）。全部 50 次正常编译、50 次指定模块 kernel replay 和五次完整 owned 审计实际退出 0，非作者逐批最终复核确认完整类型／AST／宇宙参数／标准三公理、原声明清单和源码及 250 项主要产物稳定。逐批结果见 [68](member-repair-batch68/VALIDATION_RESULTS.json)、[69](member-repair-batch69/VALIDATION_RESULTS.json)、[70](member-repair-batch70/VALIDATION_RESULTS.json)、[71](member-repair-batch71/VALIDATION_RESULTS.json)、[72](member-repair-batch72/VALIDATION_RESULTS.json)；各目录保存 `FINAL_REVIEW.json`。

这些是复用 070／071 已验线性索引证明模板的工程安排，没有把原未执行的 000–049 虚列为实际失败。每块原数据、字段、顺序、偏移、两个原公开声明和 `rows_size` 的 `rfl` 保持；私有 List 投影证书推回同一个全部有限索引命题。已绿 070／071 没有重复编译。五十份源码作为明确安装后像发布，主仓不新建同名 canonical 文件。这仍仅验收原始索引事实，不能替代父子 max 恒等式、数值 gain 或完整 P1。

68 保留一项与前述相同的 finalizer stdout 晚绑定；160 个其它原条目逐字匹配，原清单和实际 stdout 均保留。69–72 各自 160 个原发布条目全部匹配。68／69 最终复核新清单的初始绝对路径版本另存为历史文件，规范清单只将路径改为包内相对路径并绑定原版本哈希，复核和验证记录未改；该包装兼容调整没有重跑 Lean。


第七十三、七十四批完成 `Data.P5SubdivisionStoredBlock050` 至 `069` 的实际验收和非作者最终复核，各十个模块、50 个 owned 声明（40 public、10 private），全部原正常编译／指定模块 kernel replay／完整 owned 审计退出 0，仅标准三公理，源码及百项主要产物稳定，见 [73](member-repair-batch73/VALIDATION_RESULTS.json)、[74](member-repair-batch74/VALIDATION_RESULTS.json)。069 保留原 4000000-heartbeat `whnf` 超时的真实失败记录；其它未执行原稿块按工程复用分类。先前仅取消过未执行且无子进程的调度父进程，原 outer143 与新验证 lane 的真实退出 0 分开记录，没有向编译器或 checker 发信号。

至此 72 个原始索引块（000–071、292633 行）均有实际 normal／kernel／full-owned 验收，共 360 个声明（288 public、72 private）。070／071 的既有成功未重复，所有原数据、字段、顺序、偏移和公开索引命题保持。这是全部档案块的索引事实，父子 max 检查、gain 及完整 P1 仍须各自闭合。

第六十六批四个必要供应者也完成最终验收，共 113 个 owned 声明，全部为 public，没有虚构 private 计数，见 [结果](member-repair-batch66/VALIDATION_RESULTS.json) 和 [组合独审](member-repair-batch66/FINAL_REVIEW.json)。Renewal 的原数表与 knots 保持；Gate/Beta 仅原加法结合和 proof token/API 修补，其独立数学范围复用包内 `137206947…` 非作者审。最终组合复核明确披露复核者是这两个补丁的作者，未把自审冒充外审；另两模块的范围与四模块实际验收链也已独立复核。

SixthLater 原内部 `opposite_license_identity` 在原字面数据下不成立：c6、零向量的两边相差原 eta。修正为无 Source 前提的原 row≤gap 辅助不等式，完整保留原十九行、eta、七个定义，以及最终 `source_endpoint_lt_selected_tent` 的严格 `<` 声明。原稿需要的两侧严格 tent licence 仍由原 Source 的严格正性导出；没有添加更强 Source、目标许可或额外 eta 预留。该一处公有辅助名称／声明修正明确记录，不称全部旧公头逐字保持；后续只是具体 Fin 向量与 simp 控制适配。

66 的三个已成功源复用原 Member normal／kernel，新 Sixth 与最终 audit 使用原 P6 guard。collector 按每条真实命令的 state 读取对应原 journal，独立小审和晚绑定见 `late-mixed-runtime-collector-review/`；两个 state 与原 journal 前缀不改，没有为混合 state 的元数据整理重复编译。三个新发布包的原发布清单全部逐字匹配。

第五十六、五十九批完成 RemainingEighth 与 H3 的实际 normal／kernel／完整 owned 审计及非作者最终复核，分别验收 417（274 public、143 private）和 173（76 public、97 private）个声明，仅标准三公理，源码及十项主要产物跨阶段稳定。见 [Remaining 结果](member-repair-batch56/VALIDATION_RESULTS.json)、[最终复核](member-repair-batch56/FINAL_REVIEW.json)、[H3 结果](member-repair-batch59/VALIDATION_RESULTS.json) 与 [最终复核](member-repair-batch59/FINAL_REVIEW.json)。二者复用已经验收的 Descending 仿射编译器，分别以闭合有理证书校核原 4559／1188 行、41031／10692 个坐标，再证明同一任意实数输入下的原行表达式；原数据、顺序、索引和资源预算保持。名称、字面向量表示、证明 API 与 H3 文档位置的恢复例外在各包明确记录，不把未 elaboration 的旧源码称为已有同一 kernel 值。两份最终源码按明确路径作为安装后像发布，主仓未新建同名 canonical 文件。

Remaining 的三份完整原审计合计 1474948542 字节，Git 中按 [无损载体清单](member-repair-batch56/LOSSLESS_ARTIFACTS.json) 保存为 gzip，原 SHA、原发布清单和日志内容保持。实际发布程序已独立解压校核 CRC、长度和 SHA；包内 `restore_lossless_evidence.py` 可向新的目录恢复原文件。[发布工具及独审](lossless-evidence-publication/INDEPENDENT_ROOT_INTEGRATION_REVIEW.json) 保存有限文件白名单、原子恢复和 71 项隔离包装检查，未为压缩或发布重跑 Lean。

H3 正常编译、kernel 和完整审计均实际退出 0；[调度补充](member-repair-batch59/ORDINARY_POINTWISE_LANE_STATE_OVERLAP_ADDENDUM.json) 保留一个错误 state 模板造成的 16.429 秒命令窗口重叠。没有独立 OS 锁取样，故不声称该区间整条验证链互斥或有 24 GiB 总硬限制。原通过记录和产物哈希不变，后续模板已修正并增加 state 一致性检查。

第七十五至七十七批三个必要前置也完成实际 normal／kernel／完整 owned 审计及非作者最终复核，共 70 个声明，全部 public，仅标准三公理，源码及十五项主要产物稳定。见 [75](member-repair-batch75/VALIDATION_RESULTS.json)、[76](member-repair-batch76/VALIDATION_RESULTS.json)、[77](member-repair-batch77/VALIDATION_RESULTS.json)。DescendantLevel 整份复用已有 `51b3d20c` 修补；CellTestLimit 与 ActualLowerTail 仅修原测度／函数名／有限积 API，保持原声明、定义、假设和量词。ActualLowerTail 是原代数传输，不能单独视为统一均值估计的证明。

另两项实际依赖 [Mobius／HeathBrown 既有物件复用](member-two-qualified-reuse/FINAL_REVIEW.json) 沿用可靠 producer 的正常编译和 kernel 验收，在空闲原调度窗口采用已核定的原源码及十六项物件，当前 stock 检查退出 0 且源码事件为零；只补做当前上下文完整 owned 审计，21 个声明（19 public、2 private）与原公开类型／AST／宇宙／公理一致。未为复用重复原成功编译，也未重扫已有 14951 个实际导入的资格记录。锁范围证据来自已执行并审查的代码路径，没有伪称另有独立 OS 锁快照。

本次登记七个实际供应模块，共 681 个 owned 声明（439 public、242 private），目录累计 219 份已验源码后像。新的六终点共享增量构建正在继续处理实际失败；四个最终 P1 输出、完整数据与分析供应链仍须各自闭合。这些前置验收尚不构成完整 P1，也不构成全部看板蓝色节点已完成的声明。
