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

第二轮启动时已提交源码与 36 项项目覆盖的逐项比较见 [ATTEMPT2_COMMITTED_SOURCE_ASSEMBLY_CHECK.json](ATTEMPT2_COMMITTED_SOURCE_ASSEMBLY_CHECK.json)，其 recipe commit 明确固定于 `31169d69`；后续通过的修补按批次追加。补充的 [只读复用核查](reuse-observations-iteration2/PUBLICATION_FILES.json) 确认当前缺失 native 对象没有漏用 P6 现成对象，四个已知修补提交中的其它匹配模块已有当前对象，未覆盖或重编它们。该核查没有执行新的 Lean、stock、资格检查或安装。

项目看板最近读取仍返回 HTTP 401，完整蓝色节点到模块的对应清单尚未取得。四个已确认 P6 入口的验收完成；H430 Member 入口及其它已确认范围继续构建，尚不能声称全部蓝色节点完成。
