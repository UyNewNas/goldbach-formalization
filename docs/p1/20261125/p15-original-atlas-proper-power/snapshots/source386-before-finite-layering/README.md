# 原 singleton Atlas proper-power 源码接入

状态：`SOURCE_IMPLEMENTED_STATIC_REVIEW_COMPLETE_PENDING_P1_ACCEPTANCE`。本目录记录四个历史 provider 的来源、第五个 Atlas consumer 的有限接口源码及静态审查。有限接口已经实现，等待 P1 的正常编译、内核重放和全部 owned 声明验收；本目录不增加编译、内核核验或数学接受信用。

## 五个新增 owner

- `PrimeProductsMellinExactMeanInsertion`：完整采用已存在的 t05 修订选本，保留其全部字节。该选本已修订 `exactDiscrepancy_eq_count_sub_mean` 的证明体；本次不再修改证明。SourceWord 字典实际消费 `functional`、`residueKernel`、`exactDiscrepancy`。
- `P5IndependentPrimeSourceWordDictionary`：完整原字节，包括原有三个 import；完整复用 canonical `Part3AllKFamilyLambdaCorrectionBound` 链。
- `P5OriginalPrimeAllGroupHBDiscrepancy`：只将 `P5ActualEtaPsiOccurrenceBudget` 的 import 替换成已存在的 `P1OriginalSingletonPointwiseData`；全部十二条声明和证明体保持原字节。
- `P1OriginalSingletonSmoothLicence`：迁入九条历史声明，保留原 namespace、原声明名和精确证明字节。只导入已有 pointwise owner 和 canonical `P5LicensedOriginalIntegerProfile`。
- `P1OriginalSingletonAtlasProperPower`：新增独立 consumer，仅导入 `P1OriginalSingletonSmoothLicence`、`P5OriginalPrimeAllGroupHBDiscrepancy` 和 `P1OriginalSingletonProperPower`。它将完整原 Atlas singleton proper-power reserve 的有限 chart 和识别为已有 P3 labelled residual，再调用已有 proper-power 估计。

五个 owner 的当前指纹、前四个 provider 的完整来源路径、Git blob、SHA-256、长度和 import 替换见 `ADOPTION_MANIFEST.json`。原静态审查指纹、固定手稿 commit/blob、合同核对、三个 consumer terminal 和未验收状态见 `SOURCE_REVIEW.json`。九条声明在原文件、阶段一迁移后像和新 owner 中的零基、半开字节区间见 `SMOOTH_EXTRACTION.json`。字节区间以原 UTF-8 数据计，不转换 CRLF/LF。

## 九条光滑声明

1. `ActualEtaPsiOccurrenceBudget.eta_smooth`。
2. `ActualSingletonPrimeTestFamily.chi_smooth`。
3. `ActualSingletonPrimeTestFamily.chiLog_smooth`。
4. `ActualSingletonLogCollarFamily.integerWeight`。
5. `ActualSingletonLogCollarFamily.scaledChi_smooth`。
6. `ActualSingletonLogCollarFamily.profile_eventually_zero`。
7. `ActualSingletonLogCollarFamily.profile_smooth`。
8. `ActualSingletonLogCollarFamily.singletonLicence`。
9. `P5CanonicalTentNarrowSingletonTransfer.actualLicence`。

前八条在 `ImbalancedChen.P5Z` 下，第九条在 `ImbalancedChen` 下。原 pointwise18 选取和迁移记录保留；其后发布的一处 `profile_bounds` 表达修复在下文单独绑定。实际 `Licence.ambient` 仍是同一原 `profile`，其整数取值没有被 prime-only 一致性假设替换。光滑性层不导入 AllWord 导数预算，也不构造 mixed-Euler family。

## 历史 provider 的迁移后像

`provider-postimages/` 中的四份文件，以阶段一 `p15-singleton-proper-power/provider-postimages/` 为直接输入，再移除这九条声明并添加 `import ImbalancedChen.P1OriginalSingletonSmoothLicence`。它们同时保留阶段一的十八条移除及 PointwiseData import。原档案和阶段一后像未修改。

这些新后像仅供今后完整采用历史 provider 时使用，仍为未编译源码。未来必须使用合并后像，以确保十八条 pointwise 声明和九条 smooth 声明分别只由当前公共 owner 声明一次。现有 canonical Part3 定义不迁移、不复制。

## 有限接口源码已实现，等待 P1 验收

第五个 owner 的三条公开 terminal 都在 namespace `ImbalancedChen.P1OriginalSingletonAtlasProperPower` 中：

1. `original_singleton_properPowerReserve_sum_eq_labelledResidual`：精确识别所有原 chart 的 `properPowerReserve` 之和与同一 `Q/rho/N` 的 labelled proper-power residual。该恒等式允许任意复系数 `rho`，保持原 count-minus-exact-coprime-mean 有限核。
2. `eventually_original_singleton_atlas_properPower_logAccuracy`：固定 `kap < 1`、`A` 与 `eps > 0` 后，先取统一的 eventual `N` 阈值，再任取 `B`、pre-HB `K`、额外 trim 参数 `kap0`、`Q` 与实系数 `rho`。在 `0 < q < N^(599/1000)` 和 `|rho q| ≤ 1` 下，原 signed reserve 和的范数不超过 `eps * N / (log N)^A`。
3. `eventually_original_singleton_atlas_properPower_singularNormalization`：对任意正 `tol`，在相同统一性和模数、系数条件下，将原 signed reserve 和的范数界为 `tol * singularNormalization N`。

有限字典保留 `smoothNatural` 之外的额外 `eta`、原 `psi` 和每个 chart 各自的 `roughWord (beforeHBCutoff K js)`。`listExtension (actualLicence ...) [n]` 与 `smoothNatural ... n` 在全部自然数输入上相同；完整整数 proper-power carrier 通过原 `sourceWord` 单射重索引，每个自然数只计一次，`Lambda/log` 权重只出现一次。原非负 dyadic partition 的和为一，使合并后的实权重仍在 `[0,1]`，没有附加 chart 数量损失。

P3 调用固定 `k = 1`、`J = m = 0`、`M = c = K = Cρ = 1`、`C = 2`、`a = 1 - kap`、`θ = 599/1000`，以 `Icc 1 (2*N)` 为整数 carrier。这里固定的 P3 参数 `K = 1` 与之后任取的 pre-HB rank `K` 不同。原 AllGroup 中 proper-power reserve 的减号及 signed kernel 均保持不变。

独立静态审查没有发现丢权、carrier 重计、重复 Lambda、整数 licence 不一致或 P3 参数合同错误。两处有限和与 coercion 的 Lean elaboration 仍需实际核验；静态审查不替代正常编译、内核重放和全部 owned 声明验收。审查绑定的手稿为 commit `a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en/coefficient-appendix.tex`，blob `10f3e2efb2074a9b97148a5151956e1d450be13f`。

## 静态闭包与缓存复用

`SOURCE_CLOSURE.json` 现在以完整五个 owner 为显式 targets，包含 **386 个项目源码模块**。与阶段一已发布的 316 模块闭包合并后共有 **475 个模块**：相对阶段一增加五个新 owner 和 154 个首次进入闭包的既有 canonical 依赖。五个 owner 之外的 381 个活动依赖是缓存及来源核对集合，不因此成为编译请求。清单逐模块记录当前选定源码 hash；`imports` 为项目 import，`all_imports` 另保留包括 Mathlib 的完整列表。原源码指纹和本轮准确变更集合另存，不用当前后像覆盖历史绑定。

源指纹相同不等于对象已经接受；对象复用仍需实际对象指纹、匹配的源/导入记录和工具链证据。原源码基线 `fb95653d07307b43176ce2ec9772f0c0bf47c108` 保留。其后的 installer 修复、阶段一首次编译修复和九个既有后像采用，分别有独立来源记录；本次只更新元数据和静态验证器。

### 格式变化与历史审查绑定

五个新增 owner 本身在原审查之后仅发生一项格式变化：删除 `P1OriginalSingletonSmoothLicence.lean` 文件末尾多出的一个 LF，4337 bytes 变为 4336 bytes，当前 SHA-256 为 `49677aed381fbd4c661d7132208d920d4f5e366aa0a1515c5566bbbdee968c83`。变化区间 `[4336,4337)` 在九条声明区间之外；全部声明字节、区间与原名字保持不变。本轮依赖更新没有再修改五个 owner。

`SOURCE_REVIEW.json` 保留原五个 reviewed-owner 指纹，包括 SmoothLicence 的原 SHA-256 `872ecc7c62cc2b9f673f7161f7d6782053a12bdc0d27330b2de759ddc377866e`。新增的 `FORMAT_ONLY_DELTA.json` 将旧审查与当前文件精确绑定；核验脚本要求“当前文件加一个 LF”逐字节重建旧文件，同时重验九条迁移声明。Atlas consumer 没有修改。

`STATIC_VERIFICATION.json` 原样保留为**初始四个 provider、358 模块闭包的历史静态快照**。其中旧路径的 hash 反映当时状态，不能用作当前五 owner 的回执。当前检查结果单独写入 `CURRENT_STATIC_VERIFICATION.json`，不增加 Lean 接受信用。

`STATIC_VERIFICATION_BEFORE_DEPENDENCY_UPDATES.json` 是本轮依赖更新前的五 owner 静态回执原字节副本。`BEFORE_DEPENDENCY_UPDATE_BINDINGS.json` 保存当时的元数据指纹；旧 protected-exception 记录也有原字节副本。`SOURCE_REVIEW.json`、`SMOOTH_EXTRACTION.json`、`FORMAT_ONLY_DELTA.json` 和原四-provider 回执均未修改。

### 阶段一首次编译修复与九个既有后像

`DEPENDENCY_SOURCE_UPDATES.json` 绑定两组父任务已经实施的源变化：

- 发布 commit `d20acdf13882e17d97833064f5e7c54f3192b03c` 中的两处源修复：Pointwise 的 `.trans_eq` 名称不再被换行拆开，以及 TrueD 中两处 `simp` 已关掉目标之后的冗余 `tauto` 删除。验证器从固定失败源 `1a259e113c0977c8cb2814492ff3bd6ab7cdc475` 按 `FIRST_COMPILE_REPAIRS.json` 的三个精确区间重建当前全部字节。
- `p15-existing-atlas-dependencies/ADOPTION_MANIFEST.json` 中的九个既有接受后像。当前 canonical 文件逐字节等于固定 commit `a392cd8efcf4f0b4adf3d12f2d8db41370309ed3` 中的对应 postimage。原 canonical preimage、完整 source pin 和此前验收范围均保存在该独立目录；本目录只核对这次确切采用。

九源均在 386 和 rough-prime 的 362 模块闭包内，与阶段一 316 模块及原 29 个 protected 输入均无交集。活动闭包的源码指纹变化为 **10 项**：Pointwise 加九源；联合 475 闭包再包括 TrueD，共 **11 项**。所有 imports 与闭包拓扑不变。验证器用旧十行及旧阶段一比较绑定，逐字节重建完整更新前 `SOURCE_CLOSURE.json`，从而核对其余行和字段没有被静默替换。

九源的既有审查明确区分七个 proof-body-only 后像与两条例外：`P5ActualMultiGroupHBChartScale` 的 `Group` 字段括号修复，以及 `P5ActualLabelledPrimeSmoothCharts` 的局部 dyadic `R` 名称解析修复。本目录**不声称旧版与新版已经 elaboration 的类型相等**；这里绑定的是确切已发布后像及独立保存的来源、审查和验收证据。

阶段一原十八条提取区间仍对固定修复前 Pointwise 字节核验。当前 Pointwise 中十七条原块字节不变，另一条精确对应已发布的表达修复。九条 SmoothLicence 声明及两代 27 条移除后像保持原字节；旧提取清单没有被改成新的证明来源。

### Protected inputs 的五项明确例外

`ADOPTION_MANIFEST.json` 中原 29 个 protected-input 指纹不变，当前 24 个文件仍逐字节一致。五个例外为原 installer 修复，以及 `d20acdf…` 发布的 Pointwise、阶段一 README、阶段一 `SOURCE_CLOSURE.json` 和阶段一源码验证器更新。每项均保留旧绑定，并精确绑定已发布 commit 的当前文件。

原 installer 例外记录完整保留：`SOURCE_INSTALL_REPAIR.json` 与 commit `1a259e113c0977c8cb2814492ff3bd6ab7cdc475` 绑定当前 SHA-256 `901c3c585574f8427045e18bf7d78dcfa6d32b05e0c551cbc42b382584d9e08d`，只增加既已发布的 `Part3LongSlotDistribution` additive 白名单项。`PROTECTED_INPUT_EXCEPTIONS.json` 追加四个 d20 例外，没有移除任何旧 pin。

本次未修改阶段一文件、阶段二 runner 或 installer。阶段二 `run_selected.py` 仍为 SHA-256 `482cbe1d15fb6814d541b61a1b88becf75a15d206eafdb301245d29b94727bec`，`install_sources.py` 仍为 `dd0ab0451bf92865da5a531686a0221ac792d821963ce14259a6b712cb3fe8e3`。runner 原逻辑直接验证选定 commit 的完整五-root、386-module manifest 和对应源码；它没有硬编码闭包哈希常量，本次也没有新增这种逻辑。normal/kernel/full-owned API、guard 和 serializer 均未改变。

### 可重复的源码核验

在仓库根目录运行：

```text
python3 docs/p1/20261125/p15-original-atlas-proper-power/verify_source_reuse.py --write-receipt
```

脚本核对完整选本与原 Git blob、唯一 AllGroup import 替换、原十八条提取的重建前像、九条不变声明、两代迁移后像、格式差异、五项 protected-input 例外、九源原样采用，以及全部 475 个联合源码的 hash、imports、可达性与环。它扫描联合源码和迁移后像中的禁止证明 token，默认只打印结果；显式传入 `--write-receipt` 时仅写本目录的 `CURRENT_STATIC_VERIFICATION.json`。它不调用 Lean、Lake、云任务或对象就绪检查，不修改源码、对象、trace 或旧回执。

## 其余 P1.5 义务

这里实现的是原 Atlas proper-power reserve 的 supplier。额外 `eta` 已完整保留；单独的 trim／边界 reserve 估计、rough-prime 项、其余 signed von Mangoldt discrepancy、medium-Type-I 输入及完整 PP／family caller 义务分别跟踪，本目录不代替它们的源码与验收工作。P1 验收前不记入已接受证明；本目录不为整个 P1.5 声明闭合。
