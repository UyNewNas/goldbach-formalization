# Saving19 Archive v4 独立只读来源与语义审查

## 结论与审查范围

在本次冻结源码上，未发现输入遗漏、cell 映射错误、typed schema/decoder 语义改变、新增成功假设或原证明义务被删除的实质问题。候选可进入主线按单目标进行的正式验收。此结论是源码审查，不是 v4 编译、kernel、full-owned 或数据解析验收结果。

审查对象为 `/workspace/p26-recovery-candidates/archive-v4` 中 34 个 Lean 源码及来源、闭包、语义差异、验收范围文档。审查期间没有运行 Lean、没有执行候选生成器或验收 driver、没有提交远端任务，也没有修改候选、生产源码或任何对象。本轮 v4 审查只读取来源元数据，没有重新读取全部 80 MB 原始 payload。唯一写入为此独立审查目录。

本记录只冻结源码审查。随后准备的 strict runner 尚未纳入本记录，须另行核对其 Batch13 调用、单目标执行、217 个既有项目模块冻结、26 原件 before/after 绑定及新 Core 信用边界。

## 1. 来源与原件映射

26 项来源元数据逐项与主线 `ORIGINAL_INPUT_SCALE.json` 比较一致，候选中的该文件也与基准逐字相同。基准 SHA-256 为 `3e022a419c35152589c2c3fb26cb0fe5839c79a348277b0643174b4f078f3954`。其记录的来源是已绑定 v2 Core 证据 artifact `archive-v2-and-k6-retry2-evidence.tar.xz`，SHA `e775033bd14313f00b9aa81710f8494ac2a6dd93dd3b7b6afa75f0d08036b209`，成员为 `archive-v2/ImbalancedChen.P2OriginalSaving19ArchiveCore/runs/attempt-00000/LOADER_INPUTS_BEFORE.json`。本审查没有重新解包该 artifact 或把其历史 metadata 当作新执行证据。

独立检查了所有 26 个 owner 的 family、cell、module、FQN、相对源路径、源码字节数/哈希、直接 import 和实际 loader 路径字符串。每类恰有 00 至 12，各出现一次；没有跨 cell 引用、路径替换、漏项或重复项。

原 geometry 路径模板仍为 `../goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-XX-cell.witness.json`；原 moment 模板仍为 `../goldbach-research/eighth-third-moment-refinement-20261009-a23-low-XX.witness.json`。geometry 总计 65,054,970 B，moment 总计 15,134,116 B，合计 80,189,086 B；最大项是 geometry12 的 14,461,008 B。这里都是来源证据中的 byte counts，未替代 Unicode codepoint 长度。

两个聚合 map 分别恰有 13 层 `Fin.cases`，参数依次为 `geometryPacked00`…`geometryPacked12`、`momentPacked00`…`momentPacked12`，均以 `Fin.elim0` 结束。不存在默认 cell，也没有重复末项。chars 定义直接取所选 Tree 的 `toList`。

## 2. 机械 quotation 与表示边界

shared loader 源 SHA 为 `5f1ff6c68faba7bdbde44b7bb7f7aac57c1c1d71563b781ee25a5ab050717f27`。其实际语句为完整 `IO.FS.readFile p.getString`，随后调用同一 `P2OriginalSaving19PackedChars.pack s.toList`。quotation 逐个保留 empty/leaf/branch 构造；leaf 直接引用 count 与 Nat payload，branch 保留左右顺序。

没有 JSON 解析、typed decode、数学数据预检、源哈希成功条件、截断、padding、换行规范化或原文缺失时的默认输入。每个 data owner 仅定义一个 `noncomputable Tree`，直接 import 只有共同 loader；该 owner 的项目源码闭包为自身、loader、PackedChars 三项，外部仅 Lean。

PackedChars、CharInputBridge、SourceJsonCharInput、SourceJson 四份候选源均与此前固定源逐字一致，精确哈希保存在本记录 manifest。已审查的通用 Char/Tree round-trip 涵盖 Unicode、NUL、余块及完整顺序；此包没有把旧 P4A 的验收冒称新 Unicode codec 的证明。

完整原文件到 Lean 数据的外部 quotation 边界仍须通过实际路径/字节/哈希/工具及源码上下文审计。通用 pack 定理与同一 pack 的机械引用支持新版表示；本包没有声称新 packed 文本与旧 String 或旧 CharList 定义之间的整串封闭等式已通过。

## 3. typed Core 的精确对照

旧 v2 Core 为 8,552 B，SHA `df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182`；旧生产 Archive 为 10,816 B，SHA `f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49`。两份均独立与 Git commit `508d757913ea9c536c0d4f95abb35c090b940a29` 中各自的精确路径逐字核对。Core 路径是 `docs/verification/20261125-p26/archive-v2/ImbalancedChen/P2OriginalSaving19ArchiveCore.lean`；Archive 路径是 `ImbalancedChen/P2OriginalSaving19Archive.lean`。

从 `parseInteger` 开始至完整 `decodeMoments` 的 5,399 B 切片独立逐字比较相同，SHA 为 `21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30`。原结构字段、派生实例、JSON key、rational/integer 解析、数组 mapM、Q80 floors、old/new Q96 字段及全部 decoder body 均未改变。

`geometryParse`、`momentParse`、`geometry`、`moments` 的原类型和 body 仍完全相同，仅增加 `noncomputable`。去除这四处标记后的切片 SHA 为 `6837fde05e19d3faca007af68a1402a0f4dd20d97e524e7540786d35559a72b1`。尤其原 `.toOption.getD default` 原样保留；本审查没有把该 fallback 当作成功解析结果。

输入变化明确位于 geometryText/momentText：它们成为相应完整 chars 的 `String.ofList`。两个公开 parse 定义仍运行原 `SourceJson.parse`，再绑定原 `decodeGeometry`/`decodeMoments`。新增的 `geometryParse_eq_parseChars`、`momentParse_eq_parseChars` 对任意 `c : Fin 13`，仅由现有 `parse_ofList` 及 `congrArg` 得出完整 Except 结果相等。它们不要求或提供某个具体文件的 parse success；原 fuel、错误、duplicate-key、分隔符和尾串检查均未更换。

## 4. 原证明义务与量词

新 facade 的整个 post-Core 尾段在去除三处 def、两处 Decidable instance 的必要 `noncomputable` 标记后，与旧生产 Archive 逐字一致，SHA 为 `5adc6e905522a4fd0fdba949b66940e11b38ab4c61c918a9e7c84e187716a57a`。六个原 theorem 的声明及 proof body 都保留。

以下四类闭合义务没有新增假设，没有放宽范围，仍未获得 v4 验收：

- `geometry_parse_success : ∀ c, geometryParse c = .ok (geometry c)`，覆盖全部 Fin 13 geometry 输入。
- `moments_parse_success : ∀ c, momentParse c = .ok (moments c)`，覆盖全部 Fin 13 moment 输入。
- `original_cell_shapes : ∀ c, CellShape c`，保留维数、Jacobian、完整 row counts、vertex/factor shapes、cell/sourceWitness 对应、degree 6/3、Q80/Q96 分母等。
- `original_row_shapes : ∀ r, RowShape r`，保留原 OriginalRowIndex 的全部 28,918 行、相同 simplex IDs、九个互异 vertex IDs 及范围、十个 factors/floors。

`original_row_ids` 和 `original_row_count` 的原派生声明/proof 也完整保留。原 `by decide` 仍只是尚待运行的源码，不能据此声称大文件 parser/shape guard 可在预算内完成。输入表示的准备不消除数值、ownership、integral 或 endpoint 的后续义务。

## 5. 闭包、重复定义与复用信用

独立核对了 34 个候选源码的全部长度/哈希，以及 facade 闭包 251 个、Core 闭包 250 个项目模块的实际源文件、直接 import 和所有 project edges。无缺失边或环。全部 217 个非候选项目模块均通过 Git batch 读取，与声明来源 commit `e3824f6d30f5ce193c8aa86a725bfb77d941d5d7` 的对应 blob 字节/哈希一致，没有把工作树中的未来改动冒称该 commit 的源码。

这 217 个既有项目模块包括 MomentFloorConsumer 自身；其 proper dependencies 为 216。最终 REPORT 已将原先易误读的计数措辞改为含自身的合计口径。这只涉及说明文字，34 个 Lean 源码和 SOURCE_MANIFEST 未改。

Core 闭包不包含 Archive facade；所有对 ArchiveCore 的解析都指向新候选源，未导入旧 Core 对象或旧 Archive 来获取同名定义。原 36 个具名 def/structure/theorem 仍在新 Core/facade 各自出现一次，原 typed structures 的 FQN 保留。旧两个 text quotation elaborator 被新输入层替换，未发现其它生产源码调用点。

32 个输入/Core 布局模块加原 reader 与原义务 facade，共 34 个源码；其中四份字节复用、30 个新建或替换。原 helper 的局部 normal/kernel 证据不能冒称新版 P1 完整闭包的 strict 验收。旧 Core 的 224 exports 信用不转移；新 Core、data owners、maps、loader 仍须按其实际新上下文验收，旧 olean 不得与新源码混用。

## 6. 实际下游迁移风险

只读确认了两个明确位置：Original28918 的普通 `abbrev rawVertex`，以及 OwnedSource 的普通 `def originalPoint`、`def vertexId`，位于其文件的 noncomputable section 之前。它们依赖新的 noncomputable getter，后续编译可能需要相同标记传播。此处没有声称已复现编译错误，也没有修改下游。现有 mathematical statements/body 应继续保持，并在新版依赖上重新审计。

这不构成本轮输入层源码的语义阻碍，但必须保留在迁移说明中，不能声称旧下游对象或编译结果可直接复用。

## 7. 验收计划和说明文字边界

最终 REPORT 与 ACCEPTANCE_PLAN 的范围说明准确：全部 v4 源码尚未编译；没有复制旧对象；旧 String/CharList 整串桥未获信用；getD fallback 未被证明消除；四类原 guard 和全部数据解析/数值目标仍待验收。26 文件的历史 bytes 不当作 codepoints，不从 cell00 性能外推 geometry12 或整体规模。

SOURCE_MANIFEST、INPUT_PATHS、SOURCE_CLOSURE、SEMANTIC_DIFF、ACCEPTANCE_PLAN、最终 REPORT 及全部 34 源码的审查时点哈希由 REVIEW_MANIFEST.json 冻结。后续 strict runner 的审查将独立记录，不把未存在的执行结果写入本源码审查。
