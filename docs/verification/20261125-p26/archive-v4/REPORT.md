# Saving19 Archive v4：独立数据 owner 的正式输入候选

## 状态与范围

**SOURCE ONLY / UNCOMPILED。** 本包准备正式新版输入表示的源码候选，未执行 Lean、未搬运对象、未排远端任务，也未修改主仓库。由主线发布并进行新的 normal、独立 kernel、owned exports/types/axioms、实际 loader inputs 前后绑定等 strict 验收。

包中共 **34 个 Lean 源码**：32 个输入/Core 布局模块，加一份逐字原 `SourceJson` 和一个保留全部原义务的 `Archive` facade。其中 4 个是逐字已有 helper/reader 源码，30 个是新建或替换、必须重新验收的模块。源码候选准备完毕不意味着 Archive、cell00 或全部原件已经解析成功。

新版保留原 **13 geometry + 13 moment 路径**。每份真实输入独立一个 `noncomputable Tree` 数据 owner；Core 不执行原文件 quotation。共同 loader 沿 `IO.FS.readFile → 完整 s.toList → 已证同一 pack → 原 Tree 构造 quote` 生成完整字符表示，保留所有字段、Unicode、NUL、CRLF 及顺序。没有 host JSON 解析、数学预检、截断、padding、换行转换或用 hash 代替 Lean 等式。

## 模块布局与首编边界

| 层 | 模块 | 数量 | 原件读取 |
| --- | --- | ---: | --- |
| 通用表示 | 原样 `P2OriginalSaving19PackedChars` | 1 | 无 |
| 共同 loader | `P2OriginalSaving19ArchivePackedLoader` | 1 | 编译单个数据 owner 时读取其指定原件 |
| 独立原件 | `P2OriginalSaving19ArchiveGeometryData00`…`12`、`…ArchiveMomentData00`…`12` | 26 | 每 owner 正好一份 |
| 输入映射 | `P2OriginalSaving19ArchivePackedInputs` | 1 | 无 |
| 原 parser | 原样 `P2OriginalSaving19SourceJson` | 1 | 无 |
| 表示桥 | 原样 `P2OriginalSaving19CharInputBridge`、`…SourceJsonCharInput` | 2 | 无 |
| typed Core | 新版 `P2OriginalSaving19ArchiveCore` | 1 | 无 |
| 原义务 facade | 新版 `P2OriginalSaving19Archive` | 1 | 无 |

首轮可独立评审/编译的三个数据 owner 是 `ArchiveGeometryData00`、`ArchiveGeometryData12`、`ArchiveMomentData12`。每个的项目依赖恰为 **3 个模块**：本 owner、共同 loader、PackedChars；外部仅 `Lean`，无需编译 MomentFloorConsumer 及其依赖（合计 217 个既有项目模块）。对应原文件大小分别是 **195,134 B、14,461,008 B、3,451,302 B**。大文件是否满足资源预算仍由真实编译决定，本包不外推先前 cell00 原型性能。

`PackedInputs` 用 13 次 `Fin.cases` 和不可能的 `Fin.elim0` 尾项，按 00…12 顺序映射；没有默认 cell 或重复末项。其 chars 映射为相应 Tree 的 `toList`。

静态项目源码闭包（包含根模块，不是 Mathlib/Lean 的全传递模块数）：

| 根 | 项目模块总数 | 本包模块 | 外部直接 import 根数量 |
| --- | ---: | ---: | ---: |
| 任一首编 data owner | 3 | 3 | 1（Lean） |
| PackedInputs | 29 | 29 | 1（Lean） |
| ArchiveCore | 250 | 33 | 130 |
| Archive facade | 251 | 34 | 130 |

`SOURCE_CLOSURE.json` 保存每条 import、全部项目源码 SHA、缺失检查及候选拓扑顺序。其余 217 个供应商被列为已有来源依赖，**没有要求或执行可选重建**。新 Core 保留原 MomentFloorConsumer import；本轮没有借输入表示修改数学供应商闭包。

## 精确语义迁移

基准是已在主线通过的 v2 Core 源码，8552 B，SHA：
`df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182`。

原 Archive 前像 10816 B，SHA：
`f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49`。

从 `parseInteger` 开始，直至完整 `decodeMoments` 结束的 **5399 B** 切片逐字保留，SHA：
`21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30`。
这包括原 rational 解析、所有结构字段、默认/派生实例以及 geometry/moment 的全部 decoder body。

四个公开 typed getters——`geometryParse`、`momentParse`、`geometry`、`moments`——仅添加必要 `noncomputable` 前缀；陈述与函数体保持原样。特别是：

```lean
noncomputable def geometryParse (c : Fin 13) : Except String Geometry :=
  SourceJson.parse (geometryText c) >>= decodeGeometry
noncomputable def momentParse (c : Fin 13) : Except String Moments :=
  SourceJson.parse (momentText c) >>= decodeMoments
```

输入的变化明确体现在：

```lean
noncomputable def geometryText : Fin 13 → String :=
  fun c => String.ofList (geometryChars c)
noncomputable def momentText : Fin 13 → String :=
  fun c => String.ofList (momentChars c)
```

新 Core 中两个 `*_eq_parseChars` 定理仅用现有 `SourceJson.parse_ofList` 和 `congrArg` 连接同一 decoder。原 fuel、quoted/value/array/object、white、integerToken、duplicate-key、错误 payload 和最终未消费尾串检查均由**原 SourceJson** 继续定义。桥不证明某个原件解析成功。

新 Core 没有导入旧 Core；facade 只导入新版同名 Core，从旧 Archive 移走重复定义。原 Archive 的 36 个具名 def/structure/theorem 在新 Core+facade 各出现一次，原 structures 的 FQN 保持。原两个 text quotation elaborator 属于被替换的输入层；其余工程检索没有发现调用点。

这明确是**新版输入表示**。没有声称旧 Core String 或旧 CharList 与新表示的整串闭合等式已经通过。已证明的通用 `unpack(pack cs)=cs` 与可审查的同一 `pack(s.toList)` 机械引文连接支撑新表示；源 SHA 只绑定审查/输入证据，不作为数学或解析假设。

## 原义务保留

facade 保存原 post-Core 全部源码。除 3 个依赖输入的 def 与 2 个 Decidable instance 添加 `noncomputable` 外，逐字一致；规范化后的尾切片 SHA：
`5adc6e905522a4fd0fdba949b66940e11b38ab4c61c918a9e7c84e187716a57a`。

以下原闭合义务继续存在，**全部未在 v4 验收**：

- `geometry_parse_success : ∀ c, geometryParse c = .ok (geometry c)`。
- `moments_parse_success : ∀ c, momentParse c = .ok (moments c)`。
- `original_cell_shapes : ∀ c, CellShape c`：保留 dimension/Jacobian、rowcount、vertex/factor shapes、sourceWitness、degree6/exp3、Q80/Q96 分母等。
- `original_row_shapes : ∀ r, RowShape r`：保留 28918 行的相同 simplex IDs、9 个 distinct vertex IDs/范围和 10 个 factor floors 等。
- `original_row_ids`、`original_row_count` 的原声明与 proof body 完整保留。

原 `by decide` proof body 只作为未验收源码保留。这不表示 whole-file parser/shape guard 已满足资源预算；不能从新 Tree 数据或 `.getD default` 得到成功信用。后续分段解析证明仍须组合到这些完整原目标。

必要 `noncomputable` 标记可能继续向下游普通 runtime 定义传播。例如原 `Original28918.rawVertex` 是普通 abbrev，`OwnedSource.originalPoint` 与 `vertexId` 是普通 def；它们读取新版 noncomputable getter，后续编译可能需要同类标记。此次未修改下游文件。其 mathematical statements/body 应保持，并在新版依赖上重新验收，不能搬用旧依赖对象来消除该义务。

## 原件路径与来源证据

`INPUT_PATHS.json` 将每个 family/cell/module/FQN 与原 relative/absolute path、bytes、SHA 一一对应。26 份元数据逐字来自主仓库 `docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json`，SHA：
`3e022a419c35152589c2c3fb26cb0fe5839c79a348277b0643174b4f078f3954`。

元数据来源是已绑定 v2 Core 的 `LOADER_INPUTS_BEFORE.json`，位于 artifact：
`docs/verification/20261125-p26/archive-v2-and-k6-retry2-evidence.tar.xz`，SHA `e775033bd14313f00b9aa81710f8494ac2a6dd93dd3b7b6afa75f0d08036b209`；成员路径为：
`archive-v2/ImbalancedChen.P2OriginalSaving19ArchiveCore/runs/attempt-00000/LOADER_INPUTS_BEFORE.json`。

所有下表文件均从原 `../goldbach-research/` 读取，合计 **80,189,086 bytes**。这些是原始 byte counts，**不是未经证明地当作 codepoint 长度**。本轮生成器不读取任何真实 payload，也没有下载或另造其它原件。

| cell | geometry 文件名 | bytes | moment 文件名 | bytes |
| --- | --- | ---: | --- | ---: |
| 00 | `eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json` | 195,134 | `eighth-third-moment-refinement-20261009-a23-low-00.witness.json` | 28,999 |
| 01 | `eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json` | 470,901 | `eighth-third-moment-refinement-20261009-a23-low-01.witness.json` | 75,094 |
| 02 | `eighth-third-minorant-extension-20261009-a23-s23_low-02-cell.witness.json` | 6,685,325 | `eighth-third-moment-refinement-20261009-a23-low-02.witness.json` | 1,536,271 |
| 03 | `eighth-third-minorant-extension-20261009-a23-s23_low-03-cell.witness.json` | 1,113,076 | `eighth-third-moment-refinement-20261009-a23-low-03.witness.json` | 223,727 |
| 04 | `eighth-third-minorant-extension-20261009-a23-s23_low-04-cell.witness.json` | 6,464,308 | `eighth-third-moment-refinement-20261009-a23-low-04.witness.json` | 1,500,571 |
| 05 | `eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json` | 201,042 | `eighth-third-moment-refinement-20261009-a23-low-05.witness.json` | 28,973 |
| 06 | `eighth-third-minorant-extension-20261009-a23-s23_low-06-cell.witness.json` | 335,849 | `eighth-third-moment-refinement-20261009-a23-low-06.witness.json` | 58,376 |
| 07 | `eighth-third-minorant-extension-20261009-a23-s23_low-07-cell.witness.json` | 6,655,353 | `eighth-third-moment-refinement-20261009-a23-low-07.witness.json` | 1,460,077 |
| 08 | `eighth-third-minorant-extension-20261009-a23-s23_low-08-cell.witness.json` | 6,432,118 | `eighth-third-moment-refinement-20261009-a23-low-08.witness.json` | 1,488,819 |
| 09 | `eighth-third-minorant-extension-20261009-a23-s23_low-09-cell.witness.json` | 8,082,635 | `eighth-third-moment-refinement-20261009-a23-low-09.witness.json` | 1,936,155 |
| 10 | `eighth-third-minorant-extension-20261009-a23-s23_low-10-cell.witness.json` | 4,626,712 | `eighth-third-moment-refinement-20261009-a23-low-10.witness.json` | 1,059,602 |
| 11 | `eighth-third-minorant-extension-20261009-a23-s23_low-11-cell.witness.json` | 9,331,509 | `eighth-third-moment-refinement-20261009-a23-low-11.witness.json` | 2,286,150 |
| 12 | `eighth-third-minorant-extension-20261009-a23-s23_low-12-cell.witness.json` | 14,461,008 | `eighth-third-moment-refinement-20261009-a23-low-12.witness.json` | 3,451,302 |

编译工作目录仍须让这些原 relative paths 解析到 `/workspace/goldbach-research/`；不得把此前诊断 staging 路径冒称生产原路径未变。新验收还需为本次读取保留 before/after 原件绑定，不能只拿历史 metadata 代替新执行证据。

## 已有源码/对象与新验收

四个原样复用源：

| 源 | SHA256 | 本包动作 |
| --- | --- | --- |
| PackedChars | `cf65b9e0f3b0a4735cdb962d9b317ed29e8f39c8507647bab04f7e48800ad001` | 字节复制；已有本地 normal+独立 kernel 回执 |
| CharInputBridge | `18d5e23b30fd7333bb2b3a80c4bedae0ff4f8e190b45833c390a6cbffc1bba21` | 字节复制；已有本地 normal+独立 kernel 回执 |
| SourceJsonCharInput | `64c20a58a005b83aec402c9b1e65e570fdcbe35fb9530be1220596679da97396` | 字节复制；已有本地 normal+独立 kernel 回执 |
| SourceJson | `ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424` | 原 parser 字节复制；原来源/对象 pin 保留 |

已有对象与回执的绝对路径、SHA 和适用边界在 `ACCEPTANCE_PLAN.json`。本包**没有复制任何 olean**。主线只有在 module/source/import/toolchain 指纹匹配且其 strict 复用政策允许时才能复用现成对象；本地 helper 诊断不是新版全闭包 strict 回执。

共同 loader、26 数据 owner、PackedInputs、Core、facade 共 **30 个模块**必须新验收。尤其原 v2 Core 的 **224 exports 信用不转移**：新版 Core 定义及依赖改变，即使 decoder 源字节相同，也应 fresh normal/kernel/owned declarations 审计。旧 Core/Archive olean 不得与新源码混用。下游数学源码未改，也未获新版数据验收信用。

## 交付与复核

- `ImbalancedChen/`：34 个候选源文件。
- `build_candidate.py`：只读原源/元数据的统一机械生成器；已有候选字节若不同即拒绝覆盖。
- `preimages/`：精确 v2 Core 与 Archive 原源。
- `SOURCE_MANIFEST.json`：34 个 module/install-path/source SHA、pins 和源码状态。
- `INPUT_PATHS.json`、`ORIGINAL_INPUT_SCALE.json`：完整26项原路径及历史输入绑定。
- `SEMANTIC_DIFF.json`、`MIGRATION.patch`：逐字 schema/decoder、getters、facade 义务与必要标记对照。
- `SOURCE_CLOSURE.json`：静态 import 闭包、每个来源 SHA 和候选拓扑顺序。
- `ACCEPTANCE_PLAN.json`：已有精确 helper 对象来源、30 个新验收模块、全部保留待证义务。
- `STATIC_AUDIT.json`：禁止构造扫描、路径/声明唯一性、闭包完整性、source manifest 指纹复核。

本包未执行任何新编译。是否修改正式仓库、采用哪些首轮资源预算和如何安排 strict 队列，均由主线在这些具体源码上执行。
