# Saving19 原始 28,918-row pulling ownership 复用候选

## 交付结论

已准备一个**不导入旧 `P2OriginalSaving19PullingOwnership` 的独立候选**，将原十三组数据接到现有 `P2Winner9LiftingGeometry.checked_pulling_overlap_null`。新结果仍是所有原 cell、原 row 的同 cell 零重叠；与旧结果的整个 theorem header 已逐字比较相同。消费者的可选 overlay 为 6,651 B，仅改一条 import 和一条 open，其余字节均保留。

**实际原件接头尚未编译，三个原件闭合 guard 也尚未验算。** 本次仅对一个新的 Mathlib-only 有限表示 helper 完成了正常编译、独立 leanchecker 重放以及三条公共引理的类型/axiom 检查。没有启动 P1、重建旧供应商、读取或 Python 审计原 JSON、改主仓、安装 overlay 或提交远端。

不存在必须额外假设的几何结论：只要这里明确保留的原件有限条件通过，现有通用定理足以给出原目标。不需要完整 polytope 覆盖或旧模块的逐 row adjugate/leading-coefficient 证书。该候选也**不声称证明了**旧 `original_polynomial_faces` 的特定多项式等式。

## 手稿依据与目标范围

稿源为 `UyNewNas/chen-imbalanced-semiprimes` commit
`a988cba584d803ae2856a0de50efb582f4f3dd6a`，路径 `paper/release-20261106/en/`。

| 稿源 | 本次核对范围 | 文件 SHA256 |
|---|---|---|
| `numerical-appendix.tex` | 177–196：全部原不等式验顶点、face incidences、pulling、精确 simplex moments，以及正 saving 可舍弃非负部分 | `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232` |
| `argument.tex` | 278–291：当前 eighth saving 的实际密度；1098–1103：正 saving 允许在 subset 上给下界 | `87f5b5f2e25082e00b2b04d8ecc684630d64846912457dc0adade1a36fd67182` |

稿件没有在这些段落给出 Lean 的具体 negative-monomial supporting-plane 构造。这一构造属于已存在的通用 pulling 形式化证明，本次只复用其接口，不称它为 1106 稿内一条另有编号的显式公式。

原 `OwnedIntegral` 的唯一旧 pulling 消费点，是 `overlapSet_null` 中对 `original_within_cell_null_overlap` 的调用。之后仍由原 source walls、source inclusion、实际密度非负性和积分单调性构造合法 inner union。它不要求覆盖整个原 polytope。因此本候选只替换这一同型供应者，不扩大目标到覆盖，也不把支持集包含或目标积分作为前提。

最终陈述保持：

```lean
theorem original_within_cell_null_overlap
    (c : Fin 13) (i j : CellRow c) (hij : i ≠ j) :
    volume (actualSupport ⟨c, i⟩ ∩ actualSupport ⟨c, j⟩) = 0
```

新 FQN 位于 `P2OriginalSaving19PullingReuse`。旧模块和它的特定多项式声明原封不动留在生产源码中；可选 consumer overlay 改读新 FQN，没有把旧未过声明标成已过。

## 代码与确切来源

| 文件 | 大小 | SHA256 | 状态 |
|---|---:|---|---|
| `ImbalancedChen/P2OriginalSaving19PullingFiniteCodes.lean` | 3,308 B | `15bfdfbc77b0f8a6929f27dee8681b55b420e03531dd8269a45722ec6c61ca63` | 本地新 helper normal/kernel 通过 |
| `ImbalancedChen/P2OriginalSaving19PullingReuse.lean` | 7,624 B | `92885bbfdf2348efc67f574dbc1a179ba303f1fccc7a2652bfe2df1ec4cee973` | 原件接头 source-only，未编译 |
| 可选 `OwnedIntegral` overlay | 6,651 B | `630553410a7a97f4db48fa1f5939c25b163c660de8cf4efd51d21798d978c0bd` | 仅 import/open，未安装或编译 |
| 可选 `OwnedSource` GateProper 复用 overlay | 6,587 B | `ec43e27a8112def672c6686af9c94d99228a3d061a04eaf1c7703d82ceb7a447` | 仅 import/原 guard 证明，未安装或编译 |

原件源快照来自 `/workspace/p26-source-closure`，观察到的 HEAD 为
`07826355aedef5a01e76c36ad304bc6b115f3c2b`。`SOURCE_MANIFEST.json` 逐文件绑定实际读取的 SHA，未把可能存在的 worktree 内容一概称为该 commit 的已提交 blob。

现有通用几何源为 `P2Winner9LiftingGeometry.lean`，26,703 B，SHA
`d2942e81eeb4651473e1e429897f3af440aa8898ae361f9e1ed817c7ad39f750`。
其项目源码闭包恰为 20 个模块。本次没有重编它或这些供应者，也没有迁移任何对象的旧验收上下文。

新接头与当前原 `OwnedSource` 的实际源码闭包为 239 个项目模块；同时采用两个可选 overlay 后，`OwnedIntegral` 的闭包为 249。逐项 imports 与 source SHA 在 `SOURCE_CLOSURE.json`。它们不包含旧 `PullingOwnership`、`P2Winner9OriginalPullingFlags` 或 `P2Winner9PullingArchiveCore`；没有导入 Winner9 的全量 flag/rank/archive 数据。现有通用模块自身的固定依赖保留，未声称它是无任何既有数值定义的空接口。

此快照的生产 Archive 仍为原 f48 版本。今后安装 v4 Archive facade 后，闭包和 noncomputable 传播必须重新绑定，不能把本 source snapshot 当成未来已验证的上下文。

## 数据接头如何保持原义

### 顶点与 facets

`rowID c i k` 直接使用 `OwnedSource.vertexId ⟨c,i⟩ k`，其 `Fin` 范围证明复用 `vertexId_bound`。没有 `Fin.ofNat`、取模、截断、重编号或新坐标表。points 直接是 `originalPoint c`；原九顶点的顺序保持不变。

flag 的类型是 `Fin (geometry c).facetVertices.size`，表示实际 global facet 数组的位置。`facetOriginalIndices` 的生产者原 constraint IDs 完全不参与 Fin 97 构造。

`facetGate c f` 仅从下面完整闭合义务的证明中 `Classical.choose`：存在一个实际 `Fin 97` source gate，使**每个原顶点**的 facet membership 当且仅当该 gate 的 rational evaluation 为零。这正是旧 `original_pulling_checks.3`，本次分成独立闭合 proof request；它尚未验算。不是按相似名字、原编号或 host 判断接受一个 gate。

`facetMask` 是实际 facet 顶点列表的自然数 bitmask。新已核验引理证明，对任意列表和任意 Nat，某一 bit 为 true 当且仅当该 Nat 出现在原列表中；重复 ID 不改变集合，高位不截断，没有固定字长。结合上述完整 zero-set 等价，直接得到通用几何接口所需 `hzero`。`hnonneg` 则直接调用原 `original_gate_checks.2`，没有新零集或非负假设。

### 原 face ledger 路径

`originalLedger` 只投影原 `faces` 中的 vertices、pivot 和 facetSets。原 Archive 的 dimension、simplices、全部其余 schema/decoder 字段仍保留，没有重写 reader 或数据内容。

`traceFlags` 从完整 `List.range vertexCount` 和当前原 row 的九个实际 ID 开始，fuel 固定为 9。每一步：

1. 按与原 producer 相同的 face 顶点列表寻找原 record。
2. 要求 record.pivot 等于当前 row 的首 ID。
3. 只从该 record 的实际 facetSets 选择不包含此 pivot、且包含剩余 row ID 的 child。
4. 只选择满足 `mask(face) &&& mask(globalFacet) = mask(child)` 的实际 global facet。
5. 用原 child 列表递归，记录该 bounded facet index；终点必须是实际 singleton face。

bitmask membership 引理与原 `Nat.testBit_and` 解释第 4 步的精确集合交，不把 cryptographic hash 当数学相等。所有搜索失败、fuel 耗尽或错误终点均返回 `none`。

`rowFlags` 的空列表 default 只是总函数取值。闭合 `original_ledger_flag_checks` 明确同时证明 `flagTrace = some rowFlags` 和现有 `pullingCheck = true`，因此 `none` 不能被接受。原 `pullingCheck` 对整条 row 检查当前 face 中的 maximal apex、所选 gate 在 apex 非零及后续 face 交。它必须消耗与八个剩余顶点一致的八条 flags；没有把 flag soundness、最大 pivot 或 null overlap 作为输入假设。

这证明请求绑定的是**每条原 row 的 ordered path**。它不声称另外证明了旧全量 `pullingRows` 输出数组的全局顺序等式，也不声称核验了旧 `FaceChecks` 的所有 dimension、simplices count 或 maximal-intersection metadata。这些更强审计声明没有被删改、冒认或用作假设；当前内并集零重叠目标不需要它们。

### 全 row 顶点集合互异

每个 `rowKey c i` 是该原 row 的九个 vertex IDs 的 bitmask。`sortedCodes` 在 Lean 中对完整 `List.ofFn (rowKey c)` 做 mergeSort，没有引入 host 生成的排序、rank 或替代几何数据。

新闭合 `original_sorted_key_checks` 只请求对每个 cell 的完整排序结果检查相邻严格递增。当前 pinned Batteries 的 `List.IsChain` decidability 确为相邻递归，未化为所有 row pairs。新泛型引理通过现成 `List.isChain_iff_pairwise`、`List.mergeSort_perm` 与 `List.nodup_ofFn` 得到 key injectivity；排序的 permutation 保留了所有原 row。

随后证明原 row 顶点集合相等必然给出 bitmask key 相等，从而得到通用几何需要的 vertex-set injectivity。新 key guard 尚未对原数据执行；旧 `original_vertex_sets_distinct` 也不因此获得信用。这里没有遗漏最后一个 row、cell-local ordinal 冲突或 13 个 cell 中的任何一项；row counts 仍为原总数 28,918。

## 有限义务及现存供应者

| 必需义务 | 供应者／本候选处理 | 当前信用 |
|---|---|---|
| 原 parse success、cell shape、9-ID shape/范围 | 原 Archive 原样继承 | 本次没有新验收 |
| 所有原 gate properness | 已过 GateProper；另附最小 OwnedSource 复用补丁 | 沿 Root 已报旧 P1 PASS，不重编或转移到新上下文 |
| 所有原顶点对所有 97 gates 非负 | `OwnedSource.original_gate_checks.2` | 原闭合数据请求仍待实际验收 |
| 每个实际 facet 的完整 gate zero-set 等价 | 原 `original_pulling_checks.3` 的同型分离 | 新闭合 body 未编译 |
| mask 与实际顶点列表 membership | 新有限编码引理 | 本地 normal/kernel 已过，非 P1 |
| 每条原 row 的实际 ledger trace 成功及 pullingCheck | 新 `original_ledger_flag_checks` | 原件闭合 guard 未编译 |
| 每 cell 全 row 顶点集合 injective | 新 sorted-key 闭合 guard + 已核验有限推导 | 泛型推导本地过，原件 guard 未编译 |
| generic cellSupport = 原 actualSupport | 原 row_vertices/rawVertex_lookup/vertices_interpolate + 有限和交换桥 | 接头 source-only |
| 不同原 row 的实际交集零测 | 原 checked_pulling_overlap_null 一次实例化 | 实际实例 source-only |

`OBLIGATIONS.json` 给出逐项范围、供应者和状态。

## 可选 consumer 与已过 GateProper 的复用

`OWNED_INTEGRAL_REWIRE.patch` 的前像为
`ab58f4acc2a2ea93919d0ee37e5c63e1dba1f07fd704833fefc042d0bb61bafc`。
只将旧 pulling 模块 import/open 改为新模块。所有原 definitions、theorem headers、proof bodies 和最后 Q80/Q96/积分依赖保持字节不变。

当前 `OwnedSource.original_gate_checks` 仍整体 `by decide`，会在以后首次验收时重新做已经可靠的 gate-normal 首合取。`OWNED_SOURCE_GATE_REUSE.patch` 的前像为
`e18f481c54879b7a51346db7f3549c1ac12f393a194b79322a600e7bf89c1c8b`；只加入 GateProper import，并把原 guard body 改为首合取调用 `original_gate_normals_nonzero`、第二合取仍请求 `decide +kernel`。

GateProper 源 SHA 为 `143a038b688b7ea1eb944bcac8a917e22728adc1158e4ed6d254f7db6905fad1`。此补丁不改原 conjunction、任何 gate/point 定义或其它 proof，也没有重新运行 GateProper。两份 overlay 的精确逆替换均恢复原字节，记录在 `OPTIONAL_OVERLAY_AUDIT.json`。`build_optional_overlays.py` 仅写本目录，可重现这两个补丁。

## 实际局部验证

只验证了 `P2OriginalSaving19PullingFiniteCodes`，其 imports 为已有 Init/Mathlib list modules，未导入 Archive、OwnedSource 或任何项目 supplier：

- Lean 4.33.0-rc1，runtime commit `62eed1db4d67327ec8120be05f1a1b0847d74561`；Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。
- `lean -j1 -M4096` 正常编译 exit 0，1.490 s。
- 独立 `leanchecker --verbose` exit 0，1.657 s，重放该新 module。
- 三条公共 lemma 的完整类型/axioms 检查 exit 0，1.159 s；axiom union 仅 `propext`, `Classical.choice`, `Quot.sound`。
- helper `.olean` SHA：`edf50eb36566c65811cf876438af76c717f3d47d74c8e3ba0ce79a21b03020b8`。

先前失败完整保留：一次缺未安装的 Mathlib Bitwise cache，随后使用同 pin Init 中现成 bit lemmas；一次明确的 simp/隐式参数/import 问题，修成有限 `simp only`、正确隐式参数及 exact bit intersection；一次 leanchecker 子进程 PATH 缺 Lean，固定到同一 runtime 后成功，源和对象均未变化。没有提高预算或删除失败证据。

`LOCAL_VALIDATION.json` 绑定命令、路径、源/对象、工具、直接 import objects、全部日志与回执。这里的三 lemma audit 不是 P1 的完整 owned declarations 引擎，也没有声称实际原件、connector、optional overlays 或整条 239/249 模块闭包通过。

## 尚待主线实测的具体事项

实际 connector 没有可用的完整 Archive 依赖对象，本次没有为它重建旧供应商。closed facet/gate、ledger-flag、sorted-key guards 的实际真值、elaboration、内核成本和内存都须等待原件阶段。按 cell 分支请求闭合 proof 不等于已经分页验收成功；纯 sorting、ledger 搜索或旧几何 parse 展开仍可能需要后续分片/缓存优化。这里仅移除了不必要的逐 row adjugate/多项式证书路径，没有性能 PASS 声明。

v4 的 noncomputable getters 传播到 `Original28918.rawVertex` abbreviation、`OwnedSource.originalPoint` / `vertexId` 等位置的迁移问题仍在，两个可选 overlay 没有悄悄做这类迁移。真正采用新 Archive facade 时，应明确该时点完整来源并沿既有 strict 单 owner 引擎验收。

本次新 Lean 源未出现 `sorry`、`admit`、新 axiom、`native_decide` 或 `unsafe`。唯一新增数学桥都是有限表示/现有物理支撑表示之间的直接等式；最终原件 theorem 没有追加新的前提或把目标结论包装成假设。

独立 agent `/root/p26_manuscript_audit` 已只读核对冻结的两个新源，未见 ledger child、facet→gate zero-set、原九 ID、全 cell/row 量词或 support 桥的实质遗漏；该审查没有修改或编译文件，仍明确三个原件闭合 guard 待验。单独记录为 `INDEPENDENT_REVIEW.json`。
