# Cell05 56 行 gap 实现 v1

审查基线为 `40b527baa8bc54d73cdd2b26b63d3d7dbe27869b`。本次新增正式源码 `materials/p26-work/ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.lean`（5953 B，SHA-256 `d6fea35ead2155c41b91368765e4983a6c960098a0d405e2045c556c8abf94f3`）及独立审计输入 `shape_completion_runner_next_gate/owned-audits/P2OriginalSaving19Cell05AllRowGaps.lean`（2706 B，SHA-256 `9498aafa82b33b348ab622ebe98959f31363caca32a0ff6926e7cfc0ec53ea20`）。namespace 与 module 同为 `ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps`。

## 接口

仅直接导入 `P2OriginalSaving19Geometry05ScalableShape` 与 `P2OriginalSaving19RowNumericsPure`。下式用 `G` 代表前者引用的 `P2OriginalSaving19Geometry05ScalableDecoding.Complete.concreteGeometry05`。原 Shape 已把它与原打包几何字符的解析及解码结果连接。

- `boundedRow05 : Fin 56 → GeometryRow` 以原 `rows` 的长度证明索引。公开 `boundedRow05_eq_raw (r : Fin 56) : boundedRow05 r = G.rows[r.val]!`。
- `boundedRowVertex05 : Fin 56 → Fin 9 → Fin 8 → ℚ` 对行内顶点位置、全 cell 顶点 ID 和坐标分别使用实际下标界。公开 `boundedRowVertex05_eq_raw (r : Fin 56) (i : Fin 9) (j : Fin 8) : boundedRowVertex05 r i j = (G.vertices[(G.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!`。
- `all_row_gaps (r : Fin 56) : 0 < gapSumOf (boundedRowVertex05 r) ∧ (boundedRow05 r).meanGap = gapSumOf (boundedRowVertex05 r) / 9`。其中 `gapSumOf` 为原 pure 谓词使用的 `Fin 9` 顶点求和。七个各含八行的闭合纯算术命题直接从原 decoded rows 和 vertices 读取，通过 `decide +kernel` 请求核验。一个有限区间拼接引理覆盖 0–55。最后用上述两个取值等式将命题传回 bounded 访问器。源码没有另附求和表、重抄顶点、Python 输出或新的数值前提。

## 核查与验收边界

源码显式定义/定理/缩写的 20 个名字与末尾 20 次 `#print axioms` 顺序完全一致，其中 5 个公开，15 个私有。完整 owned 审计由原已验 Shape 审计逐字替换两处目标模块名得到。其将序列化声明同 declaring-module 的 environment 清单全等比较，并逐条检查完整类型、axioms、unsafe/partial/axiom 标志。实际序列化名称和 generated 声明数必须在首编对象上检查；20 仅是显式源码条数。

作者本地核对两个 import、20 个显式名及 print、现成 Cell00/01 的同类有限算术与 Cell01 的 bounded 访问器、已验 Cell05 Shape 的具体命题，以及禁用项扫描。外部 Python Fraction 结果仍只是源码审查参考。十项第 3 和 5 项的原稿背景及独立读数见 `CELL05_ALL56_GAP_PLAN.md`。另需在目标宿主核对精确 128 项项目依赖；验收由 root 在新隔离阶段进行 normal、stock kernel、full owned。作者未运行 Lean 或云作业，当前无新通过收据。

这项源码只处理两个原几何条件。在三项新检查全部通过后，可按 56 行各两个子句记账。它不证明任何完整十项行、original floor、归属、覆盖、积分或 Saving19 全局端点。
