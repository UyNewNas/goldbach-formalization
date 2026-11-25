# 原 cell00 Geometry 与联合形状：本地完成

## 结果与具体范围

三个新 owner 已一次通过 normal 和独立 `leanchecker`，没有失败、重试或警告。它们覆盖已由原 parser/decoder 证明的 `concreteGeometry00`，并直接复用 Root 已验收的 `momentConcrete00` / `Moment00Shape`。

`P2OriginalSaving19Geometry00Shape` 的七条 theorem 关闭如下实际条件：dimension=8、physicalJacobian=1、56 条 geometry rows、28 个 vertices、vertexValues.size=vertices.size；对全部 `v : Fin concreteGeometry00.vertices.size`，坐标数组长度=8 且 factors 长度=10；对全部 `r : Fin 56`，simplexId=原索引、vertexIds 长度=9、原九个编号 Nodup、全部九个编号小于实际 vertices.size、factorMaxima 与 gapWeightedMeans 长度均=10。

只有这些 shape/Nat/array 条件执行新的闭合 `decide +kernel`。它们不计算任何 Rat 值关系，也未重新运行 parser、typed decoder 或 moment 的 metadata/56 行 ID/10 floor 槽位检查。既有数据、九个 vertexIds 的顺序和所有 Q80/Q96 数值均未改变。

## 完整原 CellShape / RowShape 子句

`P2OriginalSaving19Cell00Shape` 中三个无假设结论为：

```lean
cell_shape : CellShape00
row_shape (r : Fin 56) : RowShape00 r
row_shape_bounded (r : Fin 56) : BoundedRowShape00 r
```

三个声明的完整命名空间为 `ImbalancedChen.P2OriginalSaving19Cell00Shape`。

`CellShape00` 由原 `Archive.CellShape` 正文机械特化：只将 geometry/moments 绑定改为实际两个 concrete 值，cell index 改为 0，expected row count 改为 56，witness name 改为原完整 filename。其余字节不变，包括全部 geometry 条件、原 `Fin g.vertices.size` 顶点量词，以及原九项 moment metadata 的顺序与 2^80/2^96 分母。

`RowShape00` 同样只替换实际 g/m 行绑定和原索引记法，保持原八项合取：geometry ID、moment ID、九个 vertex IDs、Nodup、所有九个 ID 界、十个 factorMaxima、十个 gapWeightedMeans、十个 Q80 floor 槽位。`BoundedRowShape00` 只进一步把两个 row lookup 改为已经证明界限的读取，仍保留原 RowShape 的各个子句。`row_shape` 与 `row_shape_bounded` 直接组合几何结果和 Root 的已过 moment 结果，不重复有限 moment 检查。

原 source 为 SHA `f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49` 的 Archive，Git commit `77c23a2a530ce8d34ec79f88181817072024d4a9`。`SHAPE_SPECIALIZATION.json` 保存原正文 SHA、每项明确替换和新源 SHA；冻结脚本再次对实际最终 predicate 正文作精确比较，确认没有删减或重排子句。

## 完整有界访问接口

命名空间 `ImbalancedChen.P2OriginalSaving19Geometry00BoundedAccess` 提供实际 `boundedRow : Fin 56 → GeometryRow`，以及保持 producer 九点顺序的 `boundedRowVertex : Fin 56 → Fin 9 → Fin 8 → ℚ`。

`row_lookup_no_fallback`、`vertex_lookup_no_fallback`、`vertex_value_lookup_no_fallback`、`coordinate_lookup_no_fallback` 和 `vertex_id_lookup_no_fallback` 明确连接原 `!` 访问与带界访问。`vertexIndex` 来自实际原 row 的第 i 个 vertex ID，其范围由全量形状定理证明；没有新映射表、排序或默认编号。

最后的 `raw_vertex_no_fallback r i j` 关闭原 rawVertex 表达式的所有 lookup 层：

```lean
((concreteGeometry00.vertices[
    (concreteGeometry00.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!) =
  boundedRowVertex r i j
```

右侧 row、vertex ID、vertex 与 coordinate 访问全部带有真实界限。另有 factorMaxima 与 gapWeightedMeans 的全部 `Fin 10` lookup 等式，便于后续 RowNumerics 直接使用原数据。以上只建立访问和原数据相同，不证明 RowDataChecks、det、体积或积分。

## 本地验证与复用

复用 Geometry 的完整 303 模块与 Moment00Shape 的完整 43 模块；共享 7 模块，故共复制并逐项钉定 339 个不同源/对象，没有重编任何供应者。新终端完整闭包为 342 个项目模块。Root 的 Moment00Shape 源 SHA `1c077c3ed062c0682fe11af0b530458b734b490f4415f6d7d77323e26cd11159`、object SHA `c8c151d48f14c9ab0b416c026443ce8ed329cf3336ddcc6808edd067db82f8b6` 原样复用。

每次调用仍固定 4 GiB / 180 秒 / 1 线程，maxRecDepth=1000000、maxHeartbeats=0。Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561`，Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。每次前后核对依赖 source/object 与原 geometry/moment 两份 input 的 SHA。所有 28 条打印 theorem 的精确 axioms 都只含 propext、Classical.choice、Quot.sound；没有额外公理。

| owner | normal 秒 | kernel 秒 | normal 峰值 bytes | kernel 峰值 bytes |
|---|---:|---:|---:|---:|
| P2OriginalSaving19Geometry00Shape | 6.309 | 3.036 | 2321928192 | 1988321280 |
| P2OriginalSaving19Geometry00BoundedAccess | 2.523 | 2.749 | 2210074624 | 1871331328 |
| P2OriginalSaving19Cell00Shape | 2.082 | 2.318 | 2210320384 | 1875959808 |

源与对象 pins：

- `P2OriginalSaving19Geometry00Shape`: source `73da3b7c6a119f53a7689b2b1bb4eb720af7aaed503864dfa5a6b97ee15085eb`; object `18e36ecc97bd6b4ece19875ede447d9e9731107ae6f0d117671ff366662921e2`.
- `P2OriginalSaving19Geometry00BoundedAccess`: source `b89ebc2dcef5d4bb020c3c815c43f2cfab6211a40f334afc36bfeaab6bcd84b5`; object `d847520e35d24b90b61ebb8e5864bd559ff9c780b281d3439f9f557694f48112`.
- `P2OriginalSaving19Cell00Shape`: source `fbd5bf8efe3cef8d1647fbab75450e6b320688ac0646f136a7fc39615f8d1a4b`; object `ffe2c3e36ebd07610dd969acd3d0a145915cae239a3f1a66a347374e04f3b7ff`.

完整环境无关 canonical source closure SHA 为 `f2388a69565391ed35be49f90383965a8eb47aec2bc3591ffab88f06f83abb50`。

## 发布与尚待接线

`DELTA_WHITELIST.json` 只收本次三份新 Lean 源、生成器、回执及来源指纹；不重复 339 个借用源，不含对象或原 raw input。`FULL_SOURCE_CLOSURE.json` 固定全部 342 个模块供复用核对。本轮没有 P1 调用、没有主仓改动，也没有重新核验任何成功供应者。

这次证明是 concrete values 的完整 cell00 shape 与联合 row shape。正式 `Archive.CellShape 0` / `Archive.RowShape` 的结论仍需新版 Core/input maps/geometry/moments aliases 与这些具体值接线；本包明确不声明已经完成该步骤。其余 12 cells、数学 floor 正确性、RowDataChecks、pulling、积分和 P2.6 总端点均不在本次通过范围。
