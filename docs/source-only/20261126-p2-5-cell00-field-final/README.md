# cell00 最后 FieldDecode owner：数组遍历表达式修复

**SOURCE_ONLY / 尚未编译 / 无新增形式化信用。**

本包仅为 `ImbalancedChen.P2Saving16Cell00FieldDecode` 提供新的最后组合源码候选。旧 attempt003 源码、失败证据及十个已经通过的分块源码保持不动。原三 ecfc owner 继续按原收据复用，最后一个失败 owner 的任何同名对象都不能作为成功输入。

## 实际失败与分类

P3 task `9c17e910ad6f41d8905ba7b17d4d7d78` 的最后 owner normal 失败。已核对完整 `NORMAL.log`：1708 B，SHA256 `623cd44b8f00065842328db445925797cbe3e3ccf8946cc92e12ded6a6a18e0b`。原文件在本包 `attempt003/NORMAL.log` 中逐字保存。两条错误均位于原源码第 43 行 `rawRoot_decoded`：一条未解决目标，一条 kernel excessive memory consumption。未解决目标中保留的是：

```lean
List.mapM rationalArray rawVerticesItems
List.mapM decodeSimplex rawSimplicesItems
```

已完成的字段等式及两个现成映射接口则使用 `Array.mapM`。这与原 decoder 对 vertices/simplices 的定义一致。当前问题归类为**形式化表达式连接**；没有新增手稿中遗漏的数学推导，也没有据此认定手稿存在实质证明缺口。

记录的失败 RESULT SHA 为 `00ae4f5be311670b1538e934574a79b56ae0808253711ae1e0c606095d6dfdf0`。本包冻结时实际完整 normal 日志已读取，完整 RESULT 和前十三个已接受 owner 的所有对象、阶段证据由执行驱动单独验证。聚合失败不抹去其已经完成的独立 owner 证据，也不能充当聚合成功。

## 唯一的可执行修改

最后一条证明由：

```lean
simp [rawActive8, rawVertices, rawVertexValues, rawFaceLedger, rawSimplices]
```

改为：

```lean
simp [-List.mapM_toArray, rawActive8, rawVertices, rawVertexValues, rawFaceLedger, rawSimplices]
```

其余可执行源码逐字相同。四个公开 theorem 的 statement 前缀与声明顺序、前三个完整 theorem 命令、九个直接 imports、namespace、scoped simp 激活及 local simp 名单均保持。`STATEMENT_IDENTITY.json` 保存精确比较，`PROOF_BODY_DELTA.patch` 给出与旧 `ce7e0131…` 源码的差异；另有如实更新的 SOURCE_ONLY 说明注释。

该变化只在最后一次化简中禁止通用数组到列表的正规化，使 `vertices_mapped` 和 `simplices_mapped` 两条原有闭合数组等式保持可匹配。它没有修改标准库或原 decoder，没有重新解析字面量，没有改变字段、数组内容或顺序，也没有新增泛型桥接定理。

## 已有工作和标准库接口复用

仓库的既有 `P2OriginalSaving16DecoderCompose.lean` 已经用 `exact List.mapM_toArray` 建立 `rationalArray_arr` 和 `decodeArray_arr`。精确 Lean v4.33.0-rc1 标准库源码也已在仓库中，无需再次获取或重新证明：

`docs/source-only/20261102-certificates-l/compact_table_cache/provenance/local-lean-v4.33.0-rc1/Init__Data__Array__Lemmas.lean`

该文件 SHA256 为 `d3d343ae6aec3ee4de41c7008e4391a923befa309428a5aea8681e6c47f32721`；其中 `List.mapM_toArray` 带 `[simp]`，结论正是将 `l.toArray.mapM f` 转为 `List.toArray <$> l.mapM f`。同文件的 `Array.mapM_eq_mapM_toList` 没有 simp 标记。`DEDUP_AND_API_REVIEW.json` 记录检索与复用依据。

## 精确源图与执行边界

| 范围 | 数量 |
| --- | ---: |
| 整个已有 Field composition bundle 的项目模块 | 22 |
| 新隔离库复用的既有依赖对象 | 21 |
| 本次唯一 normal/replay/full-owned 目标 | 1 |
| 最后 FieldDecode 的实际项目导入闭包（含自身） | 18 |
| 保持不变的公开 theorem 结论 | 4 |

完整 bundle 比最后目标实际导入闭包多出的四个模块属于 PayloadBinding/DirectParse/SourceJsonFuel/StringCharBinding00 分支，保留它们是为了原 composition 证据的完整复用，不能错误地要求最后 owner 的 AUDIT 导入它们。`SOURCE_SELECTION.json` 分别记录这些集合。

后继驱动必须仅编译本包选定的最后 owner。其他十个 split owner、三份原 ecfc owner 和八个基础对象均复用实际已接受对象；不能对它们重新 normal 编译，也不能重新执行已完成的 replay/full-owned gates。完整 owned 审计继续覆盖 private/generated 声明，接受范围仍受普通 strict normal、独立 kernel replay、完整 owned audit 三门约束。当前编译资源条件不改变；此源码候选是否同时解除 memory failure，必须由真实三门结果确认。

## 与 1106 稿的对应范围

已重新核对 1106 英文稿 `eq:current-eighth-saving`、`num:simplex-moment` 及相邻有限多面体说明。前者保留 eighth-cell saving 的因子 4、两个 residual 和八个坐标因子；后者说明精确顶点、原不等式、面关联、pulling triangulation 及单纯形矩的顺序。当前补丁只修复读取这些既有证书字段的最后组合接口，不增加或修改这些数学断言。

即使后续本 owner 通过，它建立的也只是 `decodeCell rawRoot = .ok cell00Payload`。原字符串解析、原 archive 绑定及算术/source-facts 传递仍由已冻结五 consumer 的真实 gates 建立。完整 P2.5、所有十四 cell、source-cell 成员关系及 pulling ownership 没有在此提前接受。

## 静态审查

`p25_cell00_finite_guards` 已独立核对单行变化、四结论/前三命令/九 imports 的字节身份、原 decoder 与标准库 API，并在读取完整失败日志后通过源码/证明方案审查。静态审查只支持此源码候选进入后续受控验证，不等同于编译、replay 或正式证明接受。
