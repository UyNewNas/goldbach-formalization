# geometry00 原 parser 与真实 typed decoder：本地完整结果

## 已关闭的两个最终义务

以下两个无假设定理均通过 normal 与独立 `leanchecker`：

```lean
ImbalancedChen.P2OriginalSaving19Geometry00Decoding.decode_originalGeometryJson00 :
  decodeGeometry originalGeometryJson00 = .ok concreteGeometry00

ImbalancedChen.P2OriginalSaving19Geometry00Decoding.geometryPacked00_parse_decode :
  (SourceJson.parse (String.ofList geometryPacked00.toList) >>= decodeGeometry) =
    .ok concreteGeometry00
```

第一个左侧是已验收完整原 JSON AST；第二个左侧直接使用正式 v4 候选生产 FQN `ImbalancedChen.P2OriginalSaving19Archive.geometryPacked00`。二者都使用真实 `ArchiveSchema` 中原样的 `decodeGeometry`。原 `SourceJson.parse`、原字节输入、typed schemas、各 decoder 的定义与错误分支均未修改。

右侧是具体 `Geometry` 值，不是 success tag 或默认值。公开名称为 `ImbalancedChen.P2OriginalSaving19Geometry00Decoding.concreteGeometry00`。它包含 dimension=8、physicalJacobian=1、28 个原顶点、28 个原 VertexValues、56 个原 GeometryRow、11 个 facetOriginalIndices、11 个 facetVertices 数组以及 39 条 FaceRecord。这里说明具体字面量内容；单独的数组 shape/范围/Nodup 数学检查没有在本包声明通过。

最终 packed owner 源 SHA `da4ae4ec3a769f1d1dd20b32f6cf089fe98b3825436bc24871e75e45a65f91b9`，object SHA `4f060b3667b9b20f18ce5f21de6b63c140b661cc35f630d9742728cfb2578bff`。normal 1.679s / 2,196,860,928 B；独立 kernel 2.153s / 1,865,256,960 B。AST decoded owner 源 SHA `4f955bb7b3197d3388aba0e154f9cab5e9e8679521aad67573500385a306e706`，object SHA `f6439e01827e3260c2636ea5df154a5b33c2b0102749538f8ff0582e1f21c0e4`。

## 字段与顺序

`Geometry` 的全部八个 schema 字段均由原 decoder 绑定。每个 `GeometryRow` 仍包含 simplexId、原顺序九个 vertexIds、physicalVolume、meanGap、十个 factorMaxima、十个 gapWeightedMeans、jensenBound 和 jensenFloorQ96。FaceRecord 的 vertices、dimension、pivot、facetSets 与 simplices 均保留。所有 Rat 目标保持原文本的 numerator/denominator 表达式，未用 host 浮点、Fraction 或 gcd 规范化替换数据。

原 root JSON 的 14 个字段仍保留在复用的完整 AST 中。原 `decodeGeometry` 只读取其中对应八个 schema 字段；其他原始字段依然由完整 parser 绑定，不把它们误称为 decoder 新增读取的字段。`facet_original_indices` 保持原 Nat 编号，未擅自转换成 Fin97 gate 编号。

具体 row、顶点等值从已过原 parser 的 `*ChunkNNNPush []` 使用 `List.get` 提取，携带闭合 index bound；没有 `getD`、fallback 或外部解析结果作为假设。每个 Push/list.reverse 等式按原顺序组合，56 条 row 分 14 块累积。首四条 row 的原 accessor/typed definition 与原 decode 陈述在失败整行版本和新独立 row owner 中逐字一致，记录见 `TYPED_RESULT.json`。

## 资源修复只改变证明表达

首个完整 `decodeGeometryRow` 直接 `decide +kernel` 曾触及 4 GiB 限制。阶段 marker 明确停止在 row000 的整行 decoder 证明；数据定义已经完成。没有提高预算或重跑这个整行目标。

替代形式先证明通用 `original_rational_fraction_of_chars`：原 numerator 不含 slash、原 `SourceJson.intChars` 对 numerator/denominator 的成功结果，以及 denominator 非零，推得原 `parseRational (String.ofList (ns ++ '/' :: ds))` 的精确 Rat 结果。证明使用 `String.toList_ofList` 与 List.takeWhile/drop 的既有定理消除字符往返，原 split 和所有错误条件没有放宽。另有原整数型 rational 分支的通用等式。

实际每行用原 getter 确认 scalar 文本，闭合证明 `intChars` 与非零 guards，再应用该通用桥。两个实际十元 Rat 数组及两个 Nat 字段各自做原 decoder 的闭合 kernel guard；Q96 字符串继续经过原 `parseInteger`。最终通过原 `decodeGeometryRow` 的八字段通用展开等式组合，避免重新判定整行。原始失败、两次通用桥表达修复和一次全 Geometry 组合的 Except bind 表达修复均保留。

完整 Geometry 的抽象组合定理将五个 JSON 列表与五个 typed Array 留作参数，先证明原字段 getter 和原 `Array.mapM` 绑定。最终 owner 只应用已经通过的实际列表等式，不在完整 56 行上下文中重新化简整份 decoder。最后与 higher agent 已通过的生产 packed parse 定理通过原 Except bind 组合。

## 复用、原件与可追溯性

本轮逐字复用 207 个源/对象：higher agent 冻结的 geometry parser 与 packed transport 完整 206 闭包，加一个真实 ArchiveSchema。bootstrap 逐项记录 original/copy SHA；每次 normal/kernel 前后核对所有复用源与对象，未重编 parser、transport、Schema 或分析供应商。

原 geometry00 文件为 `eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`，195,134 bytes，SHA `87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`。本地候选读取已冻结 `/workspace/p26-original-inputs/` 副本用于机械候选 quotation，保留 CRLF 与所有字符；该 staging 路径不冒充 P1 实际路径。真实生产 FQN 的 packed 数据与该原文的闭合绑定来自已过 geometry transport 证明，不靠 SHA 代替 Lean 内容等式。

Schema 源 SHA `b877c0c35ace12cd76e0ed737b3a4b1ff3917fa15c4cc32b961450ee4761418b`，object SHA `8c3b41bd6b27e92b7a3c724b5d5ee9b191b4a4079fb40bd3ff5daad34129f9cc`。原 `parseInteger` 至 `decodeMoments` 的 5399 B schema/decoder 切片 SHA `21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30` 未改。

Lean 为 `Lean (version 4.33.0-rc1, x86_64-unknown-linux-gnu, commit 62eed1db4d67327ec8120be05f1a1b0847d74561, Release)`；Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。每次调用固定 4 GiB RSS 监测上限、180 秒、1 线程、maxRecDepth=1000000、maxHeartbeats=0。normal 成功后才运行独立 leanchecker；通过后不重复核验或重编。

96 个新 owner 各有一份成功 normal 与一份成功 kernel 回执；完整终端闭包 303 个项目模块。成功 normal 合计 393.303s，kernel 合计 380.689s；最高成功峰值分别为 2,937,548,800 B 与 2,595,409,920 B。完整打印并解析 2029 个声明的精确 axiom set，全部仅含 propext/Classical.choice/Quot.sound 或空集。失败 elaboration 的错误占位输出不计入通过信用。

## 保留的失败

| owner | attempt | 结果 | 秒 | 峰值 bytes |
|---|---|---|---:|---:|
| P2OriginalSaving19ArchiveRationalChars | rational-chars-v1 | failed | 2.161 | 2149838848 |
| P2OriginalSaving19ArchiveRationalChars | rational-chars-v2 | failed | 3.695 | 2145656832 |
| P2OriginalSaving19Geometry00DecodeFields | fields-v1 | failed | 8.190 | 2296389632 |
| P2OriginalSaving19Geometry00DecodedRows000 | geometry-typed-v1 | memory_limit | 8.807 | 4299087872 |

所有失败均无 object 生成，源快照和完整日志保留。证明表达的普通错误已在相同预算内局部修复，没有改变陈述或用假设绕过数据。

## 成功回执

| owner | normal 秒 | kernel 秒 | normal 峰值 bytes | kernel 峰值 bytes |
|---|---:|---:|---:|---:|
| P2OriginalSaving19ArchiveRationalChars | 2.148 | 2.363 | 2151624704 | 1814654976 |
| P2OriginalSaving19Geometry00DecodeFields | 5.384 | 5.023 | 2303524864 | 1966436352 |
| P2OriginalSaving19Geometry00Decoded | 2.131 | 2.151 | 2197889024 | 1862860800 |
| P2OriginalSaving19Geometry00DecodedFaces000 | 2.930 | 2.429 | 2203918336 | 1863962624 |
| P2OriginalSaving19Geometry00DecodedFaces001 | 4.250 | 4.399 | 2374905856 | 2037075968 |
| P2OriginalSaving19Geometry00DecodedFaces002 | 2.863 | 3.102 | 2262224896 | 1924718592 |
| P2OriginalSaving19Geometry00DecodedFaces003 | 2.188 | 2.265 | 2199949312 | 1858019328 |
| P2OriginalSaving19Geometry00DecodedFaces004 | 2.074 | 2.093 | 2190540800 | 1853882368 |
| P2OriginalSaving19Geometry00DecodedFaces005 | 2.803 | 2.530 | 2238210048 | 1900511232 |
| P2OriginalSaving19Geometry00DecodedFaces006 | 2.473 | 2.452 | 2207121408 | 1877893120 |
| P2OriginalSaving19Geometry00DecodedFaces007 | 2.445 | 2.345 | 2194665472 | 1853145088 |
| P2OriginalSaving19Geometry00DecodedFaces008 | 1.841 | 2.114 | 2194558976 | 1846808576 |
| P2OriginalSaving19Geometry00DecodedFacetVertices000 | 2.964 | 2.903 | 2202886144 | 1863688192 |
| P2OriginalSaving19Geometry00DecodedFacetVertices001 | 2.346 | 2.421 | 2207039488 | 1863987200 |
| P2OriginalSaving19Geometry00DecodedRow000 | 4.807 | 4.627 | 2481025024 | 2140246016 |
| P2OriginalSaving19Geometry00DecodedRow001 | 6.139 | 6.209 | 2796523520 | 2454728704 |
| P2OriginalSaving19Geometry00DecodedRow002 | 4.541 | 4.359 | 2526294016 | 2184433664 |
| P2OriginalSaving19Geometry00DecodedRow003 | 4.723 | 4.134 | 2504175616 | 2154967040 |
| P2OriginalSaving19Geometry00DecodedRow004 | 4.553 | 4.461 | 2503991296 | 2162118656 |
| P2OriginalSaving19Geometry00DecodedRow005 | 4.631 | 4.032 | 2457849856 | 2116100096 |
| P2OriginalSaving19Geometry00DecodedRow006 | 4.112 | 4.096 | 2444271616 | 2102509568 |
| P2OriginalSaving19Geometry00DecodedRow007 | 6.623 | 6.257 | 2816679936 | 2472660992 |
| P2OriginalSaving19Geometry00DecodedRow008 | 4.888 | 4.606 | 2523820032 | 2181869568 |
| P2OriginalSaving19Geometry00DecodedRow009 | 4.218 | 4.131 | 2456879104 | 2114977792 |
| P2OriginalSaving19Geometry00DecodedRow010 | 4.523 | 4.283 | 2461913088 | 2119999488 |
| P2OriginalSaving19Geometry00DecodedRow011 | 4.930 | 4.425 | 2452742144 | 2102030336 |
| P2OriginalSaving19Geometry00DecodedRow012 | 7.524 | 6.427 | 2820444160 | 2478567424 |
| P2OriginalSaving19Geometry00DecodedRow013 | 4.972 | 4.919 | 2534957056 | 2193162240 |
| P2OriginalSaving19Geometry00DecodedRow014 | 4.257 | 4.581 | 2459475968 | 2117693440 |
| P2OriginalSaving19Geometry00DecodedRow015 | 4.027 | 3.946 | 2435547136 | 2094645248 |
| P2OriginalSaving19Geometry00DecodedRow016 | 6.179 | 5.862 | 2799718400 | 2458296320 |
| P2OriginalSaving19Geometry00DecodedRow017 | 4.708 | 4.458 | 2525433856 | 2184900608 |
| P2OriginalSaving19Geometry00DecodedRow018 | 3.991 | 3.623 | 2394263552 | 2053656576 |
| P2OriginalSaving19Geometry00DecodedRow019 | 5.951 | 5.310 | 2720616448 | 2378731520 |
| P2OriginalSaving19Geometry00DecodedRow020 | 4.069 | 4.006 | 2375753728 | 2033344512 |
| P2OriginalSaving19Geometry00DecodedRow021 | 5.629 | 5.904 | 2683596800 | 2341888000 |
| P2OriginalSaving19Geometry00DecodedRow022 | 6.801 | 6.899 | 2874654720 | 2532614144 |
| P2OriginalSaving19Geometry00DecodedRow023 | 7.710 | 7.015 | 2937548800 | 2595409920 |
| P2OriginalSaving19Geometry00DecodedRow024 | 4.355 | 4.259 | 2466594816 | 2124427264 |
| P2OriginalSaving19Geometry00DecodedRow025 | 4.431 | 3.913 | 2464071680 | 2122264576 |
| P2OriginalSaving19Geometry00DecodedRow026 | 5.740 | 5.550 | 2701295616 | 2359324672 |
| P2OriginalSaving19Geometry00DecodedRow027 | 4.609 | 4.543 | 2510368768 | 2168455168 |
| P2OriginalSaving19Geometry00DecodedRow028 | 4.767 | 4.654 | 2509529088 | 2169102336 |
| P2OriginalSaving19Geometry00DecodedRow029 | 4.719 | 4.478 | 2508894208 | 2167320576 |
| P2OriginalSaving19Geometry00DecodedRow030 | 5.877 | 6.189 | 2762964992 | 2421063680 |
| P2OriginalSaving19Geometry00DecodedRow031 | 4.529 | 4.575 | 2463178752 | 2120835072 |
| P2OriginalSaving19Geometry00DecodedRow032 | 4.750 | 4.424 | 2463215616 | 2121854976 |
| P2OriginalSaving19Geometry00DecodedRow033 | 4.850 | 4.312 | 2459389952 | 2118225920 |
| P2OriginalSaving19Geometry00DecodedRow034 | 4.280 | 3.941 | 2413789184 | 2063208448 |
| P2OriginalSaving19Geometry00DecodedRow035 | 5.872 | 5.906 | 2725969920 | 2384068608 |
| P2OriginalSaving19Geometry00DecodedRow036 | 4.526 | 4.433 | 2509541376 | 2167775232 |
| P2OriginalSaving19Geometry00DecodedRow037 | 4.367 | 4.239 | 2464428032 | 2121461760 |
| P2OriginalSaving19Geometry00DecodedRow038 | 4.619 | 3.994 | 2461241344 | 2119589888 |
| P2OriginalSaving19Geometry00DecodedRow039 | 4.375 | 4.173 | 2460315648 | 2118434816 |
| P2OriginalSaving19Geometry00DecodedRow040 | 4.489 | 4.117 | 2417868800 | 2065645568 |
| P2OriginalSaving19Geometry00DecodedRow041 | 5.979 | 5.233 | 2723422208 | 2381541376 |
| P2OriginalSaving19Geometry00DecodedRow042 | 4.805 | 4.449 | 2505228288 | 2163240960 |
| P2OriginalSaving19Geometry00DecodedRow043 | 6.159 | 5.975 | 2815229952 | 2474262528 |
| P2OriginalSaving19Geometry00DecodedRow044 | 4.883 | 4.550 | 2539556864 | 2198851584 |
| P2OriginalSaving19Geometry00DecodedRow045 | 4.873 | 4.354 | 2510217216 | 2164252672 |
| P2OriginalSaving19Geometry00DecodedRow046 | 4.789 | 4.622 | 2511265792 | 2169495552 |
| P2OriginalSaving19Geometry00DecodedRow047 | 4.307 | 4.228 | 2469441536 | 2126221312 |
| P2OriginalSaving19Geometry00DecodedRow048 | 4.502 | 4.142 | 2521513984 | 2179338240 |
| P2OriginalSaving19Geometry00DecodedRow049 | 4.450 | 4.295 | 2492772352 | 2146099200 |
| P2OriginalSaving19Geometry00DecodedRow050 | 4.292 | 4.321 | 2456203264 | 2114351104 |
| P2OriginalSaving19Geometry00DecodedRow051 | 4.276 | 4.180 | 2454343680 | 2112425984 |
| P2OriginalSaving19Geometry00DecodedRow052 | 4.483 | 4.083 | 2446962688 | 2105053184 |
| P2OriginalSaving19Geometry00DecodedRow053 | 4.456 | 3.928 | 2402357248 | 2048491520 |
| P2OriginalSaving19Geometry00DecodedRow054 | 6.140 | 5.639 | 2679894016 | 2337902592 |
| P2OriginalSaving19Geometry00DecodedRow055 | 4.493 | 4.059 | 2466131968 | 2123886592 |
| P2OriginalSaving19Geometry00DecodedRows000 | 1.652 | 1.974 | 2181386240 | 1844613120 |
| P2OriginalSaving19Geometry00DecodedRows001 | 1.723 | 2.058 | 2181140480 | 1845800960 |
| P2OriginalSaving19Geometry00DecodedRows002 | 1.822 | 2.127 | 2182221824 | 1846984704 |
| P2OriginalSaving19Geometry00DecodedRows003 | 1.588 | 2.049 | 2183004160 | 1848430592 |
| P2OriginalSaving19Geometry00DecodedRows004 | 1.824 | 2.149 | 2182914048 | 1849507840 |
| P2OriginalSaving19Geometry00DecodedRows005 | 1.805 | 2.015 | 2185478144 | 1850908672 |
| P2OriginalSaving19Geometry00DecodedRows006 | 1.806 | 2.082 | 2197381120 | 1852334080 |
| P2OriginalSaving19Geometry00DecodedRows007 | 1.869 | 1.951 | 2188136448 | 1853333504 |
| P2OriginalSaving19Geometry00DecodedRows008 | 1.785 | 2.005 | 2189455360 | 1854509056 |
| P2OriginalSaving19Geometry00DecodedRows009 | 1.773 | 2.130 | 2192744448 | 1855856640 |
| P2OriginalSaving19Geometry00DecodedRows010 | 2.000 | 1.968 | 2192834560 | 1857196032 |
| P2OriginalSaving19Geometry00DecodedRows011 | 1.621 | 2.051 | 2191917056 | 1858510848 |
| P2OriginalSaving19Geometry00DecodedRows012 | 1.611 | 2.060 | 2193387520 | 1859366912 |
| P2OriginalSaving19Geometry00DecodedRows013 | 1.839 | 2.040 | 2195120128 | 1861496832 |
| P2OriginalSaving19Geometry00DecodedVertexValues000 | 4.263 | 4.210 | 2288492544 | 1950367744 |
| P2OriginalSaving19Geometry00DecodedVertexValues001 | 3.959 | 3.790 | 2261049344 | 1944801280 |
| P2OriginalSaving19Geometry00DecodedVertexValues002 | 3.858 | 4.045 | 2271936512 | 1945047040 |
| P2OriginalSaving19Geometry00DecodedVertexValues003 | 3.659 | 3.928 | 2282442752 | 1978466304 |
| P2OriginalSaving19Geometry00DecodedVertexValues004 | 3.434 | 3.678 | 2255654912 | 1945026560 |
| P2OriginalSaving19Geometry00DecodedVertexValues005 | 3.651 | 3.994 | 2255757312 | 1945468928 |
| P2OriginalSaving19Geometry00DecodedVertexValues006 | 4.199 | 4.028 | 2272735232 | 1945829376 |
| P2OriginalSaving19Geometry00DecodedVertices000 | 8.968 | 5.367 | 2236301312 | 1912496128 |
| P2OriginalSaving19Geometry00DecodedVertices001 | 5.117 | 5.464 | 2255859712 | 1944031232 |
| P2OriginalSaving19Geometry00DecodedVertices002 | 4.860 | 4.792 | 2242990080 | 1910743040 |
| P2OriginalSaving19Geometry00DecodedVertices003 | 3.554 | 3.667 | 2256457728 | 1944264704 |
| P2OriginalSaving19Geometry00PackedDecoded | 1.679 | 2.153 | 2196860928 | 1865256960 |

## checkpoint 与边界

`TYPED_DELTA_WHITELIST.json` / `TYPED_PACKAGE_MANIFEST.json` 只打包本轮新增 typed 源和证据，以及来源指纹和失败快照；不重复 207 个借用源、不含 object 或 raw input。完整 303 模块的环境无关 canonical source closure SHA 为 `d751469f429b88c522c8c4007f46b6235712b492d6984c43b18a854ab3f4685c`，详见 `FULL_SOURCE_CLOSURE.json`。原件可复用 parent 已提交的 cell00 input archive；不另造原件。

这次结果是 geometry00 的真实完整 parse→typed-value 绑定。本包没有运行 P1 strict，也未证明其余 12 个 geometry cells、26 文件的整体验收、旧 Core 原 String literal 与新输入的闭合等式、全部 shape/Nodup/range guards、Q80/Q96 floor 数学正确性、pulling overlap/coverage、积分下界或 P2.6 最终端点。正式新版 Core/all-input maps 完成后，parent 可把生产 index0 定义与本包已闭合 theorem 接到 `geometryParse 0`；本包不导入旧 Core 或216个数学供应商伪称这一步已完成。
