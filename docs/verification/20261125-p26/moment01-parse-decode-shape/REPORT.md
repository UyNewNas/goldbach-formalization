# Cell 01 原矩文件：完整解析、类型解码和形状证明

## 已证明的范围

生产名称 `ImbalancedChen.P2OriginalSaving19Archive.momentPacked01` 由原样 v4 loader 和 Data01 源读取精确原件。本地无假设定理为：

```lean
SourceJson.parse (String.ofList momentPacked01.toList) = .ok momentRootValue

(SourceJson.parse (String.ofList momentPacked01.toList) >>= decodeMoments)
  = .ok momentConcrete01
```

两者均使用原 SourceJson reader 和未经修改的 ArchiveSchema。完整 75,094 个 ASCII 字节全部进入证明；原根对象末尾位置为 75,092，尾部 CRLF 另由原 `white` 规则消除。原 reader 初始 fuel 为 75,095；RawPlanner 提供的候选通用 root fuel offset 为 193，实例化为 `74902 + 193`，不以 bytes 长度代替解析器的递归条件。

实际数据包含九个 metadata 字段及 144 条 records，保存 1,440 个 Q80 整数和 288 个旧/新 Q96 整数。所有字段均由原 `decodeMoments` / `decodeMomentRecord` 的闭合 Lean 等式绑定，未删除值，未用成功标签替代具体返回值，未以默认记录补齐。

`Moment01Shape` 进一步证明实际 cellId=1、原完整 geometry witness 文件名、dimension=8、verticesPerSimplex=9、factorCount=10、logDegree=6、expDegree=3、两个原整数分母 2^80/2^96，以及全部 144 行的实际索引、simplexId、十个 Q80 槽位与有界读取等式。

这些结论只证明原件数据的解析、解码、形状与索引。保存的 Q80/Q96 数值正确性、原 `Archive` aliases 接线、几何正确性和 P2.6 积分终点未由本包证明。

## 输入与复用

原件：`eighth-third-moment-refinement-20261009-a23-low-01.witness.json`，75,094 bytes，SHA256 `03e9360189414e240818a191e5b53102aa5e8c3a1e7c18fbd8553ba020078d8c`。

该成员来自公开数值证据 ZIP，并与既有 26-input 清单逐项匹配。归档仅选取 HTTP ranges，未声称核验完整 ZIP 的 hash。原字节复制到本候选的 `goldbach-research`，Lean cwd 为相邻 `project`，保留生产 loader 的相对路径和 CRLF。每次 normal/kernel 调用前后固定原件、副本、源及依赖对象 SHA。

七个不同供应者直接复用原对象：PackedChars、SourceJson、CharInputBridge、SourceJsonCharInput、通用 ParseFromValue00、原 PackedLoader、真实 ArchiveSchema。没有重编任何 cell00 数据、解析或解码 owner，也没有重编 Mathlib。生成器和 proof templates 来自已接受 cell00 版本；本包记录全部原件 SHA、明确的 00→01 名称/数值替换及真实 lexical plan。RawPlanner 只提出候选；所有声称的字段、区间、整数及解析等式均在 Lean 内核确认。

## 本地验证结果

| 阶段 | 新 owner | 普通编译总秒数 | 独立内核总秒数 |
|---|---:|---:|---:|
| 完整纯解析 | 40 | 165.258 | 70.800 |
| 真实类型解码（包括抽出的通用组合引理） | 40 | 187.545 | 192.492 |
| metadata/144 行形状与索引 | 1 | 3.273 | 3.740 |

总计 81 个新本地 owner、88 个完整项目源（7 个供应者复用），817 条 `#print axioms` 均只含标准 `propext`、`Classical.choice`、`Quot.sound` 或空集合。此数量是打印的定理记录，不冒称 P1 对所有 generated/private/environment-owned 声明的严格审计数量。

每个调用固定 4 GiB RSS、180 秒、1 线程，未增加预算。成功 normal 最大峰值 2,376,052,736 bytes，独立 kernel 最大峰值 2,040,979,456 bytes。Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561`，Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。

## 唯一失败与修复

144 条记录和整体 typed decoder 已通过后，最终 parse/bind 直接使用 `congrArg`/`trans` 的应用发生 elaboration 内存越界：12.581 秒，采样峰值 4,296,650,752 bytes，未产生成功对象。日志已到达 `typed_whole_after_opaque_decoder_application`，故故障属于最后组合表达的资源问题，未观察到数据等式失败。

修复将 cell00 已证明的 `parse_decode_of_parse_and_decode` 原证明块逐字抽为无数据模块 `P2OriginalSaving19MomentParseDecodeBridge`（只依赖 Schema）。最终 owner 使用这个抽象引理，避免在具体大值上推断组合。具体 Moments 值与最终两个定理陈述字节不变。144 条记录证明全部复用，无成功 owner 重编。新 helper 与修复后的最终 owner 均在原预算内通过 normal/kernel；失败源、日志与回执保留在归档中。后续 cells 可直接复用这个无数据 helper 对象。

## 信用边界

本包是实际源和对象的本地普通编译及独立内核证据；没有提交新的远端编译，也没有转移或伪造 P1 回执。生产源基线为 `94148a71e2bc9b6627a98eeebd961f78076b4f08`，新增源作为本次候选单独发布。原 Core、Consumer 和分析供应者不变。

完整环境无关 source closure SHA256：`724a07b685acf851a8e87d68e7422444a7c80205bba71de0b6492e64045314f5`。`FINAL_RESULT.json`、`FULL_SOURCE_CLOSURE.json`、阶段回执、失败记录及发布白名单给出精确路径与指纹。
