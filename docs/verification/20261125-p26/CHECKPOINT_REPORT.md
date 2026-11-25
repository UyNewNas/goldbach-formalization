# P2.6：原件解析与高阶矩推进检查点

本检查点继续 1106 稿的原始十三组 / 28,918 行 Saving19 证明。**P2.6 尚未完成，原件数值 guard、全部输入和最终积分端点尚未闭合。** 生产 Archive facade 仍为 SHA `f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49`；本批不冒认整节点绿色。

## 已有 P1 严格验收

高阶矩主接口 `P2OriginalSaving19HigherMoments` 的重试通过普通编译、独立内核重放以及全部环境所属声明的完整类型与公理审计。验收对应实际源 commit `bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3`，源 SHA `9b2253f2ae8174e6ab00fd60c276643823f947e75145ca23e00ec5ccd458524c`，包含 89 项 owned / 89 项 public exports。此前失败仅修掉原证明已经完成后的多余 `simp only [inv_pow]`；失败源和回执保留，已通过的结构供应者没有重编。

GateProper 的既有成功也已取回完整证据：实际源 commit `e3824f6d30f5ce193c8aa86a725bfb77d941d5d7`，3 项 owned / 1 项 public export。它只证明所有原 gate normals 非零；原顶点对全部 gates 的非负检查仍未完成。

两者全部 172 个证据文件保存在 `facade-retry1-and-gate-evidence.tar.xz`，183,684 B，SHA `e948d480b52d2f022f3286f9cb042bd655d6ded0606d817b625b139c3428c764`。详见 `FACADE_RETRY1_AND_GATE_EVIDENCE.json`。旧失败与新成功按各自源 commit 保存，没有迁移或改写信用。

## 本地通过的完整纯解析

几何 cell 00 的完整 195,134 字符原文件已通过未修改 SourceJson reader 的纯解析证明，覆盖全部 14 个字段以及最后的 CRLF。此包新增 156 owner，项目闭包 164 个模块，1,747 条新 theorem 均打印公理；normal 与独立 leanchecker 均成功。这一冻结包绑定旧 `geometryChars00`。单独的 `geometry00-packed-transport-local-evidence.tar.xz` 随后增加 40 个 owner，复用全部 166 个既有供应者，以 37 组 / 186 个连续片段闭合完整旧字符列表与生产 `geometryPacked00.toList` 的等式，并搬运原完整 parse 定理。新增 606 条 theorem 均有公理输出，normal/kernel 通过；没有重编供应者或重跑原 parser。最终生产解析模块 source SHA 为 `45fe4bebeced2ec965e8e6ade00bfa191d2ded4ef11f876f1a1aa4651e93d324`；真实几何 typed decoding 另行继续。

矩 cell 00 的完整 28,999 字符原文件也已通过纯解析，直接绑定生产同名 `momentPacked00.toList`。新增 19 owner，源码闭包 24 个模块；其余对象只读复用。原 56 条 JSON 记录、元数据、重复键检查、分隔符、原 fuel 和末尾内容都保留。此冻结纯解析包与后续 typed checkpoint 分开保存。`moment00-typed-decoder-local-evidence.tar.xz` 另提供 17 个新 typed owner 的本地 normal/kernel 成功证据：无假设地证明原 parse 结果经原 `decodeMoments` 得到具体 `momentConcrete00`，含全部 9 个 metadata、56 条原记录、560 个 Q80 及 112 个 Q96 整数。最终完整源闭包 42 个模块；复用原 pure 层与真实 Schema 对象。生产路径已安装这些源，但尚未给予 P1 strict 或数学 floor 正确性信用。组合步骤的一次资源失败及抽象 mapM/bind 修复也完整保留。

纯解析源、生成器、正常/内核命令、全部成功与失败日志分别在 `geometry00-pure-parser-local-evidence.tar.xz` 和 `moment00-pure-parser-local-evidence.tar.xz` 中；完整逐文件清单为 `LOCAL_PARSER_CHECKPOINTS.json`。未重复保存既有原始输入：使用已发布的 `original-cell00-inputs.tar.xz`，SHA `c5dcb869db6ef12e16cd3c2414f0ede0d50842dcc5fb3b00cbb1d52258ec885b`。

这些是固定 Lean / Mathlib、4 GiB / 180 秒 / 单线程的本地诊断，不是 P1 all-owned 验收。历史失败全部保留，成功块未因最后组合步骤而重算。没有把单 cell 结果外推为全部 26 个输入通过。

## 真实 schema 拆分

新的 `ArchiveSchema` 从 v4 Core 中逐字移出 `parseInteger` 到 `decodeMoments` 的 5,399 字节；这一片段 SHA 保持 `21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30`。namespace、完整字段类型、defaults、derive、原 rational 解析与 decoder bodies 均未改。新 schema 已本地 normal/kernel 通过。

生产源码同时安装新的 Core：只导入 Schema 并移除原片段，其 getters 和两个 parse-ofList 桥保持原样。新 Core 仍未编译；旧 Core 的验收不能移交给新 owner。这样每个原件的真实 typed decoding 可以先导入小型真实 schema，不必展开所有 26 个输入及整个解析分析闭包。

首批 7 个 v4 输入 owner 已全部通过 P1 strict，包括最大 14,461,008 B 几何输入；完整 499 文件证据为 `archive-v4-first7-evidence.tar.xz`，SHA `4b1ee5569909112b72cb727edae5434a07bf659ca89398aac1defe86a561a459`。余下 24 个不相交 owner 已分为三批排队，包含所有其余原文件和 PackedInputs，排除旧 v4 Core。

这些 v4 输入任务仍固定到 `07826355aedef5a01e76c36ad304bc6b115f3c2b` 和原 runner。该任务只运行前七个输入 owner，不运行旧 v4 Core。余下不变输入可以继续在该真实旧 commit 下验收；新 Schema / Core 必须各有新上下文的验收。跨 commit 复用必须核对原 receipt 的真实 commit 与相同 source/object/import/runtime/raw input，不能重贴标签。

## 有限计算与 pulling 的既有结果复用

两个新的 prefix 辅助模块已本地 normal/kernel 通过，复用原 `P2Winner9HomogeneousRecurrence.prefixCoefficients` 和其正确性，不重造递推。第三个模块将表值接到原 `authorMoment` / `rationalMoment`，目前为独立审查过但未编译的源码。实际 row 的整数编码、全部 Q80/Q96 floor 仍待核验，不能截断负值来凑非负编码。

新的 pulling 有限表示 helper 已本地 normal/kernel 和三条公共引理审计通过；实际 `PullingReuse` 接头仍 source-only。它调用既有 `checked_pulling_overlap_null`，保留原完整顶点集合、原九个 ordered row IDs、实际 face ledger trace 和全 cell/row 的量词。三个闭合原件 guard——facet/gate 完整零集、ledger flags 成功、完整 row keys 排序互异——尚未验算。原最终零重叠 theorem header 不变，没有用目标结论作假设。

两个最小 consumer overlay 仅留在 `pulling-reuse/` 供之后采用，没有安装：OwnedSource 首合取复用已验收 GateProper；OwnedIntegral 只更换 import/open 以消费同型 null-overlap 结论。旧特定 polynomial_faces 声明没有被冒认为证明完毕。

## 稿内范围与后续闭合点

本批对应 1106 稿 `numerical-appendix.tex` 的原不等式验顶点、face incidences、pulling、精确 simplex moments，以及 `argument.tex` 允许对非负 saving 使用合法 subset 下界的段落。新字符串/列表组合、整数表示与有限代数引理服务于这些原计算；没有引入稿外解析估计。

仍需完成全部 26 个原文件的真实解析与类型解码、shape/id/count、28,918 行原 determinant/physical/means/maxima/Jensen、Q80/Q96 floors 与替换总和、实际 ownership/integral 和最终端点。所有状态逐项保存在 `STATUS.json`；`p26_complete` 保持 `false`。
