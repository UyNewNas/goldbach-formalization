# 398 个缓存目标与九个先决模块的输入审查

历史输入静态复核日期为 2026-11-13。新机器是否实际命中、102 个模块能否通过 Lean 内核和声明审计，须以新 GitHub 作业证据判定。

## 实际输入

独立从 67075207 字节的原 T01 `CHECKPOINT.json`、ZIP 中央目录、r3 原实物清单和 r4 守卫命令交叉重算。398 个 goldbach 模块来自 MathlibNt 336、AnalyticNumberTheory 44、PrimeNumberTheoremAnd 18。每条历史编译命令与 r4 实际命令在项目根替换后逐 token 一致。所有 1198 项必需输出都在选择中，1198 个真实 Lake 输出描述都匹配各自侧文件。r3 的 800 条公开或拆分 olean 及侧文件记录逐条匹配。398 份源加 3192 个 facets 共 3590 个唯一原始 payload、1277167228 字节，所有 ZIP 成员描述已逐一交叉核查。实际 setup 中包导入名的历史计数合计 1472166 次出现；当前运行还须算每个按原分组排列的物理文件散列。细目见 `HISTORICAL_INPUT_CROSSCHECK.json`。

固定 goldbach 源 `PrimeNumberTheoremAnd/Defs.lean` 首行导入 `Architect`。r4 在 Mathlib 官方缓存准备结束后执行九次 LeanArchitect 编译，再生成引用它的 goldbach 对象。只恢复 398 的工作流会在查询这项依赖时遭遇空缓存。另冻结同一 T01 原归档中九个先决模块的 153 项、11552292 字节。核过它们与 r4 的九行真实 argv，以及 r3 的 54 条 olean/server/private 与三个侧文件身份。八行原分类允许复核，余下一行原分类仍为 `PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED`。[固定依赖源](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/PrimeNumberTheoremAnd/Defs.lean#L1)

`Architect.Command` 有一条显式 `public import Lean`，包括工具链的隐含 Init 依赖。原 144 字节 setup 中外包 `importArts` 为空，原收集器的 `bool(imports)` 因而为假。按 ZIP member offset 精确取回 1650 字节源码、144 字节 setup 和 2777 字节 trace，分别重算 CRC、SHA 和长度。真实 trace 为 `synthetic=false`、`depHash=ab6e792d950a1c14`，其旧 toolchain 输入记载 Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561` 和 Lake 输入 hash `8fa8fbe052c71a8e`。原 source、编译命令绑定、原 setup、七项输出描述及同批另外两个运行的交叉事实均保留。T01 日志小归档的完整散列 `62279b4c...` 与首次采集记录一致，本次取出 419 字节 `install-toolchain.log`。它记载官方 URL、目标 x86_64 Linux 和完整版本提交。该官方压缩包的资产 ID 为 478017041、SHA-256 为 `25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210`，上传和最终更新时间均早于原运行。[叶模块固定源码](https://github.com/hanwenzhu/LeanArchitect/blob/78dd66840d3efe8c824c699fc03381cec817c271/Architect/Command.lean#L1-L3) [官方发布资产](https://api.github.com/repos/leanprover/lean4/releases/assets/478017041)

根任务已批准仅此叶的独立规则 `ARCHITECT_COMMAND_LEAF_RULE.json`。该规则以官方发行为单位绑定两个运行使用的核心库来源，检查已有的全部 11 个二进制及 8 个 ABI 对象，排除非工具链搜索根提供同名核心模块。历史 checkpoint 中没有逐个核心 olean 的散列，故只在新 GitHub 作业确证上述来源、stock no-build 和原始缓存字节后承认当前编译缓存资格。保留旧隔离记录和单独资格回执。历史原发行包、本期冷编或新的证明资格均未由本次静态审查产生。

## 拦截与运行顺序

历史 r4 守卫的 532 行真实调用中，Lean 查询只有完整单参数 `--githash` 和 `--print-prefix`。两种真实工作目录为项目根及 RUNNER_TEMP，后者出现一次 `--githash`。官方 `setup-file` 通过 Lake 自己的 `Lean.parseImports'` 读取模块头，此处无需另放行 `lean --deps some.lean`。[固定 Lake 实现](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/lake/Lake/Build/Module.lean#L1394-L1408)

两调用方共享 11 个引导源和 11 个对应 C 编译命令。原 `clang -o .../cache @.../cache.rsp` 也是实际必需调用，只允许同一 link 输出、响应文件和根映射后的 1906 字节内容。已定段取回原 `T01_CACHE_LINK.rsp`，重验 SHA-256 `05b5823f...`、CRC 与长度。实际对象操作数正好是 10 个 Mathlib Cache 目标与一个 Batteries OpenPrivate，余下均为固定工具链链接参数。运行中其余未知 argv 均须在原 wrapper 的 `os.execv` 前拒绝。P2 在资格通过后才允许清单中的 102 个项目源、FinitePiPilot 与 CandidateAudit；Stored 只允许新 031–041 的 11 源与 StoredBatchAudit。两个 scope 都需做原 runtime 探针。

| 要检验的调用或修改 | 所需行为 |
|---|---|
| goldbach 源、LeanArchitect 源、另一个语法拼法、相对路径、含 `..` 或通过 symlink 的同一目标 | 在编译器执行前拒绝，记录失败并中止 |
| Stored 父、000–030 旧源、它们的产物输出目的地 | 全流程拒绝编译，保留可执行的父对象内核重放 |
| 标准项目编译命令在资格或 source admission 回执产生前出现 | 拒绝并中止 |
| 未知工具/源、`--stdin`、`-`、未知选项、任意 `@`、嵌套响应、伪装为查询并附带源或输出 | 拒绝并中止 |
| 改写唯一 cache.rsp 中一个 object、flag、历史根或大小 | 拒绝并中止 |
| 资格后调整任一真实源码、动态生成的 audit、选定 argv 的输出或 `--setup` | 拒绝编译或使比对/验收失败 |
| 换 guard、wrapper、policy 或 `slot`，插入非许可嵌套编译、log 与预执行事件不同步 | 保留原 guard 拒绝及独立回审失败 |
| 任一真正的 no-build miss，换掉 `.trace/.setup/.hash`，添 `.nobuild` | 资格失败，保留原日志、失败成员和原始字节，零自动冷编 |

stock `leanArts` 是原始完整构建 facet。固定 Lake 缓存回放在正常模式检查当前依赖 hash；旧模式才使用 mtime。在 `--no-build` 下，miss 设置 `wantsRebuild` 并失败，当原 trace 已存在时还写 `.nobuild` 诊断。应结合准确范围的成功退出、全部输出/trace/setup 前后原散列和零受保护命令三项证据。[回放判定](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/lake/Lake/Build/Common.lean#L194-L231) [no-build 失败行为](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/lake/Lake/Build/Common.lean#L281-L293)

## 两个调用方

P2 使用 `b47ab032...` 的原始项目配置；goldbach 与 LeanArchitect 属于固定的依赖包。`P2_EXPECTED_102_SOURCE_ALLOWLIST.json` 独立从 v5 实际已审 102 行和五份 r5-r1 后像构成，对五个旧输入字节都做过核对。顺序、直接导入、101 个 ABI 闭包及额外的 FinitePiIntegral 保留，源码共 1247908 字节。实际 v6 须按这份来源逐项匹配，仍须远程完成 single FinitePi 验收、全 102 个内核以及全部声明归属、完整类型和传递公理审计。

Stored 仍单独在 `26a6b01a...` 原 profile 下恢复父的八个 facets，并逐字核查当前 470B 源与第九个历史成员，九项合计 241880 字节。已从父真实 setup 重算 133 个导入与全部 665 个有序物理出现的原散列，另与 020–030 的真实 `BATCH_OBJECTS_BEFORE.json` 核过其中 399 个 olean 类型出现。266 个 IR/ir.sig 由 T01 原文件记录提供散列，仍须对新环境的物理文件逐件验证。原 000–030 无新证明计数。新 031–041 的 45056 行、704 个 Fin 64 私有组件属于新 run 的 11 个候选。
