# Core 归档消费者独立静态审查

## 结论与审查身份

审查对象：`consume_core_artifact.py`，957 行，SHA-256：

```text
85911b447a1a4b8c455f148725ae1b5a961daae771c5b484c9db5429a2a7067b
```

脚本固定目标为集成提交 `d0366ce64272e81faf6166a8a90050f56b328d38`、树 `e2ab22b96f76c8969386296558c626c62a581700`、核心运行 `38289734671`、作业 `114946653833`、attempt 1。

**在固定 workflow 与两个固定类型导出器实际产生的原始归档合同下，未发现六个必需阶段失败、跳过、缺失，或类型/源文件/对象绑定检查失败后仍可进入 `PASS_ORIGINAL_EXACT_CORE_CI_EVIDENCE` 的路径。** 这是一份代码审查结果，不是实际核心 CI 验证回执。本审查没有取得或消费该核心运行的实际归档，也不声明该运行已经通过。

有一个不阻塞成功归档消费、但值得改进的状态准确性问题：已提供的 metadata 已经表明运行失败，而归档尚缺失时，消费者可能仅给出 `PENDING`，没有保留已知运行失败状态。具体路径见下文。

## 实际执行范围

只读审查了该消费者全部源码、固定提交的 `.github/workflows/lean.yml`、类型导出器及相应审计入口；复核了消费者的源文件散列。对消费者源码执行 Python AST 语法解析，结果通过。没有导入或运行消费者，没有构造成功 fixture，没有运行 Lean、CI 或网络轮询，没有修改消费者或仓库。本文件是本项审查唯一新增文件。

行号均对应以上散列的消费者版本。

## 六个必需阶段

| 阶段键 | 必需的实际作业步骤 | 消费者的硬性要求 |
| --- | --- | --- |
| `build` | `Build the full project` | 唯一步骤、完成且成功、真实起止时间、成功 outcomes、零退出 timing、匹配日志标记、实际构建成功 footer |
| `round4-targets` | `Check the four explicit round 4 production targets` | 同上；固定 workflow 明列四个新增 production target |
| `leanchecker` | `Recheck ImbalancedChen with bundled Lean 4.33.0-rc1 leanchecker` | 同上；固定 Lean 版本/提交、实际 bundled checker、根模块与全部接收组件检查标记 |
| `axiom-audit` | `Audit ImbalancedChen root declarations and transitive axioms` | 同上；固定 audit 版本/提交、实际根声明统计、仅三种允许公理、完成 footer |
| `round3-types` | `Export complete round 3 types and the existing conditional main bridge` | 同上；实际 198 条导出及单列的完整条件式桥类型 |
| `round4-types` | `Export complete round 4 types and the existing conditional main bridge` | 同上；实际 414 条导出及单列的完整条件式桥类型 |

步骤名取自脚本的 `STAGE_NAMES`。消费者分别核对 GitHub 原始步骤记录、原始 outcomes、各阶段 timing、各阶段原始日志及类型导出内部回执；并非仅消费一个汇总 `success` 字段。

实际作业步骤成功条件在第 307–314 行建立，在第 398–399 行逐项强制检查。第 413–414 行要求恰好六个不同的 outcomes 键；第 433–456 行分别检查每门成功、退出码为零、时间一致且顺序合理、日志起止标记一致、没有真实 Lean 错误。缺失、重复、失败或跳过阶段都会阻止成功路径。可选缓存步骤不替代任何一门。

## 源码、类型和对象绑定

| 项目 | 静态审查结论 |
| --- | --- |
| 固定来源 | `prepare` 验证精确 Git 树；metadata 强制运行 ID、完整提交 SHA、attempt、仓库、分支、workflow 路径以及实际作业/归档所属运行。ZIP 字节与 GitHub 提供的 SHA-256 和长度相符才继续。重复归档成员、歧义路径和 CRC 错误会被拒绝。 |
| 固定项目输入 | 读取固定 Git 提交中的台账、根导入、锁定文件、审计/导出器与供应源文件。已接收 production 源文件散列和显式根导入受检查；工具链/依赖 pin 与已有条件式桥/数值桥维持原有字节。 |
| 原始类型 | 每轮只接受唯一、精确 SHA 的实际回执。198 和 414 是完整声明数及逐模块数，包含 audit 的实际环境 inventory；同名重复、缺失声明和附加记录会失败。导出 JSON 必须等于原始编译器 stdout 的标记载荷，不能以单独拼出的 JSON 替代原始记录。 |
| 完整打印 | 检查完整 `pp.all` 类型及可读类型，不允许已知截断标记；固定审计入口开启完整类型/证明/深项打印和足够宽度。原始 stdout、stderr、JSON 文件以及回执自身的路径/散列均绑定，类型 stdout 还必须实际出现在该门日志中。 |
| 真实执行 | 检查 `lean_started`、真实成功退出、固定严格 `lake env lean -DwarningAsError=true -o …` 命令形状、对应轮次 timeout、内部执行时间处于实际阶段内。要求调用前不存在该审计输出对象。 |
| 对象连续性 | 每轮输入源文件与 production 对象部件的前后快照必须完全相等；两个导出阶段之间的 production 对象映射也必须相同。production 源文件集合与散列须对应固定 Git 源码。实际输出的审计 `.olean` 部件要能从归档中取出并核对散列。 |
| 全声明公理检查 | 独立根审计必须通过；两轮完整类型记录也逐条拒绝自定义公理声明及不允许的传递公理。固定 Lean audit 源码还拒绝不安全声明。没有允许 `sorry` 等绕过手段的分支。 |
| 最终合并 | 旧 591 条按明确名称拆成保留 393 与本次重新打印的 198；再加入 414，得到恰好 1005 个不同声明和明确的 23 模块统计。要求 1000 条完整 `pp.all` 与历史 5 条完整默认格式保持正确来源标签。不能把未在本次打印的旧 393 条冒充本次重新打印。 |
| 条件式桥 | 两轮完整桥记录必须一致，仍包含 `hLower`、`hUpper`。消费者输出明确保留 `main_conditional=true`、上下界及 `K`、`c` 未闭合状态；没有创建无条件主定理的证明声明。 |

对象绑定的范围表述准确：最终 `SOURCE_OBJECT_BINDINGS.json` 明记 `production_object_bytes_all_embedded=false`。production 对象证据是 runner 捕获的部件散列；归档确实携带并检验的是 audit 输出对象。消费者也没有把导出阶段捕获的对象散列说成先前内核重放日志自身提供的对象散列。

## 非阻塞问题：已有失败 metadata 被归档缺失的 PENDING 提前覆盖

### 具体路径

1. 第 255–267 行在读取任何 metadata 之前要求 `artifact_zip` 等全部输入文件存在。只要归档尚未下载，即使已经提供的运行/作业 metadata 明确为 `completed/failure`，也会先抛出 `EvidencePending`。
2. metadata 全部文件存在时，第 288、303、311–314 行把运行、作业及步骤成功条件保存为延后检查。这样在归档存在时，可以先保存第一处真实诊断，再报告失败；这一设计有明确用途。
3. 但是第 323–324 行的缺归档条目，或第 330–332 行的缺 GitHub digest，会在第 398–399 行执行延后检查之前抛出 `EvidencePending`。
4. `observed` 中运行及作业的原始状态、conclusion 直到第 337–346 行才写入。因此上述提前退出可能不保留已经观察到的运行/作业失败。
5. `run` 第 872–874 行将这类异常分类为 `PENDING`。不会进入第 859 行的唯一 PASS 赋值；也不会把失败模块接收为已验证。

### 影响与建议

该问题影响失败回执的状态可见性，**不构成错误通过证明门的路径**。对本次正在健康执行的核心运行，以及后续齐全的真实成功归档，不是接收阻塞。

可以在消费者本身改进：尽早保存已通过身份核对的运行、作业和步骤状态，将“已知执行失败”与“归档证据尚不齐全”分成独立字段；保留既有先提取真实诊断的流程。这样完成失败不会仅显示为 `PENDING`，同时也不会把缺证据误称为已完成核验。这一修改无需重启或重跑 Lean/CI。

## 状态边界

唯一 PASS 赋值位于第 859 行，之前必须依次通过 `prepare`、metadata、六门原始日志、固定输入、两轮完整类型及最终合并检查。异常路径分别为 `PENDING`/退出码 2 与 `FAILED_EVIDENCE_CONSUMPTION`/退出码 1。输出目录必须为空且位于集成仓库之外；第 881–884 行防止在此检查失败时覆盖既有输出。

因此，本审查可以支持随后消费真实、齐全的核心归档，但不能代替消费结果，也不能作为 `d0366ce64272e81faf6166a8a90050f56b328d38` 的实际编译、内核重放、公理检查通过声明。
