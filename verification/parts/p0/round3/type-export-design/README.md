# Part 0 Round 3 完整类型导出候选

**状态：仅静态复用与审查，未调用 Lean。** 此候选没有修改集成工作树、公共根或 workflow。由 P0 审核后把 `verification/parts/p0/` 下两个文件按相同路径放入固定集成提交。

## CI 一行调用

在同一正常、锁定工具链 checkout 的 **full lake build 已成功**、公共根已导入本批八个生产模块之后运行：

```sh
python3 verification/parts/p0/check_round3_types.py
```

保留原有 full build、根内核重放及根公理审查三门。此调用补充完整类型导出，不替代三门，也不发起新的生产模块验证。若调用失败，应按原失败状态保留；不把已有其他 SHA 或旧根的成功套在新集成 SHA 上。

原始结果输出到 `.lake/part0-round3-types/<UTC timestamp>/`。建议现有 CI artifact 收集器在失败时也收集整个 `.lake/part0-round3-types/`，本候选不修改 workflow。

## Lean 审计源的复用范围

`Round3Audit.lean` 基于 P0 已通过的 `LongSlotAudit.lean`，原文件 SHA256：

```text
ddef4f809fac00f3d4bb2146e9ab80374ab99f9ebc44f1d9c139ecc1d333a3f6
```

逐声明的 defining-module 查找、unsafe/new-axiom 检查、标准三公理白名单、`collectAxioms`、`pp.all`/`readable_type` 格式化及 `⋯` 拒绝代码块与原版逐字相同。只调整根导入、清点模块、精确计数和输出前缀，并单独附加原有最终条件桥。差异保存在 `LongSlotAudit-to-Round3Audit.patch`。

| defining module（均属 `ImbalancedChen`） | 预期所属声明数 |
|---|---:|
| `ActualSelectedPrefixLowerCellSum` | 9 |
| `ActualSelectedPrefixLowerOwnCubeIntegral` | 8 |
| `HistoricalPrefixCertificate` | 96 |
| `OrdinaryLowerFourFrontier` | 27 |
| `Certificates.PairedV2Geometry` | 10 |
| `Certificates.PairedV2Prefix4Data` | 11 |
| `Certificates.PairedV2Prefix4` | 35 |
| `Part3LongSlotNormalization` | 2 |
| **合计** | **198** |

全部 defining-module 声明均清点，包括 private/generated。Lean 自身强制核对逐模块计数及总数 198，Python 再核对原始 JSON 输出、唯一声明名、逐模块计数和完整类型。

另以独立 JSON marker 输出：

```text
ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
```

该桥不加入 198 条计数；要求恰好一条、确属 `ImbalancedChen.CurrentMainTheorem` 且为 theorem。对桥同样检查所属安全性、公理及完整类型。没有闭合其 `hLower`、`hUpper`；receipt 明确记录 `final_bridge_is_conditional: true` 和 `hLower_hUpper_discharged: false`。

## 执行与回执的范围

Python 入口只在准备完整的正常 checkout 中调用一次：

```text
lake env lean -DwarningAsError=true -o <本次独立目录>/Round3Audit.olean verification/parts/p0/Round3Audit.lean
```

它不执行 `lake build`、cache/bootstrap/update 或 `leanchecker`。缺少任何应已有的生产 `.olean` 时前置检查直接失败，不启动补建。

入口记录完整 Git SHA，并要求本次输入均已跟踪且没有工作区或索引修改。锁定三文件按冻结 SHA256 检查，并复用已有 `check_pins.py`。清点八个模块、最终桥所属模块、公共根，以及这些源的直接 project imports；记录其源码与所有现有 `.olean` 部件的前后 SHA256。公共根的直接生产导入也纳入身份快照，所以该检查预期在成功 full build 后运行。

Lean 的继承 `LEAN_PATH` 和 `LEAN_SRC_PATH` 在进入 `lake env` 前清除，由同一 checkout 的 Lake 设置路径。只有验证审计 `.olean` 写到本次新建目录，不覆盖生产对象。原始 stdout、stderr 分别按字节保存，并记录哈希、真实退出码和耗时。失败时分别保留两个流中的首个 Lean 诊断及其完整段落，不伪称拥有跨流的先后顺序。两个原始流还会完整转发到 CI 日志。

成功回执要求：Lean 真正退出 0；198 条唯一生产声明、八个正确计数及一个最终桥记录齐全；完整类型无 `⋯`；公理仍在标准三项内；审计对象实际存在；Git SHA、源码、生产对象部件集合及哈希前后不变。只有全部条件满足，`receipt.json` 才写 `PASS`。缺失、失败、超时、中断、计数不符或输入漂移均保留 `FAILED`。

主要输出文件：

- `receipt.json`：SHA、命令、前后输入/对象哈希、退出码、首诊断和最终状态。
- `stdout.log`、`stderr.log`：未截断原始流。
- `declarations.json`：198 条完整编译器 JSON 声明。
- `final-bridge.json`：原最终桥的单条完整编译器记录。
- `final-bridge-type.txt`：最终桥完整 pp.all 和可读类型，另明确说明仍有上下界输入。
- `Round3Audit.olean` 及实际生成的伴随部件：仅本次审计的对象。

本次静态检查包括 Python AST、三项冻结文件哈希、Lean/Python 的八模块计数一致和已通过的审计检查/格式化代码块逐字比对；详情见 `STATIC_REVIEW.json`。这不是编译器确认类型或新的证明通过回执。
