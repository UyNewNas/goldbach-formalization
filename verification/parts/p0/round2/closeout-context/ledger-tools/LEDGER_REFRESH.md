# 台账刷新入口（只读验证记录）

`build_ledger.py` 现在转入通用 `build_ledger_v2.py`。它只读取源码与现存回执，不运行 Lean、Lake、leanchecker、Actions，也不修改其他 Part 的源码、缓存或进程。

原始 `module-ledger.json`、`MODULE_LEDGER.md` 和类型文件仍是 2026-10-12 03:56:28 UTC 的快照，没有被重新生成。原生成器归档为 `build_ledger_v1_snapshot.py`，不作为刷新入口。

## 一次刷新

先在新的输入 JSON 中列出已经正式接收的完整组件集合。可从 `acceptance-input.example.json` 起步；其中只列真实已接收的 Buchstab，桥和 P2 尚未假设通过。

```bash
python3 /workspace/scratch/535d89efd063/p0-round2/ledger-draft/build_ledger.py --acceptance-file /absolute/path/acceptance-input.json --output-dir /workspace/scratch/535d89efd063/p0-round2/ledger-final
```

输出目录必须为空。以后再刷新请改用新的目录，例如 `ledger-final-2`；程序不会覆盖既有快照，也拒绝把原 `ledger-draft` 作为输出目录。`ledger-final` 只是文件夹名，不代表最终证明已闭合。

只检查输入格式、不写台账：

```bash
python3 /workspace/scratch/535d89efd063/p0-round2/ledger-draft/build_ledger.py --acceptance-file /absolute/path/acceptance-input.json --check-input
```

不指定输入时，程序从原始台账继承已接收组件清单；接收逻辑没有硬编码 Buchstab 或 `30f...`。最终更新应显式提供最新输入。

## 输入字段

| 字段 | 用途 |
|---|---|
| `integration` | `branch`、完整 `commit`、完整 `tree`；本地 checkout 不匹配时保留两者并明确记录，不改写声明 SHA |
| `accepted_components` | 完整集合，每项为 `module`、完整接收 `commit`、确切 `source_sha256`；可另给 `source_commit` 标识产生该源码的固定提交 |
| `module_overrides` | 以完整模块名为键，可指定 `source_path`、`source_original`、`unclosed_inputs` 和 `reviewed_utc` |
| `additional_modules` | 已知 26 模块以外的真实新增源码记录，形状与 `bridge-source-inventory.json` 一致 |
| `extra_results_jsonl` | 额外现存结果文件的绝对路径列表；默认读 P0、P5 的 `results.jsonl` 与 P1 closure state |
| `actions_receipt_path` | 现存 Actions 回执路径；只有回执提交与声明的集成 SHA 一致时才关联到该 SHA |

`accepted_components` 不用于把候选强制标为通过。源码 SHA256 必须精确匹配，strict 编译、相同生产对象内核重放、对应 defining-module 公理审计三个门均有匹配回执，才会进入有效接收计数。配置列出但门未完成的项仍是候选。

原审查文字含有当时的验证待办。它们带原审查时间保留，当前门的真实完成状态由日志计算。若需要正式交付的精简“仍未闭合输入”，请在 `module_overrides` 中为相关模块给出 `unclosed_inputs` 与 `reviewed_utc`；不要为了旧文案修改验证状态。

## 审计接收规则

解析器读取真实的 `P0_AUDIT_DECL`、`P0_AUDIT_MODULE`、`P0_AUDIT_COUNT`，也可解析已经使用相同格式的其他 `*_AUDIT` 前缀。

新审计必须同时满足：

1. `results.jsonl` 已有完成结果，`returncode = 0`、`strict = true`、`trustLevel = 0`、`metadata_adapter = false`，原日志有对应 `FRONTEND_OK`。
2. 该审计源码 SHA256 在执行前后一致，当前可读审计源码也匹配；实际程序包含 defining-module 枚举、unsafe/axiom 拒绝、传递公理白名单和编译器类型打印。
3. 所有声明名唯一；逐模块数量等于实际 DECL 数量；唯一最终 COUNT 等于完整总数；公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
4. `import_olean_sha256_before` 与 `import_olean_sha256_after` 完全一致，包括记录中存在的 `.server` / `.private`。
5. 被审模块的主 `.olean` 哈希等于该当前生产源码的 strict 成功对象。生产重放还要绑定同一生产对象；新 replay 若记录了目标前后哈希，也必须相等。

`returncode = 0` 但源码或导入对象变化的记录不会通过。新运行记录若含 `verification_passed`，其值必须严格为 JSON `true`；任何非空 `failure_reasons` 也会拒绝该条记录。旧回执没有这两个字段时保留原有独立源/对象检查，不补造新字段。仅有部分 DECL、没有 MODULE/COUNT、尚无完成记录、或无法绑定当前生产源码的审计不会取得公理 PASS。

原始台账已经验证的同源历史回执可以继承，例如 P5 的已核验 Buchstab。程序明确写入继承来源和原时刻，不为历史记录补造它当时没有捕获的 import 前后字段。

## 第 26 个模块

`ImbalancedChen.CurrentPairedBuchstabBridge` 已按真实源码加入 `bridge-source-inventory.json`，初次读取源码 SHA256 为：

```text
280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550
```

初始固定提交为 `null`，归属 P0，接收方为 P2/P5/P0。其两个 theorem 的源码类型会进入类型单。程序会读取 P0 验证树中后续实际源码，但只在对应编译/重放/审计完成后登记其门；只有输入显式列入确切已接收提交时才成为接收组件。

## 输出

- `module-ledger.json` / `MODULE_LEDGER.md`：动态 26 模块及配置中的额外模块台账。
- `source-theorem-types.json` / `SOURCE_THEOREM_TYPES.md`：当前源码完整 theorem/lemma 声明头。
- `compiler-declarations.json` / `COMPILER_TYPES.md`：完整匹配审计中的编译器类型，包括 private/generated 声明。
- `audit-catalog.json`：实际完整/部分审计记录及其是否满足绑定条件，保留未通过原因。
- `acceptance-input.json`：本次采用的明确接收配置。
- `evidence/`、`snapshot-sources/`：本次读取的回执、日志、配置和源码逐字快照。

完整项目构建、完整项目内核/公理门和最终 hLower/hUpper 自由入口不会因为这些组件门通过而自动成为 PASS。P5 不等待 P4-B 的关系以及 K/c、同一实际 rho、真实算术/积分供应者的未闭合状态仍保留。

准备正式刷新时另参阅 `FINAL_ACCEPTANCE_NOTES.md`。本次仅增强生成器及说明，没有运行最终 ledger。
