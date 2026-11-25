# 表达修复独立只读审查

日期：2026-11-25。主体比较基点 `8354935efb08bdae1529bcb29795a236f596f422`，主体终点 `fba34c95ffae480e6a427fc2944606dfa37bd049`；第 4 节将审查补充延至 `21c6afd94cc591d43bd450f1b994eee9d2715598`。仅核对这些差异、既有接口、选定源码 hashes 和失败日志；没有重复原数学审查，也没有运行编译。

**结论：未发现改变命题、增加假设或降低验收要求的改动。四个 Lean 文件的修改是局部表达修复；修复是否成功仍待真实编译与验收证据。本报告不计入任何新增通过信用。**

## 1. 修复内容

| 文件 | 独立核对 |
| --- | --- |
| `P2OriginalCompactPhysicalGateTransfer.lean` | 在 `fin_cases i` 前保存既有 endpoint 证明 `hi`，各分支再使用经消元替换的证明；没有改变五坐标门槛。`cases hr : table.row ...` 已把目标中的 row 重写成 `some (candidate,argument)`，此时改用 `rfl` 正好证明剩余的反身等式，没有丢失实际 row 的来源。 |
| `P2OriginalSelectedMaskPhysicalSquares.lean` | 隐藏冗余 `Code` 名称；新增 `hprefix` 只调用既有 `select_future_invariant`，用 prefix 内坐标相等得到 `select actualCode = select (prefixCode ... actualCode)`。`hprefix.trans hsel` 的方向正确，`select_some_source` 返回的实际 candidate、supportCheck、mask 和原 cap 均保持。 |
| `P2OriginalPairSourceReceiver.lean`、`P2OriginalSelectedIntegerPrefixSquares.lean` | 仅为 `open ... hiding Code`。原 `LowerSelectedCapConstructor.Code` 仍显式打开，`WholeBoxBranchSelect.Code` 本身就是它的 `abbrev`；没有替换为不同类型。这两处是同模式跟进修复，seventh 日志没有声称它们分别已经失败或修好。 |

命题声明、量词、假设和数据定义在差异中均未修改；没有新增 `sorry`、`admit`、axiom 或关闭检查的选项。日志中的恢复性 `sorry` 不等于作者源码加入 placeholder。

## 2. 主体终点 fba34c9 的 Hash 与验收要求

按原始文件 bytes（包括原有行尾）核对 `SOURCE_SELECTION.json`：**261 个 sources 和 5 个 compatibility companions 共 266 项，均同时匹配终点提交与审查时工作树，无缺失或 SHA 不符。** 新增四条 `ELABORATION_REPAIRS.json` 的 previous/new SHA 也分别匹配两个端点。

| 修改源码 | 终点 selected SHA-256 |
| --- | --- |
| CompactPhysicalGateTransfer | `f87eae04fa38484f585eb4be4b59fd04e8b0c95a54eb20ce716292c8ffdadb6e` |
| SelectedMaskPhysicalSquares | `9e0064f60cd48ee80fc6704a8b20483b5f2761bda80272898210e8e8324c4bf4` |
| PairSourceReceiver | `8f01047a8664684a5388f068b8c170ec9ea0b052ed5b18ef2bb3c95155cd5da2` |
| SelectedIntegerPrefixSquares | `112b5f48f4860d333417eec240b32be24c88c2c15487463b130547aedbcaccfa` |

manifest SHA 为 `7caad59509be2895effae57513c26f8f2526b31b5051f4cb913a738adf163a76`，与 `SOURCE_GUARD.source_manifest_sha256` 一致。source guard 仍标为静态检查，四条修复仍为 `kernel_verified=false`、`verification_pending=true`。

两个端点的整个 `verification/` Git tree 均为 `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`。runner SHA 均为 `895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30`；当前工作树也一致。因此本段没有修改 strict-owned、owned fresh compile、bundled leanchecker、完整 owned inventory/type/传递公理检查或最终 snapshot/path 校验。

一个非阻断的元数据措辞问题：SelectedMask/IntegerPrefix 的 `selection` 仍写 `reused_existing_exact_source`，PairSourceReceiver 仍写 `...visibility_only`；它们均已另附修复 manifest，且 selected SHA 正确。今后可统一这些展示标签，但不能仅靠旧标签把修改后的文件当作未改 donor source。

## 3. 两份真实失败日志

以下 SHA 是本次读取的原始日志 bytes。两文件在审查时均未被 Git 跟踪，需随后续证据提交保存；本次未代为提交。

| 日志 | SHA-256 | 字节 / 行 | 诊断分类 |
| --- | --- | --- | --- |
| [sixth-compact-physical-gate-failure.log](sixth-compact-physical-gate-failure.log) | `bc901231730aac0facf02cbe5d4194c8663e785800cc123bf4149fa7720fab0b` | 1483 / 15 | 5 次 `Unknown identifier i`（索引消元后引用）及 1 次 row equation 与反身目标的 application type mismatch；均属 elaboration/case-elimination。 |
| [seventh-selected-mask-square-failure.log](seventh-selected-mask-square-failure.log) | `3db7246ee7850dc981e5af36683d70c06a3113b174f0de4839b12f026fa87614` | 9088 / 184 | 3 次 `Code` 歧义、1 次 prefix/unprojected selector equation 不匹配，另有 3 个 unsolved-goal 诊断及 1 个缺失上游 theorem 名称的级联错误；5 条警告含错误恢复产生的 `sorry` 与 unused simp arguments。 |

日志首行有真实 Lean 命令，正文明确含错误；日志本身没有 exit-code 字段或源码 SHA，不能单凭它们断言某一后续修复已成功。与 `f8531162b8a0b61fe5ea530f6ad9f356d05a07be` / `a7f8bda10f04cdfc126db18ffd7900843bb5fa22` 的提交关联来自 `ELABORATION_REPAIRS.diagnostic_basis`，不是日志内自带的 hash 绑定。

本次没有收到或核证成功 archive，未把这些失败或修复记录转换成通过结果。后续 archive 到达后仍需单独核对源码/object、实际命令、strict compile、kernel replay 和完整 owned/公理清单。

## 4. 补充：终点延至 21c6afd

`fba34c95ffae480e6a427fc2944606dfa37bd049` → `21c6afd94cc591d43bd450f1b994eee9d2715598` 的唯一新增 Lean 代码，是在 `point_slots_le_own_upper` 原 `fin_cases/simp` 前加上：

```lean
dsimp only [P2OriginalCompactPhysicalGateTransfer.upper] at hupper
```

已核对 `upper S code i` 的原定义就是 `cellUpper S mesh (code i).1`。此行只将既有局部假设作定义性展开，使其与 finite-case goals 的表达形式一致；定理声明、分支、坐标不等式和所选 mask 均未改变。没有新假设或替代数学输入。

已读取 [eighth-selected-mask-upper-failure.log](eighth-selected-mask-upper-failure.log)：SHA-256 `772738fbbe475796b2e7ef2aa4170c3fbfec890e18f7e11f6940a1cb49f8d7f6`，2584 bytes / 52 lines，审查时未被 Git 跟踪。其唯一 error 诊断列出 rank 3/4/5 的 `cellUpper` conjunction，而 `hupper` 仍写成 `upper`；另有 3 条警告（unused `S` 和两个 unused simp arguments）。此前 Code 歧义与 selector equation mismatch 不再出现于这份日志。该事实只描述本次错误输出；本模块仍失败，不提供成功 object/kernel 信用。此日志同样没有内嵌 exit code 或源码 SHA，关联的 `fba34c9` 来自修复记录。

补充终点的 SelectedMask SHA 为 `b991d38a0934a4840088b339eec479177d4cad9c2ea23d9aeee0ee0f2b7c5278`。新增修复记录的 previous/new SHA 分别匹配 `fba34c9` 与 `21c6afd`。再次逐项核对 **261+5=266 项**，终点提交及当时工作树均与 selected SHA 一致；新 manifest SHA 为 `06794bf43fd8cf7ee5e25532a66090c42bf6ef3fbe6f75e5a7984311500e3d71`，source guard 已同步。整个 `verification/` tree 仍为 `879002f0dc10ca87c6c6069e13bdd7b2352cdfd2`，验收要求无变化。

**补充结论：此单行也是定义性表达修复；当前 `21c6afd` 文件的成功编译与正式验收仍待后续 archive 独立核证。** 本报告冻结不预先计通过；仅新增此报告，没有修改数学源码、manifest 或提交 Git。
