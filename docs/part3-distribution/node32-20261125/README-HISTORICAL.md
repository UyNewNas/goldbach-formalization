# P3.2 历史证据复用记录

本清单的状态是 **`HISTORY_SOURCE_MATCH_ONLY`**。它把六个指定入口的 130 个项目源码文件，与已有 source selection、root266 接受清单和真实历史 audit 回执绑定。它没有运行 Lean、kernel replay 或新的类型／公理审计，也不表示整个 P3.2 节点完成。

## 六个入口

- `ImbalancedChen.Part3SharedFirstFactorEnergyNonzeroReduction`
- `ImbalancedChen.Part3ComplexCRTFiniteFourier`
- `ImbalancedChen.Part3ActualCompletedZeroDifferencePayment`
- `ImbalancedChen.Part3ActualNonzeroChartEpsilonTagPayment`
- `ImbalancedChen.Part3ActualZeroTagFreeEpsilonPayment`
- `ImbalancedChen.Part3ActualKPacketAdapter`

脚本递归检查这六个入口在固定源码中的 `ImbalancedChen.*` 单行 import，并要求结果恰好是清单中的 130 个模块。Mathlib、MathlibNt 等外部供应环境继续按原验收规则信任。

## 核实结果与边界

| 项目 | 数量或结果 |
|---|---:|
| 项目源码闭包 | 130 |
| root266 owned 模块 | 89 |
| 当前源码与历史 owned 源码精确字节匹配 | 88 |
| 保留现有已验收文档头变体 | 1 |
| trusted-import 源码绑定 | 41 |
| 不同原始 owned audit receipt | 72 |
| 原始 receipt 字节哈希已重读确认 | 72 |
| 直接保存于旧 `verification/proof-continuation/.../audits` | 49 |
| 保存于 `owned-frontiers` 原始归档 | 23 |
| 复用的历史完整声明记录 | 3615 |
| 历史记录中的不同 fullname | 3612 |
| 本次新增声明 | 0 |

每个 owned 模块都绑定原 census 的 source SHA-256、object parts、声明数和原始 receipt SHA-256。72 份原始 receipt 均为 `PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS`；对应模块有唯一成功 stock replay，完整类型／公理 inventory 阶段退出码为 0，前后输入绑定一致。清单只提取这些 receipt 中属于本次 130 模块范围的记录。

3615 条历史完整类型记录均非空、无 `⋯` 截断，`unsafe`、`partial`、`axiom` 均为 `false`，传递公理仅来自 `propext`、`Classical.choice`、`Quot.sound`。清单保存各模块完整记录和完整类型的 canonical SHA-256 及安全摘要；完整类型仍由原 root266 全声明文件的固定哈希绑定，不复制十余 MB 的累计记录。

历史重复记录按原样保留：`ComplexCRT.Compatible.eq_1` 有两个副本，`MediumAtom.q1SliceAtom.eq_1` 有三个副本。它们均已登记在历史重复元数据中，除所属 module 字段外，记录完全相同。3615 是旧 inventory 记录数，3612 是不同 fullname 数；二者均不计作新证明。

41 个 trusted imports 的当前源码由现有 `continuation-20261124/aggregate.json` 中的 `local_import_sha256` 完整绑定。不能把它们扩大成 root266 owned 完整类型审计。`baseline-c509267-report.json` 并不逐项列出这全部 41 个文件，因此未被用来作此扩大声明。

### 唯一源码字节特例

`ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson` 保留现有分支的已验收文档头：

```text
历史 census 源码：4480c5b8f0bfdef5ada321e760dabe334664b4fb1465fad381919ffc70cdacf2
当前选定源码：  3f0218c06362bdd97cdc178e006f646c73e5cd4cd8dc18fc07b590fceffc2193
```

只有文件顶部第一个简单 `/-! ... -/` 文档块不同，移除该指定块后的其余字节完全相同。当前哈希也与既有 `baseline-c509267-report.json` 的 source map 相同。默认检查仍要求当前文件精确匹配 `3f0218…`；脚本不接受任意新注释版本，也不把当前字节伪装成旧 receipt 实际编译的 `4480c5…`。

## 固定来源

全部历史源码、census、acceptance 和原始 audit 的远端定位均固定到：

[goldbach-formalization / 10b89181754c78c0e77616677295ee2105de0bb6](https://github.com/UyNewNas/goldbach-formalization/tree/10b89181754c78c0e77616677295ee2105de0bb6)

本地 donor 仅用于重读原始字节；其本地 HEAD 不是发布证明，也没有被用作远端链接。脚本自身不发起网络下载。

主要历史锚点如下，清单中同时保存完整相对路径和固定 GitHub 链接：

| 证据 | SHA-256 |
|---|---|
| root266 archive manifest | `3486944402f91459f5788654ef86b7d589188028d467c5ac6580166793c70785` |
| root266 census | `e8c0e21cd551fef4610e1f2214fa1c68f83f35cdf64d4dff525fa8f31e62b544` |
| root266 全声明记录 | `a4645d341c9eb43ab597648854a4adc81517751c19d83814e5b8f9cab60ceb9e` |
| root266 root acceptance | `0c5870cd426f1505e176baa5ce332169e4d896133ca34404d3d43f244e732730` |
| 现有 aggregate import-source binding | `192bed166aa0f44085cba447b0cebdafcd341a263f2735c6eeb4274b3a1ab7f0` |

`SOURCE_REUSE.json` 是本次 73 个同源文件选择的现有记录；共享源码和文档头变体保留 `ef1479c272bdd6b24800fa10409d793f0a2fe95c` 基线。本历史清单同时绑定这些文件和三个项目 pin，不修改它们。

## 运行方式

在仓库根目录运行默认检查：

```bash
python3 -B verification/verify_part3_node32_reuse.py
```

默认模式核对被冻结的紧凑清单、130 个当前源文件、项目 pins、六入口闭包及现有导入源码绑定。输出包含：

```json
{
  "status": "HISTORY_SOURCE_MATCH_ONLY",
  "evidence_mode": "FROZEN_COMPACT_EXTRACTION",
  "original_audit_receipts_rechecked": 0,
  "new_compilation": false,
  "new_kernel_replay": false,
  "new_declarations": 0,
  "current_objects_verified": false,
  "node_complete": false
}
```

有完整原始历史树时，可再重读全部原始证据：

```bash
python3 -B verification/verify_part3_node32_reuse.py \
  --source-root /path/to/current/worktree \
  --evidence-root /path/to/original/evidence/tree
```

此模式按清单的相对路径读取旧 source plan、manifest、census、全声明记录、root acceptance 及 72 份原始 receipt，重新计算哈希、类型安全摘要和 source/object/stage 绑定。输出变为 `ORIGINAL_BYTES_RECHECKED`，`original_audit_receipts_rechecked` 为 72；最终状态仍是 `HISTORY_SOURCE_MATCH_ONLY`。

`--source-root` 默认是脚本所在仓库，可用来核对另一棵源码树。清单及既有 provenance 文件仍从脚本所在仓库读取。`--manifest` 可指定待检查清单，但其完整 SHA-256 必须等于脚本中冻结的值。

两种模式都只读，不创建对象、不调用编译器、不访问网络、不修改文件。缺失文件、字节不匹配、闭包不同、禁止公理、不安全声明、历史阶段或对象绑定不一致均返回非零退出码，并输出 `HISTORY_REUSE_CHECK_FAILED`。

## 验证范围

实施时运行了默认模式与原始证据模式。另以独立 Python 测试验证：源码即使只新增一行注释也必须拒绝；`sorryAx`、unsafe／partial／axiom 声明、空类型与截断类型必须拒绝；原始回执不能改绑到另一源码哈希。测试在临时目录或内存内运行，未改动 Lean 文件和原始证据。

当前完整 `.olean` 对象并未提供给本脚本。因此历史对象哈希的一致性不等于当前对象已存在或已通过新的 kernel replay。全节点完成与新的 CI／编译结论由各自的新验收记录决定，不能从此历史复用清单推导。
