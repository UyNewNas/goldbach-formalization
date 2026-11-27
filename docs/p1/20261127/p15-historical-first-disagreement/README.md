# 原历史系数的首次分歧：正式验收

`ImbalancedChen.P1OriginalHistoricalFirstDisagreement` 已在源码发布 `4a55b304fec91096f3c461fdda7ea2fe3eb46102` 完成正常编译、内核回放、全部自有声明的完整类型与传递公理审计，以及独立只读复核。

实际清单为 **4 条自有声明：2 条公开、2 条私有**。公理并集仅含 `Classical.choice`、`Quot.sound`、`propext`。整个 P1.5 仍未闭合。

## 已证明的结论

`nonzero_has_changed_rough_factor` 从实际 `trueDDeltaRho old fresh ... d ≠ 0` 得到原 small Rosser 因子 `a`、原共同 rough support 中的 `b`，满足 `a * b = d`，且该 `b` 的原 fresh-minus-old mask 非零。

`nonzero_has_actual_first_disagreement` 进一步给出原共同 admission 树中的真实状态：该步为奇数步，old 与 fresh 在该存储历史上不同，历史逆序是同一个 target-deleted rough universe 的子列表，且历史中的每个素数均属于完整 `d` 的素因子。原 small Rosser 附着保持不变。

这两个定理的输入没有最终中段均值界。它们证明实际非零历史系数的有限树来源，尚不证明历史系数的整原子分解、去平方自由限制的误差支付或统一 signed medium 界。

## 实际验证

| 项目 | 结果 |
| --- | --- |
| 独立无对象预检 | `job_f84f1abdb20243e3aa5872f077875af8`，exit 0；Lean 15.546 秒 |
| 正式验收与独立 readonly/export | `job_a44d125c4e504da1bb5774c808c4a2ea`，exit 0；任务 131.961 秒 |
| Normal | exit 0，20.537 秒；实际只构建本模块 |
| 原有 project dependencies | 293 个全部复用，含目标的实际源码图共 294 个模块 |
| Kernel replay | `leanchecker` exit 0，12.142 秒 |
| 全部自有声明审计 | exit 0，包含 2 条私有声明及完整表达式，没有截断类型 |
| 独立只读复核 | 独立 Python 进程返回 `REVALIDATED`，新增 normal/kernel 命令数为 0 |

预检采用 `lake --no-build env lean`，未生成目标对象；正式 normal 是目标的首次构建。原 293 个依赖、父模块验收身份、成功预检原件与原工作树由原固定检查器保护。本次没有重放旧依赖的正常编译或内核验收。

## 源码与记号修复

选定源码为 **5,545 bytes**，SHA-256 `00b11f60f73300ff8443ed72367c19f6c817fa5384d1449296b929a0155731ec`。

原源码为 5,533 bytes / `edb45d7c44440fdb68937fc0931c95c7a7ab0532ec26b1f20002b8669c8700a2`。只将一处尚未打开 scoped notation 的 `<+` 关系显式写成 `List.Sublist`；全部 proof bodies 字节保持不变。原、新源码、正反补丁及双 hash 记录在 [原、新源码与记号修复记录](repairs/sublist/REPAIR.json)。本次验证的是选定修复版本，不能称源码整体与原版本字节相同。

源码顶部保留了最初提交时的 SOURCE ONLY 注释，以保持已验收对象与源码的精确绑定；当前状态以本目录日期化的真实回执为准。没有为了改注释而重编译已验收证明。

## 完整证据

`first-disagreement-evidence.zip` 为 **713,080 bytes**，SHA-256 `2a0a3075f79bc9190e902a207489beeb4f9e1a3a5e2bd31809788549c1e464c0`。

共 86 个条目：85 个逐项列出 bytes/SHA-256 的成员，以及 `FILE_INDEX.json` 本身。包内保留完整 owner、operation、19 项成功预检原件、独立 readonly 结果及 21 个目标对象位置中实际存在的 8 个对象文件。控制端已核验全部成员 hash、索引 hash、归档 hash 与 ZIP CRC。

- [正式 PASS](evidence/PASS.json)
- [独立只读回执](evidence/READONLY_RESULT.json)
- [全部声明、完整类型与传递公理](evidence/OWNED_EXPORTS.json)
- [完整验证结果](evidence/VALIDATION_RESULTS.json)
- [原始成员索引](evidence/FILE_INDEX.json)
- [实际导出元数据](EXPORT_RESULT.json)
- 完整证据包 `first-disagreement-evidence.zip`（随本轮总归档交付）

本次新增一个正式 owner，P1.5 整体状态仍为 `whole_P1_5_complete = false`。原 21 项登记的 18/21 状态与本次三模块链分别记录。
