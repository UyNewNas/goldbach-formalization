# P2.4 原始 compact 端点的原生输入资格

`p24_qualify_native_inputs.py` 是本轮 P2.4 的独立调用适配器。它从当前
`ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint` 递归读取项目源码，
再沿实际原生 imports 取完整原生源码闭包。它不改 Winner9 的固定请求、
P6 的历史范围、现有 `ExternalSnapshot` 消费契约或任一冻结 caller 规则。

2026-11-25 的 **before** 图为 339 个项目模块、26 个直接原生入口、826 个原生模块。
其中额外的 LiuPan 链来自通用 reciprocal 算术与 U8 应用共处同一模块的导入关系。
`P2GuardedReciprocalRoundingCore` 原样抽取后，当前实际源码图为 **322 个项目模块、
22 个直接原生入口、515 个原生模块**；移除 17 个项目依赖及 311 个原生依赖。
原通用算术证明块与 U8 应用保留情况由独立的 Core 抽取记录说明。

前后证据分别为
`docs/source-only/20261125-p24-original-compact/p1_whole_native_census.json`
（before，SHA `945ca3bd3863d62a512e7f2a519adb4b5e7d33134dec52d1787780eb25e5d01e`）和
`docs/source-only/20261125-p24-original-compact/scoped_reciprocal_core_census.json`
（after，SHA `d81aef9644faf9d91f821a2162cdf7ef65de9eb9881ddbdefa748523726597ed`）。
after 的 515 个原生源码均落在固定 pin census 中，源码 SHA 全部与 before P1 探针中
实际 source-matching CP rows 相符。该探针对这 515 项的 own `.olean` 检查也全部匹配；
这些结果不构成完整 actual-import-map/runtime 资格或 kernel replay。
适配器每次仍从实际源码重算闭包，不把任一历史计数当作完成性证据。

## 准许的操作与边界

适配器只读取现有 P1 源码、对象和收据，在 P2.4 隔离 checkout 内的新目录写证据。
它不调用 Lean、Lake、leanchecker、对象装载器或本机编译器，不修改 blue 的包或对象，
不复制生产证明，不授予项目缓存、编译、kernel replay 或数学端点的验收信用。

只有所有实际原生 provider 均具有完整资格、所有当前物理输入后检通过、现有
`ExternalSnapshot` 消费者验证通过，才发布 `EXTERNAL_SNAPSHOT.json`。
不完整时退出码为 2，保存 `QUALIFICATION.json` 的 `direct_blockers` 与依赖阻塞；
它不会发布可消费的完整快照。初始化或后检错误另记 `FAILURE.json`。

## 固定历史锚

| 输入 | SHA-256 |
| --- | --- |
| T01 原始 `CHECKPOINT.json`，67,075,207 bytes | `aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a` |
| P1 member `INSTALL_RECEIPT.json`，617 provider | `f5b115fc46b5136a4d11df94052500acbc439f1190bb4cd61cdd1df02729f6da` |
| member 指向的原 P6 `MANIFEST.json` | `aff5553e88cb4434cbd2e2b9197e923a83b3312997cf822b822a790c43886ce9` |
| member 指向的 P6 `INSTALL_RECEIPT.json` | `0c0c5620ff231105d95149d631f55651454019b06c80e144e901d8d3b4a631cd` |
| 原 `checkpoint_original_protocol.py` | `cfcb50064a13632a4a0fa8372d27bf86dd91f92eb6c38482afa575cf34921aff` |

这些路径与字段通过 P1 只读任务 `job_d94adee6f9154222abbf2464e65689d6`
复查。任务于本轮成功结束，原 CP、manifest、receipt 的物理 SHA 均与上表相同。
这次读取不构成 native qualification，也不构成编译或证明结果。

选取原生记录复用 `repack_winner9_native_cache.select_payloads` 的纯选择函数，
原 source、guarded command、setup、trace、facets 和 classification 原样保留。
新调用者不调用 Winner9 固定请求构造器或范围验证器，也不伪称满足其固定 515 请求。
所需 ZIP 元数据 member 的长度、SHA 和 content-addressed 路径由固定 CP 逐项验证；
适配器不声称重新散列了整个 3.37 GB ZIP。

## 每个 provider 的检查

1. 当前原生 source SHA、长度、Git blob、直接 imports，与实际源闭包和原 CP 记录
   相符；当前包 HEAD 与项目锁定版本、CP pin 相符。member 历史名单中的 provider
   还须匹配其 source/import/map 交叉记录。没有 member 行的 provider 不受旧名单限制，
   但仍必须通过原 CP 的全部真实 guarded 完成、source/setup/trace、map/runtime 和当前
   facets 门；其收据明确 `member_provider_present: false`，不声称有 member 支持。
2. 原始 setup/trace/hash sidecars 从原 ZIP 读取，不改写历史绝对路径。空 options、
   plugins、dynlibs，真实 guarded `-t0` 命令及原 trace output descriptor 全部检查。
3. 从真实 setup 的 `importArts` 保留原分组和顺序，按原命令 cwd 解析相对路径，
   用原 CP 的逐文件 SHA 重算完整 historical actual-import-map SHA。
4. 每个原输入 source、loadable facet 的当前路径和 SHA 都重新检查。所有原路径到
   当前物理路径的映射写入 `ORIGINAL_TO_CURRENT_IMPORTS.json`。provider 收据固定
   该表 SHA、原 setup 路径、旧 map SHA 和新 map SHA；完整新 map 可确定地重建，
   不为数百个 provider 重复保存同一物理文件列表。
5. provider 自己的 `.olean`、`.olean.server`、`.olean.private`、`.ir`、`.ir.sig`
   与原 CP 的 facet 集合和 SHA 相符。路径缺失、增加无来源 facet、字节变化均拒绝。
6. 原运行时 11 项真实 payload 和 pinned Lean shared-library ABI 与当前字节相符。
   宿主 C library 差异逐项保留，不伪称相等，不安装任何 `.so`、`.a` 或 `.o`。
7. 最后重新检查所有绑定的物理输入和包版本。完整快照由既有消费者检查源码、
   依赖签名和实际 `LEAN_PATH` 首个解析路径；共享包只作为只读 external inputs。

`CURRENT_CORE_RUNTIME_INPUTS.json` 独立冻结当前 Lean/Std/Init 的源码头闭包及所有
可装载 facets。旧 package setup 不提供隐含 core 的逐项历史 hash；此当前冻结不会
被回填成历史事实，也不会解除原隔离分类。

## 已知 Architect.Command 边界

原 CP 的 guarded row 54 是 `Architect.Command`。其源码 SHA 为
`8497d574c12414908829e8b25a96e0ce52c643bd48da66b678d1623db395696a`，
原 setup 为 144 bytes，`importArts = {}`，七项 descriptor 均 matched；
但原分类仍是 `PACKAGE_PARTIAL_OR_UNBOUND_OUTPUTS_QUARANTINED`。
固定的 `ARCHITECT_COMMAND_LEAF_RULE.json` 也明确没有历史 per-core olean hashes。

所以 member 的 617 项名单以及新的当前 core 冻结都不能使这一叶子自动变成
`EXACT_ORIGINAL_IMPORTS_REBOUND`。本版适配器没有解除它的分支，也没有自动编译入口。
缺少完整且可重验的独立 fresh leaf 收据时，它会成为明确的 direct blocker。
P2 任务 `77e605315ba246b4a2c30811d34fe812` 的完整日志明确记载该叶子获得
`FRESH_PRIVATE_SOURCE_COMPILATION`；但该任务整体 exit code 为 2，运行约 454.84 秒，
后续原生输入仍有缺项，完整资格没有完成。完整旧日志保存在
`docs/verification/20261124-p2-private/cloud-jobs/77e605315ba246b4a2c30811d34fe812.json`。
若取得完整原 leaf 收据，需逐项检查
其当时的 source、实际 core 输入、运行时、命令、前后 hash、输出和日志，才能另行
审阅物理重绑。收据未知或缺失时不得补填历史依赖签名。
具体导出补项和 producer 原字节的判定方法见 `p24_fresh_leaf_reuse_requirements.md`。

## 本轮静态验证记录

脚本 SHA `7d6d21862fe96b2c504befd03d02c235839b499d034cf833abc75e57bc8230d3`
上的 15 项本地针对性测试通过，独立 reviewer 在同一 SHA 上重跑全部 15 项并通过，
未发现剩余 Critical/Important 静态问题。细节与边界记录在
`verification/part2/p24_native_input_review.json`。
这些是本地 Python 负例和源码审查结果；本记录不声称已经执行完整 P1 donor/ZIP
资格、已发布完整 native snapshot、已完成 Lean 编译或 kernel 验收。

## P1 运行方式

由主代理发布当前脚本后，在隔离 checkout 中运行：

```bash
python3 -B verification/part2/p24_qualify_native_inputs.py \
  --project-root /workspace/p24-original-compact-20261125 \
  --donor-root /workspace/blue-member-build \
  --out /workspace/p24-original-compact-20261125/.lake/p24-native/attempt-001
```

新的 attempt 目录必须不存在。此命令只做读取与资格证据输出；当前历史隔离叶子没有
独立收据时应返回 2。不要把返回 2、部分 provider qualified 或 diagnostic 编译通过
改写为完成。完整快照真实发布后，主代理才能把它作为既有私有 runner 的
`--external-snapshot` 输入；真实源编译、独立 kernel replay 和声明/axiom 审计仍需另做。

本地无编译负例：

```bash
python3 -B -m unittest discover -s verification/part2 -p test_p24_qualify_native_inputs.py
```
