# P0 Round 4：P1 固定源码接收回执

## 接收结论

**可接收的最小生产批为一个模块：`ImbalancedChen.StoredHistoricalBoxPermit`，14 项所属声明。**
来源固定提交 `744316efd1887f21c91dd4b63c218fa27704c931`；对齐已核验集成 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`。
本次只读消费者实际核验了固定 Git 文件和原始证据。没有启动 Lean、Codex、CI、下载工具链或修改任何 Part / P0 分支。
最终新集成 SHA 的规范完整构建、根 stock replay、公理与完整类型导出仍由 P0 执行；此处不代称已执行。

## 实际回执

| 目标 | 严格官方 frontend 编译 | 原装 leanchecker 重放 | 源 SHA256 | 主 olean SHA256 |
| --- | ---: | ---: | --- | --- |
| StoredHistoricalBoxPermit | exit 0，4.776 s | exit 0，24.410 s | `50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d` | `c05b355bb77a95468850321807846cfb743955e2a77d5e2aafca02185bc4a8ee` |
| StoredCapProbe | exit 0，17.538 s | exit 0，19.043 s | `41b1ac2242e8b4e84b72c98772bb52b7ec9814807466b9ef19ccb15f4e4dff49` | `9b7282d02b03c79a8ae6cc73520386934b09df64402f05ea91d2e57ae1c43cd8` |
| StoredCapAudit | exit 0，109.832 s | exit 0，7.447 s | `c5cb2cd40e7d8b591302ccb2e3b0e36c2b3a99a786385316feeec62db4617b33` | `1e2783cf117947f93707fe78d3b1bd0d403330d3b9abf9144c3fb02981831950` |

生产者使用原版 `Lean.Elab.runFrontend`、`trustLevel = 0`、`warningAsError = true`，原版 Lake runtime 运行，随后原版 `leanchecker --verbose` 三次顺序执行。原 stock Lean CLI 当时启动失败；没有把 `check.sh` 记为实际执行。
编译/重放未启用 metadata adapter。归档 runtime 驱动含官方 `unsafe Lean.enableInitializersExecution` 初始化生命周期调用；该驱动不被生产 Lean 模块导入。本消费者没有运行该驱动。生产源码无 `sorry`、`admit`、新公理、`native_decide` 或 `unsafe`。

完整 defining-module census：36 = 14 生产 + 22 probe；包括生成声明。逐条原始日志记录与 receipt 完全一致；唯一传递公理并集为 `propext`、`Classical.choice`、`Quot.sound`。
**类型格式为完整默认 `Meta.ppExpr`，不是 `pp.all`**。36 条均无省略标志，其中 14 条生产类型在 `COMPILER_TYPES_PRODUCTION_14.json`；全部 36 条在 `COMPILER_TYPES_36.json`。
源码 2 个定义及 10 个公开定理头独立保存在 `SOURCE_DECLARATIONS_12.json`；`KEY_INTERFACES.md` 逐项并列源码声明头与原始编译器类型。新集成应重新导出这 14 项全量 pp.all；不能将 probe 22 项记作生产声明。

## 本消费者实际检查

原始 archive 4,696,213 字节、130 个成员、129 个 payload 文件：SHA256 `206070fd3bb38c2334d64cead0e58405fa7f73c2400a6d0e77878a065976392a`。成员集、路径安全、字节数、哈希全部读回通过。
固定 receipt SHA256 `7f687c1d1b61ec3142de63f1458b5dcf650928348e6b4231b871a121c99d4ee1` 与 archive 内原件逐字相同。
29 个 archive repo 文件绑定到固定提交。16 个本地供应模块中 3 个本批实际编译、13 个复用；13 个旧供应源码逐字等于 P0 `28fd630…`。31 条本地直接导入对象绑定相符，3 个目标编译/重放的源、主对象和直接导入记录前后一致。
3,368 个固定缓存供应的源码/对象清单与原始固定 pin/cache 记录保存。23,606 个未嵌入引用只做跨记录哈希绑定核对，不声称在本会话重新取得或重哈希其二进制。
规范 pins、CurrentMainTheorem、CurrentNumericalTransfer、CURRENT_MANUSCRIPT_MAP、EXTERNAL_REUSE 未变。所有检查细目在 `CHECKS.json`，可复用摘要在 `REUSE_RECEIPT.json`。
本批 permit 第一次目标严格编译即通过；没有目标 Lean 诊断或 P0 证明修复。消费者第一次执行也通过。

## 最小文件所有权与导入

`INSTALL_MANIFEST.json` 列明 12 个建议原字节接收文件：1 个生产源码 + `verification/parts/p1/round2/permit/` 的 11 个 owner 文件。
其中 source / probe / audit 三个 Lean 目标是唯一新增编译目标；原始运行日志与 runtime provenance 放在 `EVIDENCE.tar.gz` 内，无需把 archive 的运行器抽出到生产依赖。

另有可保留的两份补充证据：`round2/PART0_28FD_PERMIT_IMPORT.patch` 与 `PART0_IMPORT_CHECK.json`。
P0 公共根只需新增 `import ImbalancedChen.StoredHistoricalBoxPermit`。
不接来源 workflow，不套用面向旧根的累计 `permit/INTEGRATION.patch`。本批无需更改其他生产源码。

## 数学接口及未闭合输入

唯一直接生产依赖为已有 `ImbalancedChen.SelectedPrefixRationalMesh`，在本集成中源码相同。
`storedBoxCapCheck` 对实际储存有理 cap 验证严格区间 `selectedCapLower < cap < selectedCapUpper`，无需等于自动 midpoint。
`storedMeshCapCheck` 在选定有限共同 Ico 网格上逐 cell 取实际 `I j`、`old j`、`nu j`、`cap j`，而不是枚举整个 cell 函数空间。
其 soundness 证明 old < cap、cap < nu、1/2 < cap、全部前缀平方门、所选子乘积平方门及 cap < 实际 variable envelope；actual_square_gates 保留真实自然数乘积与处理坐标 `i < k`。

需要调用方真实供应：采用表 J/I/old/nu/cap、有限 checker = true、每个 old 与继承历史有效前层的等式、实际载体字典、全局覆盖、支持和 factorization。old/new own-cube 门仍分离；未选 cell 的历史 fallback 不由该局部许可代替。此模块没有 K/c 密度或积分估计前提，也不提供它们。
接收 Part：P2 实例化采用表；P3 接真实平方乘积的分布支持接口；P4-A 在同一实际 rho/cap 上使用；P5 连接实际算术 ledger 与积分项；P0 统一导入核验。P5 依然只等 P4-A，不等 P4-B。

## 两份第五层源码：已固定，仍未编译

| 文件 | 当前固定源 SHA256 | 与 P0 前次暂存候选比较 |
| --- | --- | --- |
| HistoricalUpperFiveCellGeometry.lean | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` | 字节相同 |
| ActualHistoricalFifthCellIntegral.lean | `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de` | 仅边界处理说明注释改动；原暂存 hash 为 `dd9afad8cae4c977b8c6916e12ac38d0c4edeb5f7b1e0d42768958bae30f031a` |

Probe 另增加 `table_levelCheck` 的 kernel computation；audit 不变。差异及四目标身份保存在 `FIFTH_SNAPSHOT_COMPARISON.json` 和对应 `.diff`。
来源明确仍未取得先前独立报告的“继承前层选择、仅过单模块编译”候选身份；本批固定这两份续作并不对应或认证该先前独立候选。其状态继续 `SOURCE_PENDING`。

四目标（两生产 + probe + audit）均 `frontend_started=false`、`compiled=false`、`replayed=false`、`audit_executed=false`。主恢复队列在 162 / 683 完成依赖处停止：44 复用、118 实际编译，四目标均未开始。会话退出 130，底层 Lean 子进程独立退出码未观测；这是停止检查点，不是目标证明失败。
checkpoint archive `6de302f9952ae29b0f4e6e76cc7e2967ad9900db8265503091e8179ae90efbee`，614,322 字节、190 成员、189 payload；本消费者全部读回验证通过。此结论只验证候选证据身份，不转为目标编译通过。见 `CANDIDATE_RECEIPT.json`。
尚缺 `actualHistoricalFifthSaving` 全嵌套和到 tuple correction 的桥、采用 multilevel policy 实例、完整积分组合及 K/c 解析估计；两候选都不进入已验证根导入。
