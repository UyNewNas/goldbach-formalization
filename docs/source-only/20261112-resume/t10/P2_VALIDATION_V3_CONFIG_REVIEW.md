# P2 整数质量 R2 独立远端配置审查

**25 个驱动路径通过静态复核，共 241,459 字节。** 逐路径白名单 `P2_VALIDATION_V3_SCOPED_CONFIG_ALLOWLIST.json` 的 SHA-256 为 `06c0ec79843935f339e33fd998b25391a005eaa879ac59538b4bdcd7f91b6898`。该清单可供根任务从唯一父提交 `356c3782e9428098a2fcbfb18c689bef264d84fa` 创建分支 `ci/p2-integer-mass-r2-20261112` 的指定驱动。

- 原始 Git 对象逐份读回。97 个 baseline 完整选本记录仍与 v2 逐字节一致。4 个失败模块逐个对应已发表 `51859a24c91580f885afd2a781dcb48b07177529` 的 R2 独审后像。8,003 字节原 ABI 在同提交的 p2-recovered 路径，内容 SHA-256 仍为 `389bf428903797900dbc07a7dbf3471909f268705a389e0d61e02d7173d1c2ca`。四个修复仍按各自原来的 canonical 模块安装。
- 102 个模块名称、顺序、import 边、数据选择和三项工具链／湖配置 pin 保持。ABI 自然闭包 101 个，另加同作业强制审计的 `ImbalancedChen.FinitePiIntegral`。阶段 provenance 的单项 `overlay` 字段标识 ABI，完整的逐项 `modules` 记录才是这 5 个 source-commit 来源的安装清单。旧 P4 inventory 失败仍保留为历史事实，必须在新环境严格检查。
- 逐项重建 v2 到 v3 的两个驱动逻辑常量和 workflow 的 source/ref、manifest、分支、bundle 替换。运行步骤、串行 12 GiB trust-zero 守卫、编译和新 kernel 逐模块重放、完整所有权与 serialized 声明比较、两种未缩略类型和全传递公理保持。诊断仍在原 throw 之前，比较失败即终止。证据收集继续保留失败经手的文件，实际证明状态以新 run 的终态为准。
- 独立从父 Git 树读取了全部 7 个 workflow。6 个原样，VE 的唯一变更是加入新分支的一行 branches-ignore。新增 workflow 只对该分支且自己路径变更的 push 触发，使用 `goldbach-p0-heavy` 及 `cancel-in-progress: false`。没有第二个符合本次 push 的 workflow。实际 driver raw 父、树、25 个 blob 及运行数仍由根在发表后查验。

冻结作者注册表 SHA-256 为 `89922f3feaa15a9a3d9da81dc254ccccd2857df9ef3570ad6323ad4fe2af0b24`，manifest 为 `6d876300c58ee32a2204198142e6863b2c23d2929cab4b1641ca06d551d6714b`。驱动外置选择文件为 `0cd5a5f54143b87b16827059c2efa2a2bbd5a0c97aa29920499e43da0ef2c5d3`，实际根安装目的地为 `verification/parts/p0/P2_INTEGER_MASS_DRIVER_SELECTION.json`。选本及配置均未在本地执行。没有新增数学绿色节点或获准复用的旧证明对象。
