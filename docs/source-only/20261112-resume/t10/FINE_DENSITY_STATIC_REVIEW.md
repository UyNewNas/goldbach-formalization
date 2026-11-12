# FineDensity 源码选择与执行前置审查

**静态选本通过，实际远端驱动仍待实现。** 目标是 `ImbalancedChen.P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity`，源 SHA-256 为 `1942060c36cde2fb609dce8d370d29fa10701c5e6ed75159416e1c51cb8df7e5`。作者注册表 SHA-256 为 `bced738ce5f2f59a1d5d08639f17465679767225c8e86a0bfdb992ccddbd3afd`。独审 14 件清单 `FINE_DENSITY_STATIC_ALLOWLIST.json` 的 SHA-256 为 `918e42e3d345a0e6e903b00b8240bcda33f288576884ffb9cc15130c748d82bd`。

我从 10 个不可变提交的实际 Git 树找到每条原路径的 blob，逐件读回原始字节。对三个显式文本变换独立检查前像、匹配次数和后像。由最终源码的 import 头重建出的闭包有 1,808 个项目模块、3,436 条项目内边和 232 个不同的外部直引名，次序和源身份摘要均与清单一致。相比先前 full87，1,613 个选本逐字节一致，另有 191 个新增和 4 个已有同名 P2 修复。729 个旧第五层源确实全部同字节。原 T04 高阶 14 源中实际仅引入 12 源，另两份 `GroupedAtoms`、`JointHigh` 在本终端的真实闭包之外。这些都是源身份结论，仍无获准复用对象。

我独立重算现有官方 release 压缩包全部 323,605,374 字节的 SHA-256，得到 `8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`。22 个新原始成员的长度、SHA-256 与 Git blob 全部匹配，旧 335 项与原清单完全一致。新 reader 所需项目外相对路径应按这 22 个精确目的地安装，并记录真实解析、读回及绑定。运行时还须验证 Lean `v4.33.0-rc1`、锁定 Mathlib/native、真实 flags、setup/import/ABI 及 43 个 native research 源。P2 独立验证目标与本图交集 84 个，77 个源相同，7 个源有差异。

具体数学终端保留同一个 q、beta/k、共同预选 N0、同一 Q/rho 的密度上界和一次 compiler expense。计数仍含原有符号 `realPhysicalDistributionError` 和 `ceil(z)+(T+1)`。需要的检查包括六个实际定理、七个实际定义，以及继承的九个原第五层审计项；程序还须给出严格定义模块/序列化声明清单、全类型和传递公理。作业成功仍以实际供应模块、native 对象及原始未截断输出为准。此终端本身没有提供同一 rho 的全部有符号 PP/hUpper。

历史 `NATIVE_ACCEPTANCE_REQUIREMENTS.json` 同时写有旧 full87 精确 1,664 项及旧 1,607 项的包含关系。Fine 的数学闭包不含 `Full87R17PaidAudit`、`Full87RemoteAudit`、`P4AOriginalR17PaidIntegral`、`P4AOriginalR17SameCutoffPresieve`。未来 Fine 专用验收程序应冻结自己的精确重放集合，保留现有原 native 43 项的真实受控编译和 fresh replay。若保留单个 `T01Audit` 并新增单个 Fine 审计模块，集合为 1,808 + 43 + 1 + 1 = 1,853。任何合并两目标的验收都须另取实际依赖并集与相应完整类型。旧 full87 的验收状态保持独立。此处没有执行源安装、证明、数值证书、守护程序或 CI。
