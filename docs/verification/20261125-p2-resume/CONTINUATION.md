# P2 续作：原数值页 0080–0111 与全秩 Γ₅ Euler 预算

本轮从 `e008ae002d4cec5f01b127a11dbb13016be38c97` 继续，使用恢复后的
P2 私有编译工作区 `/workspace/p2-private-20261124`。1106 手稿固定为
`a988cba584d803ae2856a0de50efb582f4f3dd6a`。

**新增 36 个模块通过普通 Lean 编译、独立 stock `leanchecker` 重放和
完整 owned declaration/type/transitive-axiom 审计，合计 1,102 个 owned
声明。完整 P2 与实际 admissible Family 仍未闭合。**

## 本轮已验收增量

| 项目 | 新验收模块 | Owned 声明 | 精确范围 |
|---|---:|---:|---|
| 原数值页 0080–0111 | 32 | 1,088 | 原 ordinals 1280–1791，共 512 行 |
| 原 block 05、06 汇总 | 2 | 2 | 原 `checkSelected` / `Checked` 结论 |
| 完整列表的通用秩界 | 1 | 1 | 共同正幂下界与完整乘积上界推出长度界 |
| 物理 profile 的全秩 Euler 预算 | 1 | 11 | 从非零支撑推出秩界，高秩整函数恒零 |
| **本轮合计** | **36** | **1,102** | 不是看板节点数或新源码定理数 |

数值覆盖达到 **112 页、7 个原 block 汇总、1,792 行（0–1791）**。
原 Winner9 归档共 11,026 行，尚有 **9,234 行**不在当前已验收覆盖中。
这不是另一个 17,572 行历史账本的完成声明。

三个 gate 分开保留。普通编译作业为
`1858c1cc22424614b301d0dcec40da40`，重放及审计作业为
`35bb8aab714241bdb236586a3ae33e22`；后者的两个审计 worker 都以零退出。
所有 32 页都保持原 checker、原 row statements、原 archive references
和每页 16 个原行义务。唯一增加的是已经验收的 materialized helper
导入、open 和 soundness 应用；删除这些增加行后逐字节恢复原 renderer 输出。
前后哈希见 `materialized-pages80-111-source-change.json`。

## 全秩解析结论

活动模块 `ImbalancedChen.P2FiniteMarkedGamma5AllRankEulerBudget` 保留原
physical profile、old/fresh/tail 标签、Fin 坐标重排和原 `eulerWord`。
对固定 `a > 0`，定义

\[
N_0(a)=\max\{e,2^{2/a}\},\qquad K(a)=\lfloor4/a\rfloor_{\mathbb N}.
\]

当 `N ≥ N0(a)`、`N^a ≤ b`、`0 < width ≤ 1` 时，原非零 profile
供应每个坐标 `xᵢ > b/2 ≥ N^(a/2)`，并供应完整乘积
`physicalProduct x < exp(width) * N ≤ N²`。这些原支撑性质推出
`k + 2 + r ≤ K(a)`，包括重复坐标及两枚 fresh slots。

超过该秩时，先证明物理 profile 在整个实坐标空间恒零，再证明 Fin
profile 和任意原 Euler word 恒零。低秩情形直接调用已有 bounded-rank
预算。有限求和给出一个常数，同时控制每个 `q ≤ m` 和每个 `|w| ≤ q`：

\[
\left|\operatorname{eulerWord}_w(\operatorname{finPhysicalProfile})(v)\right|
\le C(1+\mathrm{width}^{-1})^q.
\]

`N0` 仅依赖 `a`，`C` 在全部移动 scale、endpoint、cutoff、width、rank
和物理点之前选择。结论没有额外的 rank 或完整乘积前提。
固定的正幂 cutoff 条件仍需由实际算术来源供应；本定理不代替这一步，
也不供应 collar 付款或 PP 分布。

验收作业 `ad5af8b1475349e7a8aa48789e358aae` 复用全部 11 个既有依赖，
完成一个新模块的三项 gate；源码 SHA256 为
`798c9417b87278c82f1f9b763bf800e6bf0ab32324fe7312a609522d6c24372b`。
9 个源码声明对应 11 个完整 owned 声明。
初次编译仅被 strict style linter 拒绝；修复只把一个 `<;>` 改为 `;`，
保持 statement、imports、全部严格选项不变。原失败、精确 diff 和接受版本
记录在 `all-rank-euler/`；没有关闭 linter 或降低 gate。

`ImbalancedChen.P2MarkedSourceRankCore` 独立通过作业
`bf050ecbd6a443f58fac442473a5528c`，SHA256 为
`991d1db3a0cf3d7f291b84ff38bb421dc0011b09a4c2b8848f4a0077b972dc76`。
这个单声明引理处理完整列表的重数与空表，要求其调用者供应下界和乘积界。
两个已验收 Lean 文件保留编译前头注释的精确字节；现行状态以收据和
源哈希为准，不能因历史注释把已接受版本和未接受草稿混淆。

## 实际来源代码与复用边界

`docs/source-only/20261125-p2-actual-source-rank/` 保存真实 U4 来源的
秩界、Euler caller 和平台等式源码。列表是
`old ++ qs ++ m.primeFactorsList`，保留全部 old slots、fresh slots、
重复素因子和单位尾；共同下界与完整乘积界都由原 history/gate 引理导出。
没有把历史深度 440 当作总秩，也没有把目标秩界新增为调用者前提。

其选源清单含 327 个文件：282 份当前仓库精确复用、38 份固定历史提交
原供应，以及 7 份新候选或机械 core。三个实际入口连同 9 个已有活动模块
形成 336 个项目模块的静态闭包，49 个 direct native roots。
独立审查确认项目路径、SHA、import 可达性和机械 owner 后像完整；
这些检查不等于共同 elaboration、kernel replay 或 owned audit。

机械抽取保留 9 个公开 FQN 和 16 段原声明正文，7 个 private helper
需要在新 compiler owner 下重新审计。原完整 owner 的后像一并保存。
Fibre 的旧 `a0/a2` owner 与新常量 core 不能共同导入；私有工作树在保存
旧源、record、audit 和对象文件后，才采用既有抽取后像。
immutable baseline 没有被修改，旧收据不授予新字节的验收信用。

历史 native 供应已经找到原源码与生产验核记录，但新增范围的对象和
原 receipt payload 尚未在当前 P2 环境恢复。还存在 active/research
不同选版及裸名研究 imports 的明确边界，需要保持来源、实际 import
facets 和运行时绑定。现有 515 个已资格化 native 输入继续复用；
没有因为对象缺失而重写稿外库定理。原查询、静态选源报告及未资格化
census 保存在该目录的 `upstream-evidence/native/`。

`docs/source-only/20261125-p2-actual-small-payment/` 保存另一条新 consumer：
将已有 scalar 小完整乘积界应用到真实 U3/U4 marked history，再以两个
`ε/2` 接回原 seed 与四轮不等式。它保留 Γ₅、大完整乘积差额、ordinaryAP
与以前轮次反馈，未声称消除全部债务。该候选仍无新编译或 kernel 信用。
其部分选源额外归档了 70 份已有 immutable 原供应，764 个已选项目模块
均有精确源定位；仍有 5 个项目 import 未在本清单中定位，以及
`P5OriginalSignedMidpoint` 原版/v3 的未决分叉。详见该目录的
`SOURCE_INSTALL_MANIFEST.json` 与 `UNRESOLVED_IMPORTS.json`，不能将其
标成完整 closure 或把未定位项称为不存在已有证明。

## 验收证据与历史去重

新包 `evidence-numerical80-111-rank-20261125.slim.tar.xz` 的 SHA256 为
`327f0963b7c43cf3410c844e279a85d6fe35b8474e2cbf0395666f52ff838a5a`。
它完整保留 36 个模块的三项 gate、owned inventory、可读类型、传递公理
结果及源/依赖绑定。`NUMERICAL80_111_RANK_ARCHIVE_VERIFICATION.json`
验证了 444 个原成员和 95 个源码引用的保真；归档验证本身不增加证明信用。

上一轮主归档以 `main-evidence-parts/` 的 37 个 raw parts 发布，避免再
重复发布同一份 44.3 MB 整包。`MAIN_ARCHIVE_PARTS.json` 保存每片顺序、
长度、SHA256、Git blob SHA 和整包 SHA。按序连接后，必须恢复
44,304,524 bytes、SHA256
`92c1067a1694ea74af4d15ee841199ab72094f2147b7651e77cf21f60e68faf4`。
其原 verifier 已通过；完整重组方法见 `main-evidence-parts/README.md`。

七包逐声明核对已经通过：**256 个去重模块、9,709 个唯一 owned 声明**，
跨模块同名归属冲突为零；允许的传递公理仅为 `propext`、
`Classical.choice`、`Quot.sound`。详见 `ACCEPTED_UNION.json` 和
`ACCEPTED_UNION_VERIFICATION.json`。
历史 checkpoint 和 main 包重复包含同一 `P2Winner9OriginalFull87Bridge`；
它的源、对象和编译闭包指纹相同，但 audit driver、receipt 与 attempt
路径不同。必须逐 owned name/type/axiom 核对后只计一次，不能把各包
摘要直接相加。该并集仍只是这些证据包的接受集合，不是整个项目节点
普查，也不宣称全部模块已经在一个统一的新 native 环境中共同导入。

## 完整 P2 的未闭合项

- Winner9 剩余 9,234 条原数值行。
- 原 same-rho signed VM/PP 估计及 `remainingRows` 的任意 log-saving
  供应；已有 proper-power 结果供应 prime/VM 比较，VM 本体另需证明。
- 实际 Γ₅ Family 的来源接线、整数支撑与 collar 付款，以及 W1/W2
  的有向差额付款；新小乘积 consumer 只处理其中明确的一部分。
- 原 Wu 实函数的 29 条 H247 endpoint licences 及相应实际积分供应。

原 all22 密度源码、Full87 seed 接线和 P3 proper-power 成果均已有可靠
出处，继续复用。上述开放义务没有被改名成前提后计作完成；本轮也没有
证明稿件存在数学反例。`full_p2_complete` 和完整 Family 状态保持 false。
