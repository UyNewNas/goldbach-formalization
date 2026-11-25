# 原 U4 Γ₅ 实际来源：秩界、物理平台与 Euler 预算接线

1106 稿件固定为 `a988cba584d803ae2856a0de50efb582f4f3dd6a`。
本目录保存实际来源接线的证明源码、既有供应的精确选版和独立静态审查。
**实际来源的三个新模块及三个机械抽取 core 尚未获得本轮联合编译、
独立 kernel replay 和 complete-owned audit；它们仍是待编译源码。**

通用的 `ImbalancedChen.P2MarkedSourceRankCore` 已在活动源码目录独立通过
三项核验，源 SHA256 为
`991d1db3a0cf3d7f291b84ff38bb421dc0011b09a4c2b8848f4a0077b972dc76`，
验核作业为 `bf050ecbd6a443f58fac442473a5528c`，完整 owned inventory 为一个声明。
它的已编译字节保留了编译前的头注释；当前验收状态以精确源码绑定的收据为准。
该引理本身只证明共同正幂下界与完整乘积上界蕴含固定长度界，
不供应实际来源的下界或乘积证明。

## 新源码的数学范围

`P2FiniteMarkedGamma5ActualRank` 使用真实 `LevelIndex`、`badLabels` 和
`roughNumbers`，保留列表 `old ++ qs ++ m.primeFactorsList` 的顺序与重数。
原历史的素性、粗糙度和尺度引理供应每个槽的共同幂次下界；
原 product gate 供应完整乘积不超过 `N`。据此得到固定秩界
`⌊frozenLeafCutoffFloor⁻¹⌋₊`，而不是把历史深度 440 当作总秩。
单位尾和重复素因子仍是同一列表证明的字面情形。

`P2FiniteMarkedGamma5ActualEulerBudget` 把该实际秩界接到已经验收的
`finPhysicalProfile_boundedRank_mixedEuler_budget`，常数位于所有移动参数之前。
`P2FiniteMarkedGamma5ActualPhysicalPlateau` 使用原 old/fresh/tail 标签坐标、
确切对数字典和原 SeedPlateau，证明真实来源处物理 profile 等于一。
这些源码不宣称已经完成 collar 付款、同一 rho 的 PP 分布或整个 Family。

## 复用与唯一 owner

`SOURCE_INSTALL_MANIFEST.json` 为 327 个选定文件提供仓库相对路径和 SHA256。
其中 282 份直接复用当前仓库已有字节，新增的 45 份包括新候选、机械抽取
以及从固定历史提交恢复的原供应。复用的原供应保存在 `reused-suppliers/`；
它们不是本轮重证的定理，也不因复制而获得新的验收信用。

三个 H430 core 逐字节搬移原声明和证明，保留九个公开 FQN；
七个 private helper 的 compiler owner 会改变，必须在实际编译后完整审计。
`owner-postimages/` 保留三个原 owner 的 import/removal 后像，之后若导入
完整原 owner，必须使用这些后像，不能同时引入两份定义。
`extraction-evidence/` 和 `review/` 保存精确反向重构及唯一 owner 检查。

`P2SeedOmegaLiteralFibre` 也必须使用仓库中已经存在的常量抽取后像：
该后像从旧 owner 移出 `a0`、`a2`，转而导入 `P2SeedOmegaCutoffConstants`。
旧 owner 与新常量 core 同时导入会形成重复定义。
云端定点重绑须先保存旧源码、编译记录和 audit；旧收据不能验收新字节。

## 当前验收边界

本目录的静态完整性、源哈希、公开 FQN 和证明正文检查已经完成。
历史 native 依赖另有可靠来源与原生产记录，仍需在当前 P2 工作区绑定
精确源、对象、实际 import facets 和运行时环境。
源清单的 327 个文件、49 个 direct native roots，以及源码声明个数，
均不能当作已编译模块数或 kernel-owned 声明数。

完整 P2 仍有独立的原始分布、W1/W2 差额付款和实际 Wu 函数 endpoint
义务；本次接线不消除这些条件。小完整乘积付款的独立候选及稿内边界
审计见相邻 `20261125-p2-actual-small-payment/`。
