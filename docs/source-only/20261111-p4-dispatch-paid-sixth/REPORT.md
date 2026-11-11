# P4：最终 All22 分派中九项 sixth 付款的共同装配

SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

基线：`6eed80494ec6432efa739c7cf1ce3e61882da3eb`。
分支：`chatgpt/p4-uniform-correction-20261111`。
本轮源码：`P4AOriginalFiniteAll22PaidSixth.lean`，安装模块为
`ImbalancedChen.P4AOriginalFiniteAll22PaidSixth`。
准确源码 Git blob：`cdef0be4f600a2cb88be6acd756e3d451c9eb40a`。
精确依赖、声明清单和安装映射见 `DEPENDENCIES.json`。

## 复用、稿内位置与归属

先核原 All22 structural ledger、T09 的
`ALL22_DISPATCH_STRUCTURE_REVIEW.md`、`LATER_SIXTH_ORDINARY_PAYMENT_REVIEW.md`、
`YELLOW_SCOPE_VERDICT.md` 及暂停交接。最终 raw telescope 已存在，
saved、eleven、later 的实际算术付款也分别已有源；不能再重做这些积分、
2631-simplex floor、八个 epoch 的素数均值或 high-sector 相等式。

原稿依据为 `UyNewNas/chen-imbalanced-semiprimes` 的
`paper/release-20261106/en/argument.tex`，Git blob
`90234d94460f1d7d59982635d7bf54c9b19250da`：
293–305 行为 finite realization 和符号敏感 attachment，
1039–1048 行为共同参数先于目标的次序，
1078–1086 行为四正项减 22 项、每次在实际父策略上计差。
根目录 `CURRENT_MANUSCRIPT_MAP.md` 是较旧记录，未将它冒充当前完整映射。

检查了 `docs/EXTERNAL_REUSE.md` 和固定依赖。本轮只用现有仓库的真实供应定理、
Mathlib 的 filter/min/max/线性代数接口，不新建任何外部解析定理。
完整非紧第三积分尾、可积性、统一 L1 误差已在
`ActualThirdPrefixTailIntegralCore`、
`ActualExtendedThirdFiniteTailIntegral`、
`ActualExtendedThirdKernelL1Convergence`、
`ActualExtendedThirdFunctionalConvergence`、
`Part4ActualThirdTailBound` 有源，故不重复实现。
历史 old3 及 ordered fresh 四正项也已有直接 cofinal 终端，
本轮直接消费 `P4AOrderedThirdPositiveRoot.original_four_positive`，
不换成另一套 compact policy。

新文件只写入本轮独立目录。前轮 P4B correction、各 T01/T03/T04/T05 冻结包、
P1/P2/P3/P5 工作、工作流及依赖均未修改。暂停记录提到的
`successor_early_135` 与 `successor_smooth_count` 草稿没有收录在当前可读远程基线；
注明未核实，不据此断言没有既有工作，也没有连接用户本机恢复它们。

## 本轮实际推导

`lowerSaved_eq_paid_source` 与 `lowerLater_eq_paid_source` 消费现有
`dispatch_saved`、`dispatch_later`，在同一 `data e q a`、
同一目标、同一 cap=N 和 cutoff 下，将真实 final dispatcher 的相邻差
识别成已经支付的 ordinary signed source。
`lowerEleven_eq_paid_source` 直接复用原 RawLedger 的恒等式。
三个 bank 都是同一 `NewFifthUnion.data` 的 definitional alias。

名义槽严格为零基 slots 3、6、7…13，共九项。
later 的八个实际 epoch 只对应原七个名义槽，不能按八项再扣一次。
选定 G7 修复版的 `originalFloor` 等于 literal slot 6；
未使用较旧替代 floor。

`exists_common_root_and_paid_sixth` 实际交叉所有见证：

`eta,eMax → n0 → 所有 n≥n0 → E≤eMax → 所有 rational 0<e<E
→ 任意 qMin → q0≥qMin → 所有 q≥q0 → a,omega → eventual even N`。

n0 是 saved/eleven/later 三个门限的最大值；E 是四正项门限、
1/64000、eleven/later 门限和调用者 eMax 的最小值；
q0 包含调用者既有 qMin 和四个供应定理的门限。
保留 `0<omega<thirdPrefixRho`、`omega≤a≤1/800`，
因此两个要求 `a≤1/100` 的供应定理可用于同一参数。
N 门限位于固定 a、omega 之后，不宣称在趋零 omega 上统一的 N 门限。

四正项 root 及 saved、eleven、later 三组各用 eta/4；
一次合并产生总 eta。无误差被删除或重复支付。

`normalized_final_eq_scalar` 直接读取原 `exact_all22_telescope`。
`exists_common_final_raw_upper` 因此得到最终实际 raw 系数的归一化密度：

```
normalize(rawRoot(finalPolicy))
  < sum(original positive endpoints) - paidSixthSlots
      - lowerEarly - lowerEighth - upperFallback + eta.
```

未付十三项完整保留为实际 signed 算术量：
early 0/1/2、第八阶 14…21、upper fallback 4/5。
m、r 可在该 N 后选择，是因为此终端没有估计或付款其相应项。

`physical_upper_lt_of_scalar` 只把这个标量界按正的
C_N/log N 放入原 physical upper 表达式，保留同一 final policy 的
实际 presieve correction 和一笔 compiler expense。
其明确的 hscalar 前提是代数转换输入；它没有新增最终 density 或 PP 假设，
也没有宣称物理 density 自身已经满足这个上界。

## 消除、剩余与验证

候选源码层面补上了九项既有付款在最终实际 dispatcher 上的共同
n/e/q/a/omega/N 装配和归一化 raw density 终端。
这不是重新证明九项原始付款。

仍欠：
- early 0/1/2 的实际误差控制、舍入及共同选择；`lowerEarlyDefect` 未设符号；
- 其余第八阶和 upper fallback 付款接入此同一 final dispatcher 的完整共选；
- 剩余 density reserve、最终同 Q/rho 的 signed PP 及真实计数上界；
- 精确源码完整编译、展开类型、import objects、传递公理和内核检查。
P1.4、P3.6、P5.6 或 P2 的整节点并未因本次组装被假定完成。
已有明确供应版本仅按 `DEPENDENCIES.json` 消费。

静态证据：新 Lean 源码禁用 token 扫描零匹配；8 个显式 export；
4 个直接供应的 Git blob 与精确基线文件逐字回读一致；
独立范围/数学审阅及另一位独立 Lean 源码审阅见 `REVIEW.md`。
这均不等于 elaboration 或编译通过。

当前工具没有可用执行环境。不运行 Lean/Lake/内核/有限证书，
不使用用户 Codex 额度或用户本机，不触发 CI、不修改工作流、不改 tracker。
提交使用 `[skip ci]`。没有新 sorry/admit/公理/逃逸，也没有状态升绿。

## 下一入口

现有编译修复流程按精确候选提交和 `DEPENDENCIES.json` 安装本模块，
并沿原 selected manifests 解析完整依赖；G7 必须用 review-repairs 版本。
编译请求保存在原 `automation/parts/p4/requests` 路径，不创建新调度。
证明下一轮从同一实际 dispatcher 的 `lowerEarly` 和
未核实的 early135 冻结线索接续；先取得/核对其来源，再补真实缺口。
不得以本报告的 partial scalar endpoint 宣称 full hUpper 或整节点闭合。
