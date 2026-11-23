# 2026-11-23 本地形式化试点

本次按用户授权尝试关闭原 `main.md` 第 119 行的「同源闭包编译、kernel replay、传递公理检查与独立复核」。实际完成 **6 个模块的本地编译、6 次逐模块内核回放和 63 条原定理的完整类型／传递公理检查**，修复两个源码文件的编译阻断。**第 119 行尚未整体闭合，黄色节点仍为 29。**

## 已验证内容

| 模块 | 本地编译 | 逐模块 kernel | 原定理类型／AX |
| --- | --- | --- | ---: |
| `Certificates.OriginalNodeArraysV1.DataCore` | 通过 | 通过 | 数据与递归定义 |
| `P2OriginalSaving19SourceJson` | 通过 | 通过 | 原见证 JSON 读取定义 |
| `P4AOriginalFull87ArchivedStageNumericReconcile` | 通过 | 通过 | 19 |
| `ActualThirdOriginalFixedpointClippedChord` | 通过 | 通过 | 18 |
| `P4BSmoothGateUpperStep` | 修复后通过 | 通过 | 16 |
| `P2PositiveAffineSimplexLogJensen` | 修复后通过 | 通过 | 10 |

表中模块均加前缀 `ImbalancedChen.`。63 条 `#check` 和 `#print axioms` 的实际输出、源与产物摘要见 [VERIFICATION_RESULTS.json](VERIFICATION_RESULTS.json)。只观察到 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。逐模块回放使用原有导入环境；它不等同于对全部传递导入重新回放。

## 两份源码修正

### 平滑上包络

[`P4BSmoothGateUpperStep.lean`](../../../ImbalancedChen/P4BSmoothGateUpperStep.lean) 的两处 `add_le_add_left` 产生了 `u + 1 ≤ v + 1`，而目标为 `1 + u ≤ 1 + v`。固定 Mathlib 版本中，后者由 `add_le_add_right` 给出。本次复用远端已存在的精确 blob `975207ba10a479f6e3c3ac2659922608e30f4d4b`，仅两处引理名称变化。定义、16 条定理陈述、正宽度要求以及 strict/closed 门的端点完全保留。

该步骤对照[固定手稿的平滑外逼近与开闭边界](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex)及[固定 Mathlib 的序与加法引理](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean)。

### 正仿射单纯形的 Jensen 步骤

[`P2PositiveAffineSimplexLogJensen.lean`](../../../ImbalancedChen/P2PositiveAffineSimplexLogJensen.lean) 保留全部 5 个定义和 10 个定理的公开声明。改动包括：绑定根命名空间中的 `convexOn_exp.map_integral_le` 并显式传入原概率测度与函数；导入标准 Lebesgue 测度实例；使用原乘除结合律完成系数 4 的重排；按固定版本参数顺序调用紧集上的可积性定理。

原稿的补充推导已给出 `dν = g dμ / ∫g dμ`、指数 Jensen、三阶修正及系数 4。这里修复的是形式化实现，未加强假设、削弱结论或增加分析公理。Jensen 在独立目录中首次修复编译成功后，原样复用其三个产物到验收工程，并另做 kernel、类型和 AX 检查；没有重复编译这次已通过的后像。

数学定位为[固定数值附录](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/numerical-appendix.tex)及[原公开配套证据](https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/tag/v2026.10.10)中的 `sixth-log-moment-jensen-20261009.tex`、`eighth-third-moment-refinement-20261009.tex`。调用的[固定 Mathlib Jensen 定理](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/Convex/Integral.lean)提供所需概率测度积分不等式。

## 范围及复用边界

使用 Lean `v4.33.0-rc1`、Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 和 goldbach `09b97db5764ade1246bfb77206baa1b124760958`。复用了固定依赖和 8,679 项官方 Mathlib 缓存。原样安装并核对 1,625 份项目数学源、335 项数据、94 个原 NPZ 容器及 43 个 native 补充源；没有改变历史工作区中的用户修改。

本次 [SOURCE_SELECTION.json](SOURCE_SELECTION.json) 保留 44 个审计根、1,619 个活动项目模块、43 个 native 补充模块和两个审计模块。因此完整节点仍要求 1,664 项回放、原九个 floor 类型及原完整类型门。六个同名生产者选版后的实际反向依赖影响为 448 个模块，本次六入口通过不能代替它们的编译与完整终端验收。

已核对旧 CDC 和 Stored 分批产物。CDC 的 3,370,363,988 字节对象包超过当前下载接口的 512 MiB 上限，尚未取得其 263 个候选的完整本地对象及导入证据。已实际读取的 Stored064–071 完整包显示八份既有证明修补与旧 full87 选源不同；这些修补已定位，尚未纳入本次六源选版。旧对象还存在本地导入／运行时身份需要重新核对的事项。本次没有把它们当成已接纳的编译缓存，也没有整批重复重建原 729 个候选。

系统调用级文件跟踪在当前环境不可用；保留了真实编译命令、编译器报告的直接依赖以及实际源／产物前后摘要。没有把这些记录描述为完整的系统调用读入轨迹。本次没有派发远程工作流，证明 goal 及定时续推保持暂停。

## 复核入口

[PilotAudit.lean](PilotAudit.lean) 仅导入已检查模块并打印这 63 条既有定理的类型和公理，不引入新定理。在按本目录选版物化的固定依赖工程中，可用 `lake env lean -t0 -j1 -M6144 -DmaxRecDepth=100000 -DmaxHeartbeats=4000000 --stdin` 读取该审计文件。逐模块检查使用 `lake env leanchecker -v <完整模块名>`。本次实际采用四份分别运行的审计驱动，逐声明输出已完整保留在公开结果中；合并的复核入口未另作重复运行。

源码中的旧 `SOURCE ONLY` 注释保留历史原字节含义；本次精确后像的验证状态以本目录记录为准。完整黄节点、父项数学供应和无条件主定理仍未取得本次关闭信用。
