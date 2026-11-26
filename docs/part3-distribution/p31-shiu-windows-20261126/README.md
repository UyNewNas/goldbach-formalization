# P3.1：有限 Shiu 窗口覆盖与原调用者

## 当前状态

`Part3MediumPrimitiveShiuFiniteCover.lean` 已按用户 2026-11-26 的明确授权重新实现；
`Part3MediumPrimitiveShiuWindowGate.lean` 复用用户提供的实际调用者，保留数学陈述，
仅修复已由编译日志定位的导入、类型表达和 tactic 兼容性问题。

两模块已在 P3 task `351cc6d42f7548a9be2714a80a31c042` 严格试编通过。
本目录接入版本与试编版本的唯一区别是把 WindowGate 的旧 `UNCOMPILED_ZERO_CREDIT`
注释注明为历史标签。最终精确 Git 提交的严格编译、`leanchecker` 回放和完整声明／
公理清单尚待运行，因此当前不增加最终验收计数，不将完整 P3.1 标为完成。

## 三个辅助定义及覆盖证明

对自然数端点 `A,B` 和商区间长度上界 `T`，定义

\[
 S_j=2^j,\qquad H_j=\min(T,S_j),\qquad
 X_{j,k}=\max(A,S_j)+kH_j,
 \qquad W_{j,k}=[X_{j,k},X_{j,k}+H_j)\cap\mathbb N.
\]

这分别是代码中的 `shellBase`、`windowLength`、`windowStart`、`window`。
在 `0<T`、`B-A≤T` 下，原闭区间内每个正整数都有合法的二进分壳，且该壳的
第零窗或第一窗已足以覆盖它；第一窗保留 `n=B=A+T` 这一闭端点。
为接入现有调用者，代码仍使用 `k∈range 8`，同时证明以下实际性质：

- 每个活跃壳都有原区间中满足阈值的实际整数点作见证。
- 任意非负函数在原保留点集上的和，不超过活跃壳的窗口和。
- 每窗基数等于 `H_j`，每壳总长度不超过 `8T`；全部窗口的总长度不超过
  `8T (Nat.log 2 B + 1)`。
- `0<H_j≤X_{j,k}`；合法壳与窗满足 `X_{j,k}≤8B`。
- 对实际保留点 `R≤n<2S_j`，若 `R/16≤T`，则 `R/16≤H_j`。

这些是 1106 英文冻结稿 `ana:shifted-divisor` 段中“按符号、二进分壳，再细分为与
`min(scale,L/g)` 可比长度”的初等展开。手稿出处为
[`analytic-appendix.tex`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/analytic-appendix.tex)，
Git blob `7cf3bbb16cd8924565eb439e474e0674f04631da`。

## 复用与重新实现的边界

用户上传的 11,898 字节文件是 WindowGate 调用者，其 SHA256 为
`6d47a7fb9a91a67ba330cd6ca519964b03cb81e2da5d358d14e50b010ebe3892`。
本轮未恢复旧 FiniteCover 源码。当前 provider 明确标记为新实现，不冒充已登记的
13,577 字节或 14,529 字节版本。它包含 6 个定义、18 条定理；原 caller 包含
1 个 structure、8 条定理。最终 owned 清单还可能包含结构自动生成的声明，须单列。

跨会话上下文服务本轮返回不可用。已完成的增量检索只读取原 P1 大 ZIP 任务结果、
已知 Git 分支增量和精确历史 registry，未重复 P2/P3 的已完成档案扫描。
P1 原任务结果现为成功、13,408 个成员下零候选；这只是原选择器的有界结论。

历史 registry 另列 `SignedSplit`、`OverlapCover` 两个直接 caller；其实际源码未恢复。
它们绑定的旧 provider 版本与上传 WindowGate 的 source68 版本不同。
因此，本次已核验的 WindowGate 兼容性不能外推到这两个未读取的 caller。

## 保留的外部假设与未完成工作

`PrimitiveShiuTauBoundary` 继续显式提供原 primitive Shiu 分析估计，常数与阈值先于
变化参数。当前代码只证明窗口几何、参数适用条件及该输入在窗口上的调用。
它不证明 Shiu 本身、素数倒数和、符号与 gcd 总装、小范围估计或最终 shifted-divisor
估计，也不提供原谱族的 `hI`、`hkernel`、`full_uniform`，不关闭完整 P3.1。

## 验证及证据

```bash
python3 -B verification/verify_part3_continuation.py \
  --group shiu-windows --expected-head <source-commit> \
  --output-dir .lake/p31-shiu-windows-verification
```

`CLOSURE.json` 绑定两个实际项目模块及九个外部导入名。只对这两个新接入模块作
最终严格编译和内核回放，继续使用原有完整声明、公理白名单和源码／对象绑定检查。
Mathlib 的常规导入信任边界保持明确，不声称本轮重放整个外部库。

- [SOURCE_INTAKE.json](SOURCE_INTAKE.json)：两源当前哈希与逐项修改来源。
- [RECONSTRUCTION_RECEIPT.json](RECONSTRUCTION_RECEIPT.json)：数学内容与严格试编记录。
- [严格试编完整证据](finite-cover-windowgate-probe-evidence-20261126.tar.gz)：两轮源码、日志及原始状态。
- [INCREMENTAL_RECOVERY.json](INCREMENTAL_RECOVERY.json)：有界恢复结果及历史 caller 版本边界。
- [增量恢复原始证据](incremental-recovery-evidence.zip)：P1 原输出、GitHub 原文和身份核对。
