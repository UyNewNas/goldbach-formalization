# Batch8 ZeroCutoff：三项三角界的最小 proofbody 修补

候选仅修改 `P1OriginalFourthZeroCutoffLimit.exists_original_fourth_actual_mean_and_cutoff_limit` 内的局部 `htri` 证明。没有改 imports、公共声明头、定义、假设、结论、常数、ε/3 分配、cutoff 选择，或后续 `linarith`。

## 实际错误及原因

完整 Batch8 原模块错误定位 `201:58`、`case calc.step`。记 `S` 为 normalized actual saving、`R` 为原 small remainder、`I` 为选中积分，留下的目标是：

`|S - R - I + R| + (|I| + |-L|) ≤ |S - R - I| + |R| + |I - L|`。

这是原隐式 `calc` 和两次 `_` 参数选择了过松中间界后的回落目标；该不等式本身一般不成立。正确的原合同仍是 `|S-L| ≤ |S-R-I| + |R| + |I-L|`，没有数学缺口或新增前提需求。

## 候选

仅在该 proofbody 中用三个局部 `let` 给原表达式命名，并明确写出：

1. `S-L = (S-R-I)+R+(I-L)`，用原 `ring` 证明。
2. `|(S-R-I)+R+(I-L)| ≤ |(S-R-I)+R| + |I-L|`。
3. `|(S-R-I)+R| + |I-L| ≤ (|S-R-I|+|R|)+|I-L|`。

两次 `abs_add_le` 的适用项和最终端点均已明确，最后一项始终保留 `|I-L|`，不再拆成 `|I|+|-L|`。这正好与已有 hposN、hR、hnear 三项误差界连接。

## 稿内范围及验证

1106 手稿 pin `a988cba584d803ae2856a0de50efb582f4f3dd6a`，`sieve-appendix.tex` 的 `sv:finite-realization` / `sv:activation-tail`：先控制 small-last-prime tail，再处理固定 cutoff 的紧部分。此改动只补齐原 formal proof 的初等三项界，没有扩大稿内数学范围。

`STATIC_CONTRACT_CHECK.json` 已确认 proofbody 外全部字节相同、全部 7 个顶层声明头相同（6 个公开）、唯一公共定义 `normalizedActualSaving` 完整字节相同，无新全局声明或选项。第五层相邻源码有同型隐式写法但未验，未把它当可靠 donor 或接受收据。

没有执行 Lean/Lake、云编译、kernel replay 或 owned audit。候选状态为等待根代理 normal 验证，之后仍须原 kernel / owned 接受流程。

完整候选在 `ImbalancedChen/P1OriginalFourthZeroCutoffLimit.lean`；补丁、原错误字节、静态合同比较和精确 SHA 均在本目录。根代理应先核 preimage，再合并发布并执行既有验证。
