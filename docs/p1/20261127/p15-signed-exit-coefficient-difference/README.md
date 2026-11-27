# P1.5 系数差分：正式验收

固定源码提交：`fbb8d60f796d4781316e95370cbd46131868c1c1`。模块：`ImbalancedChen.P1SignedExitCoefficientDifference`。

本模块已有的完整原始证明现已通过正常编译、独立内核检查，以及全部自有声明的类型和传递公理审计。实际清单共 **24 条自有声明，24 条公开声明**；公理集合仅为 `propext`、`Classical.choice`、`Quot.sound`。源码为 17,943 bytes，SHA-256 `4de8d8f28bfc304351192ed785aade7609aee909425e5109ff7c4a38236823e6`，与原始提交 `040d46058821746c69c5183b3f6c22792287c4ba` 的字节完全相同。

## 数学结果

差分采用 new-minus-old 的固定方向。在同一个素数树上，两侧保留模数共享同一个 Möbius 系数，因此非零差分只在支撑的对称差上出现，绝对值至多为 1。该系数先于被测试整数固定。

`p1_retainedPolynomial_sub_eq_union_coefficient_sum` 将两个实际保留多项式之差写成原并集模数上的同一系数和。`p1_union_coefficient_sum_eq_first_different_admissions` 将它精确接回共同树的首次不同准入及其真实后续子树。`p1_actualHistoricalFourthFifth_integer_evaluation` 保持原历史第四、第五策略，在整数除数求和中使用这个相同系数。平方自由、与目标互素、原策略方向均被保留。

完整 P1.5 还需要实际历史系数的 whole-atom 连接和完整 signed medium 分布支付。有限支撑与差分恒等式本身不支付这些解析误差。

## 原始验证证据

| 项目 | 真实结果 |
|---|---|
| 正式 P1 任务 | `job_f6a38b9975814857ae189d09b8032ec1`，exit 0 |
| 正常编译 | 仅构建本模块；原 42 个 project dependencies 原样复用 |
| 内核检查 | 原 `leanchecker --verbose ImbalancedChen.P1SignedExitCoefficientDifference`，exit 0 |
| 完整声明审计 | `PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS` |
| 独立只读复核 | `job_b94b9bab9b7943039d8e8e3716fc37ed`，exit 0，`REVALIDATED`，新增 normal/kernel 命令数 0 |
| 成功原 probe | 复用原 17 项文件及原 hash；未重新运行 |
| 原始证据归档 | 835,632 bytes，84 个成员；SHA-256 `32563cdf041fa3896bbf8779cab71d2ec3690d22061bde7768b821cddb16f33a` |

归档包含本次 owner 与 operation 的全部原记录、原 probe 的 17 个文件、21 个对象位置中实际存在的 8 个对象文件，以及只读结果和完整文件索引。控制端已逐项核对 83 个列出的成员 hash、索引 hash、归档 hash 和 ZIP CRC。源码、原有依赖对象及云端原工作树保持所记录的绑定。

[正式 PASS](evidence/PASS.json) · [独立只读结果](evidence/READONLY_RESULT.json) · [完整类型与公理清单](evidence/OWNED_EXPORTS.json) · [完整验收结果](evidence/VALIDATION_RESULTS.json) · [归档成员索引](evidence/FILE_INDEX.json) · [原导出元数据](EXPORT_RESULT.json)

本次接受一个新增 owner；原 21 项登记的 18/21 状态单独保留。整个 P1.5 仍为未闭合状态。
