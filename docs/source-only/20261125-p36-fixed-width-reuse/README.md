# 固定宽度供应的旧证明轻依赖抽取

状态：**源码准备，未安装，未编译**。本包不改变当前 canonical 文件或选中 manifest。

固定宽度候选最初的依赖预检得到 205 个项目模块。原因是旧 `P1OriginalFourthMovingPrimeIntervalBound` 同时包含一般素数区间估计及原第四层加权 bin 的消费者；其首个 import 把大量历史层密度代码带入，而新的墙带供应只需一般区间估计。

本包从固定 P15 提交 `c6b89774822580c731a236ac66dcd7466ac8a0e6` 原字节抽取该文件的前两个声明：private `one_add_reciprocal_sum_le_euler` 和 public `exists_uniform_reciprocal_interval_bound`。新的 `P1ReciprocalPrimeIntervalCore` 只导入 `ActualPrimeBoxMass` 和 `RoughAbsoluteDensity`；公开声明仍在原 namespace。

旧 full 文件增加 core import，并移除同一声明块。逆向移除 import、放回原块后逐字恢复旧文件；没有同时保留两份证明定义。原 interval envelope 只改一个 import，其余字节完全相同。另三份 coordinate/affine wall/slab 文件直接复用原字节。

`REUSE_PREPARATION.json` 记录原 Git blob、抽取 byte range、声明块哈希和可逆性。`PREPARED_FILES.json` 固定六份准备文件的字节。新的实际 import 图和外部依赖差异见 `DEPENDENCY_PREFLIGHT.json`。兼容 full 文件不在本次目标闭包中。

这是依赖和声明 owner 的调整，不是新的区间数论证明。抽取后的 owner、完整类型、serialized inventory、依赖及对象绑定仍须由后续实际编译和审计确认。完整 mixed warm fibre 覆盖以及 P3.6 仍未由此完成。
