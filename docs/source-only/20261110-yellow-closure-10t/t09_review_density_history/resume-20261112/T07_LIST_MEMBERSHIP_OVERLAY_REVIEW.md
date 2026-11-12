# 经典种子两处 List API 安装勘误

此前两份源码审查遗漏了同一处 Lean API 变化。已按冻结编译器 leanprover/lean4@62eed1db4d67327ec8120be05f1a1b0847d74561 核对 src/Init/Data/List/Lemmas.lean 第 367 行。List.mem_cons_self 的元素和列表两个参数均为隐式，提交及 v4.33.0-rc1 标签的原文件相同，152635 字节，Git blob 519a54b75079a3acb036a212f7303f8d497ecba1。

安装时选择独立目录里的 ClampLongCredit 49f8d11e（原 3ff123cd，第 39 行）与 FixedClampGeometry 72d5bd3c（原 ca82b4cf，第 27 行）。两处直接用原目标推断元素和列表，各只删除四个 ASCII 字节“ _ _”。已逐字检查全部原、选文件，精确替换可还原各最终字节。定理陈述、其他证明、计数、常数与依赖均相同。原冻结件及原审查保持归档。该勘误不增加数学结论，两模块均未编译。
