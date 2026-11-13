# 双曲余弦复合的定向加法修复

从 23fa4b92744247e6e65aacb14680024df3a3fda5 读取 T04 的 SELECTION.json 和它指定的 7377 字节源码，确认 preimage 为 337f168b4194fd0f0aa79bd79705c9ad703b84a3。对照固定 mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 的 Unbundled/Basic.lean，第 202–205 行生成 add_le_add 的签名为 h₁:a≤b、h₂:c≤d 推出 a+c≤b+d。此处范数三角不等式之后，左加数 ‖A(cosh u)‖ 保持相等，右加数用 ‖sinh(u)·B(cosh u)‖≤cosh(u)‖B(cosh u)‖。原定向 add_le_add_left 在此 pin 向两边右侧添加同一加数。

仅将这个证明表达改为 add_le_add le_rfl h。内层 h、全部其余字节、18 个具名声明头、函数值和参数均已比对。后件仍为 7377 字节，原始 SHA256 6e52e161c7541790b082d2df8d9643c58b35241238dd7a97b5ce2910c6231611，Git blob a6e796a834aa77a38db07187932bf15d585d6d38。后续固定尺度 Schwartz 估计由这个已选后件供应。审查限定源码及准确来源；编译、内核核验和新增数学叶均为零。
