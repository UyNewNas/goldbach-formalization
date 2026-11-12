# 光滑外权第 2 选本

沿用第一版全部 15 个模块、真实权函数、终端与前提。EulerBounds 的仿射斜率形参原写作 Lean 的 λ 关键字，选本改为 slope。EulerProfile 的 gate_budget 用 funext 与 congrArg 对每个固定仿射门应用一次 margin_on_chart。同一公式右边含零中心处 margin，旧的 simp_rw 会递归展开。

两源写入本目录，其余 13 源使用上级 REGISTRY 的原字节。核对依据为 Lean 4 62eed1db4d67327ec8120be05f1a1b0847d74561 的 src/Lean/Parser/Term.lean 以及 gate_budget 中的真实 margin 定义。原公式、源位置、整族正上筛的 ρ、Θ 与审查边界见上级报告。仅静态选版，编译和内核状态均未验证。
