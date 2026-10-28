# certificate_enhanced 源码交付

新增 `P2Author512EnhancedOrdinaryIntegral.lean`。PhaseB5 已经有 h-defect log-mass 源码，因此本次复用它，推进其后真正未完成的 ordinary 半边，避免重复。

普通核明确使用增强 residual：三组合法 tent 先各取 min、再取 max，固定分母为 `ordinaryA*t*u`。先用全局正分母夹紧延拓证明内外层区间可积，再分别用真实 `actualExtendedThirdLowerFactor` 的单调性与 s≥2 上的已有端点凹弦定理，证明 base 和每个 eligible plane 的实际加权积分下界。五个合法 plane 的 minorant 从 literal alternatives/eligible 逐项证明。最后接真实 sf/log 的 directed Q80 后端，再对源 foldl max 作归纳；无须假设任何目标 cell 或 integral inequality。

主导出 `enhanced_box_ordinary_Q80_lower` 给一个增强矩形 ordinaryLower 的真实积分语义。`enhanced_box_pairCell_Q80_lower` 将它与 PhaseB5 独立正 h 项相加，保留二者共用的同一增强 residual，没有把五个普通候选相加。

这是局部闭合的源码文件，尚未编译、内核验证或数值计算，正式信用为 0。实际矩形的正值/range/query guard、Q80 弦分母正值和原始 Wu bank 端点 licence 仍显式保留；它们不是目标积分假设。524288-cell fold、原始 selected L6 numerator、17572 mask/fibre、Δ8 reserve、完整增强 W1 bank、最终 c 与 arithmetic count 均未宣称完成。没有发现新的原稿数学缺口。

直接导入的 source-only PhaseB5 及其五级前驱的路径、SHA256、安装模块映射均见 `REGISTRY.json`。生产源文件与旧草稿未改。
