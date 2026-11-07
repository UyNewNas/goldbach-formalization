# certificate_rows 第三批交验

已写 `P2Winner9SelectedRowIntegerScales.lean`。指定的物理 Y/deviation 到 typed integer scales 及 row21/22 measured mixed-numerator 恒等式已写成完整局部源码；原始整体证书目标仍 task_complete=false。全部未编译，正式信用0。

row21 复用已有 row21SimplexData，mean vector 取原始 witness 的十个 stored means。row22 由它自己的九个 raw rational vertices 重建 gap common denominator、factor column denominator、整数gap/列、gap-weighted mean分子、L=lcm(meanNum)、pv、U=max pv、y=U-pv、有符号 b=ai-pv。row22 的十个 stored means 仅从原始 JSON 字段逐字抄取，另给与 computedMeans 相等的闭合证明项。没有计算或重放这些整数。

两行闭合 VertexNormalization 源码只检查有限有理恒等式：真实gap=g/gapDen、真实upper=U/L、真实Y=y/U、真实signed deviation=b/L。其字段没有积分、moment、cap、floor或certificate，所有闭合证明项均未执行。精确 rational-to-real 嵌入随后把实际顶点数组接到 gapVertices/yVertices/bVertices；gap的公共分母始终保留。

复用 PhaseB3 真实Δ8 measured moment 到 signed integer mixedNumerator 的源码，得到 canonical numerator=mixedNumerator/(12!·U·L²)。接第二批实际support/Jacobian后，两行得到：

`∫physical gap·Y·deviation² = (8!·literalPhysicalVolume/gapDen) · mixedNumerator(data,j,1)/(12!·U·L²)`。

最终两行 theorem 无 normalization 或 moment 前提；它们使用各自实际有限数据的闭合证明项。当前仍是相对于未编译依赖的源码，不能报告有限算术或内核成功。后续还须 actual physical cap、Jensen/curvature analytic enclosure、row floors、all22/all17572、reserve及当前c/K。未发现原稿数学缺口。第一、二批及旧source均未修改。精确SHA、依赖、数据位置和声明名见REGISTRY.json。
