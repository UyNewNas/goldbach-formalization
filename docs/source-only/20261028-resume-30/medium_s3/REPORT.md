# medium_s3：实际 fixed-block canonical split

已输出 `Part3MediumCanonicalFixedBlock.lean`（312 行），未编译，正式信用 0。

前稿 PhaseE 接受一个 `PhysicalSplitWitness` 后才能返回 installed 标签。本稿给出实际的 fixed-block `FactorData`：四个整数窗各自施加严格 z-smooth / 含等号 z-rough 支持；`allowed` 直接采用原始 Q2/Q3 区间和 rough-product 窗，不再有不透明 gate。

主要证明用 `primeFactorsList` 分割每个非零 q 的全部素因子。列表保留重数，因此适用于素数幂，不假设 squarefree。原有 `smallRough_factorization_unique` 随后证明每个 admitted choice 都等于这个 canonical split。

由此证明完整固定块的原始物理模数对 `selectedModuli` 恰为 `choices` 的像，且没有碰撞。每个 selected 物理对实际构造 PhaseE 所需的 `PhysicalSplitWitness`，没有把 witness 存在作为前提。任意复权重以及平方后的两份独立求和均能精确重索引；最后把字面 Lambda_d(w) 识别为原始 gamma2(q2)gamma3(q3) 物理加权和。被删除的同余指标或 n1!=n2 条件可保留在任意复 kernel 内。

这是 fixed-block 内反向支持与权重的必要连接。仍未完成全部原始 W carrier 的跨块 dyadic ownership、公共 q/d/off-diagonal slice 与原始 V 的完整绑定，也未推出恢复误差或任何 medium 最终界。不能把本稿说成 hMedium 已闭合。

本次未见原稿错误。缺口在既有 opaque FactorData 的实现接口；本稿以真实支持的构造器消除固定块内此缺口。定义中的四个窗允许一般整数区间；原稿 dyadic 可比性属于后续估计前提，不参与本恒等式。物理对显式要求非零，以匹配原稿正长度支持；没有证明 Q2/Q3 为任意实数时也自动排除 0。

直接 source-only 导入是 `ImbalancedChen.Part3MediumInstalledSplitConverse`，其目标安装路径和完整依赖 SHA 已在 REGISTRY.json 固定。未执行 Lean/lake、内核、checker 或额度检查。仅做源码检查，未发现证明占位符。
