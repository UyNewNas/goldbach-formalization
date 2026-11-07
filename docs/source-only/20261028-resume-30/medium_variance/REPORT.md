# medium_variance 源码交付

已写 `Part3ActualFilteredPrimitiveSW.lean`。文件文本闭合，未编译，新增正式验收为 0；原分配的完整 medium 方差/四 chart 连接仍未完成。

本次消除的是原稿 (14) 的一个实际系数障碍。PhaseC 已证明全模数特征在 ell=f*k 时等于 primitiveCharacter 乘 quotient-coprimality gate。新文件把该恒等式提升到同一 MediumAtom 的实际求和，严格得到 auxiliary gate r*k，且不要求 f 与 k 互素。随后直接使用原稿已假设的 UniformAuxiliarySW，导出 common C,x0 的低 conductor 任意对数节约，代价为 tau(r*k)^C0，而不是较粗的 tau(r*ell)^C0。

现有 production `uniformAuxiliarySW_lowConductor_auxiliaryCharacterSum` 保留 full-level nonunit gate，给出的 tau(r*ell) 上界本身合法，但不能直接冒充原稿 (14) 所需的 quotient-cost 估计。本次没有修改旧定理。`primitive_sum_eq_auxSW` 是旧 private AP-error expansion 的必要窄公开接口，不重复构造外部大筛工作。

同时提供真实非负的 `filteredVariance`、以 quotient-filtered primitive sums 表示的 real norm-square Parseval，以及在真实 r-filter 上的有限 weighted Cauchy。没有加入 hMedium、filtered BDH 结论或最终主定理作为前提。

还需完成低 conductor 的 f,k 求和，高 conductor 的 fixed-k primitive large-sieve 实例、粗方差/除数均值，以及正 principal Gram 核到 (15) 的完整合并。本文件不供应非零频率四 chart 的 ABL 返回，也不证明整个 (14)。未发现新的原稿数学缺口。

依赖安装：先将 registry 固定 SHA 的 PhaseC `Part3ActualFilteredPrincipalCharacterVariance.lean` 安装为 `ImbalancedChen.Part3ActualFilteredPrincipalCharacterVariance`。该 source-only 依赖和本文件都没有编译/内核证据；编译专员可直接据 registry 取用。
