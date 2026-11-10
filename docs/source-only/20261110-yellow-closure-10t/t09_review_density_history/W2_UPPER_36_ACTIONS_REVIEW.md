# W2 原 36 项、四个 Γ 的上表反馈

独立核对 43 份冻结 Lean 源的字节数及 SHA256。按文件名字典序写入“文件名、一个空格、小写 SHA256、LF”的总摘要为 `e7b60d88216e4a5c2de2883fb16573caac65c36604467ee738ac59da055ffa1a`。作者 REGISTRY 为 `64b285265964316745b77b8f9f4a8c7e081a124583dedf5121459bbbc36f0a1c`，REPORT 为 `bf2c4d20016d16dab650b28afa03e0aedaf2ca4e3a3d770b8cd7c862ce42e78f`。10 件研究输入、驱动和旧记录，11 件公开稿/发布证据，以及 16 件原 Lean、2 件 v3 直接来源均分别核验过原始字节。源码的职责是消除原 106 项银行上界中四个 W2 双素数上表反馈差；整个下筛 h34 仍有其他算术项。

**原记录。** 独立从原三行 `certify_finite_w2_action_bank.json`、原33行 `expanded-w2-midpoint-bank33-v1.json`，以及发布紧凑输入 record-0026、0451，抽取每个 action 的四条 ordinary_pair_H_weights。按原顺序、原 cell 编号与 lower numerator 逐文本比对，144 份序列共 5,852 条全部与 Lean 的 weights00_0 至 weights35_3 相同。全程没有重新计算任何数值积分。公开 record-0596 覆盖前三项。关于后 33 项，早期 geometry-only 审查保留原范围，最终 record-0453 的 counts 列出了 5,224 项 pair_weights，record-0454 保存逐项独立区间，generator-0455 和 record-0456 分别记录独立数值方法和几何。它们为原始权重提供外部复核；新的 Lean finite checks 仍需实际通过。

**四个真实核。** Γ5⁺保留三角形的 v+2u<1 边，Γ6 为相应矩形，分别拉回固定的 s₀(1−u−v)。Γ7、8 分属原 [0,0] 及 [0,1] 母窗，读取 (1−u−v)/u。每个归档单元按原直线交点分片；闭端点的 Fit 和有序互斥的开片把每片嵌到实际原 pair atom。正核允许舍去未覆盖部分。对 v 作积分，得到 log(r(1−u−l)/(l(1−u−r)))/(u(1−u))。Safe 保证分母域和非负性。前三行按原 1024 panel Darboux 下端在**每格**与零取大。后 33 行采用每片 64 格，以二阶真导数的下端乘 h²/24，加到中点值，再乘 h；有符号积分全片后才以零截断。真实导数的乘、逆、log 规则与两种原驱动相符。内部使用 Q112、32 项正奇次有理级数及朝外余项，原约束仍为 Q80。每个 laneCheck 比较每个原稀疏权重与这些计算量的下端，守卫在不满足表达式域时退回核非负给的零界。外部区间比对无法代替这 144 项守卫。

**传到实际前代。** `all36_four_original_pair_measures` 的参数 j:Fin 36、k:Fin 4、i:Fin 200，结论是原 weightAt/2^80 ≤ 该 j,k 的实际 pairIntegralAtom (.inl i)。`immutable_each_original_pair` 使用同一 precedingH g 的 200 个单元值和 201 个端点值，后者取原相邻最小且非负。重复索引及不同 Γ 的重复读取照原次数计算。原归档质量和表值各有一项 2^80 缩放，四条 Γ 合集仅除一次 5。`uniform_original_four_windows` 在 lo>0、hi≥lo、ε>0 下，先给 T≥2；随后对所有 N≥T、L∈[lo,hi]、d>0、Q=dN^L、j,k 及 g:Fin 430，给出同一原档案加前代 H 的下界 ≤ actual physicalUpperWindow + ε。前两窗及母词窗通过 `all_four_window_occurrences_reindex` 回到真实有序双素数、两个 square gate 和连续 Euler 因子 localPrimeFactor d p·localPrimeFactor (d*p) q。该局部定理对 d 只需正，不应附加 coprime 前提。

**可验收范围。** `Part5OriginalH430W2UpperBankPayment.uniform_corrected_bank_base_only` 对每个 ε>0 在目标、网格、根、t、p、430 前代索引之前选 T≥4，在 0≤t≤1/12、1/(n+1)≤11/384、p 素且与 N 互素并在真实 rootBand 时，给出原 sourceGap + 106 个 selectedLevel 修正 + 原舍入损失 ≤ 全部 occurrenceScale·baseValue 之和 + ε·actualBankTheta。用同项的非负 scale 乘 bankPairArchive−bankPairIntegral≤0，方向正确。原 36 个 W2 上表反馈至最终银行的这项不等式已供应源码；实际 count 的有符号 ordinary/switched base、Γ5 被拒部分、J₀=1/50 四轮、430+11 原全域标记计数归纳仍待。没有从 physical old-H profile 擅推 sifted count。

远端先验固定 v3 依赖、几何/积分/查表定义，分 36 action 核验每项四个决定式及原列表和计数，在同一闭包检查实际窗口及银行两个终端的类型、传递公理与 kernel。区间运算展开及递归资源未经测试；此独审无本地编译、守卫执行与绿色状态。
