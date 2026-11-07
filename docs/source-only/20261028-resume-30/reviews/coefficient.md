# Coefficient 五项独立源码验收

2026-10-28，reviewer `/root/manuscript_map`。五项均为 **SOURCE_REVIEW_PASS**，仅接受各自交付的窄源码增量。所有原分配任务仍未完成；`compiled=false`、`ready_to_install=false`、formal/kernel credit 均为 **0**。

已读五份实际 Lean、REGISTRY、REPORT，必要的 retained-leaf/depth-splice、小粗素数附着、实际系数、physical geometry 与祖先 cap 前驱；逐项重算源码及 registry 所列非空依赖 SHA，并对照原稿 `manuscript-body.tex` 256–357 行与冻结 V2 内外边界。五份 candidate hash 及所有显式非空依赖 hash 均匹配。完整机器可读记录见 `coefficient.json`。这不是完整传递证明闭包审计；Mathlib 缺少本地源文件的项目只检查到已声明 package revision，不作 API 或编译结论。

| 任务 | 判定 | 本次实际接受范围 |
| --- | --- | --- |
| coefficient_signed | SOURCE_REVIEW_PASS | retained-domain all16 的实际物理系数，经唯一 small/rough 分解展开到 owner words；对任意 signed 测试成立，并同时用于 count 与 exact coprime mean |
| coefficient_physical | SOURCE_REVIEW_PASS | H3 cell00 的非空有理开盒、全部局部 PhysicalRows、相同 raised exponent 的 full/complement squares、局部共同 caps 与 existential guard 选择消歧 |
| coefficient_rosser | SOURCE_REVIEW_PASS | 非乘法 terminal arithmetic test 的 retained leaf 重索引、真实 sign-sensitive physical rho 识别、实际 policy5 在 rank-six 后的精确 splice 差 |
| coefficient_rough | SOURCE_REVIEW_PASS | ProducerRow/testBit 到 raw31 的有限掩码字典，以及同一 rank-six 历史上的 inherited-fourth/fifth physical support ceiling |
| coefficient_bv | SOURCE_REVIEW_PASS | 实际 joint mark 的 full-q rank = 4 + residual rank；真实 common-beta coefficient 在 total rank < 4 上为零 |

## coefficient_signed

`P5All16PhysicalOwnerDiscrepancy.lean` SHA `6705b70dee1fb180df67eddfb7757ee611223f44ce6fa8f744d75267b9a6d628`。

75–104 行从前驱的 raw owner fibre identity 分配 upper gate、粗素数 sign、common beta 与 `M_res/k!`，各保留一次。108–156 行使用真实 small/rough 唯一分解及 `joint_exact_pushforward`，没有把待证系数等式当假设。165–208 行由任意测试的恒等式读出逐点 sigma 等式，再代入同一完整模数上的 labelled count/exact coprime mean；marked `t`、residual owner word 与独立 test `u` 未混同。外层使用完整 `ordinaryTuples`，包括 W。

未见循环 final-target 前提。REPORT 与源码范围一致：仍以真实 retained rough `d` 索引，未证明 unrestricted all-k 投影反向覆盖、rank exhaustion、owner-order/sorted-block regroup、重复 rough 在 count/mean 两边各自的绝对误差包络或 PP 渐近估计。

## coefficient_physical

`P5OriginalH3Cell00PhysicalBoxBinding.lean` SHA `eccf3c3582b9de369c875e93a5c6464a80474ec8453c2c92b39fb98430dbc3ab`。

71–90 行在整个有理开盒保留 62 个严格 proper old planes 和 mask9 恒等式；94–145 行构造局部 PhysicalRows 与具体共同 caps。149–196 行排除 `<30`、43、44，证明所有可能的 `Classical.choose` slot 都有相同 mask138/newCap，避免从“存在 slot58”错误推断选择器必选 slot58。200–221 行以同一实际 raised exponent 给 full 与 selected-complement integer squares。

**必须保留的范围限制：**226–250 行 `actual_h3_same_rho_support` 仅是“该 pre 的局部 cap 等式”与“该 policy 的任意非零 q 的全局支持性质”的合取；没有证明此 q 来自该开盒的选中叶，没有局部贡献/fibre 等式。REPORT 未声称局部密度收益或 K，所以不构成超报。全局祖先 cap 供应、87 域覆盖与不交、局部 selected-leaf 到 q-fibre 及 density telescope 继续开放。

## coefficient_rosser

`P1Pair12RetainedSignedSource.lean` SHA `f3238c37bc2c45aafbabafbc9cc69f4eeef12ba44d5e2b3d6852d10533564d16`。

24–117 行对任意终端测试递归证明 leaf 展开和 sign recovery，以单位局部质量及素数乘积单射消去重复计数；这适用于非乘法 AP 测试。120–170 行通过既有真实 small/rough coefficient identity 保留正叶 plus、负叶 minus 的 beta 选择。174–246 行的 stopped/frontier 递归保留 parent 对 rank k 本身的 admission，只有之后的选择使用 fresh；早于该 rank 耗尽的支路确实抵消。264–345 行接入实际 policy5、完整 marked modulus 的 coprime mean 及单位权重 arithmetic frontier 的 parent cap bound。

`fresh` 是诚实显式的未来 replacement policy 参数，不是已经构造的原稿 sixth action。third support、licensed fourth Geometry/mask、非空 pair12、严格 H5 下门槛、全部 sixth cell chronology、PP 和 density/K 均未闭合，REPORT 已说明。未见把目标解析估计当作假设。

## coefficient_rough

`P2ActualFifthRaw31SupportCeiling.lean` SHA `0d467fe52f2584cb4e99063a92ad48ddf62f53dd38203af0c2fc8a6bfb050df7`。

35–69 行从 Geometry 的 `9≤mask≤15` 证明 Fin4 的 testBit/raw31 bit 一致和第五位为零；77–107 行由该字典与既有 actual finite maxima 消除前驱 `hmask`、`hseed`，没有偷换 actual old cap 为 R0。112–144 行只在 `N≥1` 下指数化，并通过精确 nested ancestor identity 保持第四/第五物理 level 的同历史关系。

前提仍明确保留 actual third supported、licensed producer Geometry。正向 retained witness、严格 H5 下门槛和真实 sixth coefficient-to-active rough-chart 连接未证明；PhysicalCell 没有被冒充 ActiveNativeChart 或 SW licence。REPORT 符合实际窄增量。

## coefficient_bv

`P5OriginalJointFullModulusRank.lean` SHA `9475888d4ff7765cbb85e2739748313496c303ebd1d0488d6161964d34f6e447`。

26–66 行以四个严格有序原始 marked primes 识别 prefix 的完整素因子集合，再调用已证明的 row/prefix coprimality 得到秩相加。70–111 行保留真实 row witness 并专门化 common-beta 参数；115–141 行证明 low-total-rank signed sum 为零及 residual/full-rank cutoff 的准确换算。没有把 residual rank 当 full-q rank，也没有把空过滤器冒充实质 BV。

这里接受的是算术排除/分类引理。原稿 334–338 行的 low-rank analytic 分支仍需精确 chart/因子层解释及非空 below-half full-q family；coarse `153/256>1/2` 本身不足。作者明确保留这一边界，尚无证据将它升级成原稿数学反例。

本次未发现新的原稿数学缺口，未运行 Lean、lake、kernel replay、数值证书 checker 或 CI，未检查额度，未改动五项交付、旧草稿或生产源码。
