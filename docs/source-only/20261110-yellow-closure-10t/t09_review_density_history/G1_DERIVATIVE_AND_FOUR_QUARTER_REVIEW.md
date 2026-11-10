# 原 G1 导数表与物理四分段

独审原稿 `fourth-prefix-stronger-refinement.tex` 的正导数、相关 residual 和四分段部分。四个冻结主文件皆在 T03 的 `successor_G1` 中。第五个 `RowSubintervals` 按作者指定的不可变指纹审读，它依赖尚待单独冻结审查的 T02 全原行几何证明。以下仅为 source-only 判断。

| T03 源（省略 P1OriginalFourth 前缀和 .lean） | SHA256 |
| --- | --- |
| DerivativeNumerator | 6740a8c908c7b8f44eb6ed4be22c57260207a42c88cff708b621080c527097bb |
| Q80LogBounds | 459ac78b5bd93b3370b989289a3e3e613e98dae7daefb58884b1d069d6c0011f |
| N8193 | 34189a0794db9d7acd35989f28356503de5d0e5f202b2f37e1331969f44ec0cc |
| FourSubintervals | e98839edea96f389b452fab7bc29213e58449fa2e71804c2290d75cb8cfb254f |
| RowSubintervals | 37ca26bc45558c0291aedcfab25dc17522c2105f2e840e3ba3bffac0b64146dc |

**原件。** 驱动 `certify_fourth_prefix_stronger.py` 为 25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a，原稿为 cf87c684a5847d289dd748d74705c6e3977bb20b5ed8c1d0d0cadf04ee3565bf。原 `fourth-prefix-stronger-derivative-table.json` 为 b9fb8fdd3cdcb8ae89d00e561cb9a8ddcc5683365de773df7c36bbf31c406d36，Lean `P1OriginalFourthRawTableMetadata.lean` 为 8b57193d727e81fbdc31be1c65810a593121cdc6ec34e4c56561301515fea2e9。逐项比较原 JSON 的十进制字符串和 Lean 列表里的数字 token，8,193 项相同，顺序相同，首、末项分别为 1208925819614629174706176、39643994026485390435670。仅比较存档文本，未重算表项或有限 guard。

**真实导数。** 被微分的函数是原 ordinary Suzuki 上因子 `OriginalU2CoupledRecurrenceSourceOnly.upper`。取 H(s)=s·upper(s)、q(v)=log(v−1)/v。1<s≤3 时 H=1。3≤s≤5 时 H(s)=1+∫₃ˢq(t−1)dt，此公式通过在 3 左边取零的连续 integrand 跨过接点，给出 H′(3)=0 和 upper′(3)=−1/9。两侧拼接没有从区间端点的单侧导数冒充普通导数。于是 N=−s²upper′，初段为 1，尾段为 H(s)−s·q(s−1)，原 s/(s−1) 完整保留。由 q 在 [2,4] 单增可夹住 H(v)−H(u)，再用 u·q(u−1)≤u·q(v−1) 得到 N 在整个 (1,5] 单减。这一推导复用原 `q_monotone`、`lower_eq_log` 和真实 delay equation。

**存档下界。** Q=2^80、节点 s_j=3+j/4096。log 下限逐项向下取整前 24 项；上限加 24 及分母 49 的几何尾向上取整，j=0 走原精确零分支。`checkRows` 在第 j 行先比较存档值加向上取整的 s/(s−1) 惩罚与累计 credit，随后才增加第 j 个向下取整的左 Darboux 步。该顺序正确。证明把每一步夹在 H(s_{j+1})−H(s_j) 之下，累计从 H(3)=1 开始。闭式 `original_integer_links`、`original_length`、`original_last` 的源码用 `by decide`，本审查未执行。`original_all_endpoints (j : Fin 8193)` 无外给数学前提，结论为 stored(j)/Q≤−s_j²·deriv upper(s_j)。原末项正给出 `original_N5_pos`。`original_ceiling_lookup` 从 1<s≤s_j 和单减性得到 stored(j)/Q≤N(s)。小于 3 的查询落入第 0 行，正好取得 1。

**物理四段。** 对 0<w<a≤b、a≤A、b≤B 及四个上取整索引（每段的右端上界除以 w 不超过所选节点），`reciprocal_difference` 在同一段上使用 upper(s)−credit/s 的非正导数。每段得到同一个物理差 upper(p_left/w)−upper(p_right/w)，相邻项抵消。分母用正的 A、B 插值积作保守上替，每段为 credit/(4·R_left·R_right)。原 w·(b−a) 与物理原核 4/(x y z w²) 的一次 w 相消，给出 `fourth_density`。证明在 A=B 或相邻实端点相等时亦成立，无除以 B−A。

**原行实例。** `original_row_density (raw) (hr : raw∈originalFourthWireRows) (t) (ht : t∈raw.toProducerRow.box)` 只从该行实际几何、物理坐标和所选 mask 构造参数。A=integerR0/6553600 为六组旧 affine upper 的 max-min，B=integerR1/6553600 为它与新两平面 residual upper 的 max。用原 box 第四坐标下端对每段右端上取整，原严格 R1<5·lower₄ 保证索引属于 Fin 8193。对每个实际 t∈B，结论为

    4(M−L)/(xyzw) · Σⱼ creditⱼ/(4Rⱼ₋₁Rⱼ)
        ≤ 4[upper((L−S)/w)−upper((M−S)/w)]/(xyzw²).

此处两边皆指同一旧六分量包络 L 与同一所选新端点 M。已追到 `all_original_rows_geometry` 和 `all_original_rows_pass` 的真实原行检查接口，审读时该 T02 文件为 7ed0b6b93a44be61fa90bdaa60da7f21204cd67c024308e9d7a41d347346bc00。其闭合的 3,699,127 行 guard 尚须实际远端通过。这里给出的是逐点不等式。整行还要将正确的平均 gap、盒边长和四次向下取整绑定到这些物理积分，处理整族无重叠、真实 common 历史、e 缓冲及总数值，随后在同一棵实际树上接回 G1。单据本补充覆盖的五件不能给 10601625247768616959055/2^78 的完整付款，也不能升级整行。

未发现上述五件推导中改变归一化、查表方向、端点函数或隐入 Wu H/h 许可的数学问题。实际数学批准范围止于表与真实每行四分段的源码。尚没有这些字节的 Lean elaboration、kernel 或闭式证书结果。
