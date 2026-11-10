# G1 原 3,699,127 行到同一第四积分

原稿端点的完整源级证明已接到 `P5OriginalCommonFourthSourceLedger.originalFourthIntegral`。T03 的 `P1OriginalFourthCofinalGain.exists_cofinal_original_fourth_gain` 对每个 ε>0 先选 e₀>0；对每个有理 0<e<e₀、每个 0<ω≤3/200 和任意 mMin、qMin，存在 q₀≥qMin，使每个 q≥q₀ 同时满足 mMin≤refinedMesh(q) 及

    10601625247768616959055/2^78 − ε < originalFourthIntegral(original e q ω).

`exists_cofinal_union_fourth_gain` 亦在 `data e q ω` 上成立，因为新增第五行未改变这个积分读取的六个第四字段。ω 在此是传给第四构造的激活参数，应用到既有 T05 计数公式时取其 a。T05 的 a≤1/800 满足该条件，下一步可取共同 e 上界和 q₀ 下界。此处没有产生新的 β、u_c 或独立的 G4 付款。

**被审的七个新增冻结源。** 本目录先前五件解析审查为 f0e46dce14f87c10858e350c0c7be636876087181faba1d89de5257ebb49d103。下表为 T03 `successor_G1` 中补齐其后整条链的文件。原数学依据是 `fourth-prefix-stronger-refinement.tex` 与真实 `certify_fourth_prefix_stronger.py`。全行几何依赖 T02 registry 341c477396af29c3fd019d334efeef87864e068915a0435180fcd2c6661b9f2d。

| 文件（P1OriginalFourth… .lean） | 字节 | SHA256 |
| --- | ---: | --- |
| CornerIntegration | 5190 | 2571aaf5e7b0a7b5e495501e7e31dcb6e68c50c91c03378abe8d66db19d435b6 |
| RowGap | 8454 | 5f1018c8192be85461baa8da66e5b1b6c124b86527107b470e9600a5fdd65925 |
| RowQ80Integral | 7429 | 46e26e2570b80c6f7e666b1b8f3b1385685a014b479eafadc05370a4a3e40710 |
| SavedQ80Total | 3166 | 235ad644603914624aab1d603e83d1b0bfe7137a5b95af8646110ad90fadb2da |
| Guillotine | 5862 | 6c35152304371c09efa877a6ab24a45a3e517bb92f7c4018266d7113c92a08c0 |
| TrimmedLimit | 10342 | 33554557cfeff645be52c05501098ebf6d8cebade4fbb5c22e167a363802e314 |
| CofinalGain | 9383 | 6697cc6e4d53107454cdd8508361f5f14a24633efdd49c2a6bbfbfe9687a9e86 |

1. 原驱动的整数中心取 floor((lo+hi)/2)，同值选第一个平面。实际 `pick` 只在第二个严格更小时选第二个。对每个旧分量选定的 affine 是其原 min 的上界。16 个真正多线性角权在原半开盒内非负，各自积分恰为 |B|/16。逐旧分量、逐新平面的 affine 插值给 `corner_gap_le_actual`。原相关 uniform 差及经 floor 的角平均均下界积分后，取两者的 max；没有把平均差移作逐点准入许可。
2. 每个 wire 行使用同一 R0、R1、第四下端及四个上取整查表。正 gap 和四个正坐标使分母换成原盒上端可做下界。令 D=6553600，d 为原 averageUnits，r 与 q 为两个整数 residual；第 j 个物理项化为 16·D·d·Π(hi−lo)·nᵢ / [Πhi·((5−j)r+(j−1)q)·((4−j)r+jq)]。这是驱动第 1 至 4 段各自的整数 floor，最终方才相加。`original_row_floor` 的结论终点为同一原行半开物理积分。`original_sum_check` 解析原 17 字节输入，数组 lookup 由原列表 toArray 得到，累加实际各行；Q80 units=4·10601625247768616959055，除以 2^80 给公布的 2^78 分母。
3. 独立 guillotine 检查使用相同解析结果。每一步必须有坐标使所有输入行满足 hi≤切面或切面≤lo，分别递归，能成功的叶至多有一个输入 occurrence。半开产品盒让接触面严格分开，`check_sound` 在原 list 的顺序上回推出两两不交。深度 64 对应四个 16 位坐标；执行策略的起始域为整 uint16 立方和固定可行坐标选择。原驱动先分 1/200 根再递归；两者实现不同，但新 theorem 直接证明所需的原行两两几何分离，未声称逐一重现原访问节点。
4. 单一 trimWidth=1/(n+1) 及 buffer=min(commonMargin/4,trimWidth) 用于全部原行。`test_limit` 在每个真实盒上以可积的零缓冲差本身支配，正余量保证实际 residual>1，所有坐标边墙为零测，有限 list 之和可取同一 n。实际 active label 的 kernel 非负。由原行半开所有权，每 t 至多有一项；在其 trim 上真实 Γ≤L、真实 max≥M−2e，原始上函数的单调方向给 buffered test≤该 active kernel，其余物理分支可保留。最后才按当次 ω>0 加入 mesh≤ω/2 的 q 阈值，e₀ 不依赖 ω。整个 cofinal 终端不要求调用者提供 disjointness、数学积分值、历史准入或几何 licence。

**远端验收。** 真实依赖闭包应对 62,885,159 字节的存档 561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da 及 8,193 原表值，通过 T02 `originalGeometryCheck_true`、T03 `original_integer_links`、`original_sum_check`、`original_disjoint_check` 等闭式声明，再检查两个 cofinal 终端及其传递公理。这些来源可检查，尚无相应远端 kernel 结果。字节核验未执行驱动或任何一个 guard。三个全表检查的计算量及非尾递归原解码器是实际集成负担。

独审支持旧同策略 G1 独立数值扣项的源码就绪。整树 13/22 计数仍须把该界在真实 `beforeEight`/正密度和实际 ρ 上作一次同向替换；当策略换成新全 ordered 第三表时，G1 所需的旧 owner、第四积分与新 arithmetic chronology 的等式或重新估计也须在新系数上交付。原整个 All22、剩余 G4 与第 7–14 项及 PP 尚未由此得出。
