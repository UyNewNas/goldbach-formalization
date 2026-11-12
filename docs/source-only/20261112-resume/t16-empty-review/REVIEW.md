# T16 对 T15 原 Γ 空母词的独立源码复核

**裁定：原 Y18「空母词保留项及其原始来源识别」的全部源码职责通过，允许该行由黄改蓝。** 确切结果是原保留分解在每次实际 Γ 发生上的空分支权恒为零。本裁定针对下列源字节，P3.6 总项仍黄，新增绿色和内核信用均为零。

## 原黄色项的出处

原稿 `9731290e` 的 PP 公式在 `paper/source/manuscript-body.tex:258–284` 对同一有符号系数写出 AP 计数及精确的互素均值。§3 (T) 按标号重数恢复系数，§4 (F) 对每一保留的几何函数作傅里叶分离。确定哪一项属于空母词，要追溯原项目中产生该余项的代码。

1. `17813c8` 的 `P2GammaJointRetainedReduction.lean:28–52,105–139,165–185` 从原 `sourceTest` 重排到 `originalMotherOccurrences`，对无 head 的词保留原 smooth-trimmed root-label 和。该提交 REPORT 第 69、75、103 行把待办限定为该实际列表如果产生空词时的保留项。
2. `0632f2e` 的 `P2GammaRetainedSameRhoMother.lean:43–78,180–193` 将此项逐词、逐旧素数对、再对外层同一符号选择系数求和。`153bb09` 在实际 upper 秩至多二的终端减去这个 `emptyJointError`。`b538b42` 的 `P2GammaCompleteLevelMother:206–251` 和 `P2GammaRankScaledUpperLogSaving` 在通用 complete level、物理 rank-k 及 3/4 两个端点中沿用它。
3. `b12b805` 的 REPORT 第 70–71 行指名先前未能读到的原生依赖 `09b97db5…/SecondFunctionalMotherFinite.lean`。`b538b42` 的 REPORT 第 14–16 行因相同来源尚未恢复而保留该项。`f1bcf37` 的 REPORT 第 16、76–79、101 行继续要求从原定义查清该词。`P2GammaSelectedPhysicalTheta:45–47,61–74` 的 selectedEmpty 是同一 emptyPairError 在所选对族上的带权和。`f91eadb8` 的 plateau 两条端点也直接使用 selectedEmpty。由这些正向定义及创建该待办时的明确范围，Y18 的原保留项均由同一列表提供。

## 原始发生与精确付款

原生依赖为主 sourcehead `3d15576a…` 的 `lake-manifest.json` 锁定的 `09b97db5764ade1246bfb77206baa1b124760958`。独立读取其 Git 对象。`SecondFunctionalMotherLabels:8–12` 列出索引 7 到 21。`SecondFunctionalMotherBandFormulas:6–22` 在每个索引列出完整词列表。`SecondFunctionalMotherFinite:8–14` 已对该索引及该列表内每个词证明长度至少 2。Gamma7,8 各有一个长 2 词，Gamma9–15 有 14 次长 3 词，Gamma16–19 有 4 次长 4 词，Gamma20、21 各有 1 次长 5、6 词。词 112 出现在 Gamma9 与 10，词 122 出现在 Gamma9 与 11。默认行返回长度零的词列表。EVIDENCE.json 按原 Gamma 及组内位置列出全部 22 次发生。表中都是定长的槽位值，颜色 0 占一个槽，任一颜色对应的实际窗口可以为空，但不会缩短词。这里不需要从预算多项式的常数项推断，也无混合符号抵消。

`P2OriginalU5ExactNormalizedSource.sourceTest` 直接按这两层列表对每个原 `rootLabels N t cs` 求和。`P2OriginalU5WholeGroupCapacity.root_word_length` 给出选出的素数元组与颜色词同长。`P2GammaCompleteProductTrimPayment:412–438` 把两个 List.map 保重数拉平。每次实际发生上的原完备整数是 `m=(t.1*t.2)*x.1.prod*x.2`，外层保留旧标记对及其权重 sigma(t)。正整数商 x.2 可以等于 1。对每个 q，`gammaKernel` 精确是 `1[m≡N (mod q)] − 1[gcd(m,q)=1]/φ(q)`。原 emptyWordError 仅在 `cs=[]` 才取原集合、原 trim、原有符号 rho 和上述核。所有实际发生在这个分支之外，因此逐项为零，直接保留重复发生和任意 sigma、Q、rho，再作有限和。即使将原函数直接施于人为的 `cs=[]`，本证明也不要求该内层函数值为零。

原物理 `physicalUpperModuli` 展开为 `actualSmallRoughModuli`，fullUpperRho 展开为 `actualSmallRoughRho`，rankUpperRho 与 rankRemainder 各取既有的 rankRho、remainingRho，同一小 beta 参与实际系数。逐发生零适用于所有这些带符号系数，包括目标模数集和任意子族。selectedEmpty 的 S 及其补集逐 pair 为零，完全无质量下界或共 Q 选择假设。用此零重写旧分析端点时，原给定的 kappa、nu、epsilon、support、所选 rank 及共同阈值仍取旧端点所证明的范围。

## 相邻源的归属

原生 `SecondFunctionalMotherCarriers:55–71` 和 `SecondFunctionalMotherFinite:16–26` 把 Gamma1 定义为两个原 sifted counts（权 4 与 1），Gamma2–4 为三个进入有符号母式的负单素数项，Gamma5–6 为两个直接的正素数对项。Gamma7–21 才调上述 prefix 列表。原稿 `manuscript-body.tex:830–855` 保留相同前缀的两项反馈、单位商曲面和坏 Gamma5 的正计数，`own-chen-table-insertion-chain-20261009.tex:269–279,294–336` 另列 W1 的三素数正乘积。它们有各自的物理源和定理位置。全 PP 的 marked 及 upper/lower 源仍须在所属节点完成。

在 PP 正文中 (T) 的三路分块允许某组无槽而为卷积单位 δ₁，真实标记系数仍在外部。HB 的每个原始素数组 j=1,2,3，各有 2j 个因子并含一个 log；单位 log 的权等于零。`P3ActualOriginalEmptyWordExactPayment` 处理原细素数词在总积=N时的 `r=N` 分支。本项的零只取决于 Gamma 发生列表。这三类独立边界不得借本项取得付款或验核。

## 最终源码及依赖检查

| T15 模块 | 字节 | 定理 | 最终 SHA-256 |
| --- | ---: | ---: | --- |
| P2GammaActualEmptyMotherSource.lean | 5965 | 11 | `5d5071bb93f3522db2747e820a7f70822252237356942acb0f314e4d9b53c79c` |
| P2GammaActualEmptyMotherPhysical.lean | 5573 | 6 | `b8bfd896626719d02ef5f0bc8a9013e8b13ae2ad9818cfcb7f98605661bf2c43` |

Source 第 23–52 行复用现存 native 长度定理并下推到实际 root label，第 57–72 行保留给定 nil 参数的旧标记底数、正整数余商和原精确均值。第 75–105 行在原列表上逐发生、逐对及逐外层求和，消去的是指数列表未生成的分支；第 110–121 行只展开 Gamma1 原有的两个 Phi 查询。Physical 第 26–46 行将零落实到原物理 full/rank/remainder 和任意选中集。第 49–99 行与 `153bb09` 秩至多二端点及 `b538b42` 的 admitted rank、compact full-minus-rank-remainder 两条既有结论逐参数对照，使用 `sub_zero` 化掉同一函数。没有将高秩 remainder 本身付款，也没有假设任何所欲证明的终端结论。

初版 Source 的 SHA 为 `3dbe932519b10e7f9831750d94280c0a53a7d243eabdad80eff6ca6ff1f706c3`。第 43、92 行两次 `List.mem_cons_self` 给了显式实参，与冻结工具链 `v4.33.0-rc1` 的隐式参数不符。作者订正到上述最终 SHA，独立反向替换这两行即恢复初版 SHA。API 证据为先前固定 Lean 源 blob `519a54b75079a3acb036a212f7303f8d497ecba1` 的 `src/Init/Data/List/Lemmas.lean:367`，本地已冻勘误 `t09/T07_LIST_MEMBERSHIP_OVERLAY_REVIEW.md` 的 SHA-256 为 `7cc28339a0c45d5a6a0f0ce5668a4bbfe07d69f7d372f33613be1eee425ab266`。历史导入 `0632f2e/P2GammaRetainedSameRhoMother:118`、`b538b42/P2GammaCompleteLevelMother:124` 的旧字节亦各含一次同类过应用，未来重放需在安装源中修正这两处。相关历史分支文件未全部物化在 sourcehead `3d15576a` 的同一路径中，应以其原 commit/blob 识别。

## 安装补丁与来源清单

从三份实际外部项目导入独立遍历 `f1bcf37` Git 树，逐读 blob，得到 335 个 ImbalancedChen 模块、160 个外包直接导入名。257 个项目源位于历史标准路径，78 个在历史源码档。与主 sourcehead 的同路径同 blob 比较，309 个一致，26 个需要按精确历史来源取回。每个模块的路径、Git blob、SHA-256、直接导入序及两树间比较均与 IMPORTS.json 对应。未将该项目源码图当作外包完整安装或构建验收。

该依赖图中共 12 个模块的 13 处旧调用有上述 API 不兼容。T15 随包提供未来安装用 `DEPENDENCY_API.patch`。独立从原 blob 的完整字节出发，只在对应行删去两个显式实参，逐个前后哈希及行号均吻合，生成的全部 6,633 个 unified-diff 字节与交付件完全一致。其中 FirstExitPresieveProjection 的两个合法裸调用未动。没有安装或运行补丁。REGISTRY 中两份新模块的声明行、字节哈希、原稿及 native producer 的固定 Git 对象和既有 source anchors 已核。

本次逐字审查、Git 对象绑定和数学判定均为静态工作。未执行 Lean、Lake、LSP、stage、producer、数值证书、CI、内核重放或传递公理审计。本项不增加 (M) 的实现，不更改任何追踪文件。独立来源原文、精确字节和 22 次发生的位置见本目录 EVIDENCE.json。
