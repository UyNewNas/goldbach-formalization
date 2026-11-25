# Rounded reuse：独立源码与依赖审查

## 结论

**静态审查未发现阻断项。** 本结论精确绑定 `PREPARED_FILES.json` 的九个 Lean 文件，基点 `45428d4ef7eac2f19dfd17a3d3a9a4d0903296ce`、旧源固定提交 `c6b89774822580c731a236ac66dcd7466ac8a0e6`。候选仍为 **SOURCE ONLY / UNCOMPILED**；本审查没有运行 Lean、修改 canonical 源码或 manifest，也没有授予新的 owned/PP/density 验收信用。

新模块 `P3OriginalU5RoundedModulusCap.lean` 的冻结 SHA 为 `cfc11bb4aa62c234a7282eba20c523e3cd247db1637105da05ad08ab130ea678`。其新增范围准确为一个 `rawRank` abbrev 和两个连接定理。

## 旧证明的复用与重复消除

逐字核对三份 p15 修复源码及对应固定 Git blob。`P2LowerFiniteCellRounding`、`P2LowerFiniteCellBetaCompiler`、`P2LowerCanonicalRetainedTrace` 全部为原字节复制。

`P2RoundedQuotientMinorant` 的旧 quotient 定理块为 1,692 B，声明和证明原字节保留，fully qualified name 仍为 `ImbalancedChen.P2RoundedU6NativeJointLedger.rounded_quotient_sum_le_sifted`。`P2RoundedFibreCore` 的十三个旧定义/定理块原长 14,610 B；逐个按记录 byte offset 核对八处 `universe → «universe»` 后，其他字节完全相同。反向去引号精确还原旧块。两份兼容 full 文件删去新增 import 并放回抽取块，可以逐字重构旧文件。

count 入口仅替换 import 和 `rowEstimator_le_sifted` 内的证明：删除新写的同款有限 Fubini/minorant 展开，直接调用已存在的任意外乘数 quotient 定理。逆替换精确恢复原 145 行冻结稿。原定义、四条定理陈述、ordered-pair 标记、相同 rounded rho、exact coprime numerator、signed primitive discrepancy 和 centre correction 均未变。

这也修正了旧独立审查只搜索 main/donor canonical 所导致的去重范围限制；原冻结稿及原审查作为历史记录保留，本包明确使用新找到的旧接口。

## 新 U5 level/rank 供应

`selected_U5_raw_level_and_rank` 从实际 `selectedPolicy R bank buffer false N t` 的 `rawSupport` 成员开始。`pair_policy_support_iff` 给出真正的 chronological chosen 子词及 accepted run，再调用原 U5 的 `selected_U5_accepted_word_le_topCap` 得到完整外标 pair × rough product 的界。这里没有输入一个所要证明的 raw level 结论，也没有把 `sixthSupport` 当作原 `pairSupport`。

rank 推导使用同一 chosen 词中的每个 prime 满足

\[
N^{\mathrm{attachmentNu}\,\epsilon^2}\le p.
\]

外标 pair 由真实 prime carrier 保证乘积至少 1，因此 raw rough modulus 自身也不超过 `N^topCap`。有限乘积比较和 `N>1` 给出

\[
\mathrm{length}(\mathrm{chosen})
\le \frac{\mathrm{topCap}}{\mathrm{attachmentNu}\,\epsilon^2}.
\]

旧 `actual_chosen_eq_canonical` 将 chosen 精确识别为反向 primeFactorsList，最后取 Nat ceiling。empty word/r=1 的情形也在这一统一有限论证内，没有另加非空前提。`epsilon>0` 保证除数严格为正。现有旧 `actual_pair_raw_full_prefix_rank` 限定 sixth selector，不能直接替代这一实际 U5 供应。

`exists_uniform_rounded_U5_modulus_cap` 用原 `attachmentNu * epsilon ≤ buffer ≤ 1/1000` 与已验收的严格指数间隙，先取 `topCap + attachmentNu*epsilon` 和 `.599` 之间的中间指数，再调用旧 `exists_uniform_mesh_physical_level`。所得 `tau>0` 位于 `R / mesh / bank / N / t / k` 量词之前，且只使用已经推出的实际 raw level/rank。它没有把最终 rounded level 当作前提。

最终非零入口是 count 模块同一个 `roundedRho`，参数仍为 ceil(cutoff)、smallCutoff、cutoff 和 smallLevel；smallLevel 的指数正是 `attachmentNu*epsilon`。旧定理内部处理 outward negative rounding 的同 label raw witness，因此不假设 rounded word 自身已 raw-accepted。rough rank 与 small beta divisor 分开，后者的完整支撑成本已进入最终 full modulus。严格 `< N^(599/1000)` 来自中间指数和 `N>1`，方向正确。

## 依赖、旧阶段与审查边界

实际重新解析全部选中源码的 imports，核对所有 graph edges 与 SHA，并与固定基点 Git 字节比较。结果为：

| 项目 | 独立核对结果 |
| --- | ---: |
| 原 selected 源码保持原 hash | 264 |
| 新 prepared selected | 7 |
| 已在仓内、此次新选入的 UpperCoefficientPerturbation | 1 |
| 合并 selected 闭包 | 272 |
| count 入口闭包 | 147 |
| rounded modulus 入口闭包 | 264 |
| 外部 imports | 117 |
| 新外部 imports / missing / cycle | 0 / 0 / 0 |

两份兼容 full 模块不在这 272 份 selected 闭包中，不因此获得其 heavy ledger 依赖的闭包或编译信用。保持原 namespace 不会保持 defining-module 身份；抽取后的新 core、quotient 模块及消费者仍需实际 strict compile、official kernel replay、完整 defining-module/serialized inventory、full type 和传递公理审计。

旧 batch65/batch90 的 18 个阶段文件与 p15 固定 Git 原字节相同。三项 normal build 和三项 kernel replay 的记录均 exit 0，日志 hash 相符，kernel 日志含精确 replay 行；每项 AFTER_NORMAL 与 AFTER_KERNEL 的源码/对象快照一致。这只核实已有阶段的真实范围，不能代替本次依赖、完整 sidecar、工具链及新 owned 清单的绑定。旧 normal build 也未被改称本轮 strict owned 编译。

未发现新增 `sorry`、`admit`、axiom 或 unsafe 证明捷径。八处保留字 quoting 属于表达适配；旧抽取块尚未在本包 elaborated，故不以文本可逆性声称旧失败陈述的已验收类型同一。

本包供应的是完整 physical carrier 的 envelope 和同一 rounded coefficient 的 count 接线。它没有识别 raw rho 与 rounded rho，没有支付最终 density loss，也没有供应 whole-word atom identity、common physical Q、family admission 或 PP。
