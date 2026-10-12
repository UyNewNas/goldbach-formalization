# 1+1.75 Lean 形式化：Part 0 基线与接口单

版本：v0，2026-10-12（北京时间）。维护者：Part 0。
用途：可直接转交 Part 1、2、3、4-A、4-B、5 的共同协议。

**本单冻结代码、手稿、证书选择、文件所有权、最终出口及内部参数化契约。它不是主定理完成报告。**
基线没有完整当前政策、最终 boxed rho、same-mask-v2 的 Lean 实例或全部真实积分泛函。下面明确区分：
A. 已有源码声明；B. 各 Part 待证明的目标类型；C. 待上游提交的实际数据值。
B 的类型完整不意味着命题已经证明；C 不得用假设或结论字段填补。

## 1. 唯一共同起点

| 对象 | 固定值 |
| --- | --- |
| 形式化仓库 | [UyNewNas/goldbach-formalization](https://github.com/UyNewNas/goldbach-formalization) |
| 代码基线完整 SHA | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| 代码 Git tree | `1fd54b8b4d5fd89abc767ee7e8d814453453b29c` |
| 来源分支 | `codex/variable-envelope-boxes`；读取时仍指向上述 SHA |
| Part 0 集成分支 | `chatgpt/chen-p0-integration`；已从上述 SHA 建立 |
| 手稿仓库 | [UyNewNas/chen-imbalanced-semiprimes](https://github.com/UyNewNas/chen-imbalanced-semiprimes) |
| 手稿完整 SHA | `ba6ec11d800eccc54406490631895e174de85766` |
| 手稿 Git tree | `2b5af758d1b4a4799a120d4ea108679cc02f2e11` |
| 主体源文件 | `paper/source/manuscript-body.tex` |
| 主体 Git blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| 主体 SHA-256（本轮重算） | `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` |

从固定 SHA 创建各自分支；不要从初始化的 master、来源分支的未来移动 HEAD、或另一个 Part 的未固定工作区开始。
文档提交会使集成分支 HEAD 前进，但本单指定的共同证明基线不因此改变。文档提交的完整 SHA 随交付回执提供，不能冒充新的已验证证明 SHA。

已读形式化 README、`docs/CURRENT_MANUSCRIPT_MAP.md`、`docs/EXTERNAL_REUSE.md`、`CurrentMainTheorem.lean`、`CurrentNumericalTransfer.lean`、相关实际权/历史积分/Chen 均值桥及两个 workflow。
两个固定提交的完整递归树均未发现 AGENTS.md；当前工作目录祖先亦未发现适用 AGENTS.md。
代码基线的 303 个文件已逐项重算 Git blob 哈希并与远端固定树一致。该检查验证源码身份，不验证 Lean 证明。

关键基线文件 blob：

| 文件 | Git blob SHA |
| --- | --- |
| `README.md` | `eed138d863c0333e4698e7939a7bf98063957460` |
| `docs/CURRENT_MANUSCRIPT_MAP.md` | `c8c93a71f00811284d0aef149aa5efa7c66bc413` |
| `docs/EXTERNAL_REUSE.md` | `31aa71c696808b93f725e2bb5f0e753a4d8009a9` |
| `ImbalancedChen/CurrentMainTheorem.lean` | `feb9f65c5e0268b93eec458cd0faa5151181aa2d` |
| `ImbalancedChen/CurrentNumericalTransfer.lean` | `f9ca13276bee9f9c734127dd69a87902eeecb258` |

## 2. 工具链、依赖和检查工具 pin

`lean-toolchain = leanprover/lean4:v4.33.0-rc1`。
保留 lakefile 和 lake-manifest，不执行依赖升级。
直接依赖只有 mathlib、goldbach；其余为 manifest 中的继承依赖。

| 依赖 | 完整 rev | 层级 |
| --- | --- | --- |
| `goldbach` | `09b97db5764ade1246bfb77206baa1b124760958` | 直接 |
| `mathlib` | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` | 直接 |
| `LeanArchitect` | `78dd66840d3efe8c824c699fc03381cec817c271` | 继承 |
| `plausible` | `b1c4a69a7e247ab7df20460212001673d74f08c0` | 继承 |
| `LeanSearchClient` | `0498c7c070c143a3bf7379f4d99a2c63bb9d9715` | 继承 |
| `importGraph` | `18a90119a5d316358fde6c86e0ca24e59212e32c` | 继承 |
| `proofwidgets` | `b1436dc749e722c9920036b52cdc43b3451d0b69` | 继承 |
| `aesop` | `57d3325be72a842920813bcb40f96a6f7393c185` | 继承 |
| `Qq` | `ee41917ae11d38479fb8fb24745f7ca4bf0a784d` | 继承 |
| `batteries` | `41bd267b3f6b7252f6676af46d4ffc6783b64de9` | 继承 |
| `Cli` | `da07ca808b6718cb2aed14dba154e5a08b8f8ecf` | 继承 |

配置文件的 Git blob：

- `lean-toolchain`：`fd85b262bf1c734663aa8292b0101f672168788f`
- `lakefile.toml`：`c7b839a2240d9960fb1f01f0e8808a9459935e0e`
- `lake-manifest.json`：`86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f`

项目检查工具：

- `leanprover/lean-action@f061402b660e0c34644504b324e830f2991d4865`
- 该固定脚本使用 `axiom-audit v0.1.2`，并核对完整 SHA：
  `46024e005996495c65ef609368e11ab39c4222e3`
- 内核回放使用本项目 Lean 4.33.0-rc1 随附的 `leanchecker`。
- 允许传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

外部复用以现有 goldbach pin 为唯一解析数论依赖入口。不要再整体添加
analytic-number-theory-lean：两者会重复导出 AnalyticNumberTheory / PrimeNumberTheoremAnd 根。
现有 PNT/Mertens、普通 BV、实际 Rosser 权、prime-sum integral API 应优先复用。
旧 ANT 中同名但量词不足的 BV、历史条件式 Chen、普通 BV 对高阶物理支持的越界使用，均不能充当本手稿解析供应器。

## 3. 冻结数学语义

| 项目 | 精确值或要求 |
| --- | --- |
| 上界常数 | `currentK = 8452171 / 1250000 = 6.7617368` |
| 下界常数 | `currentC = 49044063 / 25000000 = 1.96176252` |
| 任意实参数 | 每个固定实数 `1/2 < b < 1`，先选 b，再选阈值 |
| 主实例 | `b = 18704241/25000000`，系数 `1/100000` |
| 次实例 | `b = 14963373/20000000`，系数 `1/1000000` |
| 第三实例 | `b = 9/10`，系数 `124889/100000` |
| 计数归一化 | `singularNormalization N = singularSeries N * N / (log N)^2` |
| 密度归一化 | `singularSeries N / log N` |
| 计数索引 | 不同加法素数 p 各一次，p < N |
| D12 | 素数或恰为两个素数乘积的余项；排除 0、1 |
| RealDb | 素数余项或 r*q 且 r ≤ q^b |
| RealB | D12 的精确补集；b<1 时等于有序 q^b < r ≤ q |
| 重复素因子 | 保留素数平方；排序不产生因子 2 |
| 无穷远 | 全部充分大偶数，主结论用 EReal liminf |
| 当前 Chen 截断 | a=417/5000，h=19/125，d=59/250，末 cutoff=1/3 |

奇异级数没有前置因子 2；密度尺度和计数尺度不可混写。
历史 6.7618、1.958654、1.96131568、外部 1.9728 均不是当前终点。
历史 chenFixedElevenWeight 或采用 a=100/1149、h=50/309 的桥不能直接改名为当前权。

### 已知手稿精确恒等式差异

固定 `CURRENT_MANUSCRIPT_MAP.md` 已记录主体约 425--429 行 Euler 比值公式的 target-prime tail 因子错误。
若第一个尾积遍历所有 p≥z，则 p|N 的第二个尾因子应为 (p-2)/(p-1)，不是 1-1/p；
或者第一尾积须排除整除 N 的素数。基线 Lean 的
`normalizedFiniteSieveDensity_eq_odd_div_tail` / `centerPrimeTailCorrection`
已使用正确公式。保留这些正确定义与常数；不要为逐字匹配错误等式而改 Lean。
本轮没有编辑手稿；最终映射必须明确记录此处校正及其固定正幂尾极限不变的理由。

## 4. 唯一采用的证书版本

权威选择来自手稿固定 SHA 下：
`verification/data/corpus-renewal-improvement-assembly-20261010.json`。

采用 same-mask-v2、阈值 7/3；同一删除区域 E0∪E1 共
6091+11481=17572 个 pair512 盒。旧 12/5 候选被替换，其 gain 不得再次加入。
历史文字中的 17772 是已记录笔误，不改变真实 mask。
H430 只用于 U3/U4，其他项保留指定 H248/h248；106 actions、430 rounds、400 项最终数组
都需要真实有限递推证明，不能把数组读入直接当作不等式。

下表路径均相对于手稿仓库；Git blob 已按固定树核对。
标记“重算”的 SHA-256 本轮由实际返回字节重算，其余是证书 manifest 声明，未重放数值证书。

| 路径 | Git blob SHA | SHA-256 / 本轮状态 |
| --- | --- | --- |
| `verification/data/corpus-renewal-improvement-assembly-20261010.json` | `154a3d0e73a84d774bc21d3da07a0e337560d11c` | `9254e419145a0a48954c3ca9af1d76a4312dd280dcdbac5bfd216d8b2f49e27c`，重算 |
| `verification/data/global-selected-numeric-completion-20261010.json` | `34c8bb0facc3e24597c09d6b2e410e63c344ef5e` | `9101ddb9d109782aa99385cb02895c13cfa3f492306f8f5aab0f576335ab90b8`，manifest |
| `verification/data/global-selected-numeric-completion-20261010-obligations.json` | `434be0e085dde5a18ff0f181af828649d39ee1cc` | `0185582f3c2e172320119d3f0f1d818805bccebbafc8f4fff272ee52b86ea6c0`，重算 |
| `verification/data/corpus-renewal-paired-certificate-v2-20261010.json` | `49499697cca96de5f7b779e95077874ce5f9d119` | `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`，manifest |
| `verification/data/corpus-renewal-paired-independent-v2-20261010.json` | `e13c1411276e32e29b8a33065a9f8161cdb847a2` | `e18e78975bb982db64fc6b4038866919bbf0702306eb26f9d42076e77b042f7c`，manifest |
| `verification/data/global-theorem-completion-assembly-20261010.json`，保留的 baseline | `9f63795c32366a585be957d15b727f2855faa5db` | `4f4c33d91e414118a5ec3b391ed37c4652b0e035fbf0e502502a6c8a753aaf11`，manifest |
| `verification/refinement-bindings.json` | `cdd3cdb0ebd50ed0c26cc171d64ef3049ed0b69f` | `2b2c50ac9f63080c0d181aaf3b6635f18c0a4a34e1cbb5ce7ef6c4da86a9172c`，manifest |

400 项表声明摘要：
`4243db3238c28e8ac7f22d848db98e7872ad3c134fc4d697058583248f46f52d`。
完整数值 archive 声明摘要：
`8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1`。
本轮未下载/重放该 archive；不能把其中继承的历史 quadrature 当作已形式化。

CURRENT-SUPPLEMENT.txt 提到的
`corpus-renewal-improvement-checkpoint-20261010.json` 不在固定仓库树中；
不得声称该文件已取得。Part 2 应以实际存在的 assembly、bindings、证书数据及其源证明建立绑定。

### 上下界预算的固定有理数

以下记号只用于本单：E 是上界 raw endpoint，u 是每项 upper reserve；
R 是下界 raw endpoint（已经是 c 单位），B0 是每项 lower reserve。

```text
E  = 9979702576710911234850619807816847864907359959/1475913550962201227946780619099353215139840000
u  = 145007961227048312210593427530128000784681/11807308407697609823574244952794825721118720000
R  = 1345983686820460038728276256001756964104092721/685738127494661151198444592354557952000000000
B0 = 2913305608548241964824517919947906098888971/5485905019957289209587556738836463616000000000

currentK - E - 2*u = 71229286727542131248758574547050908572431/737956775481100613973390309549676607569920000000 > 0
R - 2*B0 - currentC = 13457260926863633771775678584711245753/2742952509978644604793778369418231808000000000 > 0
```

本轮 Python Fraction 核对了两条有理数等式与严格正号。此事不证明实际积分界、密度界或 Chen 均值。
Part 2 必须证明 P1/P5 实际定义的积分泛函 U≤E、R≤L，以及两种误差各自的预算。
不得将 U 定义为 E，或将 L 定义为 R，从而空转证书。

实际数据验收还须覆盖：old fifth 的 292633×64=18728512 children、additional fifth 1763420 boxes、
retained sixth 632104 cubes；下界 I5 的 158251 个当前 h floors 与 679 个 a integrals；
restoration 的 98668 boxes / 789344 slanted layers；
U10/U11 的 1190700 ordered rows（含 tied-bin simplices）。
这些是 adopted obligation record 中的检查范围，不是本轮已重算的计数。
正 saving 的未覆盖区域可在已证明非负时丢弃；负 cost 上界须覆盖完整保留域；
父/子替换、旧/新估计器不得重复计入。saved-floor loss 不是实际 Y6 计数上界。

## 5. 独占文件所有权

下面是本轮指定的新叶模块路径，均不是声称基线已存在的文件。
所有已有正确 Lean 模块默认只读复用；确需修改已有文件时，由该 Part 交差异说明和补丁，P0 统一应用。
其他 Part 不改公共根、工具链、依赖、共享状态或最终入口。

| 所有者 | 独占新增文件，均相对仓库根 | 对外责任 |
| --- | --- | --- |
| Part 1 | `ImbalancedChen/CurrentPolicyData.lean`；`CurrentHistoricalSupport.lean`；`CurrentHistoricalIntegralData.lean`；`CurrentHistoricalIntegrals.lean`；`CurrentPolicyCompiler.lean`（后四同在 ImbalancedChen/） | 当前完整上/下历史政策与联合分区、继承合法性、实际支持、compiler 及真实积分 |
| Part 2 | `ImbalancedChen/CurrentCertificateData.lean`；`CurrentSameMaskV2.lean`；`CurrentRenewalCertificate.lean`；`CurrentUpperCertificate.lean`；`CurrentLowerCertificate.lean` | 固定有限数据、唯一 mask、7/3、实际积分及 H/h 数值证书 |
| Part 3 | `ImbalancedChen/CurrentPrimeProductData.lean`；`CurrentPhysicalDistribution.lean`；`CurrentCoprimeCorrection.lean`；`CurrentChenDistribution.lean` | licensed signed PP、共同区间/相位、同一 rho 的分布与重心修正误差 |
| Part 4-A | `ImbalancedChen/CurrentPhysicalWeight.lean`；`CurrentDensityBound.lean` | 实际物理权构造与 P1 的精确字典，同一 rho 的 majorant/support/系数界和 K 密度界 |
| Part 4-B | `ImbalancedChen/CurrentBadUpper.lean` | 任意固定实 b 的无解析前提 hUpper |
| Part 5 | `ImbalancedChen/CurrentChenMeanData.lean`；`CurrentPositiveFamilyUpper.lean`；`CurrentRenewalSoundness.lean`；`CurrentChenMean.lean`；`CurrentChenLower.lean` | 完整当前十一项均值、一般正 switched-family 上界桥、H/h 语义、c 与 hLower |
| Part 0 | `ImbalancedChen.lean`；`ImbalancedChen/CurrentMainComplete.lean`；`verification/CurrentMainCompleteAudit.lean`；本单、公共 map/status、最终 CI/核验入口 | 按固定提交整合；保留 CurrentMainTheorem/CurrentNumericalTransfer 条件桥；接入闭合生产者 |

表中省略目录的同一行文件均带 `ImbalancedChen/` 前缀。
各 Part 的辅助核验材料只写 `verification/parts/p1/`、`p2/`、`p3/`、`p4a/`、`p4b/`、`p5/` 对应目录。
新增其他公共名称/文件时先在交接中登记，避免两会话分别定义同一个对象。

### 依赖及先交数据原则

1. P1 先交 PolicyData / HistoricalIntegralData 的实际定义固定提交；P2 可先处理证书有限数据。
2. P4-A 的 CurrentPhysicalWeight 先交纯构造和字面对应，不依赖 CurrentDensityBound 或 Part 3 的解析结论；
   P3 可 import 该构造后工作，避免 P3↔P4-A 循环。
3. P5 的 CurrentChenMeanData 先给完整下界泛函和唯一 mask 接口；P2 的 LowerCertificate 只 import 此纯定义层，
   P5 的 Mean 再 import P2 的证书证明，不能反向让定义层 import Mean。
4. P4-A 消费 P1 的实际积分和 P2 上界证书，产出同一 rho 的 K 密度；
   P3 消费同一构造，产出对应实际分布/误差。
5. P5 消费 P4-A + P3 的一般正 prime-product 上界（U*），再证明当前均值。
   **P5 不依赖 P4-B，不等待 RealB 的专用 hUpper。**
6. P4-B 独立组合同一 rho 的密度/误差与已证源质量 log(1/b)，交 hUpper。
7. P0 最后组合 P4-B 与 P5，得到完整主定理和同阈值三推论。

## 6. 终端接口：完整待证类型

以下统一在 `namespace ImbalancedChen` 中解释。代码块是接口规格，不是已加入仓库的 Lean 声明。
这些类型完全由基线现有定义组成，现即冻结。

### P4-B → P0：current_realBad_upper

```lean
theorem current_realBad_upper
    {b : ℝ}
    (hbLower : (1 : ℝ) / 2 < b)
    (hbUpper : b < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N
```

不得另带未证 hDensity、hDistribution、hMass、等价 structure/typeclass 参数。
内部允许用有理 minorant，但出口必须保持全部固定实数 b。

### P5 → P0：current_D12_lower

```lean
theorem current_D12_lower :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤
          (D12 N : ℝ)
```

### P0 的最终目标

```lean
theorem current_theorem_1_1
    {b : ℝ}
    (hbLower : (1 : ℝ) / 2 < b)
    (hbUpper : b < 1) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) /
            singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```

```lean
theorem current_corollary_simultaneous :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ)
```

最终入口在证明体内调用已证 current_D12_lower、current_realBad_upper，再应用原条件桥。
目前没有新增这两条最终定理；不会先用未证包装生成一个同名“完整”入口。

## 7. 内部接口：完整参数类型与尚待实例化的值

### 7.1 实际物理权的共同对象

基线已经定义以下对象：

```lean
actualSmallRoughModuli
  (retainOdd : List ℕ → Bool)
  (N cap : ℕ) (w z : ℝ) : Finset ℕ

actualSmallRoughRho
  (retainOdd : List ℕ → Bool)
  (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ
```

后续 Q 和 rho 必须是同一实际构造，或有已证逐系数等式的 manuscript boxed extension。
基线 actualSmallRoughRho 是 raw-policy 附着；若 compiler 得到 boxed rough coefficient，
不能无证明地把 boxed support 当作另一棵 prefix-closed raw tree。
P1/P4-A 必须提供 compiler、系数支配及对应字典，不能仅换同名 alias。

下列参数化接口使用某个已经固定的实例：

```lean
-- 数据参数的完整类型；不是这些任意数据都满足 K 界的断言。
retainOdd : ℕ → List ℕ → Bool
cap : ℕ → ℕ
w z L : ℕ → ℝ

-- 每个固定精度内：
Q N := actualSmallRoughModuli (retainOdd N) N (cap N) (w N) (z N)
rho N := actualSmallRoughRho (retainOdd N) N (cap N) (w N) (z N) (L N)
```

这里省略的外层精度参数必须由实际定义补全后冻结，不能推断它不存在。
特别是 fixed positive nu,r 下，现有附着 reserve 先选 epsilon，再选 N0，
然后对所有 N、cap、retainOdd 同时有效；具体完整已证类型见附录。
P3 必须对 P4-A 选用的同一 epsilon/参数束有效，不能各自存在一套 rho 后拼接。

**A. 固定权版本。** 对一组确定的 `Q : ℕ → Finset ℕ`、`rho : ℕ → ℕ → ℝ`，
只有证明这组固定权达到任意小余量，才能交付以下目标命题
（这是一份类型模式，不是任意 Q/rho 的通用定理）：

```lean
∀ eta : ℝ, 0 < eta →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    physicalDensitySum (Q N) (rho N) ≤
      (currentK + eta) * singularSeries N / Real.log (N : ℝ)
```

**B. 按精度选权版本。** 若实际构造要先按请求误差选择 epsilon，数据类型相应为
`Q : ℝ → ℕ → Finset ℕ`、`rho : ℝ → ℕ → ℕ → ℝ`、`z : ℝ → ℕ → ℝ`。
需要提供的联合目标模式如下；它只对这次请求的 eta 给出密度结论：

```lean
∀ eta epsilonMax : ℝ, 0 < eta → 0 < epsilonMax →
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < epsilonMax ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
        (∀ n : ℤ,
          actualSmallRoughIndicator N (z epsilon N) n ≤
            physicalDivisorSum (Q epsilon N) (rho epsilon N) n.natAbs) ∧
        (∀ q : ℕ, |rho epsilon N q| ≤ 1) ∧
        (∀ q : ℕ, rho epsilon N q ≠ 0 →
          q ∈ Q epsilon N ∧ Squarefree q ∧ Nat.Coprime q N ∧
            (q : ℝ) ≤ (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
        physicalDensitySum (Q epsilon N) (rho epsilon N) ≤
          (currentK + eta) * singularSeries N / Real.log (N : ℝ)
```

epsilonMax 用于兼容各模块已证的有限个小参数约束；不是许可忽略这些约束。
当前 compiler 的全部额外几何/参数许可也必须在同一 epsilon 见证上证明，
并使 Part 3 的完整分布定理可在该见证直接实例化。
不能分别交“存在一个满足密度的 epsilon”和“存在另一个满足 PP 的 epsilon”后拼接。
若 PP 自身也需要按精度选参，须给出联合选参定理，同时兑现 majorant、支持、密度和 PP；
不能从 B 推出 A，更不能把固定一次 epsilon 后的结论提升为对所有 eta 成立。
v0 不猜测不存在的 currentPolicy/currentRho 或几何许可定义，
收到纯定义固定 SHA 后由 P0 发布包含全部具体许可类型的 v1 实例；所有证明必须填实。

同一 rho 还须证明：所有整数 n（含 0/负数）的实际 majorant；|rho|≤1；
零以外的真实支持 squarefree、与 N 互素；非零物理模数的指数界及 compiler 许可。
不要给含零项的显示 carrier 强加未成立的整体 cutoff。
手稿参数保持 rho0=19/96、mu0=25/128、Theta=299/500、Lambda=153/256；
Theta 与 Lambda 不可互换。高阶物理支持 theta*=599/1000 的许可须真实支付。

### 7.2 P1 → P2/P4-A：历史积分与支持

P1 先提供实际 base、Q3/Q4/Q5、后续第六/第八层、buffered caps、fallback 和联合历史分区的定义。
任一历史第五层积分目标在固定数据实例下的完整模式是：

```lean
-- 以下是数据槽，I5 必须独立定义为真实联合区域的积分。
base : ℕ → Bool → List ℕ → Bool
Q3 Q4 Q5 : ℕ → List ℕ → ℝ
cap : ℕ → ℕ
z : ℕ → ℝ
I5 : ℝ

Tendsto
  (fun N : ℕ =>
    actualHistoricalFifthSaving
      (base N) (Q3 N) (Q4 N) (Q5 N) N (cap N) (z N) *
      Real.log (N : ℝ) / singularSeries N)
  (Filter.atTop ⊓
    Filter.principal {N : ℕ | 0 < N ∧ Even N})
  (nhds I5)
```

不能将 I5 定义成待证极限，不能用 ordinary gate 替换历史联合 gate；
正负项的预算方向、完整区域及 rough fallback 按手稿兑现。
P1 还须用真实表证明附录 actualHistoricalFifthSaving_eq 的 h34/h45，
再把有限望远镜和真实积分连成同一实际上界泛函 U。
P5 负责把各下界真实积分组装成 c 单位的泛函 L。

P2 的最终数值端口在这些**实际定义**固定后为：

```lean
-- U, lowerL : ℝ 均是已绑定的真实积分泛函。
U ≤
  (9979702576710911234850619807816847864907359959 : ℝ) /
    1475913550962201227946780619099353215139840000

(1345983686820460038728276256001756964104092721 : ℝ) /
    685738127494661151198444592354557952000000000 ≤ lowerL
```

还须分别交有限近似、compiler 两项误差界：上界各 ≤u；下界各 ≤B0。
只有给出真实积分的定义、区域许可、全部证书语义和上述不等式，才能算 numerical port 交付完成。
上界 U 的完整定义及下界 lowerL 的完整定义在基线中不存在，本单不将它们伪记为现有声明。

### 7.3 P3 → P4-B：真实半素数误差

在同一已固定的 Q/rho 下，数据参数为
`num den : ℕ`、`kappa : ℝ`、`Q : ℕ → Finset ℕ`、`rho : ℕ → ℕ → ℝ`。
对合法 num/den、当前 cutoff 和当前物理权，分别交以下完整消费型命题：

```lean
∀ eta : ℝ, 0 < eta →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    |physicalDistributionError num den N
      (manuscriptHalfProductCutoff kappa N) (Q N) (rho N)| ≤
        eta * singularNormalization N
```

```lean
∀ eta : ℝ, 0 < eta →
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    |physicalCoprimeCorrection num den N
      (manuscriptHalfProductCutoff kappa N) (Q N) (rho N)| ≤
        eta * singularNormalization N
```

这两个命题只要求用于真实合法实例，不对任意 rho 或任意 kappa 作假断言。
P3 的实际声明须显式列完几何/参数范围，并为下游实际实例提供证明。
若采用 7.1 的 B 版本，这里的 Q/rho 必须取为同一已选 epsilon 的实例；
上述任意小误差形式须由 P3 对该实例真正证明。
若 P3 的误差精度也会改变 epsilon，则改用 7.1 所要求的联合选参接口，
并只消费同一请求精度下的结论，不保留不成立的固定权任意小误差量词。
signed error 外只取一次绝对值；精确 coprime mass 不得偷偷改为总 source mass。
共同区间、共同加法相位、完整 product scale 和 smoothing licence 必须保留。
普通低于 1/2 的 BV/Pan 不能无损承担 599/1000 的物理支持。

### 7.4 P3/P4-A → P5：一般正 switched-family 桥

`CurrentPositiveFamilyUpper.lean` 由 P5 负责，避免它依赖 Part 4-B。
先在 CurrentPrimeProductData / CurrentChenMeanData 固定实际 labelled source，
保留每个乘积的重数。设实际 `M : ℕ → Finset ℕ`、`weight : ℕ → ℕ → ℝ`；
这不是对任意算术过滤族的无条件断言。

P3 对该实际 licensed source 所交 signed PP 的消费型完整模式为：

```lean
∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
  ∀ᶠ N : ℕ in Filter.atTop, Even N →
    |∑ q ∈ Q N, rho N q *
      ((∑ m ∈ M N,
          if Nat.ModEq q m N then weight N m else 0) -
        (∑ m ∈ M N,
          if Nat.Coprime m q then weight N m else 0) /
            (Nat.totient q : ℝ))| ≤
      C * (N : ℝ) / (Real.log (N : ℝ)) ^ A
```

完整 licence 和外层精度/源参数量词须在真正生产者中打印；不能仅给这个结论模式就声称 PP 已证。
采用按精度选权时，P5 使用的也是 7.1 同一 epsilon、同一 Q/rho 和同一组已证许可；
不能为密度与本节 labelled source 的 PP 分别存在性选权。

P5 的一般上界桥对每个这样已经许可、且非负的实际 weight，需要给出：

```lean
∀ J : ℝ, 0 ≤ J →
  (∀ eta : ℝ, 0 < eta →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (∑ m ∈ M N, weight N m) ≤
        (J + eta) * ((N : ℝ) / Real.log (N : ℝ))) →
  ∀ eta : ℝ, 0 < eta →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (∑ m ∈ M N,
        if m < N ∧ Nat.Prime (N - m) then weight N m else 0) ≤
          (currentK * J + eta) * singularNormalization N
```

这里源质量界是一般转移的正常前提，P5 对每个实际 switched-family 必须消去它，
并证明 weight 非负、primitive coprime 修正和小素数加数误差。
J=0 也须成立，不可在证明中未经许可除以 J。
这个桥才是 P5 所需的 U*；单独拿到 K 的数字或 RealB 上界均不能替代它。

### 7.5 P2/P5：唯一 mask 与实际 Chen 均值

P2 的 CurrentSameMaskV2.lean 拥有唯一具体选择定义：

```lean
currentPairedSelection : ℕ → (ℕ × ℕ → Prop)
```

该名称是拟新增接口；必须由 fixed pair512 cells 对真实对数坐标的 pullback 定义。
同一区域同时用于 Y6 与 Y11 的末对，不能两个会话各建一个近似 mask。

P5 要交的实际均值出口为：

```lean
theorem current_chen_paired_mean_lower :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (4 * currentC - epsilon) * singularNormalization N ≤
          currentChenPairedPrimeSum N (currentPairedSelection N)
```

完整权保持
3Y1+Y2+Y5+Y6−Y3−Y4−2Y7−Y8−Y9−Y10−Y11−Y6(E)+Y11(last pair in E)。
第 11 项保留全 last range，全局仅除一次 4。
已证 currentChenPairedPrimeSum 的有限桥和 epsilon 桥见附录，不应重造。
它对 E 的阈值统一，因此允许 E 随 N 变化。
获得上述真实均值后，直接导出第 6 节 current_D12_lower，不能留 hMean 或证书有效性的未证包装。

## 8. “继承前层第五积分，仅单模块编译”候选

结论：**独立候选源码尚未取得，暂不纳入；不把它记作基线已有、已编译或已整体验证。**

已实际找到并按 blob 核对：

| 文件 | Git blob SHA | 正确范围 |
| --- | --- | --- |
| `ActualSelectedPrefixOwnCubeIntegral.lean` | `748278124de929e07af43a755256f6ff61499910` | ordinary constant-level parent 的第五前缀选盒真实积分 |
| `FirstExitHistoricalLevels.lean` | `76b9da946f179468e2894b406bc899e14a7f8e54` | 真实 T3/T4/T5 有限恒等式；没有历史 Tendsto/积分结论 |
| `ActualOrdinaryUpperFiveCubeIntegral.lean` | `2feefc5bfc5c2cad5a99e0bb49349cf478d27d53` | 普通父层在固定正 cube 的局部第五候选积分 |
| `verification/SelectedIntegralAudit.lean` | `9541d51f0051090a16b2927f454b89b07ff7cf36` | 六个指定模块的 defining-module 声明与传递公理审计 |

前三个文件均在 ImbalancedChen/。
ordinary 积分使用 ordinaryUpperFiveGateForms / ordinaryUpperFiveGateBounds old，
不包含历史 Q3/Q4 改动后的联合许可域。
历史第五 saving 则保留共同 T3 rank-four frontier、新旧各自的 own-cube indicator 和全部下一候选。

来源分支、全部可见分支及当前工作区未定位到另一份候选；
定向历史检索不可用。这里的结论是“尚未取得”，不是证明候选不存在。
后续需提供完整提交/补丁、文件路径、依赖、编译原始日志和对象来源；
再由 P0 在明确集成 SHA 上执行完整核验。

## 9. 本轮验证实况与最终门槛

### 本轮已完成

- 固定代码和手稿 commit/tree 读取与身份核对。
- 303 个代码文件 Git blob 哈希一致。
- 主手稿、adopted assembly、obligations 的实际字节摘要重算。
- 原型、对象语义、证书选择和有理数预算等式源码核对。
- 真实远端集成分支从指定代码 SHA 建立。

### 本轮未完成

- 环境没有可用 lean/lake/elan；未运行 Lean 编译、内核或公理检查。
- 直接 git clone 无法取得 HTTPS 身份；已通过 GitHub 连接读取并核对完整固定源码，
  不将读取快照说成可运行的本地 Git checkout。
- 未重放全部数值证书、历史 quadrature 或完整解析证明。
- 未新增 Lean 源码，也未新增最终闭合入口。
- 未启动 Codex CLI 或 Codex 任务。

### Actions 实际状态

在分支创建后的基线 SHA `1a80c1bcce67886f699d097fc37fd245cd3620bf` 上：

| Workflow | Run | 查询结果 |
| --- | --- | --- |
| Lean core verification | [38192468938](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38192468938) | completed / failure |
| Variable envelope verification | [38192468931](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38192468931) | completed / failure |

两个 job 均 runner_id=0、runner_name 为空、steps=[]。
因此没有 Lean 构建/回放/公理步骤执行；不将 failure 归因于源码，也不猜测未读取的启动失败原因。
本单后续文档提交触发的 runs 另以交付回执记录。

基线 PROOF_STATUS 记载六个新模块单编译、aggregate build 9776 jobs、
六个最终对象 replay 和 87 声明审计通过；这是历史文档记录，本轮未取得原始 .lake 日志重验。
其中六对象 replay 不是 full-root replay，不可转移为整个基线或未知第五层候选的认证。

### 最终核验不得降低的门槛

1. 固定一个明确集成 SHA；记录干净源码状态、手稿 SHA、所有依赖 pin、证书摘要。
2. 公共根真正 import 各新叶及最终入口；构建覆盖全部新增源，而非只编某个叶模块。
3. 使用现有 Lean/Mathlib/goldbach pin 做完整 `lake build`；执行两个现有 workflow 要求的检查。
4. 使用随附 `leanchecker --verbose ImbalancedChen` 对公共根执行项目规定的回放；
   保留实际运行命令、目标、输出与失败码。若另外回放叶模块，逐项记录其范围。
5. 运行固定 axiom-audit 全根/传递公理检查；
   新叶和最终入口沿用 SelectedIntegralAudit 的 defining-module 枚举方式，
   包含 private、generated、结构字段，拒绝 unsafe、axiom 和白名单外传递公理。
6. 保留项目 no-bypass 要求：不新增 sorry、admit、自定义 axiom、native_decide、
   unsafe、debug.skipKernelTC 等绕过项。不用删源、删导入或缩小审计范围换绿灯。
7. 打印所有终端生产者及最终定理完整类型：

```lean
set_option pp.all true in
#check @ImbalancedChen.current_theorem_1_1
#print ImbalancedChen.current_theorem_1_1
#print axioms ImbalancedChen.current_theorem_1_1

set_option pp.all true in
#check @ImbalancedChen.current_corollary_simultaneous
#print ImbalancedChen.current_corollary_simultaneous
#print axioms ImbalancedChen.current_corollary_simultaneous

#print ImbalancedChen.current_realBad_upper
#print axioms ImbalancedChen.current_realBad_upper
#print ImbalancedChen.current_D12_lower
#print axioms ImbalancedChen.current_D12_lower
```

8. 人工核对最终类型只保留真实参数范围，消去 hLower/hUpper 及其等价隐藏包装；
   证明体确实调用实际政策、同一 rho、实际 count/normalization、真实 K/c 解析证明。
9. Actions 未执行、失败、跳过、取消或环境阻塞均如实写明，不能记为通过；
   单模块编译、历史成功或数值 PASS 不代替最终集成 SHA 的完整证明检查。

## 10. 各 Part 的交接格式

```text
Part:
Base: 1a80c1bcce67886f699d097fc37fd245cd3620bf
Manuscript: ba6ec11d800eccc54406490631895e174de85766
Head: <40 位固定提交 SHA；或者完整补丁及 SHA-256>
Files:
Depends-on: <各已消费固定提交/补丁和公共数据定义 SHA>
Exports: <全限定声明名、完整 #check @... / #print 类型>
Data-bindings: <实际 policy / rho / Q / mask / integral 与采用证书的绑定>
Unproved-premises: <逐项列；没有才写无>
Verification: <实际命令、工具链、退出码、原始日志和范围>
Axioms: <完整传递公理结果>
Actions: <run URL、对应 SHA、实际结论；未运行就明确写未运行>
```

原型类型来自源码的部分见附录。本轮没有 Lean，附录不是 Lean 本轮打印结果。
P0 收到纯定义固定提交后，将内部参数槽实例化并发布 v1；
收到证明交接后按依赖整合、统一根导入与状态，再执行最终核验。
在此之前不得宣称 1+1.75 已闭合。

## 附录 A：基线已有接口完整源码类型

以下从本单固定 SHA 的源码自动抽取声明头，去掉证明体。
局部作用域为 `namespace ImbalancedChen`、noncomputable section；
使用原文件的 imports、`open Filter` / `open scoped BigOperators` 等上下文。
这些是已有源码的逐字原型，不是本轮 Lean elaborator 输出。

### D12_eq_RealDb_add_RealB

来源：`ImbalancedChen/CurrentMainTheorem.lean`

```lean
theorem D12_eq_RealDb_add_RealB (b : ℝ) (N : ℕ) :
    D12 N = RealDb b N + RealB b N
```

### current_theorem_1_1_of_manuscript_bounds

来源：`ImbalancedChen/CurrentMainTheorem.lean`

```lean
theorem current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```

### current_corollary_simultaneous_of_manuscript_bounds

来源：`ImbalancedChen/CurrentNumericalTransfer.lean`

```lean
theorem current_corollary_simultaneous_of_manuscript_bounds
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper₁ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 18704241 25000000 N : ℝ) ≤
          (currentK * Real.log (25000000 / 18704241) + epsilon) *
            singularNormalization N)
    (hUpper₂ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 14963373 20000000 N : ℝ) ≤
          (currentK * Real.log (20000000 / 14963373) + epsilon) *
            singularNormalization N)
    (hUpper₃ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 9 10 N : ℝ) ≤
          (currentK * Real.log (10 / 9) + epsilon) * singularNormalization N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ)
```

### selectedBoxCapCheck_sound

来源：`ImbalancedChen/SelectedPrefixBoxCap.lean`

```lean
theorem selectedBoxCapCheck_sound {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (l u : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu l u = true)
    (t : Fin n → ℝ) (hl : ∀ i, (l i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (u i : ℝ)) :
    (old : ℝ) < selectedBoxCap I old nu l u ∧
      (selectedBoxCap I old nu l u : ℝ) < nu ∧
      (1 / 2 : ℝ) < selectedBoxCap I old nu l u ∧
      (∀ j, prefixSquareExpr t j < selectedBoxCap I old nu l u) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < selectedBoxCap I old nu l u) ∧
      (selectedBoxCap I old nu l u : ℝ) < v (∑ k ∈ I, t k)
```

### tendsto_actualSelectedPrefixUpperDensity_normalized

来源：`ImbalancedChen/ActualSelectedPrefixOwnCubeIntegral.lean`

```lean
theorem tendsto_actualSelectedPrefixUpperDensity_normalized
    (I : Finset (Fin 5)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : b < old)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualSelectedPrefixUpperDensity N (cap N) I old nu a b m J *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousUpperFactor ((old : ℝ) / (b : ℝ)) -
        selectedPrefixUpperSavingIntegral I old nu a b m J))
```

### actualHistoricalFourthSaving_eq

来源：`ImbalancedChen/FirstExitHistoricalLevels.lean`

```lean
theorem actualHistoricalFourthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (hlevel : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base Q3 Q4 N cap z
```

### actualHistoricalFifthSaving_eq

来源：`ImbalancedChen/FirstExitHistoricalLevels.lean`

```lean
theorem actualHistoricalFifthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (h34 : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix)
    (h45 : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q4 frontier.selectedPrefix ≤ Q5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z
```

### actualHistoricalThirdToFifthSaving_eq

来源：`ImbalancedChen/FirstExitHistoricalLevels.lean`

```lean
theorem actualHistoricalThirdToFifthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (h34 : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix)
    (h45 : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q4 frontier.selectedPrefix ≤ Q5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base Q3 Q4 N cap z +
        actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z
```

### actualSmallRoughRho_majorant

来源：`ImbalancedChen/ActualSmallRoughAttachment.lean`

```lean
theorem actualSmallRoughRho_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n.natAbs
```

### actualSmallRoughRho_abs_le_one

来源：`ImbalancedChen/ActualSmallRoughAttachment.lean`

```lean
theorem actualSmallRoughRho_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualSmallRoughRho retainOdd N cap w z L q| ≤ 1
```

### actualSmallRoughRho_ne_zero_factors

来源：`ImbalancedChen/ActualSmallRoughAttachment.lean`

```lean
theorem actualSmallRoughRho_ne_zero_factors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho retainOdd N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport retainOdd N cap w z,
        q = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient retainOdd N cap w z b ≠ 0
```

### exists_actualSmallRoughRho_density_le_full_reserve

来源：`ImbalancedChen/ActualFirstExitDensityProjection.lean`

```lean
theorem exists_actualSmallRoughRho_density_le_full_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainOdd : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                (actualSmallRoughRho retainOdd N cap w z L) ≤
              reciprocalTotientDensity (fixedRoughSupport retainOdd N cap 0 z)
                (fixedRoughCoefficient retainOdd N cap 0 z) +
                  eta * singularSeries N / Real.log (N : ℝ)
```

### sum_rho_mul_halfProductCongruenceMass_eq

来源：`ImbalancedChen/PhysicalUpperWeightBridge.lean`

```lean
theorem sum_rho_mul_halfProductCongruenceMass_eq
    (num den N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ q ∈ Q, rho q * halfProductCongruenceMass num den N T q) =
      ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum Q rho +
        physicalCoprimeCorrection num den N T Q rho +
        physicalDistributionError num den N T Q rho
```

### siftedHalfProductSource_card_le_same_rho_main_add_errors

来源：`ImbalancedChen/PhysicalUpperWeightBridge.lean`

```lean
theorem siftedHalfProductSource_card_le_same_rho_main_add_errors
    (num den N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum Q rho +
        physicalCoprimeCorrection num den N T Q rho +
        physicalDistributionError num den N T Q rho
```

### currentChenPairedPrimeSum_le_four_D12_add_error

来源：`ImbalancedChen/CurrentChenSummedBridge.lean`

```lean
theorem currentChenPairedPrimeSum_le_four_D12_add_error (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ))
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ)) :
    currentChenPairedPrimeSum N E ≤ 4 * (D12 N : ℝ) +
      246 * ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) + 4
```

### eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12

来源：`ImbalancedChen/CurrentChenSummedBridge.lean`

```lean
theorem eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      currentChenPairedPrimeSum N E - epsilon * singularNormalization N ≤
        4 * (D12 N : ℝ)
```

### tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers

来源：`ImbalancedChen/RealHalfProductMassSuppliers.lean`

```lean
theorem tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers
    {b κ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hκ : 0 < κ) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)))
      atTop (nhds (Real.log (1 / b)))
```

## 附录 B：固定来源

- [形式化 README](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/README.md)
- [Current manuscript map](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/docs/CURRENT_MANUSCRIPT_MAP.md)
- [External reuse audit](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/docs/EXTERNAL_REUSE.md)
- [条件式主入口](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/ImbalancedChen/CurrentMainTheorem.lean)
- [当前数值转移](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/ImbalancedChen/CurrentNumericalTransfer.lean)
- [手稿主体](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/paper/source/manuscript-body.tex)
- [采用的 v2 assembly](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/data/corpus-renewal-improvement-assembly-20261010.json)
- [29 项数值义务](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/ba6ec11d800eccc54406490631895e174de85766/verification/data/global-selected-numeric-completion-20261010-obligations.json)
- [现有核心 workflow](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/.github/workflows/lean.yml)
- [现有 VE workflow](https://github.com/UyNewNas/goldbach-formalization/blob/1a80c1bcce67886f699d097fc37fd245cd3620bf/.github/workflows/variable-envelope.yml)
- [固定 axiom-audit 调用脚本](https://github.com/leanprover/lean-action/blob/f061402b660e0c34644504b324e830f2991d4865/scripts/run_axiom_audit.sh)
