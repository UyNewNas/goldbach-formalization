# Part 2：采用证书、真实积分与验证交接

## 当前状态

**采用目录和可复现精确数据解码已经完成；新增 Lean 证明全部是未编译候选，尚不能计作完成积分认证。**

本交接所在提交只增加 Part 2 的文件，不改 `ImbalancedChen.lean`、公共定义、工具链、Lake 配置或依赖锁定文件。

- 分支：`chatgpt/chen-p2-certificates`。
- 形式化起点：`1a80c1bcce67886f699d097fc37fd245cd3620bf`。
- 冻结手稿：`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`，由原 `docs/CURRENT_MANUSCRIPT_MAP.md` 指定。
- Lean：`leanprover/lean4:v4.33.0-rc1`；Mathlib：`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`；goldbach：`09b97db5764ade1246bfb77206baa1b124760958`。
- 首次远端验证尝试：`195f19cfcedeaf7793ccce3f1d42d27fcfe4f815`。之后还补入目录、完整原始数据、有限和接口及 A 粗积分候选；首轮运行不能用于证明后来代码通过验证。

本地下载的是官方精确版本，11 个依赖 HEAD 都匹配锁定值。但官方 Lean 在处理编译参数前调用的程序路径读取失败，报 `error: failed to locate application`；运行环境拒绝其 `/proc/<getpid>/exe` 读取。没有修改或拦截工具链/内核。

首轮三个 GitHub Actions 工作流均在约 5 秒内失败，Part 2 job 没有执行步骤，日志下载返回 `BlobNotFound`。因此这不是一个可用于修正证明的 Lean 报错。当前插件未提供 annotation 正文，不能据此断言是账单、额度或其他具体原因。详见 `verification/part2/local-runtime-evidence.json`、`ci-attempt.json`，以及 [首次专用运行](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38193423556)。

## 一、准确目录与采用判断

完整目录是 [ADOPTED_EVIDENCE_CATALOG.md](ADOPTED_EVIDENCE_CATALOG.md)，机器可读版本是 [adopted-evidence-catalog.json](adopted-evidence-catalog.json)。其中逐项记录：

- A：4 个基项、22 个采用节省项的 `source.field`、精确有理数、符号、原始文件哈希、已取得的内容层级和缺失 witness。
- B：十一项根泛函、后续整体替换、两块 paired mask、同 mask 新增量、被替换损失和两份独立误差预算。
- 全部 29 项基线数值义务、106 个动作 / 430 轮 / 400 项表的语义缺口。
- 可取得的完整归档及其元数据；未下载的二进制 witness 不冒充已经读到。

采用依据是冻结手稿与后续 `corpus-renewal-improvement-assembly-20261010.json`。v2 生成器残留的 `adopted: false` 不是最后采用判断。反过来，文件名带 `final` 或字段名带 `verified` 也不是 Lean 积分认证。

必须保持的边界：17,572 格和 `7/3` 是 **B 下界**采用数据；`12/5` 同一增益已被替换；撤回分支 `1.9728` 不参与；A 的 full small tail 只替换一次，不能又扣成额外节省。

## 二、B：真实首行的完整证明链候选

### 原始数据与解码

原始证书已按原字节复制到：

`verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json`

- 原路径：冻结手稿仓库 `verification/data/corpus-renewal-paired-certificate-v2-20261010.json`。
- Git blob：`49499697cca96de5f7b779e95077874ce5f9d119`。
- SHA256：`f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。
- 原文件使用 CRLF；mask/row stream 则按各自协议使用 LF。两个哈希概念没有混同。

七列为：`group, t_index, u_index, exact_Z, discarded_floor_Q80, extra_lower_Q160, extra_upper_Q160`。末两列的分母是 `2^160`；丢弃的已保存正项 floor 先除 `2^80`，进入 Chen 单位时再除 4。

`verification/part2/import_paired_v2.py` 校验上述文件哈希，解码全部 17,572 行，检查 E0=6,091、E1=11,481、两 mask 无重叠、排序/stream 哈希、所有有理端点与 cutoff、227 个 crossing 零 floor、完整 Q80 丢弃和，并确定性生成 `PairedV2Data.lean`。可复现命令：

```bash
python3 verification/part2/import_paired_v2.py \
  verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json \
  --check-generated ImbalancedChen/Certificates/PairedV2Data.lean
```

这些检查是数据/算术验证；不是单独的真实积分证明。

### 实际单元

原始第 0 行是 E0，索引 `(422,510)`：

| 参数 | 精确值 |
|---|---|
| `K` | `8452171/1250000` |
| `a` | `417/5000` |
| `tl` | `937361/4096000` |
| `tr` | `1875373/8192000` |
| `ul` | `194217/1280000` |
| `ur` | `388777/2560000` |
| `Z` | `76088109/532480000` |

坐标顺序 `(t,u,z,w)`，真实纤维 `a<w<z<Z`，外层为相应 `(t,u)` 矩形。`Z=min(ul,3*(1-tr-ur)/13)`；整纤维须满足 `z<u` 和 `(1-t-u-z-w)/z≥7/3`。对应几何、非空和精确索引定理均写在 `PairedV2.lean`。

实际积分定义为

```lean
pairedLocalIntegral K a tl tr ul ur Z =
  (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
    ∫ z in a..Z, ∫ w in a..z, 1 / (t * u * z ^ 2 * w)
```

`K/80=K*(1/20)*(1/4)`；没有排列因子或额外因子 2。积分是 literal 四层 `intervalIntegral`，不是把 JSON 的数字定义为积分。

### 关键声明完整类型（源码类型，未由编译器打印验证）

以下名称均在 `ImbalancedChen.Certificates` 命名空间，或显式给出的子命名空间中。

```lean
theorem pairedLocalIntegral_eq
    (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr)
    (hul : 0 < ul) (hur : 0 < ur) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * Real.log (tr / tl) * Real.log (ur / ul) *
        (1 / a - (1 + Real.log (Z / a)) / Z)

theorem RationalLogCertificate.check_sound
    (c : RationalLogCertificate) (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
      Real.log (c.argument : ℝ) ≤ (c.upper : ℝ)

theorem PairedIntegralCertificate.check_sound
    (c : PairedIntegralCertificate) (hcheck : c.check = true) :
    (c.lower : ℝ) ≤
        pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ∧
      pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ≤
        (c.upper : ℝ)

theorem PairedV2.first_certificate_checked :
    PairedV2.firstCertificate.check = true

theorem PairedV2.firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤ PairedV2.firstIntegral ∧
      PairedV2.firstIntegral ≤ (31704 / 1000000000000 : ℝ)
```

完整类型中 `PairedV2.firstIntegral` 正是上表参数实例化的 `pairedLocalIntegral`；`firstIntegral_semantics` 将它展开到四层实际核。目标区间为 `[3.1703e-8,3.1704e-8]`。原始 Q160 两端点仅作为来源字段保存，本交接没有声称证明了那个更紧区间。

证明链为：真实反导及积分等式 → 复用 Mathlib 的奇次对数级数界及其原样余项 → 检查有理证书与必要非负条件 → 对实际首行应用正确性定理。被减去的 `log(Z/a)` 使用上界；外层两个对数使用下界，乘法前明确支付非负性。

### 全 mask 的后续最小输入

现有 `sum_check_sound` 可以从每行 `check=true` 推出真实积分有限和的有理上下界，但没有伪造这些检查的完成。

独立精确 Python 候选使用外层 1 项、内层 6 项级数、`10^15` 对数向外舍入、`10^20` 单元向外舍入，得到总下界

`55858378943374979/100000000000000000000 > 558583/1000000000`。

这是有用的下一阶段证书候选，**还不是该总积分的 Lean 下界**。应先证明 186 个 t 对数、191 个 u 对数和 9,202 个不同 Z 对数，再复用它们对 17,572 行分块检查；不能仅把该总和作为一个未经证明的输入。

进入实际下界计数还需 Part 5 的 Buchstab `11/20` 下界、已采用父 majorant 的限制、Y6/Y11 配对及 saved-floor 语义。若接收接口要求 `Fin 4 → ℝ` 上单个集合积分，还需 Fubini/区域字典；这里已经定义并计算的是手稿直接给出的迭代积分。

## 三、A：实际采用的粗双图积分候选

`AboveMuSecondCoarse.lean` 处理 A 的第 5 项 `above_mu_second_coarse_only`。采用字段是 `second-prefix-upper-fallback-independent-review-20261009.json:no_grid_coarse_lower`，精确值 `640339/15210735000`。2,048 格的更大 fine-grid 值没有采用。

冻结公式源为 `proof-library/source/second-prefix-upper-fallback-20261009.tex`，SHA256 `355954ab0d4d1d23ce6045a4baa2dee3b71f124a8550e8f1eae71fbcae70821d`。该原文与 `second-prefix-upper-fallback-independent-review-20261009.json` 都已按冻结原字节放入 `verification/part2/data/`；后者 SHA256 为 `6aa6886728dfa9ddb7bdaa97727067eb040bb592ba65fa7ddceda3a51a437c45`。

在 `0<u,v<1`、`k=-3,1` 上，令 `h=1/384`，

```text
x = (75+u)/384
y = (75+k*u*v)/384
Ro = (159-5*u-2*k*u*v)/768
Rn = (159-2*u-(2*k+3)*u*v)/768
```

实际图积分为 `6*abs(k)*h^3 * integral integral u^2*(1-v)/(x*y*Ro*Rn)`。候选证明覆盖全闭方块上的正分母、整图粗分母界、真实多项式分子积分 `1/6` 和积分单调性，得到完整源码类型：

```lean
theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower :
    (3 / 95000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral (-3)

theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower :
    (32 / 3042147 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral 1

theorem ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤
      ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

代码还识别实际 endpoint min 分支、旧/新 residual 和带指定 Jacobian 因子的逐点代数式。它计算的是采用文件明确给出的两图积分；逐点 pullback 等式不自动等于已完成所有换元/不交覆盖定理。若从物理域的单个积分接入，Part 1 还应支付该换元和区域对应；实际 first-exit 树的极限关系仍是独立接口。该项只是 A 的一个节省项，在 `E` 中带负号，不能据此声称全部 `K` 已认证。

## 四、完整误差总账的采用语义

A 保留 `E=4/Theta+I1+I3_compact+I3_full_small_tail-sum(G1,...,G22)`，然后付两份独立且相等的 reserve `u`。目录精确重算了 `K-E-2u>0`，但所有采用积分和两个实际误差界未全部接入 Lean，因此不能把这个有理正余量直接升级为计数上界。

B 当前增加的 gross 是 `558583/10^9`；被替换的旧损失支付为 `1186047/500000000`，新支付 `466977/200000000`。恢复支付 `37209/10^9`，所以

```text
Delta = 37237/62500000 = 0.000595792
each new reserve increment = Delta/8
net increment after both reserves = 3*Delta/4 = 111711/250000000
```

两份旧预算已包含先前采用的允许损失，不能另加旧 E0/E1 gross、12/5 版本或已经替换的 whole-box restoration。只用额外 gross/K 调整后续 K feedback；损失回收不能除 K 当成同一斜率。

完整 raw endpoint、两份预算、每个 `source.field` 和正 slack 都在机器目录中。它们已经通过 Fraction 精确复算，尚未变成对实际全量对象的形式化结论。

## 五、接收与验证

| 接收 Part | 本批交付 | 最小未完成输入 |
|---|---|---|
| Part 0 | 固定分支提交、独立 CI、完整目录、无公共变更 | 在可运行的精确工具链上编译、严格 elaboration、内核 replay、全声明 axiom audit；通过后才整合 |
| Part 1 | [接口契约](PART1_INTERFACE.md)、实际纤维与双图解析候选 | 契约尚未由另一会话确认；完整历史 joint-cell/策略字典、必要换元/Fubini，不能假设最终 gain |
| Part 4 | A 的完整采用目录、A5 粗双图积分候选 | 其余 A 积分数据和检查器、完整保留域覆盖、真实 signed upper ledger 与 reserve |
| Part 5 | B 全原始数据、首行真实积分候选、有限和 checker 接口 | 全 17,572 行 Lean checks、实际配对/父限制、saved floor 语义、全 lower ledger 与 reserve |

在可运行的锁定工具链中执行：

```bash
bash verification/part2/check.sh
```

脚本显式构建六个新模块，严格复核它们的源文件，调用官方 bundled `leanchecker` 逐模块 replay，并审计所有归属声明及其传递公理，只允许 `propext`、`Classical.choice`、`Quot.sound`。专用 GitHub Actions 另外保存来源哈希、固定 head、完整类型与失败日志。原 root workflow 的成功不会自动覆盖未导入 root 的这些模块。

目前实际通过的是来源/数据/有理总账/Python 和 workflow 语法等检查；源码 token 扫描未发现新增证明逃逸。静态 API 审阅也不能替代上述 Lean 验证。下一步首先解除真实编译阻塞，再扩展全 mask 与其余采用积分；此交接不把候选标成已认证。
