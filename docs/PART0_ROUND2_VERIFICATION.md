# Part 0 第二轮：分批验证回执

本页首批接收 **7 个生产模块**：P5 Buchstab、P2 检查器与采用证书的实际首格五模块，以及 P0 的首格 Buchstab 桥。它们合计 **189 个 defining-module 声明**，均有严格编译、对应生产对象的原版内核重放，以及包括私有和生成声明在内的完整公理审计。

这不是完整 Chen 定理的验证完成声明。实际 K 密度、完整 c / Chen 均值、`hLower` 和 `hUpper` 仍须真实供应者；原有条件式最终桥保留原样。本轮没有把这些输入藏进新结构或类型类。

## 固定来源

| 来源 | 完整 SHA | 本轮使用范围 |
|---|---|---|
| 共同证明基线 | `1a80c1bcce67886f699d097fc37fd245cd3620bf` | `codex/variable-envelope-boxes`，不是初始化 master |
| P0 首轮文档 | `9fe1d6b8b68a97cad3a122410ad7fde1701eed35` | 没有改变共同证明基线 |
| 手稿 | `ba6ec11d800eccc54406490631895e174de85766` | 定义、量词、常数和证书版本不变 |
| P2 | `b47a8d38ac1d2bcbd9c191df1c0c4da76700af3e` | 原始源码实际读取；本批最小修复见补丁 |
| P3 首轮 → 更新 | `64598da177adf861df3763d7c465ff941388b6d6` → `7d70a2545fd819706e473eb41e4d430ad19119d8` | 后者新增 rough auxiliary SW 两模块，并修正 PrimeAP 的一行证明；尚未整体核验 |
| P4 首轮 → 更新 | `262f69822a386a9d44efc059bceba11049668d68` → `c942b4c51d9d0005f0bd566906a3f0c88eeb1dba` | 更新仅为文档；生产源码仍是首轮版本 |
| P5 首轮 → 更新 | `3b8ab5eb2041af1906ecdb108f5edd2dd61f19aa` → `db97d0fe03250f4d9a8aea34b23e9c20f67010b8` | 后者 Buchstab 源码与已核验修复版逐字相同 |
| P0 已发布 Buchstab 接收 | `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` | 已固定的首个证明组件；后续接收提交继续保留相同源码 |

P1 确有四个本地生产模块及持续构建。2026-10-12 04:43:19 UTC 的只读快照为依赖闭包 523/688 完成，四个新增生产目标尚无完成记录；本次远端读取尚未取得固定交付 SHA。未取得 SHA 不等于没有成果。另行口述的“继承前层选择的第五层积分仅过单模块编译”仍未找到对应真实源码，没有纳入当前基线或本批接收。

## 已核验生产文件与接收方

以下 `.lean` 文件均在 `ImbalancedChen/` 下；表中计数为声明数，不是仅公共 theorem 数。

| 文件 | 声明数 | 严格编译 | 原版内核重放 | 公理审计 | 接收 Part |
|---|---:|---|---|---|---|
| `CurrentChenBuchstabRefinement.lean` | 5 | PASS，P0 | PASS，复用 P5 同对象回执 | PASS，P5 | P2、P5、P0 |
| `Certificates/RationalLogCertificate.lean` | 47 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedFibreIntegral.lean` | 13 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedCertificateChecker.lean` | 58 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedV2Data.lean` | 18 | PASS | PASS | PASS | P2、P5、P0 |
| `Certificates/PairedV2.lean` | 46 | PASS | PASS | PASS | P2、P5、P0 |
| `CurrentPairedBuchstabBridge.lean` | 2 | PASS | PASS | PASS | P2、P5、P0 |

严格编译使用 `warningAsError=true`、官方 frontend `trustLevel=0`。每个生产对象的重放与源码绑定；新回执还记录直接导入对象前后哈希。审计允许的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`，并拒绝 owned unsafe 或 axiom 声明。

完整、未截断的编译器类型与三门回执在：

- `verification/parts/p5/round2/buchstab/`：5 个声明与 P5 的同对象复用记录。
- `verification/parts/p0/round2/buchstab/`：P0 最初诊断、修复与接收。
- `verification/parts/p0/round2/p2-first/`：182 个声明、五模块三门、所有真实失败诊断、修复和再生成检查。
- `verification/parts/p0/round2/paired-buchstab/`：2 个桥声明与独立三门。
- `verification/parts/p0/round2/context/`：固定来源、运行环境、P1/P3/P4 后续交接审查及历史 Actions 状态；这些上下文记录不是额外成功门。

## 关键编译器确认类型

下列以常规 Lean 记法转写完整实际类型；`compiler-types.json` 保存 `pp.all` 的原始输出，包括显式实例与宇宙参数，不以源码提取冒充编译器输出。

```lean
theorem ImbalancedChen.currentChen_buchstab_eleven_twentieths
    {s : ℝ} (hs : 7 / 3 ≤ s) :
    11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s

theorem ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound
    (c : ImbalancedChen.Certificates.PairedIntegralCertificate)
    (hc : c.check = true) :
    (c.lower : ℝ) ≤
      ImbalancedChen.Certificates.pairedLocalIntegral
        c.K c.a c.tl c.tr c.ul c.ur c.Z ∧
    ImbalancedChen.Certificates.pairedLocalIntegral
        c.K c.a c.tl c.tr c.ul c.ur c.Z ≤ (c.upper : ℝ)

theorem ImbalancedChen.Certificates.PairedV2.first_certificate_checked :
    ImbalancedChen.Certificates.PairedV2.firstCertificate.check = true

theorem ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤
      ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
    ImbalancedChen.Certificates.PairedV2.firstIntegral ≤
      (31704 / 1000000000000 : ℝ)

theorem ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_gain
    {t u z w : ℝ}
    (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2
```

首格是 same-mask-v2 的 row 0：E0、t-index 422、u-index 510。其真实积分为

\[
\frac{8452171/1250000}{80}
\int_{937361/4096000}^{1875373/8192000}
\int_{194217/1280000}^{388777/2560000}
\int_{417/5000}^{76088109/532480000}
\int_{417/5000}^{z}\frac{dw\,dz\,du\,dt}{tuz^2w}.
\]

这是独立的较弱有理包围，不是原始 Q160 紧区间，也不是全 17,572 行积分证书。点态 Buchstab 桥只使用坐标支持和已证明的解析界，没有假设新的 K/c 结论；`K/80` 已含 `1/20 × K/4`，不能再次乘入同一增益。

冻结 JSON 的 SHA256 为 `f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7`。修复后的 importer 对完整 17,572 行进行了相同哈希、mask、解码检查，并以 `--check-generated` 与已编译的 `PairedV2Data.lean` 逐字匹配。改动仅为三处结构字面量的合法布局；所有有理数、行值和 mask 保留。

## 真实诊断与修复边界

- Buchstab：保留首个 strict linter 诊断，将 `field_simp ... <;> ring` 分为顺序 tactic；未改定理。
- RationalLog：修正 strict sequence linter 和乘除表达式的规范形，使原实对数证明闭合。
- PairedFibreIntegral：修正导数 proof API、积分定理命名空间和 beta/ring 规范形；真实积分定义、界限和定理声明保留。
- PairedCertificateChecker：原分组 field 布局被 Lean 当成函数 binder，出现 `inferBinderTypeFailed upper`。改为每字段独立声明，保持原意的字段名、顺序和类型；另修两处加法次序证明。原版本尚不能 elaboration，未声称它已有可比较的编译后定义。
- PairedV2Data：首诊断为 42:54 `unexpected identifier; expected '}'`。仅修三处嵌套 record 布局，并同步生成器；原始数据逐值不变。
- PairedV2：原固定源码未修改即通过。

修复只在 P0 验证树及补丁中进行，没有更改其他 Part 的源分支。

## 未闭合输入与总体门槛

P1 须供应实际历史策略、许可/支持、采用实例及完整真实积分；P2 须完成全部实际数值证书；P3 的新的 finite rough-removal 推导仍保留同一家族 `k=1` small-modulus SW 输入，尚非实际全分布结论。P4-A 须证明同一实际 rho 的 K 密度，P4-B 须构造 hUpper，P5 须完成十一项真实均值、c 和 hLower。**P5 等待 P4-A，不必等待 P4-B。**

计数、实参数和归一化没有改变：先固定 `1/2 < b < 1`，使用 distinct additive prime count，ordered `r ≤ q` 并保留平方，不添 factor 2；计数/均值尺度为 `singularSeries N * N / log N ^ 2`，密度尺度为 `singularSeries N / log N`。

当前原装 `lean --version` 启动失败，原装 Lake/官方 Lean frontend API 和原装 `leanchecker` 的实际成功分别记录，未冒充原装 `lake build` 成功。完整公共根构建、公共根内核及全根传递公理审计尚未完成。两份旧最终入口源码、工具链和所有 dependency pins 与共同基线逐字不变。

正常锁定工具链 checkout 的逐批入口为：

```bash
bash verification/parts/p0/check_batch.sh buchstab
bash verification/parts/p0/check_batch.sh p2-first
bash verification/parts/p0/check_batch.sh paired-buchstab
```

每个入口显式构建新增目标，不借旧根 `lake build` 覆盖。它们不取代 `.github/workflows/lean.yml` 和 `verification/verify_variable_envelope_boxes.py` 规定的完整项目门槛。本环境没有把这些 shell 入口记为已端到端执行。

对 `30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb` 的 Actions 读取显示两个工作流均无已分配 runner、执行步骤为空。未盲目重跑；它们不提供 Lean 成败证据，也不能覆盖后来 SHA。
