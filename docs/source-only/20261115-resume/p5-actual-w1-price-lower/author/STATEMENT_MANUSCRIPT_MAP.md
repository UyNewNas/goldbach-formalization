# W1 原价格的下比较：source-only 候选

本轮只补原 `thetaConversion` 的一个有限比较及其在原 `integerMass` 上的实例。上次连接中断没有留下 price 目录或 partial 文件。本目录为新目录，旧 freeze、旧源和主稿均未改。候选未经 Lean 编译，`ready_to_install=false`，formal credit 为零。

记 `li₀` 为 `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral`，`C` 为 `Wu2008DoubleSieve.wuSingularSeries`。新源两个声明为：

- `thetaConversion_lower`：对所有自然数 `N≥4`、`d>0`，`4 li₀(N) C(N)/N ≤ thetaConversion N d`。
- `integerMass_price_lower`：对同样的 `N,d`、任意原 `Q`、`i : Fin 7`、`j : Fin 10`，上述比较两边乘以同一个 `Part5OriginalH430W1PhysicalRoughDictionary.integerMass N Q d i j` 后仍成立。

这是原稿归一化中可补齐的省略，不是新的分布估计。没有价格不等式、PP、J、Δ、selector 成功、非空或正总质量假设。

## 字面定义与推导

`P2EnhancedSwitchedTrueNormalization.lean:98–101` 的定义是

\[
 v_{N,d}=\frac{4\,li_0(N)\,d\,C(dN)}{N\varphi(d)}.
\]

使用固定旧源已经证明的事实：

1. `Omega3XNormalization.wuSingularSeries_le_mul`（实际 namespace 为 `Wu2008DoubleSieve`，第 36–38 行）给 `C(N)≤C(dN)`，只需 `N,d>0`。不要求 `gcd(d,N)=1`，也不要求 N 偶。
2. `Normalization.wuSingularSeries_pos` 第 66–69 行给 `C(N)>0`；`Nat.totient_pos.mpr hd` 和 `Nat.totient_le d` 给 `0<φ(d)≤d`。
3. `BoxMassTheta.box_trueLi_lower` 第 31–40 行给 `N/(2 log N)≤li₀(N)`。`N≥4` 使左边非负，所以 `li₀(N)≥0`。

因而

\[
 C(N)\varphi(d)\le C(N)d\le C(dN)d,
 \qquad C(N)\le\frac{dC(dN)}{\varphi(d)}.
\]

乘以非负的 `4 li₀(N)/N` 就得到目标方向。`d=1` 时原公式精确退化成基准价格；证明不要求 `d>1`。第二个声明只用原粗数集合的基数非负，没有重新定义 carrier。

**li 名称不能互换。** 旧 normalization 文件的注释称 “true li”，但实际标识符是上述 `logarithmicIntegral`。已读 `P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add` 第 39–44 行明确给

\[
 \texttt{trueLogarithmicIntegral}(x)=li_0(x)+2/\log 2.
\]

本候选保留 `li₀`。将它直接替换为较大的 `trueLogarithmicIntegral` 会改变声称的下界，本轮没有这样做。

## 与原稿及实际调用逐项对应

| 项目 | 原文 / 旧实际源 | 本轮对应及边界 |
| --- | --- | --- |
| 奇素数 singular factor | `manuscript-body.tex:6–12`；`Normalization.lean:55–69` | `wuSingularSeries N` 是原 `C_N`，不是 `2 C_N`。 |
| 原 marked normalizer | `manuscript-body.tex:795–806` | `Theta_Q=4 li(N) Σ σ(B)C(BN)/(φ(B)log(Q/B))`。新源只比较由此抽出的原局部转换价，不替换权或求和族。 |
| 转换等式 | `P2EnhancedSwitchedTrueNormalization.lean:92–112` | `rawMainAtom_to_thetaAtom` 已经给实际 `trueAlpha`、原 `Q` 下的恒等式；本轮不重证。 |
| 实际 W1 unsifted 质量 | `Part5OriginalH430W1PhysicalRoughDictionary.lean:16–19` | `orderedTriples (primeWindow (d*N) (cutoff Q d (W1Anchor j)) (cutoff Q d (W1Target i)))` 上求原 `roughNumbers (N/(d*a1*a2*a3)) a2` 的基数和；全部 unit、重复因子和原上端点均保留。 |
| 真实 d 的正性 | `Part5OriginalH430SeedHistoryMass.lean:24–38` | 对 `l : LevelIndex ...`，取 `d=wordProduct l`、`Q=rootQ ...`；`scale_and_alpha` 第一分量已给 `0<d`。不是新增 W1 许可条件。 |
| 原共同阈值 | `Part5OriginalH430W1TrueConvertedBase.lean:89–94` | `all70_rough_bound` 的已有 `T≥4` 与 `N≥T` 给 `N≥4`。新比较对全部 `d,Q,i,j` 同时成立；没有依标签选新阈值。 |
| 价格出现位置 | `Part5OriginalH430BankAfterW1PrimeRestriction.lean:64–66` | 原 `cleanDebt=(primeRestriction-currentK/4*(thetaConversion*integerMass))/2`。比较保留这个实际负项的正确方向；本轮没有给 `cleanDebt` 上界包装。 |
| α 与 Q 不变 | `manuscript-body.tex:808–817` | `alpha=log(N/d)/log(Q/d)` 不重设为 2；每个 RootKey 的原 `Q` 留在原质量中，未跨根识别 Q。 |
| 正乘积的较早步骤 | `manuscript-body.tex:529–558` | 原 `T≤X S_N+errors` 仍需要同一个 rho 的实际 majorant、density 和 PP。新比较没有供应这些。 |

## 去重与依赖状态

已检查 continuation 的现有 `ImbalancedChen`、已发表 h34 successor/seed 子目录，以及本次 resume 的 Lean 源中 `thetaConversion` 的 lower/le 使用；未找到这个精确 scalar 声明。此结论只针对已读本地可靠源，不声称穷尽远程未取文件。

`Omega3XNormalization` 已经证明 singular 因子单调性和另一 box-convolution 质量的下归一化；`P2EnhancedThetaReciprocalMass.mean_kernel_lower/Theta_lower` 给 universal-product 版本。本候选直接复用单调性，不复制这些通用证明，也不把 box family 改称原 W1 family。原 `all70_rough_bound` 是 `thetaConversion*integerMass` 的上界，不能反向当成本轮下界。

`DEPENDENCIES.json` 记录实际读过的 bytes、SHA、可复用旧身份记录及来源。`Omega3XNormalization` 为固定 `09b97db…` research 路径的真实源码，先前 PACKAGE_ADDITIONS 仅标作 transitive locator candidate。本轮已读其相关证明，但没有把它升级为编译通过、递归闭包闭合或可安装选本。沿用原 root/research 映射，未覆盖任何 T04 root pin。显式 imports 是三个既存模块；没有下载、包 pin 变更或本地安装。

## 精确剩余界与 HOLD

在先前 audit 的原记号中，若 `a_l=integerMass ...`、原位置权 `σ_l≥0`，`X=Σ_l σ_l a_l`、`M=Σ_l σ_l v_l a_l`，本轮有限比较支持 `4 li₀(N)C(N)X/N≤M`。这里只说明后续如何代入；没有新写聚合或 same-rho consumer。

因此原正 `K=currentK` 下，未付价格余量满足代数方向

\[
 XS_{\rho,N}-KM/4
 \le X\bigl(S_{\rho,N}-K\,li_0(N)C(N)/N\bigr).
\]

右侧没有在本轮变成小量。原稿第 507–512 行的 `S_{ρ,N}≤(K+o(1))C(N)/log N` 必须是 PP 使用的同一物理 rho，并须与 literal-li 的相应渐近及实际正族质量、共同阈值和误差尺度衔接。本轮只使用 li 非负性；粗界 `li₀≥N/(2 log N)` 本身不提供系数 1 的价格余项估计。这里区分的是：局部价格方向已可用旧引理补齐；same-rho density/PP 和它们在实际标签族上的统一供应仍是原未付分析输入。

不升级 signed Δ、relative Θ、full PP、h34、4.30/4.41。root receipt 仍为字面 `if old=[p] then originalReceiver else ∅`（receiver 可空），ordinary append 仍为整笔 rejectedChild。原 σ、E/Q/old、owner、全标签位置和继承过滤均未改变。

本轮验证仅为静态源码阅读、依赖身份比对、文件散列与 JSON 解析。没有运行 Lean/Lake/LSP、候选、helper、guard 或 fixture，没有 Git/GH 命令、下载、artifact 获取、quota 或再派任务。
