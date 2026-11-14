# 外部 prime Weil 候选独立复核

日期：2026-11-15。复核者：s05。只读固定提交源码和已有 GitHub CI；未运行本地 Lean、Lake、LSP、证明 helper 或 fixture，未触发远端构建，未修改 author 源码。

## 结论

选择 LeanPool/lean-pool 固定提交 `5dd712603d49049c7a5198e5dd725f768c5a510b` 的 `KloostermanWeil.prime_bound` / `weil1948_bound` 作为**具有可靠固定提交上游构建与公理审计证据、可直接复用的外部 prime provider**。这比 s07 的“仅发现候选”结论更强，依据是本次独立展开的完整自定义 import 闭包、关键数学连接与 CI 源码/执行状态，而非项目自行标注的 verified。

本结论不等于本项目已经导入、编译、完成 half-support 或无条件 J。本项目 pinned Lean 4.33.0-rc1 / mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 与上游 Lean 4.35.0 / mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 不同。剩余工作是忠实适配这个现成定理及既有 T25/positive provider 链，不能重新假设 hWeil，也无须重新形式化 Weil 证明。

plby/lean-proofs 固定提交 `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` 的 3√p+1 版本数学源级接口合适，已展开到全部非 Mathlib 依赖，未见占位或隐藏 Weil 假设；但未取得该提交的构建/公理审计证据，故**保留 source-only 候选，不选入可靠 provider allowlist**。

## 精确读取与证据边界

从 s07 REPORT/SOURCE_INDEX 开始，独立通过 GitHub connector 逐文件读取固定 ref，没有依赖 s09 对正确性的判断：

- LeanPool：34 个 Lean 源、6719 行（按返回文本 split 换行计数）。所有自定义 import 都在这 34 个中，剩余边只到 Mathlib；Lake 声明 TauCeti 依赖，但目标闭包没有 TauCeti import。
- plby：37 个本仓 Lean 源、8496 行；其 FormalPantheon/Waring 外部闭包为 22 个 Lean 源、4284 行。所有自定义 import 均已解析到底，剩余边只到 Mathlib。并非只看 PrimeKloostermanBound 两个直接 imports。
- 对全部 93 个返回源逐行检索 sorry/admit/axiom/opaque/unsafe/extern/implemented_by/native_decide/run_tac/elab/macro/addDecl/ofReduceBool/ofReduceNat/set_option：均无命中。普通 decide 不是 native_decide。检索是辅助证据，不冒充内核证明或完整 token parser。
- 核心定义、定理完整前提及下文列出的数学关键证明体已读；若干只承担有限索引、有限和或外围 Fourier 工具的证明，采用完整依赖扫描和上游编译/公理审计作证，不声称人工逐 tactic 再证明全部 6719+12780 行。
- Mathlib 是各自 manifest 精确固定的标准库信任边界；没有重审整个 Mathlib。
- `SOURCE_INDEX.json` 精确记录 93 源的 Git blob SHA-1、固定提交 URL 和 imports，以及工具链、manifest、CI、审计器、补丁文件的 blob。
- 另独立用 Git blob 算法（"blob " + byte length + NUL + bytes）检验 s09 已缓存的 34 个 LeanPool 文件，**34/34 与本次 GitHub connector 返回的 blob 一致**，再计算实际字节 SHA-256。结果在 `LEANPOOL_VERIFIED_CACHE_HASHES.json`。这是字节鉴别，未调用任何证明程序。

## LeanPool 定义、类型与数学链

入口 [PrimeKloosterman.lean](https://github.com/LeanPool/lean-pool/blob/5dd712603d49049c7a5198e5dd725f768c5a510b/LeanPool/KloostermanWeil/Weil/PrimeKloosterman.lean) 的 blob 为 `1696de7913a2a5610b640eaf9efdfff2806b54d6`，精确 UTF-8 字节 SHA-256 为 `183966c5dc8382c3ea2d52749295dd6d91d718f6204c3317172bd805b6c7b2e7`。

实际展开：

`∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), a ≠ 0 → b ≠ 0 → ‖kloostermanSumPrime p a b‖ ≤ 2 * Real.sqrt p`。

其中 `kloostermanSumPrime p a b` 是全 ZMod p 的有限和，在 x=0 项赋 0，其余项为 `ZMod.stdAddChar (b*x + a*x⁻¹)`。conventional-order 的 `weilKloostermanPrime p m n` 为 `stdAddChar(m*x+n*x⁻¹)`，两者交换参数是 rfl。不是截断/归一化/替代和，亦非预设一个已满足 Weil 界的抽象对象。p.Prime 的 Fact 已足以保证 p>1、非零与有限域结构，没有无法满足的 typeclass 前提。

`PrimeWeilBridge` 的 one-parameter/full equivalence 只用非零参数的变量缩放；标准式 S(m,n;p)=S(1,mn;p) 由 y=m*x 的真实有限和双射证明。两个非零系数条件保留到终点。p=2 由 PrimeWeil 的两项有限和及基本范数界单独处理，不把 odd p 假设遗留给全部素数结论。

关键链检查如下：

1. **扩域和忠实性。** ExtensionDefinitions 定义 Kext 为真实 GaloisField p n 上 x≠0 的 `ψ(x+t/x)`，ψ 为 stdAddChar 与 Algebra.trace 的复合。degree-one algebra equivalence 和 trace_self 把 Kext(p,1,t) 精确连到原和。
2. **Carlitz 生成式。** etaPoly(F)=ψ(−nextCoeff(F)−t F₁/F₀)，F₀=0 时权重 0。monic 因子的乘法性、系数向量与 monic 多项式的双射、normalizedFactors 的互逆均是真实构造。trace/minpoly reciprocal coefficient 公式将扩域值变成 eta(minpoly) 的相对次数幂；conjugacy class 的大小等于 separable minpoly degree，相关不可约多项式的 degree|n 条件由有限域嵌入付清。NewtonIndex/ NewtonSum 给出 n A_n 的带次数因子卷积。A₀=1，A₁=K₁，非零 t 下 A₂=p，n≥3 时平移最高低阶系数给出非平凡字符消去，因此 L=1+K₁X+pX²。由实际生成式推出三项 recurrence、K₂ 初值、α+β=−K₁、αβ=p 和 K_n=−(αⁿ+βⁿ)；未把 recurrence/roots 作为外部假设。
3. **Stepanov 曲线。** 真实曲线 y²=(xᵖ−x)²−4c。odd p、c≠0 给出常数项非零、导数 −1 的分离性与非 scalar-square。辅助式 f^l Σ_j(r_j+s_j f^((q−1)/2))X^(jq)，系数空间维数 2Jd。Hasse 条件方程数 Σ_{k<l}(d+k(deg f−1)+J)，严格小于变量数后由核维数构造非零系数族。非零辅助多项式由首个非零 q-block、Frobenius 模 X^q、度数限制与 nonsquare 矛盾证明；没有把“非零系数 ⇒ 非零多项式”当成公理。所有被计数点的 l 重根条件与辅助式度数上界相结合。
4. **参数和常数。** l=⌊√q⌋+1，d=ceil((q−deg f)/2)，J=floor((l+1)/2)+10(deg f+1)，高域条件 100(deg f+1)(⌊√q⌋+1)<q 支付维数与非零条件。正/负二次字符两侧共同给出 |#curve−q|<80(2p+1)(⌊√q⌋+1)+1。p 固定、扩域次数增长时条件最终成立。
5. **点数与谱。** Artin–Schreier fiber 是 trace=0 的 p 点 fiber，结合实际二次曲线到单位变量的双射，得到 #curve−pⁿ=−1+Σ_{m≠0}Kext(p,n,m²c)。ScalarExtensionSum 的 m²c 通过 u↦mu 的双射精确产生，并非误用 mc。
6. **从整体幂和到每个根。** 对全部 m≠0 及 α/β 组成有限家族，归一化 z=root²/p；在扩域 2n 上其幂和最终 ≤160(2p+1)+2。PowerSumSpectral 用 Newton identities 控制每一 powered-family 的 elementary symmetric functions，再用 Cauchy root bound 和幂增长得到每个 |z|≤1；允许重复根，不是假设根项无抵消。取 m=1 得目标两个根范数≤√p，乘积 p 再给等号，三角不等式得2√p。

这一证明并不靠论文“Carlitz/Harcos”名字授权。上游注释称生成式尚未逐式与原论文核对；本审计核的是字面生成式、trace/phase、curve bridge 和目标和的相等关系，这些在源码内有证明。它不能被误记作已完成历史文本逐式校勘，但不构成当前字面定理的缺失假设。

## 固定提交 CI 与公理信任

[push CI 43614826053](https://github.com/LeanPool/lean-pool/actions/runs/43614826053) 与 [merge_group CI 43612258371](https://github.com/LeanPool/lean-pool/actions/runs/43612258371) 的 head_sha 均为上述精确提交，completed/success。

独立读取实际 jobs：push 的 Build pool job 132507667422、merge_group 的 132499788764 均成功，Build project、Repository quality checks、Lint、索引检查均实际成功，不能只把最后的绿 gate 当构建。默认 PR-only workflow wrapper 返回空记录的现象已用 Actions head_sha API 纠正。

固定提交 `lean_action_ci.yml` 的实际 single build job：

- checkout 默认该 workflow ref；执行 `lake build LeanPool`，shell set -euo pipefail；构建 warning 亦导致失败。
- `lake exe mk_all --module --check` 配合 quality 的索引/可达性检查，避免入口落在未构建文件。
- quality 未传 --skip-lean-axioms。compiled `collectAxioms` 遍历每个 owned module 的公开声明，含 private dependency bodies，仅允许 propext、Quot.sound、Classical.choice；输出完整标记、模块列表、声明计数不一致即失败。
- 另一个编译环境审计检查全部 pool declarations 的 axiom kind、sorryAx、ofReduceBool/ofReduceNat、trustCompiler 等注入常量。unsafe 生成伴随声明从 axiom roots 略过，不是允许 unsafe 进入普通安全证明。
- validation cache 可以复用已通过审计；receipt 指纹包括模块清单、compiler import inventory 找到的传递本地源、toolchain、manifest、lakefile、checker 和 plugin 源。inventory 失败时保守 hash 全本地源。故不能声称每次 CI 都重新产生每条公理输出，但本次成功对应内容固定的验证路径。
- 我未下载 build artifacts、oleans、原始逐声明审计日志，也未独立重跑内核。远端成功状态与固定 audit 实现给出可靠上游验证证据，而不是本地编译证书。
- Lake 的唯一 compiler plugin LeanPoolLinters.lean 只注册 proof-line-count linter；已读其完整实现，无 addDecl/axiom 注入。

## plby 的完整边界与不同结论

其工具链为 Lean4.33.0，mathlib manifest 为 `db584cd6d46c92f209a44c0f1c829460d327499d`，不是本地 rc1 pin。Waring 来自 FormalPantheon `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1` 的 Warning 子目录。lakefile 的 post_update 调用 git apply 兼容补丁，这是构建时外部操作而非 proof theorem；本审计没有执行它。

目标 theorem 的真实前提为 [NeZero p] [Fact p.Prime]、2<p、a≠0、b≠0。Kloosterman.sum 展开为 unit 指示函数乘 stdAddChar 的 Fourier sum，再字面展开为所有单位 x 的 ψ(ax+b/x)。Möbius 变量 x=t/(t+1) 对应 t≠0,−1 与 x≠0,1；ψ(a+b) 为单位范数常数，漏掉 x=1 成本1。双简单极点系数为 coeff(0)=b，coeff(−1)=−a；支持集大小2，2<p 付清 s<p 条件，得到 (2s−1)√p+1=3√p+1。

下层 RationalRootRadius 的 HasEvenExtensionSquareRootBound 看似 conditional，但实际由 RationalStepanovExtensionSum.hasEvenExtensionSquareRootBound 构造：每个足够大 even extension 的 fiber 上界来自辅助多项式的非零、Hasse重数与度数估计。非零用指定简单极点处 mixed-radix local-order injectivity，不靠“系数非零”直接跳过；参数 hp>1、s<p 在最终 two-pole 调用均支付。Artin polynomial 是真实 monic polynomial Euler weight 的有限和，超过2s的系数通过 derivative probe 平移正交消去，constant coefficient=1。有限 Euler/closed-point/trace identity 把真实扩域和连到 reciprocal-root 幂和；Waring.BoundedPowerSums 用 Vandermonde（重复根先按正重数合并）导出半径，不预设 Weil 界。未发现隐藏 hWeil 或未支付 hbound。

完整 import 闭包还经 CompositeKloostermanCompletion→FourierCoefficientSum→ChenTwo 拉入外围 fifth-power 工具；不能只审 rational 主链。共37+22源，无敏感 token 命中。兼容补丁中实际命中这22源的只有 ChenThree、ChenTwo、FivePrimePower、FourierCoefficientSum、NonfivePrimePower、PrimeGauss 六个文件；逐块读取，变化为 letI/haveI 写法、simp 显式列表、名字限定、移除可由 classical 支付的 DecidableEq 参数并补 classical，未加入假设/公理或改写 Kloosterman 定义。

该固定 SHA 的 Actions head_sha 查询 total_count=0，combined statuses 为空；只支持“本次没有取得 CI 证据”，不能推断从来没有其他系统构建。本审计没有完整人工重跑每个外围 proof 的 elaboration。故即使数学连接可解释，仍不把它升级为已经内核确认的可靠 provider，也不选择它覆盖证据更强的 LeanPool。

## 对 T25 / half-support 的独立数学适用性

这是独立的纸面接口核算，不把 s09 的结论当证据，也不替代将来的本地适配 AL。

固定整数 m≠0，CRT 后每个 good prime 的两个系数仍是同一个非零单位 twist×m。用 LeanPool 的字面全非退化 prime theorem，得到 diagonal H(p)≤2√p。无需一般不同系数 gcd 版，也无需 sharp prime-power Weil：p∤m 时 k=1 用2√p；k≥2仍可用旧的平凡 p^k；p|m 是有限坏素数，沿用 p^k 的局部 majorant。

对0<δ<1/2，good-prime一次项为2 p^(−3/2+δ)，可求和；高次项 Σ_{k≥2}p^(−k(1−δ))≪δ p^(−2+2δ)，也可求和；坏素数有限且各局部几何级数收敛。于是既有非负 Euler-product/majorant 架构确实应将 T25 的 δ<1/4 提升到 δ<1/2。不能误写成 endpoint δ=1/2，也不能把 m=0 包含进去。

对固定正 exceptional τ>1/2，选 max(0,1−τ)<δ<1/2，则 1−δ<τ。T25 几何 O(Y^(1−δ)) 配合已付完整 singleton regular/principal/incoming/hol 成本，及有限 exceptional-family 正下界，可像已审 positive6 一样迫使实际正 infinity 的 rhoK=0。全量词需要保留 q、固定非零 Fourier m、该有限 family 的 test 下界常数，随后才能组成 hHalf/provider。

这个结论只消去相应 cusp coefficient，不推出 globalSelberg eigenvalue gap；也不自动产生 Kim–Sarnak 7/32。最终 unconditionalJ 的账户仍须等本项目的 faithful adapter、T25半阶版、实际 positive-half provider 与 conditionalcritical5 接线逐项冻结/复核。当前 AL 明确 fullJ=false、globalSelbergGap=false、localHalfSupportClosed=false、本地 formal credit=0。

