# 六个 external-Weil 桥接证明独立复核

日期 2026-11-15；s05。状态：**SOURCE_MATHEMATICS_PASS / UNCOMPILED**。本次完整读取六个新 Lean 证明体及所调用的关键定义/前提，未重证已签的上游 Weil、fullregular12/cubic6、positive6 和 conditionalcritical5，也未运行 Lean/Lake/LSP/helper/fixture。

对象：`output/resume-20261115/s09/half-support-next/external-weil/FREEZE.json`，SHA-256 `2341187fc31db5f1ad1925b956b22ba3ab44dc0db6047fd21d3c92b50d5a937e`。实测 53/53 冻结文件 bytes/hash 相符，LOCAL_READSET 的 13/13 旧依赖相符。六体的 sorry/admit/axiom/opaque/unsafe/native_decide 检索无命中。所选上游 provider 及34源精确哈希由本目录 ALLOWLIST.json 单独签认。

结论：六体的数学源级推导通顺，真实 physical sum→prime Weil→半阶 Euler price→真实 singleton trace→正 infinity rhoK 半阶支持→原范围 J 的链条不再把 hHalf/hWeil/hJ 作为 theorem 参数。**这是可供后续固定环境验收的源码结论，不是本项目已被内核接受的无条件 J 完成证书。** 上游 4.35 CI 不验证本地4.33.0-rc1适配；formal credit=0、fullJ=false、globalSelbergGap=false。

## 手稿范围先核

重新只读原固定手稿 commit `9731290e8f53cffda44129906cde6a965eaa869b` 的 `paper/source/modules/distribution-medium-completion-20261010.txt` §10(iii)、(v)–(vii)。它明确列 complete Kloosterman Weil，并要求同一 positive m interval、同一 additive phase 跨 levels，权重采用 R(n)=sqrt(|n|)rho_ABL(n)，J 的范围 X≪max(M,Z²/M)，大小为 (ZM)^ε(Z+M)M。新源码没有用 arbitrary moving interval、任意 level-dependent phase 或 globalSelberg 替换它。

六桥接接入的是已审 conditionalcritical5 的原量词和常数：ε>0、固定A≥0之后存在C>0，随后所有S、j、Q、X、ω；Q>0、X>0、S⊆classicalLevels Q、X≤A max(M,Q²/M)。最终 RHS 为 C((1+Q)(1+M))^ε(Q+M)M，小参数时的1+项与已审范围一致。底层 critical 仍含同一任意合法[a,b)及所有prefix，故没有通过本次替换缩窄已审 common-partial-interval能力；最终 named endpoint 用的是其 full_window 实例。

手稿的 Kim–Sarnak7/32是独立输入，不能从本次τ>1/2的系数消零得到。此前手稿中省略 prime Weil 的形式化供给现在有可靠现成上游定理，属于可接入的已建立输入；本次没有发现新增实质数学缺口。剩余是实际源码接入与内核验收，不把这种状态歪写成新的数学假设。

## 1. Part3FixedMarkPrimeWeilBridge

- L18 physical_eq_prime 使用旧 `Physical.kloosterman_eq_zmod`，该旧定理把 literal range-c、Coprime gate、positive Fourier phase 精确转成 `Σ_x if IsUnit x then stdAddChar(m*x+n*x⁻¹) else0`。在 prime field，IsUnit x iff x≠0，因此与上游 `kloostermanSumPrime p n m` 逐项相等。反系数顺序正确，没有共轭、负号、p因子或删除单位 gate。
- L30 conventional-order equality 直接用上游已证参数交换等式。
- L38 prime_physical_sqrt 仅假设 p.Prime 与 p∤m；n为任意整数。若 n≡0 modp，调用的真实 `kloostermanSumPrime_zero_left` 给−1，范数1≤2√p；没有漏掉 n=0 或 n非零但p|n。若 n modp≠0，则两个 nonzero hypotheses 明确供给 prime_bound。
- p=2在上游已经单独付清；本桥接不添加odd假设。sqrt_eq_rpow 后与majorant的p^(1/2)一致。m=0时p∤m不成立，不能误用；后面sum要求m≠0。

## 2. Part3FixedMarkHalfEulerMajorant

localCost仅改 good-prime、k=1 为2p^(1/2)，其他情况仍为p^k。k=0得到1，因此factorization.prod在指数0和modulus1处一致。prime-power公式不需要k>0；physical归纳的prime_pow分支有k>0，拆k=1时使用新prime bound，其余用实际norm≤p^k。

CRT分支先取得gcdB/gcdA在q/r上的单位性，再用旧真实CRT式。之后准确使用 S(m*u,n)=S(m,n*u) 把第一个固定mark恢复成m；第二参数可任意变化。这里不是错误地假设majorant(mu)=majorant(m)，也没有改变m的坏素数集合。physical_le_majorant对所有整数n成立，故递归所生第二参数一律覆盖。

d=0时literal range0和为0，majorant(0)=空积1，物理上界成立；price显式把d=0设成0。d=1时物理范数≤1且majorant=price=1。不能把 modulus0 与第二Fourier参数n=0混为一事：两者均被单独处理。

price_prime分别为 bad p 的p^(−1+δ)、good p的2p^(−3/2+δ)。price_higher对k+2≥2全部为(p^(−1+δ))^(k+2)，没有要求高次prime-power Weil。所有 multiplicativity、非负性证明与旧T25 body相比保持原结构，新增CRT/unit-scaling imports明确列出，不靠删除PrimeMoment后碰巧的传递import。

## 3. Part3FixedMarkHalfEulerSummability

全文对旧T25版本的逐项diff：除了import/namespace，数学修改只在一次素数price −5/4+δ→−3/2+δ，以及许可δ<1/4→δ<1/2。每个改动后的不等式都重新核算：

- r_p=p^(−1+δ)，δ<1/2⇒指数<0，prime p≥2给0≤r_p<1。
- bad(m,δ,p)在p|m时才非零；m≠0使这些自然数p位于range(|m|+1)。该论证对正、负m都用natAbs，不错误地声称“所有坏模数仅素数有限”而忘记函数定义在全部ℕ上。
- good一次项指数−3/2+δ<−1，higher-tail指数2(−1+δ)<−1。两项都是ℕ上的rpow可求和，因此在素数上当然足够。δ无需额外>0，代码允许更负的δ也正确；δ=1/2不在声明内。
- 高次tail=r_p²/(1−r_p)≤r_p²/(1−r_2)，分母严格正，反函数单调方向正确。local_sum显式分k=0、1和k≥2，首项price1=1。
- 全局不是未经验证的无限Euler乘积换序：先对finite smooth-number集合用现成有限prime Euler定理，再支配每个finite sum_{d<N}，用Π(1+env_p)≤expΣenv_p给统一界，非负级数于是可求和。d=0 indicator分支及price0另行支付。
- physical_twisted_summable允许每个d独立的unit u(d)和任意n(d)，但固定m≠0，并在d=0赋0，直接由同一非负majorant支配；无Petersson supplier、regularization或hWeil假设。

## 4. Part3OriginalHalfMarkTraceGrowth

全文与已审positive6 FixedMarkTraceGrowth比较，除了namespace/import与δ<1/2许可没有改证明结构。仍是真实same_infinity_cutoff_trace及其absolute summability，不是新定义一个满足界的spectral。

固定m>0和δ<1/2，v=1−δ>1/2，K=(8πm)^v Σ_{k≥1}price(m,δ,k)≥0。这个K只依赖m、δ，在∀q、∀Y>0之前选定。q∤k的term为0；cutoff非零迫使Y·4πm/k≥1/2，即k≤8πmY。|cutoff|≤1，majorant/k=k^v price，v≥0允许以(8πmY)^v支配。最后对绝对可和trace逐项求和，得到真实‖spectral‖≤K Y^(1−δ)。没有假设Y≥1，也没有q依赖常数偷偷出现在K中。

## 5. Part3OriginalPositiveHalfSupport

L26–64完整证明按真实q、正m、exceptional index i固定。令s=τ_i>1/2、v=(s+1/2)/2，则1/2<v<s；δ=1−v<1/2，正好可调用新geometry。常数可依赖此固定坐标和v，所有这些均在Y→∞前确定；pointwise得到每个坐标为0已足以形成后续∀q,m,i的support命题，不需要不真实的uniform-in-m常数。

`open private others slot_floor from ...PositiveMarkOrder` 精确绑定已审positive6源 SHA `f45f55ec791bce7ac1094c0196dd8bd0214465bb738ca23f34a2ecf792d489a8`：

- others通过完整regular_dyad与hol_price，将真正principal、incoming和hol singleton范数和支付为D Y^v（Y≥1）；low-order成本已在既有paid regular来源付清。它不只支付one-side主项。
- slot_floor取整个finite exceptional family的τ上限T<1后调用正test下界。得到一个c>0、Y₀≥1，对所有family成员同时成立，并通过其他项非负将目标坐标下界嵌入完整complement。没有只对被选单个τ取正性、却忽略其余项可能为负的漏洞。
- mark_split是spectral=complement+principal+incoming+hol。取实部，用−Re(z)≤|z|及以上两种支付，推出c·r·Y^s≤(A+D)Y^v。这里r=|basisR|²>0在非零反设下成立。
- 对正的Y^v消去乘因子得到(c r)Y^(s−v)≤A+D；`mul_le_mul_iff_left₀`的实际pinned API是取消右乘正因子，沿用前次已核的方向。s−v>0，所以rpow_atTop产生严格矛盾。
- rho_zero使用真实basisR_eq_half_native并支付m≠0，除以2的零条件正确。
- L75的positive_half_support直接展开旧定义，量词精确为∀q m:ℕ+、∀i∈exceptional q、τ_i>1/2→实际infinity cusp1的basisRhoK(q,i,1,m)=0；无改常数、无τ≥1/2、无零/负Fourier marks或其他cusps的额外声称。

这消去实际目标Fourier坐标，不证明eigenvalue不存在，不等于globalSelberg。

## 6. Part3OriginalNativeJFromPrimeWeil

L14–21只组合已审conditionalcritical5的`original_range_of_half_support`与新`positive_half_support`。新theorem参数中没有hHalf、hWeil、hJ、native-gap或新typeclass字段；它把旧唯一的数学provider premise传入了一个明确的proof term。不是用旧conditional结论冒充无条件结论。

已审critical的D/T/U/V/P顺序、完整基底、所有Y初始估计、六子窗每窗PN/12与加性VN预算保持未改；不重新计成单个24窗预算。四mother Q,2Q,4Q,8Q仍按先前报告各自应用dyadic结果和自己的参数缩放。本次six-body只补provider，没有改变这些常数或原范围量词。最终任意A的max(1,A)^(3/4)传输来自原已审定理，允许使用稍松但固定的3/4幂，并不意味着又遗留τ>1/2支持假设。

## 许可与验收边界

53文件freeze**已经包含**upstream/LICENSE（11358 bytes），SHA-256 `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`。本次独立读取上游固定commit根LICENSE的Git blob `57bc88a15a0ee8266c259b2667e64608d3f7e292`，对本地license重算Git blob相同。34源作者/Apache-2.0头保留，复用记录有精确commit；本次无须要求author补license或改原freeze。此项为文件/出处核对，不是新的法律意见。

remaining acceptance只按已写REUSE_AND_ACCEPTANCE_PLAN执行：隔离候选保留项目pins，先实际导入上游entry再顺序检查6桥接，输出目标声明的真实types与transitive axioms。不得将上游4.35的oleans/CI当成本项目4.33rc1的验收。源码中module/public section语法、Mathlib APIs、private-name导入和项目的实际module search路径均尚无本地或项目pin的编译验证；本报告不据静态阅读捏造兼容性成功。若修改任何源来适配，应另冻新版本，原53文件freeze与本AL绑定不变。

本轮只写s05报告/AL，未修改53文件包、旧依赖或author源码。

