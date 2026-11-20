# P4 原 two-long expanded core 独立数学审查

结论：**AL，仅限冻结三源提供的 E4 子项 `M*y²*D^(3/2)` 的数学供给。** 已进一步核实它的几何前提可用于本稿真正的 no-medium 两母支，绝非只证明一个无实际参数可用的抽象不等式。**完整实际 no-medium、原母行到新核心的已写定理、E1/E3、端点、母积分及 H_N 恢复仍 HOLD；本包未编译，形式验收亦 HOLD。**

独审者 `/root/n21_p4_branch_review`，非作者。审查日期 2026-11-21。只读源码、JSON、哈希及词法声明；未运行 Lean/Lake/LSP/native kernel、项目 helper/fixture/stage/setup/guard，未做 Git/GitHub/CI/artifact/额度操作，未改作者文件或旧 freeze。

## 1. 冻结与签名核验

审查对象固定为 `output/resume-20261120/n07-p4-actual-upper/no-medium-branch/FREEZE.json`，74265 字节，SHA256 `1079149a3caaee7da9ce7fb5980d5dbafc569e889991a2d9ce306a2b9642abf5`。

7 个冻结包文件、原 SOURCE_RECEIPT 的 20 条来源、freeze 补充的 2 条 support 来源均逐项 bytes/hash 匹配；24 条公开声明的行号、声明至 `:=` 前缀及 UTF-8 哈希全部匹配。记录见 `VERIFICATION.json`。这不是 Lean AST、elaboration 或完整传递 import 选择证明。

三候选 SHA256：Weil `f94cf46ddd007696088098b86fabd77e43a3f69c8007babdb3fb897e0442e18f`；P2 `5ab54a8ebe7872b147a17615c9aa864104d2da578361d07676873d4a8628d876`；ExpandedCore `cc3606e5d3b4e7f40662b6d3f40583ec06c1d90eac80e506524877e5292011ce`。原 SOURCE_RECEIPT 为 `67dd3ba50a7d813ffa27368d52cedf616737c23580a73492945ab36bb53cc50a`。

## 2. 算术链的独立判断

| 核查点 | 裁定与依据 |
|---|---|
| 素数界与退化频率 | `SquarefreeWeil` 35–75 分别处理 p 同时整除两频、只整除首频、首频不被整除。双可除用平凡界保留 gcd=p；一零轴用 prime swap；另一频可为零。供应者 `prime_physical_sqrt` 38–51 无奇素数条件，p=2 包含。 |
| q=1 | `SquarefreeWeil` 113–115 保留；旧 `NaturalInternalP2.naturalCore_q1` 122–124 及 `P1AxisCancellation` 48–61 给原 discrepancy 精确为零。 |
| CRT | `CoprimeKloostermanCRT` 110–120、173–177 的两个 Bezout 局部单位同时扭转两频；新 77–83 连用两次 `primitive_center_gcd`，不是首频 fixed-mark 界。gcd 与 tau 在互素分解下乘法性正确。平方自由仅令 prime-power induction 的指数等于 1。 |
| 局部 P2 是否漏用 prime-power | 旧 `InternalP2Modes` 唯一直接调用 hWeil 是 61 行 `hWeil q hq (b*j) k`。新链逐层重证该 q 的 kernel/modes/tsum/naturalCore/profile 界。旧 P1 的 periodization、轴恒等式、频率除子包络及固定 N2 衰减不调用另一个模数的 Kloosterman Weil 界。无需建立全 CompositeWeilInput。 |
| 归一化与 mean | 新 P2 173–189 仍是原 `alpha*(UV/q²)` 乘完整整数双频和，以 `(q/U)(q/V)` 精确抵消；centered kernel 保留 `c_q(j)c_q(k)/phi(q)`，两轴由恒等式消失，不是删掉 Fourier 质量。非互素 `m` 分支 190–191 用原 AP 与 coprime mean 同为零。 |
| 原 Q 的平方自由性 | Q=`moduli N (N^omega)`；`Full87CompiledCounting.moduli`=`UpperTaggedBetaAttachment.support N N w (cutoff N)`。后者 157–165 从实际小/粗两支的 squarefree 及互素性证明原物理模数 squarefree。fallback rho 41–43 是同一附件构造；新 `actual_modulus_class` 不要求调用者另加 sf 前提。 |
| Brun 后模数 | `HBMellinBrunProfiles.mellinBrunCore` 101–117 与新 `brunCore` 80–86 一致：模数仍 v，目标 N，短积变 `short*d1*d2`，尺度变 `U/d1,V/d2`。`LiteralBrunSubstitution.pair_divisor_substitution` 110–148 是同一个算术核 K 的代换。未对 `v*d1*d2`、`c²*d` 或碰撞后放宽的 nonsquarefree 模数使用原 v 的 sf。 |
| 实际 signed 系数 | 新 rho 是完整 `FiniteSmoothCount.coefficient` 的复数嵌入。仅非零 rho 被限制到 D；零贡献的矩形外点未冒充 active 支撑。调用 `JointP2ModulusMoment.squarefree_p2_modulus_moment` 80–125 的通用定理，未调用 jointRho 专用结论。 |
| HB 短序列 | 使用既有 `shortSequence` 的有符号 ordered-fibre pushforward，碰撞值不合并坐标；单位与重复位置均保留。L1 只在完整 count-minus-exact-mean 成形后的误差估计中取，符合补篇 252–253、287–294；未把 signed beta mean 换成 abs-beta。 |
| 12/29 预算 | 新 189–194 独立证明 `(1+log x)^s ≤ 4096(log x)^12`，s≤12；没有调用旧 s≤6 的结论。模数 log16 + 角色 log12 = log28，常数 `8192*8^16` 由一次 log 吸收，得 29。 |

`905a...`、`763f...` 仍仅是选定的 Ramanujan 身份/展开来源，不是 Kloosterman Weil 供应。外部 prime theorem 的 34 模块闭包及 Lean API 仍需 ROOT 精确编译验收；本独审未扩大该证据。

## 3. 本稿实际参数确实能支付这个子项

原稿 `argument.tex` 196–199 与 `coefficient-appendix.tex` 621–629、811–817 明确是原 no-medium 小 M 路线。两个 small-beta 参数 `omega=nu*beta²`、`ell=nu*beta` 不是两长变量的长度指数，也不是完整模数上界 D 的指数。

实际同一族的供应为 Nov12 `P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity` 58–97：一次选定 beta、k，`nu*v=19/96`，`0<beta<1/8`、`beta²<v`、`omega<a`、`ell<1/1000`，并可同时满足 `ell<etaPP/32` 与 `ell<extraPPMargin/32`。其 93 行给**这个同一 rho**的非零完整模数 `d<N^(599/1000)`，不是仅小素数 cutoff 的界。

Nov12 `P4BOriginalHighRankLocalLevel` 18–22 定义 `theta=1199/2000`；44–75 对真正 live 两母 source，使用 `0<kappa≤zeta/10000`、`kap0<kappa/(4(1+kappa))` 及上述 hRange，得到 `N≤x^(1+kappa)` 和每个 active `d<x^theta`。它明确不要求 medium selector。取 `D=floor(x^theta)`，整数性给所有 active d≤D；x>1 给 D≥1、D≤x^theta。这样 hlevel 是已有物理范围的直接运输，不是新假设目标。

原两母坐标不是任意 rank 假设：`P4BUpperPairOrderedRowModes.rowBank` 210–219、`modeBank` 277–294 实际枚举 `j,l∈range 3`，坐标数为 `2(j+1)+2(l+1)≤12`。`pair_row_reindex` 182–208 与 `RowGeometry.sum_rectangle_append` 48–75 保留 Fin.append 的所有原 occurrence。两个不同 long 坐标删去后 ShortPositions 的基数≤10；不按素数值或块值去重。

`OriginalPrimeAtlasReserveBranches` 104–112、130–133 的真实 no-medium 测试是全部原坐标中不存在长度处于 `[X^(3*zeta),X^(1/3+zeta/4)]` 的槽，X=`R cj*R ck`。在一个真正 live 两母行上，每母原乘积大于 `N^(19/96)`（原 `normalized_support`），每母≤6槽；若某母全短，其乘积至多 `64 X^(18*zeta)`，与 ζ≤1/400 及 X≲N 矛盾。三条 long 的 lower 乘积则大于 `X^(1+3*zeta/4)`，与完整乘积 O(X) 矛盾。故充分大 N 时恰好两 long、每母一条。Mobius 截断≤固定常数·X^(1/3)，故 long 只能为 one/log；这是原稿 621–627 的同一推导，已有 `ActualTwoLongOrderedGeometry`/`ActualTwoLongLocalParameters` 为同一路线提供有限坐标证明体。

对**新候选真正的** `M=shortScale`，剩余≤10槽各 lower≤X^(3*zeta)，直接得到 `M≤X^(30*zeta)`。不要把旧 `ActualTwoLongLocalParameters` 的“短整数乘积 owner 尺度”与此 M 写成相等。`HighRankMotherScale.live_geometry` 51–87 给 X≤16x；因此

`M ≤ 16^(30*zeta) * x^(30*zeta) ≤ x^(40*zeta)`

最终第二步仅用 ζ>0，余下 10ζ 支付固定常数与 X→x 运输。各短块 `2 lower≤x` 最终成立；所有长 lower≤完整整数乘积≤4x，故可用固定 c=4。死行应在原有限 rowAtom 层凭源权重全零删除，再做 Fourier/三角估计；不能声称死行的 Fourier amplitude 必逐点为零。

**40ζ 只支付 M，没有吞掉 Brun y²。** 原 `Z=beforeHBCutoff K [cj,ck]`=`roughF(2^(6K+4)*X)`（`OriginalChartRoughCutoff` 17–22）。由 X≤16x、x≤4X，固定 K 的实参 t 满足 x≤t≤C_K x；充分大 x 时 `log t≤2 log x`、`loglog t≥loglog x`，直接得 `Z≤x^(2/(loglog x)^3)`。这同时说明不用把旧 owner 尺度的 cutoff 结论直接当作新 live x 的结论。原 `j=floor((loglog x)^2)` 满足 `2j+1≤3(loglog x)^2`。于是 `log y/log x≤6/loglog x`，其中 y=`Z^(2j+1)`。给定 ε>0，统一大阈值使 y≤x^ε。`OriginalOneLongExplicitBrunRates.support_is_subpower` 64–97 已给这一含系数 2 的算术；不能把真实 chart Z 擅换成较小的 roughZ(x)。

可以具体取 ε=1/16000。在 ζ≤1/400、theta=1199/2000 下，

`40*zeta + 3*theta/2 ≤ 3997/4000`，

`40*zeta + 2*epsilon + 3*theta/2 ≤ 1599/1600 < 1`。

所以 **M*y²*D^(3/2)≤x^(1−1/1600)**，含真实 Brun 双支撑与全部上述常数运输。固定 log29、profile 的固定 log 幂及以后需要的 log54 均可用更强局部 A 支付。这里说明可用的数值余量，不声称 log54 和母积分已经接好。真实频段若用 `(log N)^K`，由 N≤x^(1+kappa) 可最终送入 `(log x)^(K+1)`，仍是阈值前固定的指数。

## 4. 可补有限字典与真实未付数学分开记账

以下连接未由冻结三源输出完整 P4 theorem，但可由已经核读的具体等式完成，无需新的解析估计：

1. 原 no-medium 测试依赖 block 坐标，可随 `allGroup_actual_branch_split`、`normalizedAtlas_pair_eq_rowBank`/`pair_row_reindex` 传到两母 Fin.append 行；在取三角界前删除真正无源支撑的行。
2. 对选定两条 long，`RetainedRowReindex.rectangle_signed_pushforward` 112–156（参数 F 任意）把同一 `residueKernel v N` 保留在 short fibre 上。其 lowerQ 包装器不能直接当作 P4 等式，应只复用这个通用有限恒等式。
3. 对已形成的**平滑 Brun polynomial**行，`LiteralBrunSubstitution.smoothBrunTupleCore_eq_expansion` 214–221 逐 v 给新 `brunCore` 的真实内和。它对所有 m,N,q 量化；外乘原 rho 并有限交换短积/v 求和就得到新 `rowCore`。不需要、更不能假定原 rough 行已等于 upper polynomial。
4. hlevel、rank、M、D、U,V、短块上端及频率 gates 按第 3 节在原同一参数族实例化。完整公式不需要新 `hModes/hUniformPP/hE4`。

真正尚未支付、不能归类成单纯改名的部分：rough→upper/gap 的 E1 精确互素均值与 E3 的第二份 mean；原两个 individual interval 的端点误差；把这些误差与保留的 original normalized mother amplitude 积分及全部标量/截频/碰撞账合流。`H_N=C_N*N/(log N)^2` 从未出现在新局部核心结论中，不能因新结论为 x/log^A x 就直接记 hUpper。母行/整族完整恢复仍须真正写出并审查。

## 5. 结论边界

没有发现本窄算术链需要新的外部估计、无法满足的实际参数条件，或 signed mean/phase/物理 q 偷换。冻结候选可作为原两母 no-medium 的有用 E4 展开核心供应；原实际参数与几何已有正 power reserve，相关未接字典具备上述具体可补路线。

此 AL 不授予：一般合数/prime-power Weil、完整原分支、rough E4、H_N/hUpper、已完成母恢复、Lean 编译或 kernel 通过。若后续分析先丢弃原物理全局 squarefree 或换成 c²*d，必须重新处理相应模数；此次 AL 不覆盖。
