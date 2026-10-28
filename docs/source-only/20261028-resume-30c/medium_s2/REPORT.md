# medium_s2 第三批：同一 Gevrey ψ 的实际 S2 与原始 Shiu 返回

新增两份闭合源码，共 928 行、54 个定义/引理声明；第一、二批冻结文件未改。未运行 Lean、lake 或 checker，正式信用 0。`task_complete=false` 保留原完整 S2 子任务口径；本次指定的实际双端 ψ 对象、移动余数 Shiu 调用与 V/l 局部返回已写成源码，`local_step_complete=true`。

`Part3OriginalS2SameGevreyPacket.lean` 解决审阅者指出的真实对象差异：旧 `commonSmoothWeight` 没有被等同于 `paperPsi`。新增 `s2TermWithM` 显式接收 m 权；旧函数仅由 `s2TermWithM_old_specialization` 作其原有特例。`samePsiTerm_formula` 则逐字给出 **同一个**已构造 `paperPsi(q/Q1)` 与 `paperPsi(m/V)`，保留同 d、两份原 α 互素门、移动同余、复共轭及 φ(q*d*s)。新 m cutoff 的全部非零支持在既有有限 m carrier 内。

该文件重新证明实际双端 ψ 的有限 (F)，并给出 `samePsiPaperBlockPacket_eq_packet`，直接连接原 `paperBlockOuterCarrier`。`samePsiFullBlockPacket_eq_kept_add_tail` 保留 kept 与三个交叉/尾项，证明被估计的包确为实际 full-minus-kept S2。自由 n2 的同一系数质量及第二批实际 H 几何均复用。

新的非零乘积 carrier 按真实 m 权过滤，因而 `psiMNImage_physical_interval` 证明 `x/2≤v≤5x`，其中 `x=U*V`。这一限制是后续 Shiu 的真实对象前提；没有对包含任意小 m 的旧完整 Cartesian image 直接套用长区间 Shiu。

`Part3OriginalS2SameGevreyShiuWindows.lean` 为原有 signed `a` 构造 `b=(a mod l).toNat`，证明 Int/Nat ModEq 等价及 `Coprime(l,b)`。非零实际包的 reduced-residue licence 从真实 γ2、γ3 支持和 primitive q 导出，不要求整个含零系数的 image carrier 都满足互素性。

令 `K=floor(x/2)`。四个具体窗口 `[2^j K,2^(j+1)K)`、`j=0,1,2,3` 覆盖全部非零 Gevrey 乘积。`psiDivisorProgression_le_originalShiu` 对这些实际窗口调用已有 **原始** `PrimitiveShiuTauBoundary 1 α κ` 的 `X,H,q,b` 定理；H=X 的原始短区间门、阈值、模数门、移动 reduced b 均逐项核对。该 boundary 是先前原稿准确引用的 primitive 接口，而不是新造的 S2/progression 结论。

随后复用已有 `uniformEulerConstant_bound`（钉住外部 Mertens 第二定理）和 `totient_ratio_le_divisor_count`，将四窗口的原 Shiu 右侧支付为

`Tψ(l,a) ≤ (15/2)*A*D_euler*(x/l)*τ(l)*log(8x)`。

与第二批 H 合成，得到 `samePsiPacket_le_V_over_l` 的显式返回：

`‖Aψ_(l,D,R)‖ ≤ 90*A*D_euler * (M*N²/(Y*l)) * τ(l)^5 * L(P) * (1+log(4Q2Q3))^4 * log(8x)`，

其中 `N=U`、`M=V`、`Y=Q1*D`、`P=floor(8Q1Q2Q3)`、`L(P)=1+log(max(1,P))`。自由 n2 对应的 N 因子完整保留。

最后 `physical_modulus_shiu_margin` 取 `α=1/10`，从 `l≤x^(4/5)`、`x>3^9` 推出所有窗口的原始 Shiu 模数门。`samePsiPacket_physical_modulus_return` 再取 `κ=1/10`、`x≥3X0`，给所有 `1≤l≤floor(x^(4/5))` 的统一返回；同一 primitive 常数先于 atom、signed residue、l。该公开定理将 smooth-tail 参数本身固定为实际 `d.scale`，没有留下另一个无关 x。

仍须推进完整 S2：新双端 ψ 的非零 smooth-tail collapsed-filter 字典、全实际 dyadic 块家族及 mixed-block 覆盖、统一对数余量与原 (8) 的 collapsed-tail 最终支付；以及正 principal/Poisson 整体合成。经典 primitive 的基础证明按用户边界递延。没有发现具体原稿数学错误；旧 m cutoff 对象不一致是实现接口缺口，本批通过实际新对象处理。所有结论仍仅源码，未声称内核验收。
