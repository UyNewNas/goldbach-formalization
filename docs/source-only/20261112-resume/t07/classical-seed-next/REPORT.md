# 经典 U3 种子中的 Γ9–21 长字

源码交付包括七个模块。原经典带、夹持带、$K=681/100$、$Q$、真 li、半开窗、重复颜色字和端点都沿用旧文件。源码尚待 Lean 编译及内核验证。Γ5 先前的独审为 `T07_GAMMA5_POOL_CREDIT_REVIEW.md`，其作用域是外层经典根。

## 已付的原计数

在经典带 $N^{57/224}\le p<N^{1/3}$，令 $d$ 为该 $p$ 的任意原始因果位置的旧字乘积，$R=Q/d$，$T=\log_N d$，$\nu=\log_N Q$。原请求从列表 `[p]` 开始。每条边只在列表右侧添加 `appendedWord`。保留、换格、W1/W2 固定读和一、二素数边都保持 $p\mid d$。冻结给出 $\nu\le 1/2-\tau$，所以

$$
 T+3(\nu-T)=3\nu-2T\le 3/2-2(57/224)=1-1/112.
$$

每个原位置都有 $R>1$、$R\ge N^{\mathrm{frozenResidualFloor}}$、$\alpha=\log(N/d)/\log R>3$ 和 $dR^3\le N^{1-1/112}$。任意含 $r$ 个新增素数的原字有 $\prod q_i\le R^{5r/11}$。因此，$m\le R^{3-5r/11}$ 的整个尾商都在小乘积区。三素数字的界为 $R^{18/11}$。全部 20 次出现的 $r\le6$，所以两个旧的五、六素数单位项也在此区。五个实际素数截止值来自该位置的同一个 $Q$。

对固定 $0<\kappa\le1/112$，取 $X=N^{1-\kappa}$。每一实际标签 $(l,\boldsymbol q)$ 使用原 `roughNumbers (N/(d·prod qs)) q_penultimate`。一侧取 $d(\prod q_i)m\le X$，另一侧取 $X<d(\prod q_i)m$。素数测试为 $d(\prod q_i)m<N$ 且 $N-d(\prod q_i)m$ 为素数。每个小纤维的未测个数至多 $X/(d\prod q_i)$。原 `P2EnhancedShortWordUnitBound.reciprocal_labels_eventually` 保留完整列表并统一给出 $\sum_{\boldsymbol q}1/\prod q_i\le5^r$。原 20 次出现合计至多 $20\cdot 5^6 X/d$，其中 112、122 均各出现两次。范围内的所有重复素因子也继续计数。

`all_marked_small_products` 分别证明小乘积的正素数计数和其未测整数乘 $(K/4)\,\mathrm{thetaConversion}(N,d)$ 后各至多 $\varepsilon\sum_{l\in B}\mathrm{levelMark}(l)\theta(N,Q,d_l)$。每一阈值先于 $N,n,\tau,p,\mathrm{dep},B$，可依赖预选的 $\kappa,\varepsilon$。空子族和零质量可直接代入。证明使用真 li 的原 `Theta_lower` 及 `rawMainAtom_to_thetaAtom`。相对误差来自先保留 $1/d$ 的原子估计。这里无需用某个小格的正质量替换全族质量。

`classical_inclusive_long_cost` 将同一实际经典族的**全部未测 Γ9–21** 收到旧二十个非单位 Buchstab 积分，逐 $d$ 使用真实 $\alpha$，误差为一次 $\varepsilon\Theta_B$。公式两侧都有 $K/4$。旧 `original_Gamma9_to_21_theta_upper` 供应二十个严格 erase-one 非单位项。原 `unitWordMass_eq_product_count` 识别原整数单位项。`native_unit_le_small` 以同一 $d\prod q_i\le N$ 判断将其放回已付小载体。这里已经覆盖原来分别用 J20、J21 正曲面上界的两个单位计数。原一般 $\alpha\ge2$ 范围仍保留原曲面。旧十八个短字单位估计继续有效，未重新做其积分或数值证书。

## 剩余素数测试的真实载体

`prime_tuple_reindex` 在固定原位置、颜色字、严格排序素数列表之后，将保留下来的尾商 $m$ 唯一写成 `Nat.primeFactorsList m`。乘积是逆映射，颜色和外层位置始终保存在外层求和。所有相等的尾素数、恰等于倒数第二颗素数的尾素数及其各次出现均保留。未测整数使用相同因子化，因此这两个和逐个对应。

`actual_large_prime_tuple` 给出整个旧字、原新增字和规范尾字的真实乘积 $X<M=d\prod q_i\,m\le N$。其中至少有五个素数槽，至多有 $\lfloor1/\mathrm{frozenLeafCutoffFloor}\rfloor$ 个。每颗均 $\ge N^{\mathrm{frozenLeafCutoffFloor}}$。该正数在 $N$ 以前固定。等于 $N$ 的端点仍在未测数中，素数侧用严格 $M<N$。原稿的 $k_{\mathrm{HB}}=3$ 群分解中，每个原组至多六槽。按原稿选 $12\zeta<\mathrm{frozenLeafCutoffFloor}/2$ 并舍弃不合物理组尺度的矩形后，若每个变量均在中段外，则每个组都需要一颗长变量。总乘积至多容纳两颗。故这批大乘积只需处理中等长度的解析分支。这里实现的是原输入的五槽下界、固定上界和幂次下界，HB 分布估计本身仍是独立责任。

`actual_large_product_difference` 在全部经典因果位置证明原 `switchedPPBalance` 与大乘积后的有向收支之差的**绝对值**至多 $\varepsilon\Theta_B$。两者的 Γ5 项逐项相同。`classical_seed_and_four_rounds_large` 在真实 `seedPositions` 接回 $1/50$、四轮前代反馈、两个非负抵扣及七个普通 AP 项。正的 Γ9–21 主量仍在大载体内。一般后代的 Γ5 也仍是实际收支。

`original_E_and_S_after_small_switches` 另在原正宽夹持根使用既有 Γ5 总付款。原掩码长字的重复项和目标中心先按 `prime_word_purified` 及 `exact_errors_theta_payment` 收款。设 $U_p$ 为旧 `otherSeedTerms`，$P_p$ 为其中正号的 `longPrime`，$B_p$ 为已付的原坏 Γ5 转换价，$L_p^+(X)$ 为新大载体的加法素数计数。对固定 $0<\tau\le1/12$、固定 $\kappa>0$、所有充分大的偶数 $N$ 和全部原细网格 $n$，终端是

$$
 5\big(\Theta_{\rm clamp}-\sum_{p\in\rm clamp}(E_p+S_p)\big)
 \le \sum_{p\in\rm clamp}(U_p-P_p+B_p+L_p^+(X))+\varepsilon\Theta_{\rm clamp}.
$$

此处 $U_p-P_p$ 精确保留原 4∶1 锚点、三个负单素数窗口、四个好配对、W2Charge 与原碰撞和中心项。当前种子作用在 5 倍根计数上。整树根权 7/2 和其 row12 条件属于后面的原全黄入口。

## Γ5 的同模数做法在 Γ9–15 的边界

写 $a_0=50/227, a_1=100/353, a_2=10/29, a_3=25/61, b=5/11$，$w=u_2$。以下各行的第二列是原闭包中 $\sum u_i+w$ 的下界，第三列给出该原域内的严格有序内点，其 $\sum u_i>1$。第三列的整数统一除以 1000，便于复核。

| Γ | $\sum u_i+w$ 下界 | 内点分子 |
|---|---|---|
| 9 | $4a_1$ | 380, 390, 400 |
| 10 | $3a_1+a_2$ | 330, 340, 440 |
| 11 | $a_1+3a_2$ | 340, 390, 400 |
| 12 | $3a_0+a_3$ | 278, 282, 450 |
| 13 | $a_0+2a_1+a_2$ | 280, 340, 440 |
| 14 | $a_0+3a_2$ | 270, 430, 440 |
| 15 | $a_1+2a_2+a_3$ | 340, 400, 440 |

七个下界均严格大于 1。因此每窗都有一块正体积区域，裸前缀 $d q_1q_2q_3$ 已超出 $Q$。其余有 $\sum u_i<1$ 的位置，也满足残余对数预算 $1-\sum u_i<w$。即使只拿原 Γ5 普通核 $1/(1-\sum u_i)$ 作比较，它也大于 $1/w$，而原 Γ9–15 的统一替换上界为 $(K/4)c_\omega/w<1/w$，其中 $c_\omega=70893/125000$。这解释了整段为何继续需要稿中的正素数乘积估计，也区分了作为外部模数的 $p$ 与内部筛素数。

## 最小未付项及原稿量词

对原限定因果选择的固定正标记盒，或可由这些固定盒逼近的原族，以原权 $\mu_l$ 保留所有标签。现在还需对 $M>N^{1-\kappa}$ 的同一真实族证明有向平均

$$
 \sum_{p,l}\mu_l\left(L^+_{p,l}(X)
       -\tfrac K4\,\mathrm{thetaConversion}(N,d_l)L^0_{p,l}(X)\right)
   \le o(\text{相应原物理总质量}).
$$

这里 $L^+$ 和 $L^0$ 是 `allLarge true/false` 的两个具体整数和。主稿正素数乘积定理给固定排序和单项式约束的几何族，极限是通过所有充分大偶数的绝对误差。真正调用时还需保留原词颜色、原目标删素数、物理夹持及有向闭格标记，在一次总质量内把**整族**送到共同光滑外逼近。任取随 $N$ 变化的精度、单个 $p$ 或任意因果子集不能直接代入此分布结论。本文逐 $p$、逐子集所证的只是物理幂次、未测成本和真正幂次小误差。

正分布主项要与同一实际 $\rho_N$ 的精确互素均值合并，粗糙 HB 槽带一致 SW，三组归一化依赖每个整盒原许可。原中段估计、$7/32$ 谱输入、真实权重的全族混合导数和主量过渡并未由本包提供。根层 Γ5 的同完整模数 BV 已获独审，在任意后代 `largeBalance` 内其单独许可仍需确认。七个普通 AP 余量的原外 $p$ 聚合与一般继承位置也应各按其原量词使用。四轮前代实反馈、原 W1/W2 母词的其余带号 base、closed-cell 计数采用与不可变 430+11 均仍开放。

## 可复核的原件

稿本固定为 `chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`。原区间及两末端单位曲面见 `proof-library/source/replacement-second-seed-route.tex`。$K,c_\omega,1/50$ 的具体改动见 `second-seed-omega-certified.tex`。经典模数有界倍数与其局限见 `second-seed-stable-prefix-extension.tex` 第 48–55、103–125 行。可变固定素因子下界和 HB 中段分支见 `generalized-one-step-double-sieve.tex` 第 126–201 行。实际 PP 与同系数三组条件见 `distribution-prime-product-completion-20261010.txt` 的 $M$、$PP$ 及 `global-positive-upper-completion-20261010.txt` 首节。原标签、原非单位供应和本包直依赖均在 `REGISTRY.json` 按提交、路径、字节与指纹登记。
