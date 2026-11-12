# T23 全部加法素数收据的适用性核查

对象是已冻结的七源包 `discrete-primebox-next`。全收据的原计数搬运仍待证明。本补件记录有限求和及现有算术行的适用范围。七源包的独审范围和 Y24/H34 的状态沿用原登记。

## 对同一个原历史求和

固定真实根素数、RootKey、完整 shape 和整数词 \(w\)。用 \(O_w\) 表示 `rootHistory` 中与这组数据匹配的列表位置，重复位置按其原次数保留。位置 \(o\) 带有原系数 \(\mu_o=\mathrm{mark}(o)\)、乘积 \(B_o\)、根键的 \(Q\) 和 \(z_o=\mathrm{memberCutoff}(Q,o)\)。写 \(E_o=\mathrm{frozenCarrier}(N,B_o,\mathrm{rootMask}(N,p),z_o)\)。对有效历史，T17 的物理整词粗糙性保证 \(E_o\) 中的标签均属于原加法素数集 \(\mathcal P_N\)。展开 `SingleReceiptTheta.probe` 并交换两个有限和，逐字得到

$$
 \sum_{\ell\in\mathcal P_N}\mathrm{probe}_{\ell}(w)
 =\sum_{o\in O_w}\mu_o\sum_{\ell\in\mathcal P_N}1_{\ell\in E_o}
 =\sum_{o\in O_w}\mu_o\,\#E_o .
$$

T17 的 `owned_member_masked_count` 给出 \(\#E_o=\#\mathrm{originalReceiptLane}(N,p,D_o,z_o)\)，其中 \(D_o\) 为实际词去掉根素数后的乘积。若使用未加根掩膜的 `receiver N`，同一位置有额外的 \(\#\mathrm{rejectedChild}(N,B_o,D_o,z_o)\)。`all_emitted_original_receipts_plus_rejected` 已在每个根键与深度的全部位置上精确求和。根处 `original_U34_masked_origins` 已还原 U3/U4。

此前的 `actual_shape_word_mark` 给 \(\sum_{o\in O_w}\mu_o\le1\)。这说明每个固定 \(\ell\) 的探针至多为 1。全部 \(\ell\) 的探针和多出各不相同的接收者基数。原加法素数是按计数测度求和，逐标签质量为 1，总质量为 \(\#\mathcal P_N\)。没有与原恒等式相容的已有常数总质量权可直接代入。

## 原误差与已付误差

对同一物理词，记 \(I_v\) 为固定 Program 的全部门和原根带指标，\(\theta_v=\mathrm{thetaAtom}(N,Q_v,w.\mathrm{prod})\)，其中 \(v=0,n\) 标记理想图与冻结图。七源的 `markedError` 为

$$
 \frac{1}{\mathcal H_N}\sum_w |b(w)|\,|I_0(w)\theta_0(w)-I_n(w)\theta_n(w)|.
$$

可对两侧共同的任意 \(|b|\le1\) 使用同一 \(T,N_0(n)\)，包括某个 \(\ell\) 的冻结探针。将上式对所有 \(\ell\) 相加，逐词权变为上一节的带标记基数，且仍旧乘着 \(|I_0\theta_0-I_n\theta_n|\)。原始计数行取的是 \(I_v\) 乘该侧的收据基数。`common_factor` 的确在两侧共享算术前因子，但其等式左侧仅为 \(\theta_v/\mathcal H_N\)。它没有把普通素数收据基数分解成此原子。逐标签同一阈值不能消除因求和而出现的 \(\#\mathcal P_N\)。

若想在两侧同准入的一个词上把两边的原行分别逐词表示为 \(b(w)\theta_v(w)\)，写 \(C_v(w)\) 为该侧该词的原带标记收据基数。在 \(\theta_0,\theta_n>0\) 时，这种表示要求 \(C_0(w)/\theta_0(w)=C_n(w)/\theta_n(w)\)，还需原尺度上的标记界。以上有限恒等式没有这条比例恒等式。只求有向总和时可以使用平均筛估计，无须证明这个逐词要求。

## 仍需的算术估计

固定标记可匹配的原位置，取相应一侧的确定截止。只在一侧准入的词需要控制该侧原收据在差集上的总质量，精度先定、随后对足够大的 \(N\) 在 \(\mathcal H_N\) 尺度下变小。可用原正族的上筛，将这部分计数控制于其真实一侧的 \(\Theta\) 质量和已付的平均算术余项。同准入位置若两侧物理截止不同，实际基数差还包含截止之间的粗糙性收据壳，须由精确相等或相应方向的算术收据给付。原根的 `original_root_plateau` 已使两个均不超过 \(N^a\) 的根截止得到同一计数。跨图若重新选取位置或标记，还须额外识别两侧的原位置。原正负行也可在同一许可下合并求和后直接控制，无须逐项上界。

原稿正文第 795–817 行给同 \(Q\) 的非负标记族平均缺陷界。T07 的 `all_good_pair_count_means` 给四个普通双子窗口的有向比较，其中保留原 `laneAP` 与 `oldHMass`。T24 的 `fullPrimeTupleMass_le` 在真实正元组上保留 exact-coprime correction、signed PP 余项与小素数费用。T19 的 `independent_upper_routes` 已在 106 行父级保留两条可用的上界方向。这些结果可用于相应原族，当前冻结端点未给上述全收据筛变的总算术预算。此处只裁定从七源包直接消费的边界。
