# pp_twolong 第五批：P1 双 periodization、双轴消去和实际整数滤波

交付三份闭合源码。D 三源/登记/报告 raw SHA 已重新核对保持冻结；E 源码没有 hP1/hP2 输入，也没有将 P1/P2 外置。原完整任务、完整 P1/P2/E4 均仍开放，未编译，正式信用 0。

`Part3TwoLongP1AxisCancellation` 复用项目已有 literal Ramanujan `S(0,k)=c_q(k)`、`S(n,0)=c_q(n)`、unit scaling 和 `c_q(0)=phi(q)`，直接证明原 P1 kernel

`S(b*j,k;q)-c_q(j)c_q(k)/phi(q)`

在 j=0 或 k=0 的整条轴精确为零，包括轴上的非零 Fourier masses。代码还把 actual inverse-short center 的 unit 许可从 primitive a/m 导出；q=1 既在谱核层面证明全零，也直接在原有限 fixedMCore 的 AP count 和 exact coprime mean 上证明二者相同。

`Part3TwoLongFilteredIntegerFrequency` 没有仅换一个 d*k 参数名：用实际 support 双射将 Z 上 `d|j` 的 filtered tsum 精确重索引为 j=d*k，再消费 D 已冻结的所有 H>0 预算（含 H<1），得到 2H/d 和双频 4HK/d²。它还用 Nat.sum_totient 与实际 gcd-divisor set equality，把 `gcd(q,|j|)` 写成原 q-divisor/totient filter，接入已存在的形式化 Ramanujan gcd bound。

`Part3TwoLongActualDoublePeriodization` 对实际 compact-Schwartz f(n/U) 构造 dilation，证明 Fourier 缩放和 affine Poisson，给出完整频率 norm summability，进而证明双 affine periodization 的 UV/D² 系数、两个真实 Fourier 参数与两个相位。对 D 的 upper-upper、gap-upper、upper-gap 三份实际固定 transition profile，Schwartz/C∞/compact witnesses 均由源码构造，实际 caller 不再要求它们作为假设。

完整 P1 仍欠原 natural compact AP carrier/exact mean 到 complete finite unit residues 的算术双射与归一化、该有限 unit sum 与 double Poisson 的交换及 centered-kernel 识别。完整 P2 还需以真实 N2 证明 C2 Fourier decay，接具名 composite Weil 和已形式化 Ramanujan，装配 E 的 actual filtered-Z 重索引和 D 的 q 无关 Weil/Ramanujan budgets。现有 Schwartz rapid decay 不能冒充该固定 N2 常数。三份原 HB expanded-support smooth Brun core/Mellin binding 和 x-dependent E4 也仍保留。

这些未完成项没有改写成 hP1/hP2。未发现新的原稿数学缺口。精确源码/导入/原稿 SHA 与剩余义务见 REGISTRY.json；未执行编译、checker 或额度检查。
