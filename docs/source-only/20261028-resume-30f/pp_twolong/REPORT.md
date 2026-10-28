# pp_twolong 第六批：原自然 carrier 的 P1 与实际 N2 Fourier 衰减

本批提供四份闭合源码草案，未编译，正式信用为 0。E 三源、REGISTRY 和 REPORT 的 raw SHA 已逐一重核，未修改任何前批文件。原 task_complete=false，整项 batch_target_complete=false；本批完成的局部步是原 natural compact-carrier 的实际 Schwartz P1 和固定 N2 Fourier 衰减，完整内部 P2 尚未装配。

`Part3TwoLongNaturalResidueCore` 从原独立定义的 fixedMCore 出发，将自然数有限 AP count 和同一 alpha 的 exact coprime mean 按真实 rowMass 推前到完整 ZMod q 余数。原 complete-product unit 条件并未换成无限制均值。primitive a/m 时求和降到 x=(a*m^-1)*y^-1 的实际单位图，均值独立分解成两份 unitMass；m 非 unit 时原 count 和 exact mean 均为零。

`Part3TwoLongNaturalPeriodization` 用实际 support 双射证明 wideWindow 中的自然数 AP 行等于完整整数 affine periodization。正支撑 [1/2,5/2] 保证整数自然化没有负数或零附近的漏项。由此得到原 natural fixedMCore 到真实单位图 periodizations 和其 exact unit-product mean 的等式。

`Part3TwoLongNaturalP1` 对生产代码的 literal Kloosterman 定义证明单位群取逆的真实双射。单位图直接产生 S(k,b*j)，取逆重索引将其转为原稿的 S(b*j,k)，并从两个实际 unitMass 分别得到 c_q(j)、c_q(k)。实际 Poisson modes 的 norm summability 支付 Z×Z 的 absolute convergence，并据此交换有限完整余数和与两重 tsum。最终 naturalCore_P1 保留原 alpha、原 inverse-short residue、两个 Fourier 实参、exact 1/phi(q) mean 与 UV/q^2。它没有 hP1/hP2 输入。该 P1 结论适用于源码的实际 compact Schwartz profiles；本批不声称一般只有 C2 假设的 Poisson 接口已实现。

`Part3TwoLongN2FourierDecay` 使用实际普通二阶导数构造 f-(2*pi)^-2*f''。通过 Mathlib 的真实 Fourier derivative 定理得到 (1+t^2)*fhat(t)，再付该函数的真实 L1 范数，导出固定常数

`2*(1+((2*pi)^2)^-1)`

乘原 N2(f)/(1+|t|)^2 的界。常数与 q/U/V/delta/Mellin 参数无关。实际 upper/gap Schwartz profiles 接上 D 已证 delta^-2 N2；A 的实际 selected Mellin mode 接上其已证 cube N2，得到固定 modeConstant*(1+H)^2 Fourier 界。这里的 Mellin mode 是 A 的 literal cutoff*phase；没有将它冒称为任意 upper/gap*phase 或 peer 的另一 log chart。

完整 F target 仍开放：需把具名原 classical composite Weil 的精确 gcd 预算与 E 的真实 filtered-Z 重索引、D 的 uniform Weil/Ramanujan frequency mass 装配成内部 P2；本批既未消费也未假设 P2。对 expanded smooth three-Brun profiles 的 Mellin-twist delta 预算、原 HB geometry 的完整 smooth/Mellin binding、同一 physical-rho 的模数求和与 E4/final PP 也仍开放。P1/P2 没有外置为 classical primitives。未发现新的原稿数学缺陷。

所有实际前提、源码/导入 raw SHA、冻结 E 及 scope review 的哈希列在 REGISTRY.json。只进行了源码阅读、数学静态核查和 raw SHA 核对；未运行编译、lake、checker、额度查询或新代理。
