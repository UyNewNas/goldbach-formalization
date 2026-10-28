# transfer_power 源码交付

本轮输出 `P5ProperPowerSignedModulusPayment.lean`，共 11 个 theorem、261 行。源码文本闭合，未编译、未执行 checker、零正式验收信用；整个分配目标尚未完成。

前驱 `P5ProperPowerSignedMeanHBTransport` 只有同一 signed count/mean 的 HB 恒等式，明确缺 absolute modulus payment。本文件消除这处有限证明义务：对同一个复数 rho，把精确 signed row 拆为 residue count 与 coprime mean；非零 complete-product difference 的所有同余模数都是真正自然距离的约数，因此只付其 divisor count。complete product 恰等于目标时独立付物理模数 #Q，而不使用零的约数集。mean 始终保留同一个 rho 和 phi(q)，不替换成总质量。q=1 的完全抵消也对任意 product 得到证明。

该预算直接应用前驱的实际 marked proper-power word（保留 chi、eta、ambient W、完整 product），再借前驱 exact HB identity 传到 atlas。额外用每个坐标都是 t 的约数，把 exact-product integer word 注入 `(Fin k → t.divisors)`，得到 fibre≤tau(t)^k。这保留了所有有序重数，没有把复合数 replacement word 错当全素数 tuple 而套用 rank^rank。碰撞部分随后取得显式 amplitude×tau(t)^k×(R #Q+meanBudget) 界。

这里仍缺原始 W_N 的实际 licence/振幅、Lambda/log 分割、proper-power reciprocal-tail/tuple mass、divisor subpower 与 full22 active modulus polynomial range。原稿所述 power-small 结论尚不能由这份有限预算单独推出。

必须区分两种 diagonal：本文件的 product=t 是 signed modulus sum 的零距离碰撞；最终 ordered bad count 的 r=q 是素数平方。已有 `P4BDiagonalSquareBudget` 仅能在 signed PP 已处理后，以无权 receiver count 恢复 latter 的 O(sqrt N)。不能用 sqrt N 直接支付本文件的 signed rho term。prime remainder 的 r=1 仍走已有 good-receiver 分支，不能加入 bad semiprime source；固定 b 后统一 even threshold 的量词也仍按原稿保留。

所有导入路径、SHA256、实际消除的义务与余下边界均在 `REGISTRY.json`。source-only 前驱必须按 registry 的安装映射提供给编译专员。本轮未识别新的原稿数学缺口。
