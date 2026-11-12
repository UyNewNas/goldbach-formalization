# 原吴 248 代的高端读点与真实计数

本次仅审 P2.9 的指定 248 代历史。三份源码已将高半格的独立许可消去，并在经典吴源盒上接回 W1 锚及 W2 第一项的真实计数。最终 h248 的数值许可仍有显式低半 H247 前提。

历史表每轴 200 格。原 30m 模块逐一读八个 JSON，固定 24、56、120、184、248 代原数据。W2 在第 24 次迭代前为空，其后依次使用旧表、lower-K 换基、variable-kernel 换基以及换基旧表追加新行。W1 自 56 起替换有效基线。新 tagged_schedule_eq 按原顺序逐行投影；重定价只换 base，保留原参数、点、下标及重数。已有 schema guard 负责 zip 长度和原数据形状。新增 archive_geometry 检查三组真实动作的写目标 $i<100$、读点 $i\ge100$、原读取的两个槽重数 4 和 1 以及 $\mathrm{gridAt}(i)<s\le\mathrm{gridAt}(i+1)$、$s>3$。原查表闭交界的保守最小值仍属既有消费者。所有 guard 均未执行。

原正种子只写前 60 个 H 格，h 初值为零。对 $i\ge100$，W1、W2 均跳过该写位置；一次迭代只有保留与上交叉后缀二者取 max。历史 log 权重非负、两代间旧值逐格单调，故最后后缀支配保留值。high_last_suffix 给整数恒等式，读取前代 h，从 $\max(50,i-49)$ 开始，每一乘积按原 $Q=2^{80}$ 向下取整。high_endpoint_from_lower_tail 只对实际读取子尾要求前代 h 的右端点界；辅助证明用零填充未读格。原上交叉积分 $\int_{\max(2,s-1)}^5 h_\delta(u)\,du/u\le H_\delta(s)$，前代下交叉则使用前前代 H。保留单调性使最后一代低半 H 的逐格界也上控更早的低半 H。与指数反单调性合用，原闭格右端点给 $G_i\le H_\delta(\mathrm{right}_i)\le H_\delta(s)$，正改进从上系数中减去。

native_point_and_gamma_one 对任意固定 $g,k$、$0<\delta\le1/10,\varepsilon>0$，先合并该代有限真实读点的阈值，再允许所有达阈值的偶数 $N\ge4$ 及满足 wuSourceBox $(k+1)$ 的秩、$\Delta,V$。使用 $Q=N^{1/2-\delta}$、原平方前缀、指定 Wu 窗及恒真接收器。原 markedPhi 与 wuBoxPhi 的元组等式、markedTheta 与 boxTheta 的纤维等式保留相同乘积的所有原标签。W2 两个正计数在同盒同 Θ 上按 $4:1$ 加权并只除以五。该出口使用解析 $H_\delta$，对它没有存档数值假设。initial_point_prices 只处理初两代高端零值；later_point_prices 要将第 $n+2$ 代实际整数代入，则需真实的第 $n$ 代低半 H 界。owned_gamma_one 只允许非负权重的完整原盒，允许重复与零总质量。增强水平、盒内筛选和负权未由该定理许可。

actual_bank_from_low_upper 的前提为全部 $i<100$ 的 $\mathrm{outputAt}(247,\mathrm{true},i)/2^{80}\le H_\delta(\mathrm{gridAt}(i+1))$；输出为原 BankEndpointLicences。给所有表 247 读点单独定价所需的足够前提是表 245 的低半。原正种子全家族、W1/W2 实际基线、单项与配对正费用及其必要同系数分布尚需付款。本包没有无条件证明 17,572 项的全档案作用、整个 P2.9 或 430+11。

安装选择 HighPointAncestry 的 review-r1/28d33b25，其余两个模块保留 fed50d37 和 4c743de6。修正只在既有 rewrite 中显式传 n、i、hi，不改纸面命题。已按正式 fecfaff4 的路径与本地原字节核 258 个工程模块及其导入名，外部 138 个名称只是名单。另核原稿 9731290e、原生吴三个证据、八个 JSON 和九个 producer 的原始内容身份。两个只能在当时本地定位的 helper 是 P2EnhancedW1IntegerPrimeGraphStep (9db8da9b) 与 P2EnhancedW1OrderedPositiveTripleWord (2acb72ee)。八个 JSON 中旧 combined、lower-K、variable-kernel、W2-variable-kernel-savings 四个在稿本钉点缺少对应路径。清单仅记录这些身份，不含文件，也不据此认定可远端安装。此次未本地编译、展开 guard、运行 producer 或重放数值。
