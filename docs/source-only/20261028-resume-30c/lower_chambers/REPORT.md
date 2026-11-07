# lower_chambers 第三批源码交付

新增两份源码，原始 broad lower/chamber 目标保持 false/OPEN。局部本批墙支付与 finite common buffer 连接已写全；未编译、正式信用为 0。前两批不作修改。

`P2OriginalThirdLowerWallReserve.lean` 把实际第三层原稿墙写成明确的有限 CLM 族：9 个 cutoff/order/first-square/second-cube/W-parent/activation 等号；每个非空 mask 的 W-left/W-right、tent bend、parent-left/right 等号；全部不同 mask 的同侧 ties 和左右交叉 ties。每个 linear form 的非零性都由实际坐标向量检验或有限 mask ext 证明；同一 mask 的相同表达式不进入 proper wall catalogue，保留 inherited chamber。W=v(sum) 的 min 等号被拆到真实两侧，不把 tent 当全局 affine。

该明确墙族通过现有 `affinePrimeWall_volume_zero` 得到实数体积零测，并可限制到任意相同原 carrier。算术 prime atoms 另行保留：原始 actualPrimeBoxTuples/filter/tupleWeight 定义的 exact wall mass 通过具体 finite-index 等价精确重索引到现有 unionMass，进而趋零；固定正 strip width before N 的 reserve 直接消费现有 `exists_actualPrimeAffineWallStrip_mass_lt`，没有重新假设 desired prime mean 或从零测直接删素数原子。生产库具体 source hashes 已登记。

`P2OriginalFiniteWCommonBuffer.lean` 构造 LocalWBox 的实际 rebuffer：所有端点不变，beta/delta 缩小为正数后普通门槛与 winner 余量保留。topCap 约束没有使用错误的单调方向，而从真实正第三端点重新证明。对有限 cover 用 finite induction/min 选择一个正有理 r<=tau，同时不超过每盒原 beta/delta；实际返回新的有限 family，全部 beta=delta=r，端点与 cover 保留。该 common r 可直接进入前批实际 mesh WBoxCheck receiver，父 cap 与原 unselected bits 不变。

仍缺：定量 sufficiently fine common mesh 与总 compiler loss；strip reserve 对完整 same-rho signed lower 及真实 row/descendant weights 的应用；mixedWinner gapLower、第四/第五 causal Trace、算术 W licence、全 lower mean。此批只绑定第三层 W/tent 原始墙；后层父依赖墙仍需单独生成。未发现新的原稿数学缺口。

本轮仅静态审阅定义和证明逻辑；没有 Lean/lake、编译/修编译、kernel replay、checker、CI、额度检查、Git/index 或看板修改。完整 path/raw SHA、paper anchors 和剩余前提见 REGISTRY.json。
