# certificate_omega 第三批交付

本批新增两个完整局部源码文件，合计550行、27个声明（以 REGISTRY 精确字节为准），未编译、正式信用0。`task_complete=false` 针对原始完整证书目标；`local_step_complete=true` 与 `batch_target_source_complete=true` 指本批真实 SharpCellError、sourceCell 和 query soundness 的源码步骤。

第一文件从真实 Buchstab 入手。现有1/2-Lipschitz tail 与初段1/s合成 [1,∞) 上1-Lipschitz；固定上游 `hasDerivAt_mul_buchstab` 给出实际 slope(s)=[omega(s-1)-omega(s)]/s。由全局函数差界及分母 s>=2，显式 slope 在 [2,∞) 上2-Lipschitz。随后复用 Mathlib 单调导数推出凸性的定理：±omega+x² 均凸，故真实 endpoint chord 的误差至多 (x-a)(b-x)。这条证明只要求开区间内的一阶导数，允许整数结点的二阶导数不存在。

同一二次形状同时给出原始两个常数。用项目已有 endpointChord 积分与 quadratic remainder 的精确积分，得到 delayed omega 的 h³/6 梯形误差，进而证明每个原始 mesh8192 递推格的 SharpCellError，不再留下局部误差前提。取二次形状上界 h²/4，得到原始 sourceCell 的 endpoint max bulge；再接现有实际 C0 上界及112-bit ceil/min，证明逐格 upper token 的语义。没有用较粗的 Lipschitz h² 误差替代原始 h³ allowance。

第二文件接实际算法。真实 U节点语义给 pointUpper，原 sourceCell 的 min(C0,max(endpoint)+bulge) 包住真 omega。对原始 cell.drop(first).take(last-first+1) 证明精确 getElem 成员及 max fold 支配；原生 key 的两个固定有理参数给出真实 floor 网格覆盖。于是 SourceProducerValid 就蕴含原始 queryMax 对整段实际 argument 的 uniform upper，不再依赖旧 BridgeValid、不同 rectangle checker 或外加 QueryCover。最后把同一 query 上端点接现有同一 row1014347 的真实 ordered parent 质量 Z_B 上界与原 omegaCostToken，有向 costHi 因而语义安全。点值 query token 仅用于表示 upper 常数，绝未冒充包含全部 omega 值的区间。

唯一剩余的算法前提是原始 SourceProducerValid p，它内部只有整数/有理数组长度、确切初段/递推、正分母、cell定义和扫描max，没有实数 omega cap 或最终结论。本批没有构造/恢复实际 U/cell 数组，没有证明某份字节满足该 predicate，没有执行 checker。故它不能证明某个历史 endpoint 或 saved floor 已通过；后续仍须实际数组证据、floor_Q*P 比较、所有 native keys/rows、mask/fibre/reserve 与 current c 连接。

安装顺序：先保留第一、二批精确 SHA 的 source-only 依赖，再安装 BuchstabQuadraticError，最后 DirectQuerySoundness。REGISTRY 收录生产辅助、旧原始 source 和外部固定提交的原始函数/convex 接口哈希。未修改前批、生产、Git 或看板；未编译、未执行数值回放、未检查额度。未发现原稿新增数学缺口。
