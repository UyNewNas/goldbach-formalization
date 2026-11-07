# medium_s2：实际 S2 光滑尾块的不等式 (F)

新增 `Part3OriginalS2ActualBlockPacketBound.lean`，429 行，31 个定义/引理声明（含一个私有辅助引理）。文件文本闭合；未运行 Lean、lake、数值 checker，正式验收信用为 0。

本轮完成原有 `block-packet-first-missing-inequality.md` 明确留下的第一个有限证明义务：

`‖A_(l,D,R)‖ ≤ T(l,a) * H_(l,D,R)`。

`A` 直接使用已有 `paperBlockOuterCarrier`、实际 `actualPsiQWeight` 和三个 `actualThreeTailTerm`，并非另造一个抽象可估计的 packet。`coefficientCarrier` 保留同一个 d 的两个真实 roughFiber；块过滤和左模数 `q*d*r=l` 对 n1,n2,m 独立。`actualPaperBlockPacket_eq_coefficientPacket` 给出两种有限求和的精确字典。

证明先在固定 q,d,r,s 上精确分离三重和：原 `s2TermWithCoefficients` 等于原系数除以 **φ(q*d*s)**，乘自由 n2 的原始互素质量，再乘保留 n1 互素门与移动 a 的实际 m*n1 同余和。`coefficientInnerSum_factor` 逐点核对两个互素门、原 m*n1 顺序及共用平滑权，不要求额外交叉互素。

随后复用现有两类非重复的有限引理：原 Λ 的 q2,q3 纤维范数 ≤ τ(d*r)/τ(d*s)，以及原 m*n1 正纤维 ≤ τ(v)、零纤维因实际 cutoff 消失。自由 n2 由一有界 α 支付为其真实互素支持基数 B(q*d*s)。三项光滑尾分别估计，三角不等式给系数 3。最终 H 完整保留 φ(q*d*s) 分母、同 d 的 s 求和和 q,d,r 的实际因子重数。

唯一数学假设为原始 `MediumAdmissible`；没有把 (F)、Shiu 包估计、medium、PP 或最终目标作为前提。原始 Shiu 定理尚未被调用。

此外从真实非零 Λ 的求和中取非零 γ2*γ3 见证，再用原始 γ 的互素支持和 `q2*q3=d*r`，证明每个实际贡献的左模数 `q*d*r` 与 `a` 互素。`nonzero_actualPaperBlockPacket_coprime` 给非零原始块包的 reduced-residue licence；没有误称整个 image carrier 上每个零系数也满足它。

仍未完成分配任务的全部目标：H 的 dyadic 几何估计 `H ≲ (N/Y)*τ(l)^C*log(x)^C`，以及原始 primitive Shiu 在移动余数上的应用和 collapsed-tail 最终求和，仍须续推。不能据此宣称 V/l 包估计、完整 S2 误差或 medium 命题关闭。本轮没有发现可证实的原稿错误；这里消除的是已记录的实现缺口。

源码依赖都在旧的精确 source-only 草稿中，安装名称与哈希见 `REGISTRY.json`。本轮未改生产源码、旧草稿、Git 或看板。编译专项可按 registry 安装依赖后直接取用此文件；所有类型与证明仍待实际内核验证。
