# 第二批 medium 五项独立源码审阅

五项均为 **SOURCE_REVIEW_PASS**，限本次六份 Lean 的数学逻辑、原稿范围和精确依赖记录。六份共 1826 行；未运行 Lean/lake/compiler/checker、未修编译、未安装或查额度。`compiled=false`、`kernel_verified=false`、`formal_credit=0`。五项原完整目标均 `task_complete=false`，窄步 `local_step_complete=true`；完整 medium 和主定理继续 **OPEN**。

| 任务 | 实际消除的窄义务 | 仍待连接 |
| --- | --- | --- |
| medium_s1 | literal choices 注入 divisors(d*w)，原 gamma 一界给 Λ 除数界；strict small/rough 给互素；paperPsi q-majorant 与实际 cap 进入固定块正核预算 | 同一 Gevrey ψ 的 common-m coprime count、全局实际块家族、d 均值及渐近绑定 |
| medium_s2 | 实际 H≤12N/(Q1D)·τ(l)^4·L(P)·(1+log(4Q2Q3))^4；自由 n₂ 支付为 2N，保留 φ(qds) | primitive Shiu、dyadic/collapsed tail、同 Gevrey q/m 对象绑定；真尺度 V=MN²/Y |
| medium_s3 | 六坐标 [2^k,2^(k+1)) 唯一 ownership、有限 bank 基数；完整 W 双独立 key；ownedSlice 与 trimmed canonical choices 双向重索引 | smooth complement、preliminary Cauchy 共同 q/d、真实 S3/V 限制与 Rcal(N+Y) 恢复界 |
| medium_variance | 实际字符按 f 分纤维，φ(f)/φ(fk)≤1/φ(k)，有限 product cutoff 重排及普通固定除数矩；原 SW 直接实例化 lowEnergy | high conductor fixed-k 大筛、粗方差与加权 (14)、Gram (15)、四 chart 返回 |
| medium_poisson | 同 paperPsi 的实际 shared W/中心项；真实 gcd·lcm 几何、同 residue 的完整三相位、逐行统一尾界与 W−2V+U | clean E2 商字典/原稿(21)、enlarged q carrier、实际全 l₁ 预算与谱返回 |

S1 的 commonMCount 明确仍用旧 scaledDyadicCutoff；S2 的上游 s2TermWithCoefficients 也保留旧 commonSmoothWeight，ActualPsiWeightAdapter 只替换 q。新 H 为纯系数几何，故其窄步有效；不能据此把 S1/S2 全链改称原稿同一 Gevrey q/m 的已完成实例。Poisson 这批使用原任意 S,w 的有限恒等式显式插入 paperMWeight，没有把旧 bump 与 paperPsi 等同。

S3 原始两份 q₁/d 保持独立，全部 exact d、w 在同一 dyadic key 内求和；没有把 D 个单独分布余项相加。作者已只修元数据为 task_complete=false、local_step_complete=true、original_batch30_task_complete=false；assigned_next_step_complete=true 仅记录这次 ownership/重索引局部步骤。两份 Lean 未改。

中间有限引理的点态界在公开 uniform theorem 中由真实 UniformAuxiliarySW 实例化；未把 hMedium/hPP/hUpper/hLower/hCertificate、BDH 或最终目标作为新前提。没有发现具体数学反例或已证明的原稿缺口。普通除数/ totient 外部接口沿已钉住的生产导入复用；未声称本轮核验外部源码 API 或完整传递公理闭包。

五份 registry 共 37 条可解析本地 path/SHA 配对全部吻合；每份候选、registry、REPORT、必要前驱的当前 SHA 和逐条记录见 `medium.json`。静态注释/字符串扫描闭合且未见禁用证明占位符；此记录不授予任何内核或完整 theorem 信用。
