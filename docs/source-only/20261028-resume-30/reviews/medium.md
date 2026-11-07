# Medium 五项独立源码审阅

审阅者 `/root/dependency_inventory`；仅静态数学逻辑、原稿 scope、循环前提及本地哈希核对。没有运行 Lean/lake/compiler/checker，没有修编译或检查额度。五项均为 **SOURCE_REVIEW_PASS**，只覆盖下列窄源码范围；内核验收和正式信用均为 **0**。完整 medium 与主定理继续 **OPEN**。五项均保留 TASKS.json 原目标口径的 `task_complete=false`；Poisson 另记 `local_step_complete=true`，不改变作者原 registry 的任务完成状态。

| 任务 | 审阅结论 | 实际消除的窄义务 | 仍待完成 |
| --- | --- | --- | --- |
| medium_s1 | SOURCE_REVIEW_PASS；原任务未完 | 保留两份物理 totient 的 S1 正核分离；通过现有 τ₂/τ₄/τ₈ 普通均值得到整个 d-block 的 1/(QD) 对数预算 | 实际 FixedBlock 家族、literal Λ、q cutoff、物理 caps 与 Y=QD 渐近绑定 |
| medium_s2 | SOURCE_REVIEW_PASS；原任务未完 | 对原 same-d paperBlockOuterCarrier 证明有限 (F)，保留 free n₂ 质量及 φ(qds)；非零实际包获得 gcd(a,l)=1 | H 几何、primitive Shiu、dyadic/collapsed tail，真尺度 V=MN²/Y |
| medium_s3 | SOURCE_REVIEW_PASS；原任务未完 | 全重数 canonical smooth/rough split；真实固定窗 allowed；完整固定块物理对↔choices 的无碰撞重索引 | 全局 dyadic ownership、原 deleted-W/off-diagonal carrier 与 V、恢复误差 |
| medium_variance | SOURCE_REVIEW_PASS；原任务未完 | imprimitive 特征保留 r·(ell/f) 门；原 auxiliary SW 给低 conductor 任意对数节约；real Parseval 与 weighted Cauchy | f,k 求和、高 conductor fixed-k 大筛、(14) 与 principal Gram (15)、四 chart |
| medium_poisson | SOURCE_REVIEW_PASS；原任务未完，局部步骤完成 | actual paperPsi 有限 residue packet 的 signed lattice 截断恒等式及物理 cutoff；固定 A,K 后统一阈值与显式 l₁ 汇总 | 完整 E2 dictionary、actual lcm/phase 绑定、真实 outer l₁ budget、全部 held closure 的编译验收 |

关键数学核对：S1 的 τ(d)³、τ(q)、τ(r)²、τ(s)² 和 q²d²rs 分母一致，先取 q≥Q、d≥D 再扩大正支撑，未用 x^ε 代替普通均值。S2 没有丢掉自由 n₂、移动 residue 或 φ(qds)，三项尾给出的 3 正确；不能把 (F) 误称完整 V/l 估计。S3 使用 primeFactorsList 保留素数幂，selectedModuli 不通过 choices 定义，因此双向支持恒等式不是循环假设。Variance 使用原命题明示的 UniformAuxiliarySW，未假设 weighted BDH。Poisson 保留相位至精确截断，再取绝对值；H<1 与任意正 V/L 均留在标量尾定理的统一量词内。

所有 registry 中显式且可解析的本地 path/SHA 对均与当前字节吻合；精确源、registry、report 哈希及逐条依赖核对见 `medium.json`。Mathlib revision 和既有外部普通除数均值只是沿既有导入链复用，未声称本轮核验其完整传递公理闭包。未发现须更改数学陈述的具体错误，也未发现把 hMedium/hPP/hLower/hUpper/hCertificate 或最终目标作为新前提。

原稿依据为 `manuscript-body.tex` SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd` 与 `distribution-medium-completion-20261010.txt` SHA `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`。本结论不支持任何完整 medium、谱返回或主定理完成声明。

Poisson 最终注释修订已通过逆向单次字节替换重建旧 SHA 核对：仅 `h=+/-1` 改为 `h equal to plus/minus one`，证明正文未变。最终 source SHA `4e38f12391f5fc72adbbb7f767e198b96a956dba98bb85ecb8034fb11093dfce`；registry SHA `37be03e99b48c0406ddb51bfa74c8cf7fecccf457b6bf13661669a1373433c70`；REPORT SHA `7a5252575675499d755bc3e250e95c212b26d75a5c630baa00a9aa3952767481`。作者 registry 与本验收均保持 `task_complete=false`、`local_step_complete=true`。
