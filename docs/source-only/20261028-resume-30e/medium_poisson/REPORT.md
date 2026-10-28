# medium_poisson 第五批源码交付

本批完成必要局部连接：真实 λTrim/key/active-d/q-piece/双符号实 H 构造族，完整 clean 物理 Poisson 项及其有限和等于 `(V/d) × typed E3`，并把独立 genuine literal common-d Poisson 纤维逐频接到该族。原始大任务与本批完整目标仍未完成：`task_complete=false`、`batch_target_source_complete=false`；局部步 `local_step_complete=true`。所有文件 `compiled=false`、`formal_credit=0`、`ready_to_install=false`。没有执行 Lean/lake、数值 checker、额度检查或派生代理。

## 原稿与依赖边界

原稿 `distribution-medium-completion-20261010.txt` 第17行采用 rough 素因子 `p>z`，其补集是 smooth `p≤z`。D 批 peer 的 `strictReceiverCutoff z = floor(z)+1/2` 对 `z≥0` 给自然数支持的精确翻译，保留所有素数幂；本批 λTrim 调用均传该 receiver。没有增加“z 不等于素数”的新前提。原稿 unified-interface 第51—83行要求真实个别因子窗口、q 独立的 Λ 与共同 preliminary d，第93—136行给 E3 分母 `q*w1*w2`、clean 门与真实慢相位，第138—153行给实 H 的符号/q-piece 拆分。

依赖使用 source-only 精确路径与 raw SHA，未安装或假称已编译。D 本人、D S1 atlas、D cutoff 算术桥、E S3 PrimitivePsiSource/LiteralS3Stages/GenuinePoissonFibre、E S2 ActualKeyCoefficients 均定向消费。E S2 最终冻结接口 SHA 为 `52217e7b1fc920e30483fdb601fc60b3b580f484152977de29a8e1103256cb87`，不是其早读旧值。所有安装目标和递归依赖 manifest 均登记在 REGISTRY。

## 证明主线

1. `GevreyCleanE3Assembly` 先完成 D 批 untrimmed canonical Λ 项的乘积装配：在既有 typed E3 clean carrier 上复用完整 lcm、CRT 相位、合法 inverse 和同一 paperPsi Fourier，推出原物理项等于 `(V/d)*coeff*weight`，再求和、除以原始 V。该文件仍属于 untrimmed 辅助层，不能当作真实 λTrim 绑定。

2. `LambdaTrimPoissonFamily` 实际构造新族，不要求调用方给 `blocks` 或 `SourceBind`。其有限索引是实际 keyBank 内的 key、该 key 的 activeD、三个原 qPiece 和 Bool 符号。每个块继承真实 atlas λTrim 系数及合法 d，与 `actualProfile` 只更新实际 paperPsi/Fourier。S1 旧 singleton h 字段被真实 H 的正/负窗口替换；不存在把 S1 惰性字段当 E3 频率窗。actual λTrim 的 nonprimitive-d 零项证明允许 activeD 限制，不假设全 d 都与 a 互素。独立 E S2 keyKept 接口给原 inclusive 个别-window 系数与新族 λTrim 的精确相等。

3. `TrimmedCleanE3Assembly` 另定义保留 `B.lambdaD` 的完整物理项，加入独立真实源具有的 primitive-q mask。该项在 clean carrier 上等于 `(V/d)*(actualProfile B).coeff*weight`，完整 raw/V 恰等于 typed E3/d 加原样 nonclean/V。其 general-D 完整 lcm、CRT residue、alpha/λTrim、paperPsi、Fourier 和 h 都保留；没有把 nonclean 改成 clean 相位或假定全部覆盖。整个构造族也有相同的精确 clean/nonclean 和式。

4. `SourcePoissonFamilyDictionary` 消费 S3 peer 独立定义的 literal common-d restored m-sum，证明 actual `sourceMode` 与新族项的逐频等式，q/d/r/s/n1/n2 和原完整 lcm/CRT 不变。在实际 key floor(H) 处实例化其真正 off-diagonal Poisson 源恒等式，零模、有限保留频率和 omitted packet 同时显式保留。该恒等式仍在 peer 原始 fibreCarrier 上，并未被定义成新族总和。

5. `PoissonFrequencyOwnership` 证明 `floor(H)` 的整数有限窗口恰等于两个真实 signed-H 窗口的和（h=0 的实际系数为0），兼容 H<1 时空和，且不以 ceil(H) 制造额外频率。另由实际 λTrim 支持证明 nonprimitive d 与 rough owned-window 外项的 sourceMode 为0，供下一批完成整载体重索引使用。

## 仍然 OPEN 的必要步骤

独立 literal preliminary retained 源总和到 genuineRawE2 的整个有限载体恒等式尚未完成。逐频字典、字段构造及实 H 双符号和式均不能代替该总和绑定。下一步必须把 qPiece/primitive-q、active-d、粗因子半开 owned-window 与 FixedBlock 闭端点、n-carrier 和乘积求和次序逐一重排，实际零项已有部分支持引理。

peer 的 offDiagonal 源排除 n1=n2，而本批完整 rawBox 还包含对角原项，其被保留在 nonclean 补集中。两者的精确对角修正必须显式接回，不能直接写成总和相等；原 S1−2Re(S2)+S3、single-zero、零模和 omitted 支付也不能省略。nonclean general-D/root 的估计、实际全部系数预算、Abel/rectangle 调用和 spectral return 仍属原稿内部待证。

D 批旧 `PreliminaryBlockFamily` 对未过滤 dCarrier 的每个标签要求 FixedBlock 的 d 与 a 互素，而实际零系数标签不必满足这一条件；本批采用由真实非零支持证明允许的 activeD/key 新族，未假称旧 unfiltered receiver 已获整源构造。该 receiver 适配是实现边界，不是原稿数学反例。未发现新的原稿缺陷。

## 文件与 raw SHA

- `Part3OriginalGevreyCleanE3Assembly.lean` — `82f8d0332d55eff7b1c5d5fd049d3e63caa12b2b6e0fa35d32901284ff67bf09`；125 行；安装为 `ImbalancedChen/Part3OriginalGevreyCleanE3Assembly.lean`。
- `Part3OriginalLambdaTrimPoissonFamily.lean` — `7491382943243ebad3f9a6902dc6831538dd231a999a06d54a4d5864d0895f3e`；227 行；安装为 `ImbalancedChen/Part3OriginalLambdaTrimPoissonFamily.lean`。
- `Part3OriginalTrimmedCleanE3Assembly.lean` — `4b916c0cb3d4c51746afe2c360f07f137fd9215738c8eb8551e5121d07c277cb`；153 行；安装为 `ImbalancedChen/Part3OriginalTrimmedCleanE3Assembly.lean`。
- `Part3OriginalSourcePoissonFamilyDictionary.lean` — `f08385164fd887064389d97059dc0371c5db3e30365e9a5cc6bdc9012a9aa469`；127 行；安装为 `ImbalancedChen/Part3OriginalSourcePoissonFamilyDictionary.lean`。
- `Part3OriginalPoissonFrequencyOwnership.lean` — `7185781ee7905482d93b6d8d26200697efff55c8d64d5e56e827ebfee94174ea`；124 行；安装为 `ImbalancedChen/Part3OriginalPoissonFrequencyOwnership.lean`。

`REGISTRY.json` raw SHA：`e842ebcc6488a343b09defa9e498bc155749920b125baa03d11dfdb50518b08b`。

只对上述五个 Lean 文件做有界注释/字符串词法闭合、禁用占位 token、声明/import 字符串和 SHA 检查；均文本闭合，未见 sorry/admit/axiom/unsafe 代码 token。这不是 Lean 语法/elaboration/内核验收，不产生形式信用。完整后续义务在 REGISTRY.remaining 中原样保留。
