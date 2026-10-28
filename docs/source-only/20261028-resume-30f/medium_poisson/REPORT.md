# medium_poisson 第六批 F 源码交付

本批补入 E 留下的实际整载体重索引和对角修正，并把原始 primitive S3 的 clean 部分接到既有物理五次 Abel；所有 nonclean general-D/root 与 restoration/zero/omitted 修正均保留。新增 7 个 Lean 文件，共935行、43个公开定理及1个必要局部 finite-Fubini 私有引理。只做源码提案与静态文本登记；未编译、未核验，形式信用0。

原始大目标和完整 F 派发目标仍 OPEN：`task_complete=false`、`goal_complete=false`、`batch_target_complete=false`、`batch_target_source_complete=false`。`local_step_complete=true` 只指下述有限恒等式、实际调用字典与独立展开的局部源码完成。没有把后半目标改名、缩小或转成外部 primitive。

## 接收与原稿边界

开工前已逐一重核 E 的5个 Lean、REGISTRY、REPORT raw SHA，全部与最终冻结值一致；未改 E 或任何前批。E REGISTRY 为 `e842ebcc6488a343b09defa9e498bc155749920b125baa03d11dfdb50518b08b`，E REPORT 为 `c05ebb65482463bbeea9b24a79800d4629ccc2cd5a8e645b312daa0f0add007a`。已 ACK root/board 并告 reviewer。

定向重读 manuscript-body 第177—239行、medium module §7 约296—321行与 unified-interface 第51—153行。原稿实际要求 clean CRT 相位(21)、真实慢相位、一次五坐标 Abel、coprime-coloring、两份 Λ 的独立 st=d 展开、两个 product 上界差、non-Hermitian polarization 和谱返回；该段没有统一命名的“四 chart”源对象。root 与 reviewer 已确认这一文本边界，本批按实际对象推进，不新造四个名字冒充分支覆盖。

原数值 rough cutoff 仍为 z，原稿 p>z/smooth p≤z 通过已冻结严格 receiver `floor(z)+1/2` 精确翻译（原解释要求 z≥0）。本批有限身份用已有 receiver λTrim 源，可对任意 z,y 写出；接回原 inclusive 个别-window kept 系数时须使用 E 已证明的 z≥0、y=roughY(x) 接口。没有假定 untrimmed Λ=λTrim，没有增加避开素数边界的新前提。

## 真实整载体连接

`Part3OriginalPoissonCarrierCells` 把实际 primitive-q 过滤移到精确零 mask。真实 λTrim 支持证明 inactive d 为0，并允许两份 rough 半开 owned-window 分别扩到 FixedBlock 闭窗口，补入端点均为0。其 `blockRaw_eq_q_cells` 接到已经存在的实际 `coefficientRawSum/rawBox`，保留 q/r/s/n1/n2/h 六坐标及全部 nonclean 物理项。

`Part3OriginalWholePoissonCarrierReindex` 从 peer E 独立的 `fibreCarrier`、`headCoefficient`、`retainedModes` 出发，使用 exact real-H 双符号和 floor(H) 窗口，完成实际 primitive q、dyadic d、两份 rough/alpha、三个 qPiece 和整个 keyBank 的有限求和重排。`retainedSourceKey_eq_keyRawFamily` 和 `retainedSourceTotal_eq_genuineRawE2` 不接受 SourceBind 作为前提；两边源对象独立，且都包含对角与 nonclean。m 的原同权重纤维和真实 Poisson 转换复用 peer E 的已冻结 genuine-source 身份，没有换 ψq/ψm 或另定义候选源。

`Part3OriginalPoissonSourceCorrections` 将 actual primitiveS3 接回全族。`literalS3Normalized_eq_typed_nonclean_corrections` 给出原 S3/V 全 key 和 = typed clean E3/d + 全 nonclean/V + 明确 correction。correction 同时包括 deleted diagonal、减 retained diagonal、两份减 single-zero、off-diagonal genuine zero 和 omitted 模。不会把 off-diagonal 源与含对角的 raw 总和直接等同，也没有宣称任何零模已与 S1/S2 抵消。

## 实际 Abel、一般 D 与独立 Λ 展开

`Part3OriginalSourcePhysicalAbelCaller` 直接使用 Medium-Phase-Sol6 的 `E3_five_abel`，并复用其四个已有 empty-endpoint 引理处理非 OrderedBox。actual hCarrier 另外证明 H<1 整体为空，因此即使 scalar interval 看似非空也不会制造频率。实际全部 clean 块进入 `actualFamilyAbel` 的既有 coeff5/weight5 塔；完整源恒等式同时保留 nonclean/corrections。另直接实例化既有 retainedArgument_normalized，保留 Q/q0、D/d、log^5 和完整慢相位。这里没有假设或声称实际 prefix/variation 估计。

`Part3OriginalNoncleanGeneralDPackets` 按真实 D=gcd(d*w1,d*w2) 精确、互斥、穷尽地分纤维，并证明 preliminary d|D。每个 payload 仍是原完整 coefficientPhysicalTerm，保留 full lcm、constructed CRT residue/root 与 signed Fourier 模；未在 nonclean 上使用 clean lcm=q*d*w1*w2 或不合法 inverse。`literalS3Normalized_eq_Abel_generalD_corrections` 是这一整源调用的明确等式。

`Part3OriginalActualLambdaPairExpansion` 对两份 actual λTrim 分别展开各自 trimmedChoices，两个 st=d 独立保留，γ2(us)γ3(vt)、各个原窗口与 smooth trim 都留在原 choice 源内。每份物理 q*d*w 模数证明等于该份原 q*q2*q3 完全乘积，q 未被改成 qd。现有实际 clean coefficient 的分母 q*w1*w2 与 inverse phase 保持原定义。没有把两个选择强制相同，也未宣称已完成 non-Hermitian polarization。

## 独立零模 port

本批单向消费 F S3 冻结的 ActualS3ZeroCentering（SHA `1bc53d2e14ace9f14b2d32ccd7acb1f38865ae1c80b738f5d77853d3ed262e0f`）及其 NativePrincipalSource（SHA `ca0e1f114ba7513326e8c79a7c3878fa68e3dac138106d03fe86e3dd4d9718eb`）。`Part3OriginalPoissonZeroCenteringCaller` 先证明本源 offDiagonalZero 就是 peer 的 genuineOffDiagonalZero，再把 actual S3 correction 接到 native MT+P、roughReplacementCorrection 与真实 diagonal zero。该 peer 的 rough clean 仅为 (r,s)=1 和 (s,ell)=1；没有偷加 (r,ell)=1，也未用更强 E3 clean 替换。双方均未使用 variance/Gram 界，无结论依赖环。

## 完整目标仍缺什么

全载体与 correction 身份已写入，但一般 nonclean arithmetic 分支到各自合法 canonical inverse/root/retained-phase 调用仍未全部证明。所有这些项被完整保留，分 D 本身不是它们的估计或运输完成证书。

还须在真实分支上完成 coprime-coloring 覆盖、product-window 的两个上界差、non-Hermitian polarization、各系数/多重性支付；两份 actual Λ 独立展开已交付，不能以此宣称后续分支全覆盖。实际 coeff5 rectangular prefix、weight5 完整有限差分 variation、一次 x^(5κ+o(1)) 支付和内部 spectral return 仍 OPEN，须从原稿精确经典 primitive 推导，不能假设 E2/medium 最终结论。

真实两 single-zero Rcal(N+Y)、gcd/close-pair 任意 log 支付、rough replacement、omitted-lattice 的全 l,V 与系数预算仍待证。原 outer Cauchy 的实际权重/多重性、S1−2Re(S2)+S3 和 positive principal Gram、common interval/phase 谱返回的全链也仍待完成。F S3 的 finite deletion budget 不被冒称全支付。本批未发现新原稿数学缺陷；以上均是明列的内部实现义务。

没有编译、lake、proof/numerical checker、quota 检查、新代理、functional decision 执行、生产/Git/他人或前批写入。只对本目录7个 Lean 做 bounded comment/string/token 文本检查并登记 exact raw SHA/import。文本闭合不代表 Lean parsing/elaboration/kernel 通过。

## 文件与安装 raw SHA

- `Part3OriginalPoissonCarrierCells.lean` — `9d276c6dfc0ee49399c07b32e055d683099994c02fe8c70dd425bab181ddd01a`；160行；安装目标 `ImbalancedChen/Part3OriginalPoissonCarrierCells.lean`。
- `Part3OriginalWholePoissonCarrierReindex.lean` — `1c61abc1315622311b4b511d4846d9b379b0c1c943b726845d46bbb200d4b9bd`；220行；安装目标 `ImbalancedChen/Part3OriginalWholePoissonCarrierReindex.lean`。
- `Part3OriginalPoissonSourceCorrections.lean` — `b83fa8551396e0052a432505eda689768edf64d415e0b0c099c1060cd370766c`；157行；安装目标 `ImbalancedChen/Part3OriginalPoissonSourceCorrections.lean`。
- `Part3OriginalSourcePhysicalAbelCaller.lean` — `b1dada7b0307df2cede604baf72ddb6fca135efdc57bc1bc5065ebcfdc90f968`；123行；安装目标 `ImbalancedChen/Part3OriginalSourcePhysicalAbelCaller.lean`。
- `Part3OriginalNoncleanGeneralDPackets.lean` — `176735081425057ba917932d8e4757004ad14561b6d3f8e34116029fb29f0af4`；93行；安装目标 `ImbalancedChen/Part3OriginalNoncleanGeneralDPackets.lean`。
- `Part3OriginalActualLambdaPairExpansion.lean` — `1c44d44b88e08a6c16ebd5fdaf0302f2014a0a4a854458ea42e1ebe270ec5a8e`；97行；安装目标 `ImbalancedChen/Part3OriginalActualLambdaPairExpansion.lean`。
- `Part3OriginalPoissonZeroCenteringCaller.lean` — `63e7ae87996e4f054ee3f52aa52321559c9a5d5ad0c4c23f97f5ab506121c059`；85行；安装目标 `ImbalancedChen/Part3OriginalPoissonZeroCenteringCaller.lean`。

`REGISTRY.json` raw SHA：`91c6a4ae333390e6f4d225c62f411358d8c57311043c819ebcd5c299fc90ff90`。

29个实际 source-only 导入及 Sol6 递归叶子、E 和 F S3 的持有 manifest 均已按 raw SHA 重核并列出真实安装映射；这些文件均未被本批安装或编译。剩余义务与真实前提详见 REGISTRY.remaining/true_premises。
