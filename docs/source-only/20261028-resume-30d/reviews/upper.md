# 30d upper 独立源码审阅

审阅者：`/root/review_upper`。四项均为 **SOURCE_REVIEW_PASS**，只接受下述局部源码数学构造与报告范围。`compiled=false`、`kernel_verified=false`、`formal_credit=0`、原始 `task_complete=false`；完整 upper 与 K 均为 **OPEN**。

| 项目 | 局部验收范围 | 作者 batch target |
| --- | --- | --- |
| upper_chronology | 原导航 cell1 的独立96行 guard、实际 prime/frontier bank、firstStop、冻结父值链及 slot16/chronological42 | 窄目标完成 |
| upper_fifth | 两个 named parent 全128 child 的独立 ratio、sharp L3/U4、Q80 floor 语义及带 reserve 的 owner 下界 | 窄目标完成 |
| upper_mesh | 双端实际 verdict 的 adopted bank、真实遗漏积分、有限 raw bank 共同 e 后 q 与含 trim 的 B13 | 未完成；局部增量完成 |
| upper_jensen | all64 reserve 精确重组；两个真实 licensed parent 零遗漏的任意容差策略；actual signed integral 接符号 sharp Q80 总量 | 未完成；named 策略局部完成 |

## 方法与证据边界

已读本批 INSTRUCTIONS/TASKS、继承的源码审阅规则、10份最终 Lean（共1938行）、四组最终 REGISTRY/REPORT、原稿及必要前驱；不以作者摘要替代源码。实际原导航 JSON/cell-01 与本批 affine 定义逐项对读，原 refinement 与 exact-floor producer 的有理式、符号方向与新 floor 接口对读。

重算10个活动源码 hash、四组 registry/report hash，以及按项目去重的67条显式当前 path/hash 记录（17+14+17+19），全部匹配。67不是跨项目全局唯一依赖数。长路径只用 Windows extended absolute path 读取，不改旧字节。机器可读记录含完整 SHA 与声明行锚点。

未运行 Lean/lake、compiler、checker、数值回放、有限 `decide` 或额度查询，未派代理。有限表的 `decide` 与 mathlib API 尚无执行/内核信用；没有据此声称验证全128次计算、某个数值 Q80 总量或整个传递导入/公理闭包。仅写本批两份 review；前批 review 与作者/生产文件保持冻结。

## upper_chronology

直接读取原导航：cell0/cell1 都有96行，只有 row90 将 mask58 的 A 平面改为 C；cell1 的 selected_mask=129、left-mask 表与实际 literal pattern1 一致。没有拿归档 gain 数值作证明。新模块从自己的全部96行导出 CellGuard；共享四行只导出 Cell0Affine，不借用相冲突的 cell0 完整 guard。

row34 给出 A(t0)<R，而实际 all-eleven 的 first3/mask6 licence 会在该 descending cell 强迫 R≤A(t0)，所以所有实际 sixth 改进均不适用。于是 sixth 精确继承实际 fifth seed，随后证明该实际 seed≤R；没有将真实父值直接替换为 R。rank7 的实际祖先 Rosser own-cube admission 比较使用同一冻结 sixth。原 slot15 的继承、mask26 排除再导出 slot16；chronological42 仅消费相应15+13分支。相反的 mask58 平面与原 descending 条件证明 cell1/cell0 不交。

bank1 保留全盒严格仿射下界、真实 firstStop endpoint 与实际 third joint/rough licences；同一原始 prime-box/frontier membership 供给这些条件，并非假设目标 CurrentParentGuard 或 slot16。尚无该 bank 的统一覆盖或充分小的墙/trim 质量。其余12个未采用域、后续17/18/19、完整58/87及最终物理系数仍欠。报告范围准确，无必需修订。

## upper_fifth

child-specific A/C ratio 使用真实 mask28 与实际 child 下端点，给出 `min(max32 A,max32 C)`。连续盒上的上界由正分母交叉相乘和坐标增量的非负性证明，避免把角点极值当作未经证明的前提。全128 range/e-range/非负 prefactor 的有限 `decide` 仍未执行，本审阅不额外授予该计算信用。

sharp upper4 保留原本的 `x^9/[9(1-x^2)]` 尾项。它与 `log(1+x)-log(1-x)` 之差的导数为 `(4/9)*x^10/(1-x^2)^2≥0`，零点差为零。令 a=b−e，实际条件给 a≥2、z=e/[2(b−1)−e]、y=(a−2)/a∈[0,1)；由对数恒等式与 a>0、e≥0 得 `[a*L3(z)−e*U4(y)]/(ab)≤Q_b(e)`，减去 upper-log 的方向正确。

展开的 L3/U4 多项式与原 refinement/producer 的 rational formula 相同。prefactor 等于真实 V*A；Q80 是真实 rational minorant 乘2^80再取 Int.floor，d≤0 精确回退0，无 all-positive 前提。floor≤minorant≤Jensen≤whole-child positive kernel；all64/owner 的有限求和与半开 childOwner 分割只执行一次。立即得到的是 literal-positive owner integral，需要实际 signed bridge 才能进入真实贡献；本批 Jensen 第三源明确提供该连接。

未计算符号总量，未证明与历史存储整数逐字相同，也未覆盖完整292633 family。窄 ratio/log/floor source target 的报告属实，无必需修订。

## upper_mesh

adoptedOwners 在同一 decoded labels 上取0/e两端实际 selectedFifthCells 的交，并筛两端真实 firstStop；因此能对其自身 J 提供 B13 的原选择/stop verdict。被删 labels 的覆盖没有由此自动获得。

fixedParent 是真实 raw originalBox 与 ambient `Ico [0,19/96]^5` 的相交；max/min 剪裁与体积公式处理空交。omittedParent 是真实 fixedParent 减 baseline adopted union，等同实际 decoded-cell remainder，包含可能的部分 cell。用实际核的可积性得 parent−baseline 精确等于遗漏积分，再以 M乘真实遗漏体积控制。涉及物理不重计时仍需真实 raw-key injectivity；标量求和本身不构造物理分割。

有限 raw bank 的 retained−parent 误差≤bankEnvelope+真实 trimVolumeBank。统一策略先选一个 rational e，后选 q，得到 `<eta/2+trimVolumeBank`；只有保留真实 `trimVolumeBank≤eta/2` 才推出 `<eta`。更细网格、完整 decoder 与双端 verdict 不能代替这一历史 trim 控制。没有额外 owner-count 或64倍因子。

报告明确 `batch_target_source_complete=false`，局部构造/条件式通过；一般归档 trim、全历史 ancestry、same-rho 与完整 upper/K 仍欠，无必需修订。

## upper_jensen

all64 半开 childOwner 对 retained/omitted 的精确分割，经常数1的有限可积求和得到一次 `M*rawOmittedVolume+modulus(e)*rawRetainedVolume`，没有64倍 reserve 或 decoded-owner 重数。

对两个固定 strict-margin named parents，真实 held owner source 从原始正 margin、Gamma/third/rough/own-cube gates 与实际 firstStop 供给 selection。它并未假设目标 rawOwner identity。完整实际 decode cover 与这些 licences 合成 rawRetained=原 parent，从而全128 child omitted=∅；这一零遗漏结论仅适用于这两个 named parents。

量词是任意 eta>0、固定 admissible omega，然后共同 rational e、q、chi=e/20、beforeN 的有限 named J5。reserve 总量由真实公共 envelope 控制到 eta，bank 不在看见 N 后重选。最终229行源码显式 rewrite `selected_namedJ5_eq`，然后使用实际 two-parent integral identity，解决 selectedFifthCells/namedJ5 的接口对齐。

第三源直接消费冻结的 child-specific sharp Q80：借原 actual-fourth/Geometry/record/gate bridge，把 literal-positive owner integral 逐项比较到实际 signed rawOwnerIntegral；没有对有符号 Möbius 和作错误单调性推断。Bool/child/owner 只交换并求和一次，得到实际 `fullSelectedIntegral≥symbolicSharpQ80Total−eta`。总量未求值，历史字节来源未证，全归档 baseline trim 未闭合。最终报告保留这些缺项，`local_named_policy_complete=true` 与广义 batch/task false 一致，无必需修订。

当前第二源活动 SHA 为 `9c440bf9c9ebea9afb08f909ca7e27e30edb076d24f82e93e3e4495b2c0652fc`；旧227行 `20900c8c…` 只作本批修订历史，不作活动 pin。最终三源均已按冻结字节审阅。

## 最终冻结记录

| 项目 | REGISTRY SHA256 | REPORT SHA256 |
| --- | --- | --- |
| upper_chronology | `a8627f6bfb7a8ccd53c81a7fe2c855e0374c781bb54fe56474ae2ed07997b1b6` | `42dec28b49d6822b9fc75a869ae7302fdf9a8ac8ecc84651f5ff1070fe30f29d` |
| upper_fifth | `1db8ecfe5796e5da396bab3daa366dca960b01b4e41355a573ee71b29455ba5a` | `cc2e8d592e076f98afc64b73eb0194a5c4a433c80dbdc77fbe09ef4fcc274cab` |
| upper_mesh | `3b84b703829ed2546b26a1e77ee9270d739d6ad94d8c0dc6eb435273775c76f8` | `bbc4dbd238e28083a49c3eb4c37a14e64d97bb027db960f3f62301fcd8e1d5bf` |
| upper_jensen | `f24b5bfadae0f2cac743278719619b354dcfeec7dbdacb055972dd775aeb3942` | `52364fdbd96c4dd6d52b03430304a83151c614291f8b865856bc102cd4408c5b` |

| 最终源码 | 行数 | SHA256 |
| --- | ---: | --- |
| P4AOriginalAscendingCell1ActualChronology.lean | 382 | `f7bf94542948ace32cd33802b6f72afbd9431e100bc13087e112d070fa4e9e88` |
| P4AOriginalAscendingCell1Affine.lean | 196 | `588af35121292ea1ac16bba9532e3ccbb397bf2006bfd6c1d7128e0c8696f4e3` |
| P5NamedFifthChildSpecificRatio.lean | 176 | `5377f9724f6051056eddae1faf8059fe3cb8a3bbb6b65ff2afa7bec08187a29f` |
| P5NamedFifthQ80FloorSoundness.lean | 188 | `326346be7336aee65f58ff8ee8680e50a48e1ed16704844f5f3eba63def00c58` |
| P5OriginalSharpDirectedLog.lean | 144 | `8d50207ff413c917a6842a48b3fc5d3783d3674a1f0ee7ea50fbab484e466801` |
| P1OriginalFifthAdoptedOwnerBank.lean | 237 | `a52ecf8fd672136f3e2e22289914356094483698020512dd18de6bcde7bf00e4` |
| P1OriginalFifthUniformAdoptedBankError.lean | 150 | `5c0012206c93e05871ead313c5e410217e751073f81e76b3abf6c2806c59973d` |
| P5AllChildrenReserveReassembly.lean | 136 | `3862325bab8e3361432dbe1bdb055b81a8fc5b18c353167e05cb5dc7953c44ff` |
| P5NamedOwnerReserveArbitraryTolerance.lean | 229 | `9c440bf9c9ebea9afb08f909ca7e27e30edb076d24f82e93e3e4495b2c0652fc` |
| P5SharpQ80ActualFinitePolicy.lean | 100 | `ca0d3a5e8b610056814db9d223373b44e9936e28fcda5d0a7a9b4a6665280c30` |

冻结的30c review hash：

- `upper.json`：`e9ced6c13972b3fd1cf41d26975093ec5d3becab95ad38f9b28b6d369b0bf348`。
- `upper.md`：`49d23113912f00fee14b511f769e1426671ef4abd935e88e98103521fad12b4b`。

需要修订项：无。未发现新的原稿数学反例；此结论不扩展局部 source pass 的范围，不增加编译/内核信用。
