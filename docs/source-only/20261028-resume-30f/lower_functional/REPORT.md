# lower_functional 第六批 F 源码交付

本批四个 Lean 文件共 598 行，均为未编译、未作 kernel 验证的源码。E 的三个 Lean 文件、REGISTRY 和 REPORT 的最终 raw SHA 已重新核对，保持冻结。原完整任务及整项 F target 均保持 false；local_step_complete 只登记下面已写出的证明链。

`P2N48LiteralHighQueryGeometry.lean` 从原 n48 整数端点直接证明未裁剪 rawQueryLower/rawQueryUpper 的整数分式身份，以及所有 high-band 原生盒的 `2 ≤ rawL ≤ rawU ≤ 8`。这是符号端点不等式，没有执行行数据或 Omega 检查。独立 Omega 作者在此基础上冻结的 `OriginalPairedN48AllNativeQueryGeometry` 进一步覆盖两种 term 的全部原生盒，包含网格对齐的闭右端点；其实际 argument containment 与 global raw scan 语义供后续接收器使用。

`P2N48OriginalHighBlockWeights.lean` 将 independent replay 的实际 J112 `block_mass/weights` 指令翻译到四种 high-band block。保留原 48 项反向 Horner、`/97` log tail、幂、`J(1!)` 除法、四角带符号乘法、`mom[j+1]=(j+1)*mom[j]-ex*L^(j+1)`、交替 `(-1)^k choose(r,k)`、从 `J(0)` 开始的 List.foldl 和从 `J(1)` 开始的左结合 block 乘积。原 ln 的 range-reduction 在这些 ratio 上为零步，末尾的 `0*LOG2` 用 token 等式消去。原相邻端点对相等测试也由符号证明识别为四种 high pattern。

真实 mass 不是这段程序的定义：`original_high_row_token_contains_trueMass` 消费冻结 E 的 half-open/closed a.e. transport、真实 Fubini 和带额外 inverse-z 的三种 tied moment，再证明实际 `parentUnweightedMass (fullParent r)` 落在原程序 token 中。适用范围是 term=1、iw≤iz≤iy；`originalRowZToken_contains_formula` 对任意记录的公式包络不被解释为 low-band 的真实质量。96 个固定 bin ratio 的正 log divisor 只写了 closed `decide +kernel` proposal，未执行。

独立 Omega F 接收器绑定同一个 `rowOriginalQueryToken r`、`originalRowZToken r` 和同一个完整 SourceRow，包括原 ordinal、key、method 和 Q80 floor。原 `stored*P112 ≤ max(0, baselineLo-costHi)*Q80` 检查没有被改成 unclamped 检查。零 floor 分支使用生产 `P2SeedOmegaGlobalEnvelope.actual_buchstab_global_cap` 的真实解析上界与实际 raw argument ≥2；它不以 ceiling(C0) 替代真 C0。`actual_required_all_row_old_cost_proposal` 的 producer、log 和实际 retained-row floor 决策全是未执行源码，未报告任何具体 numerator、数值或通过结果。

`P2N48RetainedPriorityRemainder.lean` 使用原 ordinal-to-key decoder 和 half-open box 的真几何唯一性，证明本 crop 内排除的 priority/其他 method parent 在相同 adopted mask 下落入 uncoveredDomain。随后证明精确集合分拆和实际 kernel 的积分可加性：

`uncoveredCost = excludedRawRows 的实际成本之和 + outsideRawCropCost`。

这里的 priority 域只是原 archive crop 内的同 mask parent；没有把它说成全部 40000 个 priority parent 或 516779 个 child 的覆盖，也没有假设 priority child maximum 等于 parent 积分。crop 外的实际域保持显式。

`P2N48LiteralDirectedFunctional.lean` 单向消费上述独立接收器，消去原 hOld、真实 Z-enclosure 和 check=true primitive，形成 retained actual cost、whole actual coefficient 及正确负号方向的 lower-functional 源码定理。完整实际成本仍为 retained + excluded + outside 三项。既有真实 nativeJoint harmonic supplier 在固定 deletionMask 后 N→∞ 的极限也被接到完全相同的三项；这不是新增的 AP/计数密度定理。

原稿 897–905 要求 U10/U11 在同一四前缀分区选最小成本，并以 priority refinement 替换 parent；1354–1369 明确负上界需要整个 retained domain、全部 ordered/tied n48 行。本批保留这些边界。仅 retained method-zero 的真实上界不能把 excluded 或 outside 两项设为零。

尚未解决：所有新旧 finite proof proposals 的实际可归约性、elaboration、资源和 kernel 验证；原实际 endpoint/numerator 字节证据及 finite containment 的成功执行；全部其他 method、priority child replacement 和 crop 外成本的数值上界；完整 signed distribution/AP 密度及十一项 lower 主链。Omega 接收器的 `.toList.all` 有限项也未执行，不宣称其计算实现已经验证。没有发现新的原稿数学反例；这些是明确的实现和验证缺口。

依赖图是 E real-moment/source → F literal weight；独立 F raw-query/source → F Q112 receiver；二者 → F required-row bridge → 本目录 final functional。没有 final functional 反向供应前提。精确 raw SHA、安装/import 映射、每项真实前提及未执行决策列在 REGISTRY.json。

未执行 Lean/lake/compiler、任何 finite/large numerical checker/replay、额度查询或新代理；未改生产、旧 batch、其他作者、Git/index 或看板。`compiled=false`、`kernel_verified=false`、`formal_credit=0`、`ready_to_install=false`。
