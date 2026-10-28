# lower_square 第二批：实际 signed rho 小因子扩展

新文件 `P2OriginalSelectedNativeSmallExtension.lean` 共 246 行、11 个定理，完成一个实际小素数扩展步骤。第一批所有文件保持冻结。当前 `local_step_complete=true`、`task_complete=false`；尚未编译、内核未验、正式信用为 0。

本批先读了第一批独立 lower review，按其“实际 native atom 与同 cap 后继连接仍缺”的边界继续。核心不是另给一组小素数平方支持作为输入：从真实 `activePairs policy N enum w z L` 的非零 signed coefficient 取出它实际使用的 beta 符号。非负 rough 系数使用已存在的 `actual_minus_residual_well`，保留所必需的 `w²≤L` 首素数截断；负 rough 系数使用本批由实际 `upperWeight_active` 的原始立方集测试推出的 `actual_plus_residual_well`。因此，规范小因子词 `s.primeFactorsList.reverse` 在真正小层级 L 上的 D-well 支持是结论。

随后，`append_unselected_same_cap` 把这段新词以 false 标签接到旧 SourceForm 的带标词。旧选中标签逐项不变，完整门槛以实际完整旧乘积 B 开始，选中补集门槛以 A·C=B 开始，所以两者恰用同一 residual budget，保持同一个物理 cap。该扩展也可供实际 rough descendant 的原始 D-well supplier 使用，但本文件没有发明该 rough supplier。

实际应用 `actual_signed_small_extension` 保留真实 `(s,r)`、原始 rho 的符号系数和同一物理 cap。旧词的乘积为 `B*r`，预算为 `(B*r)*L≤N^cap`。实际 small-support 证明每个新素数严格小于 w，而旧词的物理 cutoff 为每个旧素数至少 w；这给出追加词的真实递减顺序。复用现有唯一分解与 sorted-union 字典，证明追加词恰为 `((B*r)*s).primeFactorsList.reverse`。重复值与标签全部保留；没有宣称外部 B 与 s/r 的未证互素性，也没有据此声称完整乘积已平方自由。

仍需实现的完整目标：从实际 L5/L6 已选分支与真实冻结父历史产生 rough 后继词及其两套门槛；从该真实 rounded cap 推出每个分支的剩余预算；构造并连接覆盖 W/tent 的实际有限 bank；必要的碰撞/平方自由支付；再接同一 rho 的 AP/BV/PP 与 signed lower mean。这里的 incoming gates 和 budget 都是明确的前一阶段接口，没有被冒充为已构造的实际全局分支供应。

原稿核对范围为 280–297、720–735、808–817 行。未发现新的原稿数学缺口。本批仅做源码静态检查、第一批冻结 hash 核对与依赖 hash 登记，无 Lean/lake、数值 checker、测试、额度查询或 Git 操作。所有 source-only 导入的路径、安装目标及 SHA 均在 REGISTRY.json 明列，供编译专员后续处理。