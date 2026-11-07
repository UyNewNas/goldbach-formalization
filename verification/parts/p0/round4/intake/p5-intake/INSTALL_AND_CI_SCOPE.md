# P5 依赖证据的安装与根 CI 覆盖范围

固定 P5 提交 `7b1283e4a70874e4fb7004bafad0793069bdea71` 相对直接父提交新增 173 个文件。建议全部按原路径、原字节接入：1 个 handoff、1 个审计 `.lean`、171 个 `round4/s1lowerrosser/` 原始证据/命令/类型/对象/诊断/恢复记录。该集合内部证据相互引用，拆掉原始恢复日志或失败快照会削弱可追溯性。最小安装清单 `INSTALL_FILES.json` 每项只有 `path / git_blob / sha256`。不要复制此 intake 中额外的 context、upstream-api、decoded-objects 或 P0 review 文件，也不要从 P5 旧祖先接入 InitialSource/InitialMean 候选。

敏感内容扫描没有发现 token、Bearer 凭据、私钥、签名或临时下载 URL。唯一域名规则命中是 `restoration/raw/reused-P1-cache.log` 第 5 行的公开无签名 Mathlib 缓存入口，query、userinfo 和 fragment 都为空；可保留原字节。没有需要排除或改写的文件，原固定 SHA 不受影响。

## 可直接用于最终回执的范围文字

本批接收的是锁定 goldbach 依赖中 `MathlibNt.SieveTheory.LiLiuGoldbachS1LowerRosser` 的单节点证据：固定源码已由生产者完成严格编译、原装目标模块重放，以及实际 defining-module 全部 8 项声明的传递公理审计与完整类型导出；P0 核对了固定提交原件和编译、重放、审计之间的相同源码/对象/导入绑定，复用这些成功记录。本次接收不增加 `ImbalancedChen` 自有生产模块数，不宣称重新重放其整个导入闭包。

对现有已验集成 SHA `28fd630ef7cc38eba86beb6c0ba123336b5d05f2` 的固定源码图审查表明：`ImbalancedChen` 根展开到 272 个项目源码节点（含根）和 820 个固定 goldbach 节点，剩余外部叶仅为 Mathlib、Lean、Batteries、Architect；S1LowerRosser 不在该依赖闭包内。静态图存于 `ROOT_DEPENDENCY_SCOPE.json`，这不是编译器或内核回执。若新集成根和显式 CI 入口未导入 S1LowerRosser，则新根 `lake build`、根 leanchecker、根公理/类型导出均不得被描述为覆盖这 8 项。它们的验收证据仍应单列为上述 P5 固定单模块回执；只有新入口确实导入并实际执行成功后，才能另行记录对应的集成验证范围。

已接收下界使用真实有限差载体、单位权、严格端点、真实 Rosser 权/totient 主和，以及原标准 AP 前缀误差，没有把实际解析目标作为新增结构或类型类假设。该模块只供应有限主项减误差下界；归一化误差支付、完整 beta 密度/主尺度、十一项 Chen 均值、解析 c 和 hLower 仍需真实供应。同一实际 rho 的 K 密度界及 hUpper 也仍未由此获得。最终入口仍保留明确的 hLower/hUpper 条件；P5 只等待 P4-A，不需要 P4-B。
