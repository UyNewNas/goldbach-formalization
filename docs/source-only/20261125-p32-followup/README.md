# P3.5 后续增量：completed 零差项的物理外层费用

**状态：`SOURCE_ONLY_NOT_COMPILED`。** 此处保存本轮手稿核对中写出的 550 行增量，尚未经过 Lean 编译、kernel replay 或完整声明／公理检查。它不由 `ImbalancedChen.Part3Node32` 导入，不计入 P3.2 的六入口、130 模块闭包或其 138 条历史终端声明。

看板第 8 版中，`P3.5.child-3` 负责原始全族的共同模式及 zero/tail 重组，`P3.5.child-5` 负责 OriginalData 的两个 zero lane 归一化费用。因此停止将这部分扩张为 P3.2 的完成条件，并在此保留工作，供对应节点继续。

## 已写内容

- 在同一实际 weighted completed 能量中作 zero/nonzero 精确拆分，保留非零部分的符号。
- 将局部零差界接入真实 `finiteLogScalar` 的平方上界，并在实际 tag/residue carrier 上使用 Fourier 系数质量作加权 Cauchy。
- 写出保留 `tau(D)^2 / D^4` 的精确物理归一化。
- 通过已存在的除数次幂界及收敛级数支付有限 `D` 与 `delta | D` 的总和，无需假设 `D` 是 `x` 的小次幂。
- 保留全部 `(g*l)^2` 根／剩余类费用，得到保守的 `C*G*L^3` 枚举界。

对应冻结手稿为 `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 的 `paper/release-20261106/en/analytic-appendix.tex`，尤其 `ana:W4-expansion`、`ana:bare-Cauchy-factor` 及零差项的物理返回段落。

## 继续时的输入与剩余义务

`SOURCE.json` 冻结本文件 SHA-256 以及唯一额外历史供应模块的 commit、路径、SHA-256 和 Git blob。该供应模块已在可靠的远端树中存在，未再次复制进本轮 P3.2 的正式模块目录。继续时先复用它及其已有依赖。

此草稿尚需实际编译修正。数学组装仍需将原始外层按实际 feature/root 分纤维，把同一个模式 `m` 移至全部有限标签外，并在原相同权重下通过求和极限接回实际标量。非零 completed 核继续保留给 P3.5 的谱返回。不能把原标量直接等同于 zero/nonzero **能量**的线性和。
