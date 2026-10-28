# transfer_lambda 第三批：真实 native rank-four 测试函数

交付 `P5NativeSelectedFourIntegerProfile.lean`：254 行、22 个声明。未编译，正式信用为 0。`local_step_complete=true`；完整 all-rank Family 构造尚未完成，故 `batch_target_source_complete=false`、`task_complete=false`。

原稿 258–277 行的 `W_N` 是独立 labelled original-prime test word `u` 上的几何函数；CapPlan/marked word `t` 参与的是物理 `rho_N`。两者不能直接认作同一个变量。本批因此没有把 CapPlan 的 sharp arithmetic selector 塞到 `u` 的 smooth profile 内。

定向核对找到了真正可构造的 native rank-four 源：`P5ZU1011OriginalMaskSmoothBoxRealization.signedSmoothCover`。其参数是原始 247 状态、实际 native owner cell、同一选中 paired-row mask、固定 smoothing mesh 和 width。它不是任意 Part3 `W`，也不是 rank-two P4B 代用品。

新文件用这些有限参数定义 `Data` 和实际独立测试函数 `profile/primeWeight/integerWeight`；正实坐标上取同一 native signed smooth cover，非正坐标上取已证明光滑的零延拓，`N<2` 时归零。`defaultData` 明确选 `width=1/1000`，直接核对原始 `lower=417/5000`、`upper=59/250` 的两项安全余量；共同逼近需要的更细 width 仍可按同样余量构造 Data。

新增实质连接有：

- 从真实 lower/product support 推出每个非零整数坐标都位于 `[1,N]`，从而证明完整 integer bank 有限及 prime support 有限。没有把有限性留作 Family 字段假设。
- 构造这个 native profile 的真正 `Licence`，证明其在独立 Part3 prime tuples 上精确等于原来的 `currentMaskFourWeight`。
- 把原来同 mask 的 inner/outer smoothing sandwich 接到该 prime weight；没有把 sharp indicator 与 smooth function 当成相等。
- `native_cover_binding` 仅给候选自身的定义一致性实例，**没有补齐独立实际 selected atom/caller 的原始 binding 缺项**；实际 signed-row box count 的全阶 Fréchet chart tensor 预算已接到同一个候选 profile。
- 从该实际 tensor 预算的零阶推出一个先于 `N` 和 inner/outer 方向选择的整数幅度常数。这里没有增加 arbitrary `Wnorm` 假设。

尚缺的关键数学实现是 ordered `Family.eulerWord` 与 mixed multiplicative-chart tensor 的字典；有 tensor bound 并不自动等于 Family 的 syntactic `mixedEuler` 字段。本文件也没有证明所有实际 CapPlan term 已对应这个 original247 state/owner/mask，更没有给其它 rank 置零后冒称全 rank 覆盖。完整 native Family、各实际 caller 的 licensed smooth approximation 及相同 rho 的 PP 仍开放。

只修改本任务 30c 目录；前两批冻结。`REGISTRY.json` 记录直接 import、显式使用前驱、手稿 hash、安装路径和全部剩余义务。未运行 Lean、lake、checker 或额度检查。未发现新的原稿数学缺口。

Root/reviewer 冻结范围纠正：本批只接受真实 native rank-four 支撑、有限性、Licence、tensor 和零阶幅度。候选自身的等式不计作实际独立 caller 身份的进展，后续必须读取并连接独立定义的原始 selected atom。
