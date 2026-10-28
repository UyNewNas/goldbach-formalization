# transfer_lambda 第四批交付

新增两个文件，共 320 行、22 个声明。第一批到第三批源码保持冻结；第三批 REPORT/REGISTRY 先按 root/reviewer 指示修正了范围。

本批没有再用“候选两边同定义”填补真实 caller 身份。`P5ActualSelectedAtomSmoothCaller.lean` 的 `selectedAtom` 直接读取生产源码的 `originalCell (outerUnion rows) state`、原始 Ico native owner cell 和原 source cube，再定义独立 sharp prime weight；定义中没有 smooth candidate。

原稿允许的是保持真实 mask 的共同光滑逼近，sharp indicator 通常不能与 smooth cover 相等。因此本批证明的是实际分解：

`同一 rho 的 sharp caller = 同一 rho 的 native smooth caller + 原始墙 reserve 上的误差 caller`。

误差在 cube 内由生产 `original_mask_error_supported` 限制到同一 `originalReserve`；cube 外必须处于宽度为原 smoothing width 的真实 collar，未把整个 cube 补集当小误差。计数和 exact coprime mean 都原样保留，绝对支付明确为

`(1 + native amplitude) * Σq |rho(q)| * Σwall-tuples (residue indicator + coprime indicator / phi(q))`。

`actual_rows_eq_signedError` 与 `native_selected_actual_rows_exact` 将这个身份接到原先独立定义的 `actualSmoothSignedRows`，其物理系数就是原来的 `jointPresievedSigma`。物理 mark `t` 始终在 row sum 中，独立 test word `u` 始终在测试函数中，没有混为同一 tuple。`native_selected_actual_rows_wall_payment` 的整数幅度常数直接来自第三批实际 native profile 的零阶预算，并选在目标 `N` 前。

第二个文件 `P5NativeFourFamilyCallerFields.lean` 消费同批 `pp_derivatives/P5NativeSelectedFourOrderedEuler.lean` 的实际 real derivative dictionary 和 `native_mixedEuler`。对同一个 native profile，构造全空间 smooth、真实正指数 lower/product support、有限 prime support、完整 ordered `eulerWord` 预算；其 logarithmic exponent 可以取 0。最后把这个 fixed-rank FOUR 见证与上述独立 sharp caller 的 reserve receiver 联结起来。

这不是完整 all-rank `Family` bank：没有给其它 rank 置零，没有声称所有 CapPlan term 已有正确 original247 state/native cell/selected-row 归属，也没有证明墙 reserve 在完整 signed modulus 求和后达到最终渐近误差。实际 CapPlan 到数据的 source-form licence、其它 rank、全 chart 汇总、proper-power modulus 支付和完整 PP 仍待接齐。因此 `local_step_complete=true`，`batch_target_source_complete=false`，原始完整 `task_complete=false`。

本批源码逻辑范围可以独立审阅；没有运行 Lean、lake、checker 或额度检查。`compiled=false`、`kernel_verified=false`、`formal_credit=0`。两文件 raw SHA、所有直接及显式调用前驱 raw SHA、手稿位置和剩余义务均记录在 `REGISTRY.json`。未发现新的原稿数学缺口。
