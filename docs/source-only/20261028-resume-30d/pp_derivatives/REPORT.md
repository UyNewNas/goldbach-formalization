# pp_derivatives 第四批：native rank4 有序 Euler 字典

新增 `P5NativeSelectedFourOrderedEuler.lean`，272 行。前批、生产、Git、看板均未改；没有编译或 checker，正式信用为 0。

本次消除 transfer_lambda 第三批的真实缺口：`native_mixed_chart_tensor` 的全阶 Fréchet 张量界现在连接到 Family 语法中真实定义的 `eulerWord`，没有把两者直接当作同义名称。`wordDirections` 用 head-first 的 `Fin.cons` 保留有序字母串和重复坐标，通过 Mathlib 真正张量递推及常值多线性求值得到 `occWord_eq_tensor`；每个单位方向范数≤1，故点值由张量算子范数控制。

既有 grouped occurrence chain 在 identity owner 下给乘法 chart `p_i*exp(z_i)` 的真实 Euler 字典。随后专门实例化到 `NativeSelectedFourIntegerProfile.profile D side N`，D 是原 original247/native owner/selected-row mask 的有限源数据。对一般 HB owner 映射也保留同一字典，`map owner` 不增字母串长度。

Family 的 derivative 字段要求所有实点及小 N，故源码没有只停在正坐标。非正点的某个坐标落在真实 `N^(lower-width)>0` 支撑阈值以下，其邻域上的 native profile 恒零；局部微分归纳证明每个有序 Euler word 仍恒零。`N<2` 沿原 profile 的实际零分支处理。正点用真实 native 张量界、固定 width、实际两侧 `totalBoxCount` 和 `log(N)>=log(2)` 推出每一固定阶的全局常数，再对有限阶≤r求和并取自然数上界。

端口 `native_mixedEuler D r` 给出一个先于 side、N、所有实点p和长度≤r字母串的正自然数 C。实际平滑数据D固定，因此可用 Family 指数字段 `B=0`。`native_grouped_occurrence_budget` 进一步证明相同C先于任意 occurrence count、重复owner、dyadic U和z；没有出现人为 `m^r` 或重复label损失。

这是原大目标中真实 rank-four 的字典及预算步骤，`local_step_complete=true`、`batch_target_source_complete=true`；全秩覆盖、各实际 CapPlan caller 与独立test u的数据绑定、同掩码reserve和共同平滑逼近仍开放，故 `task_complete=false`。没有用别的rank置零冒充全覆盖，没有把marked t当成u。

依赖raw SHA、安装路径、端口与边界见 `REGISTRY.json`。第三批自己的源码保持冻结 SHA `e74a8e2492758caac1cbd2c9db04bfc610a18233e5b0dea1e2593d7a17575f01`。未发现新的原稿数学缺口。

root 批准静态限定名纠正：两处 `signedCoverBoxCount` 改为其真实定义命名空间 `ActualFourSignedCoverJetPayment`；定理和数学范围未变，未编译。此修订后 D 源码重新冻结。
