# medium_s2 第四批：同 D 全 mixed 尾、collapsed filter 与实际 receiver Λ

本批五份 Lean 共 1,138 行、60 个定义/引理声明，均为文本闭合源码。未运行 Lean、lake、数值 checker 或内核验证，正式信用 0。第一至三批源码冻结未改。`local_step_complete=true`；原完整 `task_complete=false`。以下仍保留原范围 (7) 的明确模数门及完整 preliminary carrier/window 连接，因此 `batch_target_source_complete=false`。

主结果在 `Part3OriginalS2FixedDMixedTail.lean`，不是较弱的 whole-family V0 界。`fixedDFamily` 一次取所有 `D≤small<2D`，其内全部 r、s 独立 roughFiber 都保留；没有要求 r、s 同箱，也没有逐个 exact d 调用误差定理再相加。`fixedD_level_lower` 在算术求和前证明 `q*small≥Q1*D`，随后对真实子族几何直接取 `Y=Q1*D`。

`fixedDModulusPacket_return` 保留原自由 n2 因子，得到真正的 `V(D)/l` 返回，其中 `V(D)=M*N²/(Q1*D)`。`fixedDTail_eq_collapsed_packets` 将这一个全 D 族重排到原 `sm(l;z)>y` collapsed filter。`fixedDTail_le_collapsed_arithmetic` 再以固定除数阶 5 汇总。最后复用已写原 (8) 的任意对数支付，`exists_fixedDTail_arbitrary_log` 的 C、X 先于 **全部正 D、atom、移动 residue**，给出

`‖fixedDTail(D)‖ ≤ C * V(D) * log(x)^(-A)`。

`fixedDActualCoefficientSum_eq_family` 和 `fixedDActualS2_eq_kept_add_tail` 使用原 `s2Carrier` 以及同一个 Gevrey `paperPsi(q/Q1)`、`paperPsi(m/V)`，证明原 full/kept 差正是该尾。`exists_actualFixedDS2_deletion_arbitrary_log` 已直接给这个实际源码差的范数界。`fixedDTail_eq_all_mixed_owners` 以独立 `(log2 small, log2 r, log2 s)` 有限 owner bank 精确覆盖该族所有 mixed bins。

`Part3OriginalS2MixedFamilyGeometry.lean` 将第二批纯几何扩到真实 coefficientCarrier 的任意有限子族，只要求该子族的字面 `q*small*r=l`、真实支持以及 `q*small≥Y`。这是上述同 D 主线需要的端口；没有把 H、Shiu 包界、S2 或 medium 作为前提。其证明仍保留 φ(q*small*s)，自由 n2 支付为 2N，原三元重数支付为 τ(l)²，s 和使用已有普通除数均值。

`Part3OriginalS2FullMixedCollapsedTail.lean` 给新双端 ψ 非零项到原 collapsed filter 的精确适配。只从真实非零 Λ tail 取见证，复用 `tail_both_moduli_in_collapsed_filter`，没有套用依赖旧 m cutoff 的旧项函数。它另给包括全部 d 的 V0 全族界和有限 owner 重排；`Part3OriginalS2FullMixedTailPayment.lean` 保存该独立 V0 界及共同标量 log 支付。**V0=M*N²/Q1 的界未用于吸收 D**；同 D 主线直接重新使用 `Y=Q1*D`，所以不依赖“超对数小量可补回任意 x^o(1)”这种错误推理。

本批还立即消费 medium_s3 新的精确 cutoff 端口 `Part3MediumReceiverCutoffArithmetic.lean`（SHA `5575c681f5a7d5cf7530d6082a6fe56f8a52f14cb38ef0bf543b313f400e233d`）。`Part3OriginalS2ReceiverLambdaBinding.lean` 利用 `receiver=floor(z)+1/2`，将原 `p≤z` inclusive split 精确送到 strict receiver split；原 z 恰为素数也成立，analytic z 与 y 均未更换。

其中 `lambdaSmoothKept_eq_actual_receiver_keySum` 已把原 kept Λ 等同为 **现有实际 `lambdaTrim`** 的 receiver key 纤维和。它复用 `ownedSlice_eq_image_trimmedChoices` / `sum_ownedSlice_eq_trimmedChoices`，并证明物理 γ 纤维与独立构造的 `lambdaTrim` 相同；没有假设未来 binder，也没有继续留下 no-boundary-prime 条件。

仍未完成的内部连接：

- 从原 MediumAdmissible 的长度条件/范围 (7) 实例化 `physicalCap≤floor(x^(4/5))`。本批把它作为明确真实模数范围门保留，未将其重新命名为外部 primitive。
- 接原 preliminary `literalS2` 的全部共同 key、q/m carrier、个别 fixed windows、删除/恢复门与 primitive mean。已完成 receiver 算术 Λ 端口不等于整个二次式 binder；尤其不能把两份 Λ 的独立 key 展开直接当作“同一个 key 的平方和”。
- 全 S2 的 principal/Poisson、rough-gate removal 与 exact-product restoration 的整体合成，以及完整 medium 命题。

原始 Shiu 仍使用前批已经准确列出的 `PrimitiveShiuTauBoundary`，其基础经典定理证明按用户范围递延；本批只消费实际原始接口与前批真实返回。未发现可证实的原稿数学错误。本批解决的尺度/receiver 问题均为实现或接口范围问题。所有源码、依赖和先前冻结字节的 raw SHA 见 `REGISTRY.json`。
