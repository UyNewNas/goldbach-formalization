# P1.5：历史系数至首次分歧的已验收证明链

**本轮三模块链已经正式闭合；整个 P1.5 仍未闭合。** 本次完成的是原历史系数的有符号差分、边界支撑及实际首次分歧见证。三者合计 **49 条自有声明，45 条公开、4 条私有**，均通过正常编译、内核回放、完整类型与传递公理审计，并经过独立只读复核。

冻结稿件仍为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en`。本轮没有更换稿件版本，也没有将缺失的解析结论改成假设或新公理。

## 1. 实际新增验收

| 模块 | 自有 / 公开 / 私有声明 | 原依赖复用数 | 原正式源码发布 |
| --- | ---: | ---: | --- |
| `P1SignedExitCoefficientDifference` | 24 / 24 / 0 | 42 | `fbb8d60f796d4781316e95370cbd46131868c1c1` |
| `P1HistoricalBoundaryPolicyDifferenceSupport` | 21 / 19 / 2 | 56 | `96beb9f97836d6832ccffe0dbdc5fd8e9957303d` |
| `P1OriginalHistoricalFirstDisagreement` | 4 / 2 / 2 | 293 | `4a55b304fec91096f3c461fdda7ea2fe3eb46102` |

三次 normal 均只构建对应的新 owner。后两项包含前一项的依赖，表中复用数不可相加作为独立模块总数。已验收的旧依赖没有重新实现、重编译或重新计算验收信用。

公理并集仅为 Lean 的标准逻辑公理 `Classical.choice`、`Quot.sound`、`propext`。完整清单包含私有及生成声明，类型同时保存可读形式与完整表达式；没有靠截断声明范围取得通过。

正式任务依次为 `job_f6a38b9975814857ae189d09b8032ec1`、`job_e11a7ce15000432eb9a8ef370d97e5d4`、`job_a44d125c4e504da1bb5774c808c4a2ea`。三项均 exit 0。Coefficient 的独立只读任务为 `job_b94b9bab9b7943039d8e8e3716fc37ed`；Boundary 和 First 在各自正式任务后启动独立 Python 进程复核。所有独立只读结果均为 `REVALIDATED`，新增 normal/kernel 命令数均为 0。

分项证据与完整验收索引：

- [Coefficient 验收](../p15-signed-exit-coefficient-difference/README.md)
- [Boundary 验收](../p15-boundary-policy-support/README.md)
- [FirstDisagreement 验收](../p15-historical-first-disagreement/README.md)
- [三模块机器可读验收总表](ACCEPTANCE.json)
- [进度与原登记的独立状态](PROGRESS.json)

## 2. 这条链实际证明了什么

**系数差分。** 在同一原素数树上保持 fresh-minus-old 方向，证明原 Möbius 系数差的交集消去、对称差支撑及绝对值至多 1，并把两个保留多项式之差精确改写为共同树首次不同 admission 的原后续子树和。系数先于被测试整数固定。

**边界支撑。** 非零差分产生共同 admission 树中的真实分歧状态；其存储历史来自原 carrier，历史素数属于同一模数的素因子。原局部策略一致性可以将差异定位到相应 boundary owner。

**原历史系数。** 沿已验收的历史系数字典，两个新的公开定理

```lean
ImbalancedChen.P1OriginalHistoricalFirstDisagreement.nonzero_has_changed_rough_factor
ImbalancedChen.P1OriginalHistoricalFirstDisagreement.nonzero_has_actual_first_disagreement
```

从实际 `trueDDeltaRho old fresh ... d ≠ 0` 得到完整分解 `d = a * b`：`a` 属于实际 small Rosser support，`b` 属于原共同 rough support，原 rough mask 在 `b` 上确实改变。随后的见证发生在奇数步，使用同一个 target-deleted rough universe，并且历史中的每个素数均整除完整 `d`。

这保留了原小素数附着及符号方向。稿件里的两组实际代入为：

| 用途 | old | fresh |
| --- | --- | --- |
| comparison | `S false` | `R false` |
| saving | `eight false` | `six false` |

## 3. 修改量与原始证明保持

Coefficient 的 17,943-byte 原始源码未改。Boundary 仅把四处 `<+` 显式写为 `List.Sublist`；First 仅处理同一原因的一处记号。其根因是原源码没有打开该 scoped notation。两份文件的全部 proof bodies 均保持原字节，修改前后源码、双 hash 及正反补丁完整保存。源码整体分别变为 20,356 和 5,545 bytes，不能称整体源码字节未变。

原失败 probe、随后真实成功 probe、首次 normal、kernel 和完整审计分别保留。不存在用成功记录覆盖失败记录的情况。原 SOURCE ONLY 注释属于初次源码来源；已验收源码保持固定，当前状态由日期化验收回执给出。

## 4. P1.5 尚未闭合的准确命题

### 4.1 两个原历史差系数到整原子的连接

现有字典保留实际系数 `trueDDeltaRho`、原 small Rosser 附着和完整乘积上的过滤：

\[
\operatorname{panModulusCutoff}(N,B)<d<N^{599/1000}.
\]

尚需把 comparison 与 saving 两组实际历史差构造成有限整原子族，并证明保持上述过滤和原符号的系数／任意算术测试恒等式。使用已编译的 finite-fallback 家族时，compiler 差异及去掉平方自由约束带来的 collision 必须显式保留并支付。

现有 `Params.rho` 固定为 finite-fallback 的 compiled coefficient，`Params.S` 固定为 `wholeHigh`，并非可以任意填入原 `trueDDeltaRho` 与 `historicalModuli` 的参数槽。首次分歧见证本身不证明这两种系数相等。

### 4.2 对实际整原子族的统一 signed medium 界

完整目标要求：固定稿内合法参数和任意精度 `A > 0` 后，先选择同一个 `C > 0` 与物理 `N` 阈值，再对所有实际 `Index`、chart、HB row、selected slot、允许频率、word 及三个 modulus owners，证明

\[
\bigl\|(I.\operatorname{atom}\ K\ D\ E\ G).\operatorname{signedError}\bigr\|
\le \frac{C\,I.x}{(\log I.x)^A}.
\]

常数和阈值不能放到各行、频率或 owner 之后选择。现有 admissibility 与 auxiliary SW 只提供相应合法性；U06 的已知 signed 结果还限制 rank-three、low-head 和 `U ≤ x^(1/16)`，不能直接当成全域结论。

已有 `eventually_policyRemaining_sub_medium_logAccuracy` 估计的是 `policyRemaining - historyMedium`，最终 count residual 仍保留原 `historyMedium`。本轮继续复用这些 reducer，没有把它们改称最终中段支付。

完整下一目标签名、量词顺序和稿内对应位置见 [剩余目标](review/MINIMAL_REMAINING_TARGET.json) 与 [数学范围复核](review/FINAL_SCOPE_REVIEW.json)。这两份是范围记录，不是含空证明或额外假设的 Lean 定理。

## 5. 新 P3 供应已扣除的工作

本轮同时定向核对了 P3.4、P3.5 的新验收，并取回 P3.6 刚完成的 `job_8a5e401c2bc64687a63644ff4a159b7b` 原归档。该 P3.6 任务新增 7 个 owner、92 条声明，原正常编译、7 次内核回放和完整清单审计均通过。它们是其他分支的验收成果，不计入本轮 P1 的 49 条声明。

P3.6 现在已经有实际 U5 joint cell 到 sorted prime-slot box 的精确识别、任意实测试下的同一系数恒等式、完整模数上界、低／高模数精确拆分、经典低模数支付及正计数余量。BV 以上的 U5 余项也已精确缩为 residual rough rank 至少 4。上述组件均应视为已有。

其末端定理仍保留 `highRankPrimitive`，没有估计该有符号高秩和。新的 U5 `rho` 按 joint coefficient 的符号选择 beta 成员；P1 原字典先按原 rough Möbius 选择附着成员，再乘 fresh-minus-old mask。两者不能未经系数恒等式证明直接替换。实际 U5 的排序识别也保留 `SortedGT`，不自动支付去掉平方自由约束的碰撞误差。

P3.4 的新增实际能量分块和相位接口、P3.5 的实际 C4 归一化与条件化 envelope 同样是可复用的已验收组件；所读接口仍未供应上述 P1 全域 signedError 结论。详见 [P3.4/P3.5 范围](review/BRANCH_GROWTH_READONLY_RESULT.json) 与 [P3.6 新验收补充](review/P36_LATEST_SUPPLIER_REVIEW.json)。P3.6 新补充优先于较早范围快照中关于尚未验收 U5 候选的描述。

## 6. 原登记与对象供应障碍

原 21 项登记仍为 **18/21**。未关闭的三个原登记项是 `P1OriginalSingletonProperPower`、`P1OriginalHistoricalProperPower`、`P1OriginalSingletonAtlasProperPower`。本次三个新 owner 属于后续独立证明链，不能将两组数字拼成原登记 21/21。

原有 23 个第四、第五均值模块以及 Dictionary、MellinVariation、Partition、GroupLog、PolicyComparison 等既有验收继续保留。指定 donor 对象在已查的已知根中未取得，P3 本次可达性检查仍返回 429；原只读接收入口另有随机设备访问失败。没有降低隔离要求、改写原验收或重新编译旧证明来绕过这些边界。详见 [接收入口诊断](proper-power-diagnosis/DIAGNOSIS.json) 与 [本次 P3 可达性结果](proper-power-diagnosis/P3_REACHABILITY.json)。

这些对象供应与执行条件的问题，和上述尚未闭合的数学形式化连接分别记录。本轮没有建立冻结稿件的数学反例，也没有据此宣称稿件错误。

## 7. 原始证据完整性

三个原验收 ZIP 分别包含 84、86、86 个成员，保留完整 owner、operation、原预检、原对象及独立只读结果。控制端已逐项核对所有索引成员、索引本身、归档 SHA-256 和 ZIP CRC。另有两次独立本地收据复核；它们不增加新的编译或验收信用。

最小下一数学连接已经固定为：从 `remaining_trueDDeltaRho_test_eq_pair_sum` 出发，对两组原历史策略构造保持符号、小素数附着与完整模数过滤的整原子分解，再接统一 signed medium 供应。当前总状态保持 `whole_P1_5_complete = false`。
