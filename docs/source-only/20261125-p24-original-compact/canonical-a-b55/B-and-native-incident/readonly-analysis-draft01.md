# B 原 rfl 失败：首轮只读定位

状态：仅完成源码分析及诊断稿；没有运行诊断，没有修改生产、原选项、数值、判据或审计规则。根代理负责提交和解释真实结果。

## 已确认的事实

原 B 任务 `e8a3e965a5dd4185b15e8cca81de00b6` 在 b55 源 pin 下通过 zero322 前置检查，随后原第一条定理的 `rfl` 在 4.312 秒失败。原日志只报告 `cachedHistoricalEndpointCheck` 与 `true` 的定义等式检查未成功，没有报告已归约到 `false`、超时或 OOM。全部正常后检通过；失败后 registry SHA256 为 `3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445`。

锁定 Lean commit 为 `62eed1db4d67327ec8120be05f1a1b0847d74561`。以下源码原件已保存在本目录，其 SHA256 与 URL 见 `pinned-evidence-index.json`。

1. **错误发生在 Meta 前置检查。** `MetaRfl.lean` 中 `Lean.MVarId.applyRfl` 先执行 `approxDefEq <| isDefEqGuarded lhs rhs`。只有成功后才构造并 assign `Eq.refl`。实际日志文字与此处的失败分支一致。因此现有结果没有提供完整闭计算的 kernel 验证结果。

2. **`maxRecDepth = 0` 不会立即超界。** `Exception.lean` 的 `withIncRecDepth` 明确检查 `max != 0 && curr == max`；当 max 为零时直接进入增加深度分支。`CoreM.lean` 的 `withOptions` 原样把 `maxRecDepth.get options` 写入 Core 上下文；`MonadRecDepth CoreM` 读取这个字段。选项文档也明确零表示无限制。不能通过擅自更改原 B 两个局部零选项来试图修复。

3. **guard 捕获范围须结合 CoreM 实例解释。** `MetaBasic.lean` 的 `isExprDefEqGuarded` 源码为 `try isExprDefEq a b catch _ => return false`。但普通 `Core.tryCatch` 会重抛 interrupt 与 runtime 异常，其中 `isRuntime = isMaxHeartbeat || isMaxRecDepth`。因此它可以把普通错误或其他 internal 异常转换为 false，但不能据 `catch _` 声称它吞了所有资源异常。此前关于“任何异常”的宽泛表述已向根代理即时更正。

4. **尚未定位实际不可约常量或 Classical 实例。** 当前 cachedRunFuel / runFuel 保留原 Nat 递推、guard、成功后递进及错误/停止分支；cachedKeepRunning 源显式通过 `inferInstanceAs` 提供原 Nat/Rat 合取的 Decidable。读到的源没有给出 Classical choice 是本次失败根因的证据。源级检查也不能代替实际 elaborated declaration value 或 raw 异常。

## 首轮最小诊断

`P24CachedEndpointRawDefEqDiagnostic.lean` 精确 2,863 字节，SHA256 `2eb7dc403ee25098cfe711ab887d3988fe6c87a8872cca758d49ed36dd06cf4e`。

它只导入已经编译的 CachedRun 和 Lean；保留原两条 `maxRecDepth 0` / `maxHeartbeats 0` 局部选项。它对原 Bool 等式两端只执行一次 `approxDefEq <| isDefEq lhs rhs`，不再调用 guarded 版本。begin 输出记录实际生效的选项和递归深度；正常返回记录 Bool；异常记录种类、完整消息、深度/心跳/interrupt 分类并原样重抛。每条输出即时 flush。它不赋 endpoint proof、不核验 Eq.refl、不安装任何观测表或 state/evaluator definition。

这个 probe 保留原闭目标，不承诺仍只耗费 4.312 秒。如果前置检查本身继续深入计算，仍以原外部 job / Lean 资源界限终止；没有增加任何资源。首轮目的仅是区分“普通 false 返回”和“被 guard 遮住的真实异常”。

执行草稿为 `p2-B-raw-defeq-b55-draft01.sh`，其完整 SHA 和对应 Python/tail/builder 在 `raw-defeq-wrapper-draft01-manifest.json`。它从已审 shape wrapper 复制完整 source/runtime/native/full324 setup，固定当前失败 registry 与原 B 失败日志，调用原只读 verify_compilation 检查321和A102。只创建新的诊断目录和 lossless stdout gzip。每种子进程结果后均检查完整324 source/object/native snapshot、registry、原工具/runtime、原A审计目录及B失败日志不变；完整读取并验证 gzip 原始字节 SHA。保持32 MiB余量。原子进程非零不会被改成成功，rc0但后检失败返回125。

本地验证限于 Python AST / compile-only、bash -n、嵌入 Lean 源字节与复制 helper 逆比对；未执行 Lean。scope 代理已独立只读核对 Lean 与 execution tail，没有发现具体问题。无论 diagnostic 的返回值为何，都不授予原 B compile、kernel replay、owned audit 或324完成 credit。

## 后续界限

收到真实结果后再选择下一步。若出现明确异常，先按该异常定位；若正常返回 false，才使用受控 WHNF / actual elaborated instance 检查追踪停点。目录内较大的 `P24CachedEndpointBlockedWhnfDiagnostic.lean` 是未测试的备用草稿，未作为首轮提交，不能用其输出替代原闭目标或门控。
