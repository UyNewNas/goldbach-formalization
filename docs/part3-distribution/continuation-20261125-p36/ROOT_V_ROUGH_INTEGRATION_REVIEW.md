# Root V 与 rough endpoints 正式路径接入：独立差异审查

审查由 p36_cache_review 在接入前只读完成。审查基点为
`b341a4adba19a3ecc7ac31c7e25a04240b9f0424`；准备记录原字节保存在
[ROOT_V_ROUGH_PREPARATION.json](ROOT_V_ROUGH_PREPARATION.json)，SHA-256 为
`083472e40275225add19d45749b3990a0af91459b8b777b3e16b01b500a77c99`。

## 审查结论

没有阻断项。审查者从三个冻结文件的 raw bytes 出发，按准备 JSON 的顺序应用
RootV 两条、Coarse 三条替换，每条唯一命中，逐字重建出准备稿；RoughEndpoints
全文件字节不变。未发现隐藏修改、新增假设、改变声明参数或结论文本、替换原始
rho、改写数学构造。冻结候选尚无已接受的 elaborated type，本审查不声称此类
已编译类型等价，也不供应 Lean、kernel 或公理验收。

| 模块 | 精确 SHA-256 | 全部差异 |
| --- | --- | --- |
| RootVInputs | `9f504bc69d73f8c5d348e3b2a6e802818e02c10f5429691cfba718ae23f36662` | List scope；同一 buffer 不等式的显式 Rat cast |
| CoarseRootV | `66bf2e863e5391831f15d1706064e74a84a5d0812077701994b298ac8cccc00d` | 同一 epsilon 不等式的 Rat cast；显式 m_aux；abs_add_le API |
| RoughEndpoints | `beb38ce7f666d8e60fa39a03c169871b11503a19b93a50fc0cc2a955d7a79c4a` | 无 |

适配依据是已保存的 BufferedRoot 第 21 次 cast 诊断、PairReceiver 第 17 次
mesh 推断诊断、count 分支第 16 次 abs_add unknown identifier，以及此前的
List scope 修复。它们是同版本的同模式后续修正，不是这些新候选已经直接报错。

## 独立依赖复核

基点的 261 个主源码全部匹配 manifest SHA；仅加入三个候选后为 264。
RootV、Coarse、RoughEndpoints 的项目闭包分别为 258、258、260，联合为 261；
missing/cycle 均为 0。117 个显式 external imports 与准备记录一致。
Mathlib.Topology.Instances.EReal.Lemmas 原本已由 CurrentMainTheorem 导入，
只是旧 inventory 少列一项；候选没有增加外部依赖。这里不把显式外部入口计数
冒充外部包内部递归依赖的验收。

联合闭包不使用 P2OriginalU5RootQ、P3OriginalU5PhysicalModulusCap、
P5OriginalU5NativeRootCover；主 source set 仍保留三者。qPoint_cast 已由既有
主源公开，不重复应用历史 visibility patch。runner 未改变。

## 审查建议与实际接入顺序

审查时建议先核证 main 成功 archive 再接入。main 后来已确认 TIMED_OUT，
只读诊断任务前有长队；该建议并未被标为已经满足。根代理基于上述独立依赖图，
将纯源码接入提前，保留 main 原固定 pin、全部已有源码和原失败证据，不同时
重排编译，也不把接入记为 main 或新模块成功。这个顺序调整记录在
[ROOT_V_ROUGH_INTEGRATION.json](ROOT_V_ROUGH_INTEGRATION.json)。

每个 owned 新模块仍须 fresh strict compile、bundled kernel replay、完整
defining-module declarations/types 及 transitive axioms 审计后才可获得验收。
完整 P3.6 的原系数 whole-atom tensor/admission、公共 physical Q 等义务保持开放。
