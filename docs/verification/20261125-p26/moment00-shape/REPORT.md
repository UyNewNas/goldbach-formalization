# 原 moment cell00 的完整形状证明

新增 `P2OriginalSaving19Moment00Shape` 已通过本地正常编译和独立 leanchecker。6 条公开 theorem 检查了已由原 parser + 原 decodeMoments 得到的真实 `momentConcrete00`：全部 9 项 metadata、56 条原记录的数目、每条记录的 simplexId 等于原索引，以及每条记录恰有 10 个 Q80 槽位。

metadata 固定原 cellId=0、完整 geometry witness 文件名、dimension=8、verticesPerSimplex=9、factorCount=10、logDegree=6、expDegree=3，以及 2^80 / 2^96 两个分母。量词覆盖所有 `i : Fin 56`；没有抽样或遗漏最后一行。

`row_bound` 与 `row_lookup_no_fallback` 对每个实际索引证明数组界和 `!` 读取等于带界读取。因此这些 shape 检查没有通过 Inhabited/getD 默认值兜底。`row_ids_and_floor_sizes_bounded` 又把同一记录 ID 与槽数结论明确写为带界数组访问。

本次不证明保存 floor 的数学正确性，也不冒认完整几何 CellShape、RowShape、其它 12 个 cells 或完整 P2.6。最终把这些具体值结论接到新版 Core 的 `moments 0`，仍需其真实 input maps/Core/Archive 接线与相应验收。

## 验证与复用

正常编译 2.109 秒，采样峰值 2,187,411,456 B；独立 kernel 2.002 秒，峰值 1,851,883,520 B。两者使用同一 2,480 字节源 SHA `1c077c3ed062c0682fe11af0b530458b734b490f4415f6d7d77323e26cd11159`，同一对象 SHA `c8c151d48f14c9ab0b416c026443ce8ed329cf3336ddcc6808edd067db82f8b6`。六项打印 axioms 的并集只有 `propext`。

全部 42 个供应者 source/objects 从已通过的 moment00 typed 闭包逐字复用，前后逐项核哈希，没有重编。其 source bytes 也逐一与真实 Git commit `77c23a2a530ce8d34ec79f88181817072024d4a9` 核对。新闭包为 43 个项目模块。

资源预算保持 4 GiB / 180 秒 / 单线程；Lean commit `62eed1db4d67327ec8120be05f1a1b0847d74561`，Mathlib pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。这是本地 normal/kernel 结果，不是 P1 全部 owned 声明审计。

## 保留的失败与修正

第一次 normal 在 `getElem!_pos _ _` 的两个隐式位置误推断 container 为 Nat，产生类型类错误，没有对象。该失败日志中的自动 error placeholder 仅属于失败 elaboration，不是已接受证明；失败源和回执保留。v2 只把这两个参数改成实际 array 和 index，所有 theorem 陈述、原数据和其余证明字节均未变；随后 normal 和独立 kernel 均成功，最终没有非标准 axiom。
