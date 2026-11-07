# upper_fifth 第四批：actual child-specific A/B 与原稿 sharp-log/Q80 soundness

交付3个闭合源码文件，共508行。前三批冻结未改；没有编译、lake、kernel、数值checker或Q80总量。所有新增 formal_credit=0。

`P5NamedFifthChildSpecificRatio` 将两条 named parent 的全部128个 actual child 绑定到每个 child 自己的两平面32顶点 maxima，再取较小者。对这两条 mask28 源记录，每平面 residual 的最大值恰好在共同 lower vertex；有限源码证明与 producer32顶点 maxima 精确相同。另用正分母、真实坐标顺序直接证明整个 closed child 的实际新 residual 上界，并给实际 active e 区间。它没有把“顶点检验足够”作为前提。

`P5OriginalSharpDirectedLog` 保留原稿三项 lower3 和四项 upper4 的精确1/9尾项。lower3复用固定版本[Mathlib原始log级数下界](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean)；upper4通过差函数的非负导数 `4*x^10/(9*(1-x^2)^2)` 推出，继而证明 actual Q 的有向下界。原 producer 的 expanded lower/upper 分子分母也给出纯代数恒等式。没有用库中较粗的 remainder 替换原稿锐化式。

`P5NamedFifthQ80FloorSoundness` 用同一 actual child 的 improved b、exact signed d、原整数几何 prefactor、原 sharp-log 有理表达式，再向下取整至2^-80。d≤0保持精确0。给出所有128个 child 的 floor≤actual certifiedJensen≤whole-child kernel，并将完整64 floor符号求和减去原先真实 owner reserve，接到 actual clipped literal-positive owner积分。b允许逐child变化，owner clipping没有被去掉。

这些有限数据的 sign/range/maxima 源码证明写为 `by decide`，尚未执行；本批没有任何checker通过记录。`batch_target_source_complete=true`仅指这两父128child的本批符号soundness与真实对象连接已写完；`task_complete=false`保留原始 broad target。full历史family、archive-to-typed loader、stored floor provenance、reserve达到epsilon预算、buffered joint tree、actual signed physical density及当前K均未闭合。未发现新原稿数学缺口。

精确raw SHA、导入路径、固定Mathlib版本、源码接口和剩余前提均见REGISTRY.json。等待独立源码验收；用户专项负责编译。
