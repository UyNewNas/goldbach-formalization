# 第二批 certificate_enhanced

已针对 actual `enhancedL6Box i j` 的 h→mu 与 a→h 两条 512 等分网格，补全五个弦候选的 directed denominator guards。

宽度由源 affineRange 的负斜率角点规则直接化为常数步长 dt、du：普通二候选为 dt/2+du、5dt/2+du；增强二候选为 (dt+du)/2、5(dt+du)/2；singleton 为 dt+du。证明在所有 i,j 上完全相同，且逐项以精确有理数比较证明至少一个 Q80 ulp，再复用现有 `point_lo_pos_of_one_ulp_le` 得 literal lower integer 严格正值。没有用“正宽度自动给正Q80下端点”这个不成立的捷径，也没有执行 512² checker。

新增 `actual_box_positive_ordered` 同时消除正矩形的外部几何前提。主定理 `actual_enhanced_ordinary_Q80_lower` 因而对任意 `i j : Fin authorPairs`，直接把实际 `ordinaryLower actualSf actualLog (enhancedL6Box i j)` 的 Q80 解码值接到第一批的真实 enhanced ordinary integral；最终定理没有 hden、正性或顺序假设。eligibility 始终采用 literal 源码判定，五候选按最大值处理的证明复用第一批冻结文件。

这一第二批窄目标源码闭合，`local_step_complete=true`、`batch_target_source_complete=true`。按原始完整30目标口径，`task_complete=false`；完整证书目标与主定理继续开放。所有代码尚未编译，正式信用 0。h bank、源整数输出fold、原始mask/fibre、Δ8 reserve、current c 与独立 floor-proxy 上界继续开放。未识别新的原稿数学缺口。

只新增本目录的 Lean、REGISTRY.json 与本报告；第一批与生产源码均未修改。直接与关键传递依赖的 SHA256 及模块安装映射见 registry。
