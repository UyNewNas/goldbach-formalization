# coefficient_physical 交付

本轮新增 `P5OriginalH3Cell00PhysicalBoxBinding.lean`，文本闭合，未编译，正式验收信用为 0；原分配任务整体尚未完成。

原 PhaseC 只核对严格中心的 62 个 proper old planes，不能据此宣称完整物理许可。本候选将中心扩展为半径 `1/100000000` 的真实开盒，在整个盒上证明严格排序、第三激活、62 个严格旧平面与不应截去的 mask9 等式。随后证明全部 14 个 `PhysicalRows` 字段、76 个带标签物理行，以及同一 raised exponent 上 8 个完整平方门和 5 个 selected-complement 平方门。

给出了对整个盒统一的有理局部 cap 对 `lambda3=567/1000`、`lambda6=596/1000`，并证明第三 cap 小于原始基线 minorant `v(t1)`。这是真实局部有限构造，不能自动替换已存在的全局祖先函数。实际算术应用仍在同一个 `pre` 的 `rosserAncestor 3` 与 `rosserAncestor 6` 上显式保留四个标量条件：第三下界、六阶下界、第三不大于六阶、六阶不大于源比较 `R`。

另外补上前驱存在量词的一处实现细节：证明存在 slot58 不能保证 `Classical.choose` 返回 slot58。本候选证明在该盒和六阶下界下，所有可能被选择的 slot 都使用同一个 `mask138` 与同一个 `newCap`；旧等父类 `<30` 与特殊 slot43、44 被严格排除。因此新 cap、selected mask 与实际 `physicalRho` 支持真正对应，不依赖未证明的唯一 owner。

尚缺全局合法第三/第六因果 cap 的供应、共同祖先 partition、87 域覆盖与不交、同系数密度和 K 的最终连接。这里没有证明新分布定理、正性、积分收益或全局 upper。未发现原稿数学缺口；本轮消除的是实现层面的局部许可与 existential guard 歧义。

直接依赖的 source-only 模块、安装路径及当前精确 SHA-256 见 `REGISTRY.json`。没有改动旧草稿、生产源码、Git 或看板；没有执行 Lean/lake 或大型证书检查器。
