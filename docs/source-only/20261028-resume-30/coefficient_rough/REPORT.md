# coefficient_rough 源码交付

本次输出 `P2ActualFifthRaw31SupportCeiling.lean`，共五个公开引理。文件文本完整；未编译，正式证明信用为 0，原分配的整条 rough-SW 应用仍未完成。

## 实质证明

前一 inherited-fourth 草稿把“实际 ProducerRow.selected 的坐标和等于数值 raw mask 的 subsetSum”留作 `hmask`。本文件根据 ProducerRow.Geometry 的精确范围 9≤mask≤15，以 7 个数值掩码的有限布尔表证明 Nat.testBit 与原稿 raw31 的除法/模2位定义一致，且第五位为0，再用有限和重索引消除该假设。没有增加行选择、积分结果、gain 或 SW 假设。

随后把真实第三 supported Gamma、第四 producer finite maximum 的 raw31 比较，与已写第五 eligible-candidate 比较合成；对全部11类 PhysicalCell 得到实际 exponent5≤oldCap。此前第五草稿要求调用者提供 inherited4≤oldCap，本文件也消除了这项前提。最后将此式转为同一 prime history 上的 physical level5≤N^oldCap，并保留 fourthLevel≤fifthLevel 的祖先恒等式。pair17/pair12 的 oldCap 可严格大于R0；代码不作错误等同。

## 到 SW 的真实边界

已定向核对 ActualW Phase4 和 LiteralLog Phase5。它们的 SW caller 针对实际 ALL16 ordinary W 的 ActiveNativeChart，精确保留 independent test word、真实 rough cutoff、Mobius cutoff 和 count/mean 的相同 log 标量。六维 PhysicalCell 并不自动给出该 ActiveNativeChart，因此本次没有把它强行套在任意 sixth physical rho 上。

仍须绑定实际 selected-third support、各 licensed producer Geometry；证明 H5<actual exponent5 的正向历史见证及 retained-prefix 链；构造准确 sixth physical coefficient 到合法 rough chart 的同系数等式。后续 Fourier inversion/L1/tail 与全 PP 也仍开放。没有发现新的原稿数学缺口，这些是形式化实现/实际对象绑定义务。

## 取用

两个直接导入仍为 source-only：P2InheritedFourthRaw31Embedding、P2ActualFifthCandidateBelowSixthRaw31。REGISTRY.json 固定其路径、SHA256 与预期安装名；先按对应名字交给编译专员取用，再放置本文件。本任务未改生产文件、旧草稿、Git 或看板；未执行 Lean/lake、数值 checker 或额度检查。
