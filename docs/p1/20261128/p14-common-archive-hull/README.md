# P1.4 公共第五层 cap 与实际父层增益截断

对原完整档案 sourceData，公共第五 cap 精确等于 max(原第五 cap, inheritedFallback)；changedParents 与实际 changedParentPrefixes 定义相等，其区域为前缀长5且原 inherited4<fallback；实际 parentExcess 等于正部 max(0,fallback−oldInherited)。四条原声明保持，仅将最后一个证明 change 右侧写为定义相等的 oldInherited，修复重写匹配。失败尝试0保留，不计信用。

此为连续核/精确cap恒等式，不是有限带符号算术密度单调性；实际密度共同近似、非零余项支付及全局预算仍未闭合。整个P1.4/P1.5、18/21及三HOLD均不变。旧SeedHull/Preservation验收及原产物复用，旧normal/kernel执行0次。普通导入不新增独立full-owned信用。

新owner在冻结Member原guard/toolchain/core和串行lane中通过隔离normal、sole-module kernel、完整actual-owned审计及coupled指纹复查，并经独立只读复核后封存；不是Lake named-target或fresh import closure的重验。源码中旧SOURCE_ONLY标记保留，局部状态以本目录验收回执为准。
