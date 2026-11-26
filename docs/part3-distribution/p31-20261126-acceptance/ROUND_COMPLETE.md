# 本轮完成：四个 P3.1 组件，共 125 个环境声明

## 正式验收并集

本轮四个目标组件已完成精确源码的严格 Lean 编译、bundled `leanchecker` 内核回放、
完整环境声明／传递公理清单及源码／对象绑定验收。此前三模块的 **107** 个声明与
最后 kernel 模块的 **18** 个声明逐名不相交，去重并集为 **125**。

| 模块 | 实际验收源码 | 源码顶层声明 | 自动生成声明 | 环境声明 |
| --- | --- | ---: | ---: | ---: |
| CommonPoissonLanesCore | `d28d340...` | 17：6 定义、11 定理 | 15 | 32 |
| ShiuFiniteCover | `d28d340...` | 24：6 定义、18 定理 | 12 | 36 |
| ShiuWindowGate | `d28d340...` | 9：1 structure、8 定理 | 30 | 39 |
| CommonPoissonKernelLanesCore | `8e89550...` | 13：5 定义、7 定理、1 abbrev | 5 | 18 |
| **合计** | 两次正式任务 | **63：17 定义、44 定理、1 abbrev、1 structure** | **62** | **125** |

这里的“源码顶层”计显式具名声明；生成列单列证明辅助项、等式引理、结构投影、
构造器和递归器。之前已经接受的基线模块和条件接口定理继续复用，没有加入这个
四模块计数，也没有被重新宣告为本轮新证明。

完整名称集合、来源哈希和每模块报告绑定见
[ACCEPTED_SCOPE_UNION.json](ACCEPTED_SCOPE_UNION.json)。联合记录逐项核对了旧三源
仍与其 `d28d` 验收版本相同，新 kernel 源与其 `8e895` 验收版本相同；没有把旧
107 个声明重新归为最后任务的新增成果。所有四模块实际公理并集都只包含
`Classical.choice`、`Quot.sound`、`propext`。

## 两次精确提交验收

前三模块的验收源码为 `d28d340b0240dc5cd8658893d07b61637ee94aa2`，tree
`24ac67c09f7fbd2aa7c1d6cc37710e0ef8231302`。原 P3 task
`c8f3589c6e604553bb5075f6c358270d` 成功，两个 group 分别退出 0，70 个记录阶段
全部通过。原 [ACCEPTANCE.json](ACCEPTANCE.json) 和
[三模块证据包](p31-final-verification-evidence-20261126.zip) 保持原样。

最后 kernel 模块的验收源码为 `8e895502586ad41d5222ed5fd54386855b909b32`，tree
`dab003597c3064fa021b6924ccb642f4775a122a`。原 P3 task
`8172cbb2c4a340358d38b706c9b6455a` 成功，34 个阶段全部 exit 0；证据在同一任务
成功后内嵌导出，没有再次排验收或导出。该 task 运行 148.862 秒，完整输出 73,434
字节，无截断。详见 [kernel RUN](../p31-kernel-lanes-20261126/RUN.json) 和
[原始 report](../p31-kernel-lanes-20261126/verification/report.json)。

Kernel 的 [完整证据包](../p31-kernel-lanes-20261126/verification-evidence.zip) 为
236,982 字节、53 个成员，SHA256：

```text
cde3814da4442181eb64c806f9aa7187e93308dababc9f95210148e118a531cb
```

归档保留原内嵌导出的全部成员，另附原任务终态 metadata、完整 raw 输出、命令和
本地分类核对。ZIP CRC 与全部成员 SHA256／大小均核验通过；未包含对象二进制或
其他任务。原始报告、声明清单和定理类型在各组件 `verification/` 中有逐字节副本。

## 已接通的数学内容

- **公共整数频率分块。** 复用原证明，保留零频一次、共同二进区间、正负真实频率
  和补集上的实际尾级数，处理零截断及二的幂端点。
- **有限 Shiu 窗口覆盖。** 按用户授权重新证明初等窗口几何、保留点见证、非负和
  比较及总长度预算；原上传 WindowGate 已与这个新 provider 接通并完成正式验收。
- **原物理完成核的分块。** 恢复原完成核及负号引理，把公共频率分块传入有限物理
  模数加权和，保留每项 `c.Coprime z` 过滤、负频 Fourier 参数和真实补集尾项。

旧 FiniteCover 的未恢复字节没有被冒充为已找到；有限恢复搜索的结果、两次 lane
失败和局部表达修复、kernel probe 及来源片段记录继续保留。源级来源／闭包／修复
JSON 保持原字节；各次正式报告直接绑定 `SOURCE_INTAKE.json` 与 `CLOSURE.json`
的文件哈希，修复记录由来源提交保留。其中接入时的 pending 标签属于历史状态。

## 复用边界与 P3.1 的剩余工作

Lanes、Shiu、kernel 三个验收 group 的项目源码／对象绑定数分别为 **53、2、54**。
Lanes 的 52 个、kernel 的 53 个非 target 项目供应者均在 strict 前后冻结；Shiu 的
两个项目模块全部是 target，没有额外未选中的项目供应者。各组审计后项目对象均
保持不变。只对本次选中 target 作新的 strict／内核回放，不宣称全部 Mathlib 或
历史供应者已经再次内核回放。

**完整 P3.1 仍未闭合。** 仍需接通实际原族的 `OriginalData` 和全局截断／carrier／
packet 识别、谱核两侧 Fourier 因子的 `hkernel` 与相关一致性供应者，以及原全谱族
的 Theorem J/A 组装和最终谱估计。物理完成核的分块恒等式只完成其中一个具体步骤。

`PrimitiveShiuTauBoundary` 仍显式携带 primitive Shiu 分析输入；本次窗口验收没有
证明该外部分析估计。未恢复的 SignedSplit／OverlapCover 调用者也未被宣称兼容。
上述剩余边界不改变本轮四个已验收组件的具体数学陈述和正式证据。
