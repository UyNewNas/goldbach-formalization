# upper_mesh 第三批：真实截面与 B13

交付两个新 Lean 源码，共 577 行、29 个声明（14 个公开定理），另有 REGISTRY.json。文件文本闭合；没有编译、内核验证或数值重放，正式信用为 0。第三批窄源码目标 `batch_target_source_complete=true`；完整原目标 `task_complete=false`。

## 已消除的真实义务

`P1OriginalFifthActualCrossingSections.lean` 直接在固定四坐标截面上比较两点各自的真实半开 Ico mesh owner。由物理坐标顺序证明第0格索引有序，由同一截面的其余坐标证明对应标签相同；用原始 box 的 first-coordinate Gamma rise 得到 `Gamma(k)-Gamma(j)≤(z-x+step)/2`。grid400/key≤77 与实际 raw/cell membership 直接供应 outer-full Gamma 前提；没有要求一个全局扩展或 clamp 后的 selector。

实际 `selected/firstStop` 对称差经原始七个门槛展开。四个 ordering 门槛不随 buffer 移动，因此其 crossing 不可能；剩余保留独立的 initial first cube、第三 cap 的 first cube，以及原始 third cube。实际 Gamma VALUE drop 给第三层差≤41e/20，故截面进入一个 initial strip 和两个真实 owner Gamma bands。对每个 band 中任意两点用上述 quasi-rise 控制直径，得到截面测度≤(428/75)e；随后调用实际 raw-box Fubini，证明

`volume(D0 △ De) ≤ (428/75)e/400^4`。

这个常数不乘 decoded child 数，也没有把待证截面或五维体积估计放入前提。半开格的等式面保留在真实 owner 和闭 strip 内。

`P1OriginalFifthActualB13IntegralError.lean` 接第二批具体 `rowModulus` 与 `rowMassBound`，证明真实 positive literal variable-MI kernel 在实际 owner union 上可积、grid400 raw box 体积恰为1/400^5。积分差分成同域 kernel motion 与固定 kernel 的域变化。后者利用两个 directed lost pieces 各自非负，按一次 symmetric-difference volume 支付，没有多出2倍。由此得到真实 B13：

`|∫De f_e − ∫D0 f_0| ≤ rowModulus(raw,e)/400^5 + rowMassBound(raw)*(428/75)e/400^4`。

其中 `f_e(t)=max(0,literalRawKernel(e,raw,t))`，仍是相同 saved mask 的 variable MI 减去 tuple-dependent fifteen-tent+W rawFourth(t)-2e kernel；未断言其等同任意实际 old4 政策。

## 精确保留前提与剩余事项

真实 raw 必须 grid400、key0≤77；B13 还要求五个 integer lower key≥1。q>0，0≤e≤3/51200，step≤chi≤e/10。有限 J 的每个原始 child 必须同时满足0与e处的 selected membership，以及两处 literal firstStopCellCheck=true。后两类 verdict 的存在或在 moving-family 上的保存没有从 Gamma 数值界推断。

因此，具体历史归档所有行的 selection/firstStop/adoption verdict 或 independently quantified omitted-child trim，仍需供应。第一批 schedule、第二批具体 kernel supplier、第三批实际 B13 可以在这些真实 verdict 齐备后共同使用。完整87域共用祖先、same physical rho、当前K reserve与最终上界仍开放。未发现新的原稿数学缺口。

精确 SHA：

- CrossingSections：`e3327e62af26b957159a6a959a2fbb914a615ff16566f2cf8afde7bad1cdb092`
- B13IntegralError：`16f5d88e0b74ee73d5519871317fc72c685f250412d7c112113882197410bd16`

直接导入、同批依赖、held source 与原稿的精确路径/原始字节SHA均在登记中。个别旧 frozen 路径超过Windows260字符，哈希读取使用 extended absolute path 前缀；未移动或修改任何旧字节。没有修改前批、生产文件、Git或看板。
