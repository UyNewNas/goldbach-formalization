# medium_poisson 源码交付

新增 `Part3OriginalPhysicalPoissonTruncation.lean`，候选安装路径 `ImbalancedChen/Part3OriginalPhysicalPoissonTruncation.lean`。本文件文本闭合；未编译，正式信用 0，须先安装并验证 registry 中固定 SHA 的 source-only 依赖。没有改动生产文件、旧草稿、Git 或看板。

## 实质连接

原来两个最新叶子分别拥有 exact paperPsi Poisson 包与 uniform scalar signed tail，却没有把有限原始同余计数的实际复数截断误差与该标量尾和连接。新文件定义实际 signedWindow、omittedPacket、finitePacketError，先证明相位模为 1 后的逐项范数等式，再由同一绝对可和级数的差证明有限窗口截断恒等式。有限同余计数、精确零模、两个频率符号及任意整数 residue representative 全部保留。

物理 `physicalH` 的 cutoff 条件由 `D*L<=32*Q*R^2*S^2` 与正参数直接推出，未假设尾和结论。继而 fix A before x0；一个 x0 对所有正 V、所有正整数 L、D、所有 residue b 和满足实际几何 bound 的 Q,R,S 有效，不需 L<=x 或 L<=V。另有一般实数 H 版本，故 H<1 的第一个遗漏 ±1 不被丢掉。

最后 fix A,K before x0，把实际复数 c_i 乘包的有限和误差压到 x^(-A)，输入仅为逐行真实几何和显式 coefficient l1 budget `sum norm(c_i)<=x^K`。这是统一阈值的有限汇总；实际 E2 系数的预算本身仍待实例化。

## 前提和边界

- exact Poisson 和 actual psi norm tail 均从 registry 固定源码引用；全部仍 source-only，不能称作内核已验。
- actual modulus L 必须由调用者绑定原始 lcm(p*r*s,p*r'*s')；新文件只消费此前已有的精确 D*L 几何 bound。
- 完整 E2 dictionary、chosen paperPsi 到实际 completed dispersion row 的身份，以及实际 coefficient l1 budget 尚未闭合。没有假设或宣称完整 medium theorem。
- 这一步未发现原稿数学缺口；剩余是实际对象绑定和编译验收。

检查只做源码逻辑、禁用占位符静态扫描及固定依赖 SHA 记录，未运行 Lean/lake/数值 checker，也未检查额度。Mathlib 的无穷和接口只读核对了固定 revision 的官方源码，链接保存在 registry。


Scope correction: `task_complete=false`, `local_step_complete=true`. The original assigned E2 object binding remains open; only the local packet/truncation connection is source-complete. A root static lexer finding was corrected by replacing the accidental nested-comment opener in prose with `plus/minus one`; no proof body changed and no compiler was run.
