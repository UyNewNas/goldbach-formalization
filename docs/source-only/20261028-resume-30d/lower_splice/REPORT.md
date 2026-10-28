# lower_splice 第四批

新增 `P2OriginalI3ActualSmallRosserAttachment.lean`，连接两份真实 `actualLowerSmallRoughRho` 的第三阶段差值。全部未编译，零正式信用；原完整任务与本批完整目标仍false。

关键恒等式 `pair_difference_original_mu` 保留原始 μ(b) 的符号来选择实际 β：μ≥0用小素数lower Rosser，μ<0用upper Rosser。不能对roughDelta=new−old重新按符号附着，因为移除正μ项会令差值变负，而它仍须使用原来的lower β。已证明这条原始μ分支恒等式，并通过公共support零扩展、严格small/rough唯一因子分解，得到实际physical attachedRho在a*b处的准确公式与一界。

共同physical支撑被证明恰等两份actualLowerSmallRoughModuli的并；支撑外差值严格为零。由此可把任意signed physical sum无重数地拉回small/rough pair，count和精确coprime mean始终使用同一个真实attachedRho。signed discrepancy既等于count−exact mean，也等于保留原始μ分支的pair discrepancy。

真实附着采用small primes<y与rough primes≥y、<z。`roughUnion_supported`来自实际fixedEvenRoughSupport的prime-factor支撑定理，保证互素与乘积唯一。另按这个真实y-carrier重建了带原SourceForm标签的rough frontier恒等式；没有把前批0下界carrier改名冒充y-carrier，也没有声称两者整个source相同。

尚未完成：实际Trace续接到frozen ordinary-plus的old/new quotient residual。这需要同一reached frontier的继承前缀admissibility、已冻结total level、W/tent原始算术licence与后继比较，不能仅把该续接恒等式作为新前提。small Rosser附着本身不能替代此步。有限A/weight保持显式，原稿prime-product应用还须实际source识别及m≤N支撑。

前三批文件冻结未改；未运行Lean/lake/编译/修复/大checker/额度检查；未改生产/Git/看板。源码与关键import raw SHA在REGISTRY中。未发现新的原稿数学缺口。
