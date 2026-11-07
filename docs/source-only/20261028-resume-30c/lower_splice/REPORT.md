# lower_splice 第三批

新增 `P2OriginalMixedThirdSignedFrontier.lean`。沿第二批真实 mixedWinner/BranchTable/Trace，构造只完成第三更新的有限阶段；第四/第五更新另属于 I4/I5，未混入 I3。

关键步骤不是先假定两个策略相同：直接展开实际 Trace，证明任何两 CapPlan 在 rank≤3 的累计 retention 一致，因为第三 cap 在本rank admission之后才冻结。因此新策略被证明等于使用原seed策略到rank3、再接真实mixed第三阶段的depthSplice。既有FirstExitDepthSplice定理于是直接给出同一个真实seed frontier上的signed第三差值。

Frontier保留完整history、sign、mass和remaining carrier，并附上来自同一incomingCode的mixed SourceForm标签。源码还证明每个tag的长度恰3、sign=false、mass等选中局部权重乘积、选中prime仍来自原roughUniverse、原seed Trace累计门槛已通过；W标签再连接回同一mixed表产生的实际W Trace cap。没有用最后一次odd bypass代替此前累计门槛。

复用生产库的实际prime-product注入/Möbius系数，定义先于测试整数固定的signed new-minus-old rough rhoI3，并证明其多项式与任意整数divisorSum等于同一tagged frontier。随后以相同rho写出有限source count和精确coprime mean，证明signed discrepancy等于二者之差，并把count替换成真实Trace frontier求和。全程保留符号，没有换成绝对误差或总source mass。

边界：rhoI3只表示真实rough第三阶段的差值；完整sign-sensitive small-prime attachment、W/tent原始算术licence、同quotient ordinary parity-Rosser continuation及其old-plus-minus-new-plus密度尚未证明。有限outer source A/weight为显式输入，未声称任意A就是原稿prime-product族；使用N-m的residue解释仍需其真实m≤N支撑。原完整任务仍false，本轮batch目标也保留未闭合。未发现新原稿数学错误。

第一二批保持冻结。未改生产/Git/看板，未运行Lean/lake/编译/修复/大型checker/额度检查。全部未编译、零正式信用，精确源码与依赖SHA见登记。
