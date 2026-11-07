# certificate_rows F交验

新增四份完整候选源码，已写到本批原始完整目标的最终真实积分/floor theorem，没有以局部小目标替换F目标。作者冻结时尚缺整链独立验收与形式执行，故保守保持 batch_target_complete=false、batch_target_source_complete=false；candidate_entire_dispatched_chain_written=true，local_step_complete=true。原始全局task_complete=false，未编译、正式信用0。

`P2Winner9T10TailJensen.lean` 补核心数学缺口。tail=(1-y)^(-10)-S10 的二阶导数为110倍order12/degree8负二项余项；显式有限恒等式把余项分子写成 y^9 Σ_{j=0}^{11} choose(8+j,j)(1-y)^j，因而在[0,q],q<1上非负。由此证明tail凸，再对tail本身应用Mathlib真正Jensen，得到f(EY)+Σc_k(EY^k-(EY)^k)<=Ef(Y)。这是GAP比较，未用点态minorant冒充。

`P2Winner9ActualT10Moments.lean` 用前批真实Δ8稀疏多项式积分重建两行actual physical Y^k moments，并给它们与原始t10表达式的独立闭合有理比较；另把literal J_T绑到实际4·gapMass/meanProduct。新finite证明项未执行。

`P2Winner9ActualRowProbability.lean` 从相同真实support及真实gap、正mass构造withDensity probability；由compact正性证明全部可积/范围条件，将tail Jensen、实际meanY=1-1/U和actual moment identity组装为真正 1+T10 <= E[P^-10]。

`P2Winner9SelectedRowIntegralFloor.lean` 仅对非负横向项插入degree6 binomial minorant，保留完整P^-10给T10比较。实际70项mixed moments使其积分严格等于full Q6，不重复Q0。再以原始factor4、全部十个真实因子和actual J_T把概率界转回原始density integral。最终把原始Q96 raw floors接到真实物理积分：row21为33553775924834770601/2^96，row22为6463231997558714529/2^96。没有将desired analytic enclosure或moment bound作为前提。

代码声明了这些完整candidate theorem bodies；没有声称它们已elaborate/kernel成功。整链依赖先前未执行的determinant、integer scale、independent sparse-polynomial/convolution与directed floor证明项；编译专员需实际执行，可能需要资源安全的等价reduction实现。所有前批源码/REGISTRY/REPORT均逐SHA冻结未改。全局97策略约束、all22/all17572、会计/余量及c/K仍是原目标未完工作。未发现原稿数学缺口。精确依赖、raw SHA和安装导入图见REGISTRY.json。
