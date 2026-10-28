# 第四批 certificate 独立源码验收

五项均为 **SOURCE_REVIEW_PASS，仅限下述窄源码范围**。原始完整目标全部 OPEN，`task_complete=false`、`compiled=false`、`formal_credit=0`。没有运行 Lean、lake、编译器、kernel、`decide`、producer、数值 checker、递推回放或额度查询，也没有再派代理。

直接阅读实际 Lean、原稿、原始记录、必要前驱及最终 REGISTRY/REPORT。225 条已登记 path/SHA 引用逐条吻合（含重复）；11 份新 Lean 共2794行。去除嵌套注释与字符串后，未见有效 `sorry`、`admit`、`axiom`、`unsafe` token，注释闭合。原JSON另做465组字段转写比较，零差异；只是字面数据绑定，不是数学 checker。前三批 review 保持原字节冻结，完整哈希见 JSON。

| 项目 | 本次窄结论 | 未完成边界 |
|---|---|---|
| certificate_omega | 原Omega8192 canonical数组、结构不变量、payload唯一性 | 有限guards/具体值/历史绑定 |
| certificate_rows | 真实两行闭support解析域、可积性、Q0 raw有向算术 | 物理积分enclosure、采用的Q6 |
| certificate_enhanced | 原184+64整数程序、真实log coefficient、条件lower一步 | 55增强端点解析许可 |
| certificate_triple | 原始singleton路径反覆盖、同mask、重复质量相等 | 十一root与完整mixed source图 |
| certificate_floor | 真实320项Mercator余项、decimal enclosure及finite sum提案 | guard/sum两个有限提案未执行 |

## omega

`OriginalPairedN48CanonicalArrays` 保留n48 wrapper的mesh8192、P112、81921个U与81920个cell、48项sourceSmallLog、原sourceStep运算顺序及原query scan。`buildU` 的prefix保持性与三个严格更早索引，将顺序追加连接到原Python预分配后改写算法，没有读取未来默认槽位。

`SourceProducerValid` 被压缩为log正分母与整数cell非负两个纯有限guards；length、逐行递推、cell map及max scan均由结构证明给出。任何满足原predicate的payload具有同一U/cell/query，unused nodes没有被误称为原始输出或byte唯一性。第二文件给出两份闭合 `decide +kernel` 提案，并接30c真实native query/cost语义，没有把所求real uniform bound列为前提。

这些提案未执行，`canonicalQueryNumerator`只是确定定义，没有实际numeral或guard通过凭证。历史dump/序列化字段、P112 cost/switch、Q80 floor及其他native keys仍未绑定。位置：CanonicalArrays第24–245行；ProofProposals第31–68行。

## rows

实际row21/22顶点、均值、U/L、v_j/L的有限guards，经非负且和为1的barycentric weights，把factor/P正下界、P≤U及a_j/P≤V_j延伸到完整闭物理support。显式q=1−pLower/upper满足Y≤q<1；a_j与P之间整段位于(0,V_j]。密度连续、分母非零和compactness给出真实可积性。R/M ceilings仅是局部几何界，不是97项继承policy许可。

Q0四个literals与原gzip witness的records[21]/[22]逐字一致：row21 T_Q80=`16007085917676593648460`、raw_Q96=`33473824252327663860`；row22分别为`15389547820376111661547`、`6447903780770652011`。raw/Q96≤exact Jensen*(1+T10+Q0)方向正确，archive raw字段保持同一记录。row22较小的curvature raw未被当成selected floor。

尚未证明该exact表达式≤物理积分。E[P]=1、T10正余项、−log二阶Taylor、求和指数化及Jensen质量/均值连接仍须补齐。采用的是更晚Q6，原k=1 measured identity不能替代k=2..6的moments/convolution。有限guards与rounding项均未执行。位置：AnalyticCaps第27–255行，CurvatureFloorWitness第21–71行。

## enhanced

实读oneRound确认所有ordinary、W1/W2 RHS使用immutable old，current仅保留max；W1先于W2，per-product floor顺序保持。W动作不改变lower，故实际h248 lower化为h184与64个旧H后缀的有限max。

465组原JSON字段静态比较覆盖200log权、H184/h184各200项、70W1与36W2的base、point、ordered weight rows、targets，全部一致。W1用实际lower-K new_base，旧3W2用variable-kernel new_base，新增33用原selected base。unused W1 upper只是lower副本。这里是184+64原历史，不得混同seed-only430。

真实log契约先 `I80.point(right)/I80.point(left)` 再intervalLog，保持原quotient rounding，未替换为不同舍入的直接ratio-log。lower一步经真实Buchstab theorem，在前代Nonnegative/Sound条件下成立；这些条件并未为literal184或各upper states建立。200权及55terminal agreement的闭合decision也未执行。

因此55 copied bank值只归约到明确整数程序，**没有55条增强端点解析许可**。positive seed/前184、70W1/36W2增强count induction、child signed means、positiveK switches及原full/selected/alpha/cutoff仍OPEN；真实gain/correction signed coefficient未构造。普通ρ的4/R不能代替增强cost的4(1−H248)/R。位置：RawRound第25–105行，LiteralData第13–859行，LowerArithmetic第32–147行。

## triple

新增的是实际源域的条件式反向覆盖。IntegerStep采用production SingleRule与整数prime，query按原BH/W1/W2规则计算。SourceEdge是实际singleChildren membership，加rank、physical mesh及对已冻结H.cap的原own-cube支持条件，没有ParentTests或最终count bound作为前提。归纳推出computed acceptance、full/selected、同Q/word/window、prime closure及residual≥root/2^length；深度≤440给统一gamma0/2^440。真实query给child cutoff，不重置alpha或query到2。

实际literal70 targets导出selected W1的target，再由physical cutoff推出ceiling。prefix编码严格保持oldword和History.advance；递归admittedChildPredicate与computedFrozenMask函数相等，根E仍在原rootB冻结。`actual_selected_triple_covered`迫使该类source triple进入同一export occurrence；新增末定理把真实repeatedTripleMass精确识别为outerweight1的occurrenceMass，没有丢失重复label。

这消除了所述singleton subclass中的任意空filter问题，未覆盖全部430源族。十一root实例、每条rank/mesh/owncube原许可、pair children、retains/argument transports、source/program ownership、真实parent list及P上界仍须提供。400表/trace数值等式、seed/action/count soundness、positiveK及H248 correction也未闭合。位置：ScalarTargets第14–78行，ActualW1SourceCoverage第37–525行。

## floor

有限polynomial导数恒等式S′₂ₙ(1+y)=1−y²ⁿ，使log−S和nextTerm−(log−S)从0递增，导数分别为y²ⁿ/(1+y)、y²ⁿ⁺¹/(1+y)。因此真实320项even partial与正321项y³²¹/321上下方向成立，没有借用未经证明的log enclosure或sharp tail。

decimal10⁸⁰的outward floor/ceil、signed四角乘法、正分母division、整数division和原power/alternating loop都有real contains传播。原17572个Row fullproxy保持ordinary max、signed residual moment(57/64、5/2、1)、精确闭cell H_B、正RH及strict crossing零支。30b普通source上界方向修复与30c完整saved numerator链保持。

四类floor-proxy queries的[1,3/2]与正分母guards写成闭合decision提案，故只处理原logq zero-shift用途，不覆盖extra-gross/fibre的nonzero-shift分支。`selectedProxyUpper`为实际interval upper的有限和；λ=466977/200000000。sum<λ也有闭合 `decide +kernel` 源码项，未使用pasted total或将所求sum当调用前提。

**两个有限decision均未执行，不能声称已得到数值sum<λ或kernel接受。** 后续传递到frozen saved/4仍显式要求原每行fullSourceRowCheck=true。该upper-proxy仅控制saved lower-estimator数值，不给真实removed Y6 count上界。h248 endpoint analysis、same-mask arithmetic family、net gain/currentc仍OPEN。位置：Mercator320第20–199行，FiniteCertificate第33–206行。

## 最终冻结

每份Lean、REGISTRY、REPORT的最终raw SHA及225条依赖引用均在 `certificate.json`，包括floor最后冻结的Mercator `5c271c04058ca473fbea6203131c415cead819ef00ae80a262e3511f437d8008` 与FiniteCertificate `dd3151cf52b88cfda0d2e793fe8e6f01238f2bce89788cf251ebe3ac9e3dcc68`。

在这些精确前驱的源码意义下，未发现新循环最终目标前提或数学方向错误。所有源码仍须用户负责的安装、elaboration与kernel核验。五项窄SOURCE_REVIEW_PASS不改变原始完整30项目标OPEN与正式信用0。
