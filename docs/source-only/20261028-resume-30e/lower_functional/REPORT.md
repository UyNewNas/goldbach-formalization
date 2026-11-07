# lower_functional 第五批E源码交付

本批3个Lean文件共619行，全部源码闭合、未编译、零正式信用。D三件raw SHA已重新核对并冻结未改。

本轮补齐原n48高带三种tied加权块，指定z坐标仍携带额外1/z，实际密度为1/(u*z²*w)。令L=log(b/a)，真正积分分别为：

- zwTie (r,s)=(0,1)：`1/a-(1+L)/b`；
- uzTie (r,s)=(1,0)：`(L-1)/a+1/b`；
- uzwTie (r,s)=(1,1)：`(L-2)/a+(L+2)/b`。

`P2N48TiedMomentPrimitives.lean` 用真实triangle/triple域的Fubini和FTC证明这些积分，再明确证明它们分别等于原producer的 `(1/a)*J1`、`(1/a)*(L*J0-J1)`、`(1/a)*(L*J1-J2)`，保留原signed alternating符号和r/s槽位。没有用普通volume的1/m!代替非对称加权矩。

`P2N48AllHighBandWeightedMass.lean` 将half-open fullParent与closedOrderedParent的差集束缚在原nullBoundary，从而先得到a.e.集合相等，再用setIntegral_congr_set传真实积分。原splitFour坐标保Lebesgue体积，实际t变量分离，zw/uz/triple低块逐一接上上述真实积分。故四种高带pattern全部得到真实Z公式，并通过actual archive decoder供应actualRetainedRows。它还导出独立omega作者需要的同父key=(39,47,0,0)精确log闭式；该出口不依赖omega作者的E后继。

`P2N48AllPatternDirectedMassPorts.lean` 证明原n48每个bin的真实log ratio均在[1,3/2]，复用certificate_floor已经冻结的纯D `mercator_contains`，不依赖其proxy总量。三个tied signed公式通过既有四角乘法、减法和定向Q80 rounding形成真实Z包络；finite rational containment再接同一原始DirectedPayload。最终actual baseline/omega-cost ports和同一actualSelectedCoefficient消费者都不再要求调用者传真实Z-enclosure、hBaseline或hOmegaCost。原rowPayloadCheck、Omega cover/numerator检查及uncoveredCost仍原样显式保留。

没有执行任何actual payload、log、Bernstein、row、floor或数值检查。decimal320/Q80包络是相同数学moment的严格包络，不声称与历史Python I/J指令输出逐字节相同；actual payload containment还需验证。旧decoder两项有限命令也仍未执行。任何Omega原始范围超出当前cover支持的情形不能用空cover/假PASS消去。

本批`batch_target_source_complete=true`仅指所派真实三tied矩/Fubini和全模式端点接口的数学源码已写全；原完整`task_complete=false`，compiled/kernel=false、formal_credit=0、ready_to_install=false。完整负域uncoveredCost、其他methods/priority replacements、实际finite payload与AP/密度/lower主链仍OPEN。未发现新原稿数学缺口。

精确文件、依赖、peer输入与安装/import映射见REGISTRY。
