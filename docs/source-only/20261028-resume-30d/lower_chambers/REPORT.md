# lower_chambers 第四批源码交付

新增两份局部完整源码。原 broad task 保持 false；本批完整 target 尚有剩余，batch_target_source_complete=false。30c 两份最终源码 raw SHA 已复核匹配，前批未修改。未编译，formal_credit=0。

`P2OriginalCommonActualWMesh.lean` 给出实际 canonical exponentCode 的第三层代码，保留 corrected [epsilon,w] 网格、前三 unmarked 位和 prefix 因果性。显式证明 qLo<=x<=qHi、cell width<=actual mesh step、端点向量到 x 的距离<=step。对前批 finite common-buffer cover 用 Mathlib 的 metric Lebesgue-number lemma，得到一个对整个紧集 K 和所有 mesh>=M 同时有效的实际网格阈值：闭胞端点进入同一个原始 licensed rational box，真正构造 CellRefines，再得到同一 r 的实际 WBoxCheck。M 不依赖逐点 x 或算术 N。

实际 compiler cap 的损失精确为 `r+(3/8)*(qHi3-x3)`，故 0<=loss<=r+(3/8)*step。取 r<=tau/2、step<tau 后，整个紧集的该损失<tau。同一个物理 prefix/denominator 的 ordinary query 差值等于 cap loss / x3，因 x3>=epsilon 可进一步界为 tau/epsilon。这里明确未把 stored whole-box wQueryLower 的额外坐标和分母误差算作已经支付。

`P2ActualLowerRhoEntryWallPayment.lean` 直接使用生产构造 `actualLowerSmallRoughRho`。row 数据只给 retainEven/cap/w/z/L 等真实构造参数；单位系数界由现有 theorem 推出，不是额外 envelope 前提。相同 native rho entry 同时进入有符号墙和绝对墙，原 target-deleted prime carrier/tupleWeight 不变。逐项单位界把绝对墙质量压到前批具体 third-lower wall strip mass，从而 reserve -> fixed width -> N0，统一所有后续 row 数据和单个 modulus pullback。

仍缺关键完整目标：独立 tent-winning chambers 的全部 receiver；stored wQueryLower 全误差与最终 compiler/functional propagation；完整 residual modulus 求和和固定 normalized absolute-density envelope；实际 mixedWinner gapLower/因果四五层及算术 W licence、原素数锐端点和 hLower。当前 entry payment 不冒充全模数 row density payment。未发现新的原稿数学缺口。

仅静态审阅定义及证明逻辑，查询了 Mathlib 主源接口；没有 Lean/lake、编译/修复、kernel replay、checker、CI、额度检查、Git/index 或看板修改。依赖 raw SHA、paper anchors、量词顺序和剩余假设见 REGISTRY.json。
