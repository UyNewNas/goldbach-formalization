# lower_chambers 源码交付

新增两份局部完整 Lean 源码，未编译，正式验收信用为 0；原分配目标仍是部分完成。

`P2OriginalMixedThirdWTentSelector.lean` 不改变旧 `supportCheck` 对 W 的排除，而是建立独立 mixed third bank。旧 composite tent 行保留原 support-mask/side 检查；W 行保留自己的 `WBoxCheck`、空 selected mask 和实际 W query。selector 先检查继承，再对完整 tent 动作和 W 作有限严格 whole-box 比较。已写明继承优先、只读前三码的因果性、来源保留、选中后逐点 affine 最大值，以及非空严格 W chamber 推出实际选中 W 的证明。W 被选中时可提取独立 W licence 和精确 `WThirdTable` 行；没有伪造 rank3 tent eligibility。

`P2OriginalThirdWRationalChamber.lean` 把旧 obstruction 附近的正邻域具体化：x 端点在约 [0.049,0.051]、y 在 [0.039,0.041]、z 在 [0.029,0.031]；对 `0<=rho<=1/100`、`0<buffer<=1/10000`、`0<delta<=1/200000`，从有理余量推出完整 `WBoxCheck`，包括对实际 `baselineCap rho` 的历史测试、首坐标 gate 和 buffered full squares。进一步提供 `epsilon=1/1000`、mesh=999（1000 bins）、前三 codes=594/473/351 的明确实例，包含原反例点 `(1/20,1/25,3/100)`，取 buffer=1/20000、delta=1/400000 后得到实际非空 `WThirdTable` 行。这里并未把“存在合格 W cell”作为前提。

仍缺完整原稿目标：全部 W-winning chamber 的有限覆盖和墙损失、第三 mixed bank 与第四/第五 frozen-parent stages 的接合、实际 Trace/同 rho 计数均值、W 算术 factorization licence。最大值定理比较的是原 affine endpoint；共同缓冲后保留 winner 的余量仍需后续绑定。明确实例的全 mixed-bank 严格差值也未执行归约。

本轮仅核对定义、源码和手工有理算术；没有运行 Lean/lake、编译、数值 checker、kernel replay、CI、Git 变更、看板变更或额度检查。未发现新的原稿数学缺口；旧 tent-only bank 属于已明确的实现遗漏。
