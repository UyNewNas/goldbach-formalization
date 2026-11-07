# medium_s2 第二批：真实 H(l,D,R) 的几何估计

新增 `Part3OriginalS2ActualBlockGeometry.lean`，362 行，22 个定义/引理声明。第一批 (F) 源码冻结未改。新文件文本闭合，未编译、未运行 checker，正式信用 0。

对第一批实际定义的同 d 块和 `blockGeometryCost`，在原始 `MediumAdmissible`、`D>0`、`l>0` 下，`blockGeometryCost_le` 给出：

`H(l,D,R) ≤ 12*N/(Q1*D) * τ(l)^4 * L(P) * (1+log(4Q2Q3))^4`，

其中 `N=d.U`，`P=floor(8Q1Q2Q3)`，`L(P)=1+log(max(1,P))`。这个 H 就是第一批 (F) 中原 `paperBlockOuterCarrier` 的实际 H；未将其更换为抽象预算，也未把 H 估计作为前提。

证明的各项支付如下：

1. 原 α 的区间支持给自由 n2 的真实互素基数 `B(q*d*s)≤2N`。
2. 由实际 roughFiber 的 q2,q3 见证证明 `small*s=q2*q3`，得到右侧完整模数 `q*small*s≤P`，随后复用已有 `reciprocal_totient_le_logBudget`，原 φ(q*d*s) 支付为 `2*L(P)/(q*d*s)`。
3. `q*d*r=l` 给 `d*r|l`、`d|l`。因此两份 Λ 的原除数包络变为 `τ(l)^2*τ(s)`。
4. q 的原 dyadic 下界与真实块下界给 `q*d≥Q1*D`，在求和前保留 `1/(Q1*D)`。
5. 实际不同 q,d,r 三元组由 q,d 两个 l 的除数唯一决定 r，故重数 ≤`τ(l)^2`。配合真实 s 投影的无碰撞注入，将正 s 支撑扩到 `s≤4Q2Q3`。
6. 复用第一批 medium_s1 的 `sum_tauR_div_le_log`，以普通全整数 τ₂/φ 均值支付 `Στ(s)/s≤(1+log(4Q2Q3))^4`。未使用 `x^epsilon` 点界，未引入 squarefree 限制。

最后 `actualPaperBlockPacket_norm_le_geometry` 将该 H 界与第一批实际 (F) 合成，仍显式保留移动余数的原除数 progression `T(l,a)`。其前提只含原始数据和物理正尺度，不含新目标型 Shiu/S2/medium 假设。

这消除了上一批列出的 H 几何义务。乘上下一步原始 Shiu 的 `x/l`，因 `x=M*N`、`Y=Q1*D`，所得正是 `V/l=M*N²/(Y*l)`，自由 n2 没有被丢弃。

完整原始 S2 子任务仍未关闭：必须将非零包已有 reduced-residue licence 与原始 primitive Shiu 精确连接，证明所有块的统一对数参数和 collapsed-tail 最终支付。因而 `local_step_complete=true`，`task_complete=false`；这里没有声称完整 medium 或主定理完成。未发现具体原稿错误。源码依赖、SHA 与外部普通除数均值归属见 `REGISTRY.json`。
