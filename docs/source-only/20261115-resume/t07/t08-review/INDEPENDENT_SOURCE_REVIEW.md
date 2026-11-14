# T08 原根 receipt lane 独立源码审查

审查者：T07，2026-11-15。结论：**SOURCE_MATHEMATICS_PASS_UNCOMPILED**，仅限以下精确有限恒等式；formal/kernel credit 均为 0。未运行 Lean、Lake、LSP、proof/helper、fixture 或 candidate；未下载 artifact，未改 Git/GitHub 或 Lean 源。

两份新源没有发现数学缺口。已发现并由作者在 ROOT 授权下修正文档的一处歧义：必须写字面 if/else，不能把它提升为反向 iff。该修正不改变 Lean 源或其前提。本审查绑定修正后的最终冻结。

## 精确冻结与修订历史

| 文件 | bytes | SHA256 |
|---|---:|---|
| `t08/Part5OriginalH430FirstReceiptExit.lean` | 9879 | `18df2d6b4675bbede70eaa5fddda5034f599e3e3e3dc23efe098fb36e30384c6` |
| `t08/Part5OriginalH430ReceiptLaneRigidity.lean` | 8734 | `2b7514abe1522fe05f5635d032f7c62080c122ae61c5a3ef953ee3bb7692de0b` |
| `t08/STATEMENT_MANUSCRIPT_MAP.md` | 7089 | `9622035fb3a742e1cb804386c7f270a79afd9a3b90e11623ebdcd14846273ab8` |
| `t08/FREEZE.json` | 8362 | `42b782574a0c0ef771afdb73528c6039ca02507043ec243196a045f82b7651f5` |

路径均相对 `output/resume-20261115/`。以上已从实际磁盘重新计算 SHA256。旧 FREEZE 为 7535 bytes / `48f4b0de6bc1b6b045d130b2e25fb2004459c22bf1219d94274e4713efb4ae97`；旧 statement 为 6831 bytes / `0e7013ee57fe53ba381656d39ffdb7217d1d42dc21e87f67a3b7a69fb7fd4781`。最终 FREEZE.revision_history 保留两者。作者 freeze 的 `independently_source_reviewed=false` 是作者原时点记录；本独立 AL 单独给出审查结论，不再回写作者 freeze。

## 实际对象和量词

对每个自然数 `N,n,m,p`、原根标签 `k : Root`、实数 `t`、原 `c : RootKey n m` 和真实 `o : Occurrence N`，在且只在原有前提

```
2 ≤ N; 0 ≤ t; t ≤ 1/12; 1/((n:ℝ)+1) ≤ 11/384;
p ∈ rootFibre N n m k t c; o ∈ rootHistory N n k t p
```

下，令 `B=parentProduct o.current.old`、`D=o.current.old.tail.prod`、`Q=cellQ N n c.1`、`z=cutoff Q B o.current.node.physical.argument`，接受：

```
originalReceiptLane N p D z =
  if o.current.old=[p] then originalReceiver N p else ∅

(frozenCount N B (rootMask N p) z : ℝ) =
  if o.current.old=[p] then ((originalReceiver N p).card : ℝ) else 0

o.current.old≠[p] →
  (frozenCount N B (receiver N) z : ℝ) = ((rejectedChild N B D z).card : ℝ)
```

第一条不是 `(lane=receiver) ↔ old=[p]`，也不是 `lane.Nonempty ↔ old=[p]`。`originalReceiver` 可能为空；没有加入非空假设。对应源位置为 Rigidity:46、89、104。

`originalReceiver` 是原 `chenSiftedQuotientPrimeSource N p (N^a)`；`rootMask` 是原 additive prime `ell` 上的 `receiver N ell ∧ ChenPrimeRough (N^a) ((N-ell)/p)`；`originalReceiptLane` 是其原 root quotient 标签下的真实有限过滤，不是新 abstract family 或人为令零的计数器。T17 已给 exact pullback、masked-count 和 count-split；本次复用它们，只补上真实所有历史位置的退出见证与未附素数路径的 cutoff 控制。

`rootHistory` 来自固定 commit `001d139e667eb5cb42f1e9ca8f02de221b00db5c` 的原 Request recursion：根词 `[p]`，fuel 430；`children` 在当代 request 上 resolve，并仅展开上一代 `iterate g` 的真实 winner。`ChosenPath` 每一步使用自己的实际 request 和递减 fuel。`Coherent` 的几何/整数条件在原根和 child 中均由既有定理供给；root-facing T08 定理没有额外接受任意 Member、h34、count estimate 或不受控标记函数。

## 首次附素数：各分支完整核对

设尚未附素数时物理 residual 为 `L`、argument 为 `s`。根的原 clamp `s=max 2 (L/a)` 给 `s≥2`、`L≤a*s`，其中 `a=417/5000>0`。FirstReceiptExit:180–199 由实际 frozen root 建立此事实，并通过 replay 传递。

| 实际边 | 原实际输入与推导 | 核对 |
|---|---|---|
| retained | `.retain` 不改物理 query，不追加整数 | 保留 `s≥2,L≤a*s`；不能把 retained cell label 误当新 transport cutoff |
| 70 W1 fixed | `s≤W1Target i≤W1Anchor j` | residual 不改，argument 只增，保留不等式 |
| 36 W2 fixed 两 anchor | `s≤row.s≤row.s0/phi1` | 同上，使用原 `W2_target_le_fixed` |
| BH lower | `s−1≤L/x−1`，`x>0` | 得 `s*x≤L≤a*s`，故 `x≤a`；未丢掉 `1<w<2` |
| BH upper | `max(2,s−1)≤L/x−1`，`x>0` | 同样 `x≤a`；保留闭端 |
| W1 singleton | `x/L∈Ioo(1/anchor,1/target)` 且 `s≤target` | 得 `x<L/target≤a`，原 7×10 行全覆盖 |
| W2 三 singleton | 上端分别 `1/row.s,a2,a3`；原36行 `row.s≤phi3`、`a2≤a3` | 每个 `x/L<1/row.s`，从而 `x<a` |
| W2 四 pair | 原严格 `W2PairDomain` 经既有 `strict_pair_iff_half_not_wall` 到 `pairHalf` | `pairHalf_below_target` 对两个坐标均给 `<1/row.s`，没有以弱 `a3≤1/2` 代替实际 target 上界 |

T08 的 W2 pair 证明在附词 `[large,small]` 中选 `small` 作存在见证，足以杀掉 rough root receipt；既有 pair lemma 实际对两坐标都给上界，故无误把较小坐标当成第一个 word letter。严格说新 `child_first_receipt_exit` 陈述的是“一次首次附加事件的附词中存在小素数”，并未另输出每个附加素数都小的定理。

原 `child_admission` 从真正 `singleChildren/pairChildren` 给 `q.Prime ∧ q.Coprime N`。当 `physicalPrime N q = 417/5000` 时，`N>1` 与 `q>0` 允许 real-log/rpow 字典，得到实等式 `q^5000=N^417`，精确转为自然数等式；素性推出 `q∣N`，与互素矛盾。因此 BH 的 `≤a` 确实升级为 `q<N^a`。没有零测度删端点，也没有未声明的 N 实数域或大 N 假设。

这里的“全部实际边”是现存 Request recursion 的严格 production carriers。原母式的端点/old-prefix repeat 补项仍在既有 window dictionaries，T08 不把这些补项宣布消失，也不声称将所有 raw mother atoms 重新列入其严格 children。此限制与原后续 source dictionary 一致。

## 根词、每代位置、原 mark 与 owner

`nextRequest.old = r.old ++ appendedWord ...`，pair 原顺序 `[q1,q0]` 不变；`ReceiptState` 明确保留 `old=p::xs`。一旦 `xs` 包含上述小素数，后续 append 永远保留这个字母，`List.dvd_prod` 给它整除真实 `tailProduct`。因此 `originalReceiptLane_empty_of_small` 的 roughness 矛盾用的是根后面的真实严格前缀，不涉及产品分解重建或删除重复路径。

在 `old=[p]` 支，`xs=[]`，`tailProduct=1`。真实 `rootHistory_support` 和原 root fibre 给 `Q=B*N^L`、`B>0`、`s≥1`，故物理 cutoff 精确为 `N^(L/s)≤N^a`，足以使整个原 receiver 都通过 lane 过滤。固定/retained 路径可以有正深度；源码正确使用词等式而非 `path.length=0`。

`LevelIndex = Fin (levelRequests ... G).length`，由历史 LIST 按 remaining generation 筛选，重复 occurrence 仍是不同位置。`levelMark=(path.map edgeWeight).prod` 沿用原权：retain/BH/W1fixed 为 1，W1prime 为 1/2，W2fixed true 为 4/5，其他 W2 为 1/5；没有重置为一或按 receiver 数除权。

接受 Rigidity:129 的每个实际位置子集 `S` 恒等式：原 masked count 的 `levelMark` 加权和等于 `#originalReceiver × rankOneWeight S`，其中 rankOneWeight 只是在 S 中筛 `old=[p]` 后加原 mark。146 对每个 `G:Fin 431` 分别求原 rootFibre；159 对每个 `g:Fin 430, act:Original106Action, c:RootKey, b:Box mesh` 沿用既有 `positions = selectedLevel.filter(boxOf=b)`。原 request owner、路径/物理 cell、enhanced/classical 标签和 Q 均保留。不同 generations 没有混加；U3/U4 两标签独立应用，重叠仍保留各自项。

## 原稿、复用和禁止提升

已实际读取并核对稿件 SHA：`manuscript-body.tex` 的 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`，以及 insertion chain 的 `09f84f41e97dbd2267baee01a0a7c7c765e696a00688809086394c10f24623ee`，均与固定 `9731290e...` 记录一致。稿件795–817为正标记普通 Θ、同 Q 与实际 alpha；819–855为原 BH/W1/W2反馈；857–877为430和共同441近似；887–892为真实 max-two 根。Insertion chain253–355逐项给本次使用的物理窗和先代归纳。T08 没有更改这些前提。

对于已附素数位置，普通 count 等于**整笔** rejectedChild，普通 Θ 和正 mark 也仍存在。把负号 masked count 换成普通 count 必须补回整笔差额，不能将其叫作已付小误差。`boxTheta` 的定义仍是同位置上 parentTheta 的原正和，不乘 receiver cardinality。该结果诊断 rootMask 永久继承路线的限制，不否定“正根比较到较低 cutoff 后保留完整普通 receiver”的另一条原路线。

ROOT 另行报告已只读刷新远程 `chatgpt/p5-h34-full-tagged-actual-fin-20261112`，当前仍为 `001d139e667eb5cb42f1e9ca8f02de221b00db5c`，与作者历史 pin 相同；本审查记录为 **ROOT 外部 dedup 补充**，不伪称本人刷新远程，也不改作者历史 `branch_ref_refreshed=false`。既有 `547e9976...` actual-Fin 双标签结果没有被重做或当成全滤器许可。

本次 lexical scan 两 Lean 源没有 axiom/sorry/admit、unsafe/partial、native_decide、run_cmd 或 #eval；这是静态源码检查，不是展开后 AX 闭包或编译证明。仅允许源码数学审查通过，不允许提升 h34、ordinary Θ 下界/上界、native proper/equality/inherit 质量、完整 Member 算术解析许可、relative own-Theta、同一430/441 realization、hLower、7/32 或 full PP。新源的实际 elaboration、完整双类型、逐声明 AX 与 kernel 验收均未进行。

## 直接依赖身份复核

磁盘三个直接旧依赖 SHA 与 FREEZE 一致：OriginalReceiptMemberPullback `172f06c06ccd609e6293abdff07c7401c81b5dc51ae734ccd48ac4273c013119`；SelectedMemberBox `8df77699dc064f0cc36527c9e81cb0e44ddc2dcffb02796e7f3d50e9a9117a89`；P2OriginalPairChildWindowDictionary `a10b20a1876e21c56d5eae8aade1ebbc7c8e4cb712afb7c633d21c58b21e17de`。

另以本地只读 bare mirror `git show/rev-parse` 核对 `001d139e...` 的实际旧源与 blob（无 checkout/修改）：RequestedHistory `9103005991a106805aea773e1039af040c0e9c4a`；RequestedBranches `104ca3f95f0ce95a71abbbb33996d5ed64dc6179`；RequestedAdmission `8cbf985c9de8d86bcd27a5645c8626780d645222`；RequestedMember `3ee28117e22de53281fd755ef2c8cc1c98114f6a`；RequestedLevelBankSupply `138b4f2928088b4c2173610a39e8159116452e57`；IntegerItineraries `628e3beea491c45cc2bdf59bd0152cbe05440304`；FrozenIntegerSupport `fa65ecf42298fe7fae0f8af9a0866bb2147fa3a7`；TaggedArithmeticReceivers `edfdd8a262234e3d92649284fce73ba1bd1a6633`。这不是新的全项目依赖编译闭包验收。
