# P4 10:40 轮：十九项同策略付款接到真实计数

SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

基线：`d9b924277736f577f23a5e17dd0483988880f730`。
分支：`chatgpt/p4-uniform-correction-20261111`。
两个新增源码和准确 Git blob：
- `P4AOriginalFiniteAll22Nineteen.lean`：`abadf4d9fbbec16085deb732f4e3388e35500218`。
- `P4AOriginalFiniteAll22EarlyDefectCounting.lean`：`fb3aa5371d57b599fac9726603aaf3d179dd38db`。
安装映射及精确依赖见 `DEPENDENCIES.json`。

## 恢复、查重与稿内范围

远程 P4 仍停在前轮交接头 d9b92427；yellow-closure 仍为 3a46b3f0，
takeover 仍为 124d09f9，没有发现仍在写本分支的后续轮。
本轮只新增自己的目录及原 P4 编译请求，不改前轮数学源、
其他任务冻结包、工作流、依赖和状态表。

重读 All22 structural review、前轮九项付款终端及 T09 的
fallback/R17 审核。当前 November 6 英文 argument.tex 仍是
blob 90234d94460f1d7d59982635d7bf54c9b19250da。
293–305、1039–1048、1078–1086 行要求实际 finite realization、
共同参数先于 N 和四正项减 22 次实际父策略差。本轮不改变这些对象或顺序。
CURRENT_MANUSCRIPT_MAP 的旧记录没有被当成当前完整映射。

直接复用而不重证：
1. 前轮九个 sixth 名义槽及其实际 final dispatcher 共选；
2. R17 `original_ordinary_saved` 的完整 87 算术源、原八槽及 seed 的两次增量；
3. 原 `lowerEighth_eq_paid_source` 的 high-dispatch 恒等式；
4. final finite fallback 的 `gains` 和 `Canonical.paid`；
5. 原始 All22 的 K/两本 reserve/精确 slack 恒等式。

完整非紧第三积分尾、可积性和统一 L1 逼近已有源，本轮继续消费其下游
实际四正项终端，不重新实现 raw gap、积分尾、PNT、外部解析定理或其他路线。
EXTERNAL_REUSE 与固定依赖已核；仅做已有成果到同一真实策略的最小适配。
P1.4/P3.6/P5.6/P2 的整节点没有被假定完成；实际调用只限依赖清单点名的版本。

## early 0/1/2 的实际缺口

只读核查了完整 source-only 子树（5214 项，未截断）及相关最新 refs。
暂停记录中的 early135 registry 对象
d7909c82f6073277f62eee33c2a92ee69a418006 精确读取仍返回 404；
它标记 mathematical_source_included=false。因此此稿仍未核实，不视为不存在，
也没有连接用户本机恢复。

已有历史 G1/G2/G3 下界不能直接支付 final `lowerEarly`：
`fifth_on_owner` 只在 frozenSupported 历史 owner 上成立，
而 actual `cap5` 包含 `max (protect n R.scalar fourth) (rounded n fifth)`。
整个 fresh→orderedFifth 的 signed 前沿、owner 外部分和保护/舍入损失
仍需真正控制。新终端完整保留既有 `lowerEarlyDefect`，没有给它设符号。

## 十九项共同装配

名义槽为零基 3…21 共十九项，early 0/1/2 不在其中。
前轮 sixth 九项、本轮 eighth 八项和 fallback 两项各用 eta/3。
八个 later epoch 仍只算七个原名义槽；全部 87 的 savedGain 已含
seed 两次增量，不再另加。

共同次序为：

`h → m0 → 任意 m≥m0 → r0 → 任意 r≥r0 → n0 → 任意 n≥n0
→ E≤eMax → 任意 rational 0<e<E → 任意 qMin → q0≥qMin
→ 任意 q≥q0 → a,omega → eventual even N`。

保留完整原域 `0<omega<thirdPrefixRho`、`omega≤a≤1/800` 和
fallback 所需 `omega≤h`。r、n、q 可继续增大，e 可继续缩小。
取 cap=N、z=N^(19/96)，用实际指数比较满足 eighth 原供应的 N^mu≤z≤cap。

新 raw 终端是：

```
normalize(rawRoot(finalPolicy))
  < quotedAll22Raw + lowerEarlyDefect + eta.
```

这是十九项真实付款后的实际最终 raw 系数界；不是已经去除 early defect 的 K 界。

## 同一最终 rho 的物理密度和真实计数

随后调用 final bank 的 `Canonical.paid`，一次选择
`eps < min epsilonMax (h/nu)`，再选 k 和共同 N0。
由原输出和 eps<1/8 得 `0<nu*eps²<thirdPrefixRho`、
`nu*eps²<a`、`nu*eps²≤h`。因此同一 beta/omega 同时满足
raw 和 compiler 的全部条件。

只使用 ordinary eighth 付款，不再加一次 eighth positive-presieve/beta 费用。
原 compilerReserve 付一次。通过原 reserve_raw_is_actual_final 和正的 C_N/log N，
得到同一实际 F、Q、rho 的物理密度候选：

```
physicalDensitySum Q rho
  < (K - densityReserve - exactSlack + lowerEarlyDefect + eta) * C_N/log N
      - actualPresieveCorrection.
```

未花掉的 densityReserve 和 exactSlack 原样显示，没有假定 early defect 可由它们支付。

同一终端还给出真实 `RealB b N` 的有限上界：
源集合基数乘上上述物理界，加上同一 Q/rho 的
`realPhysicalDistributionError`、`Nat.ceil z` 和 `T+1`。
完整保留 `0<b<1`、`0<T` 和实际 ceiling sieve gate；
没有换权、删误差或改端点。另保留原严格 q<N^0.599 支撑界和 compilerExpense 付款。
这里的 distribution error 仍是带符号的真实量，没有假定 uniform PP 已得出。

## 验证与交接

两位独立只读审阅分别核查 raw 调度/十九槽字典和同 rho compiler/count 连接，
未发现必要修复或阻断；见 REVIEW.md。
新源共 3 个 raw theorem、1 个物理界 definition 和 1 个 counting theorem。
禁用 token 文本扫描无匹配。Git blob 回读和直接依赖指纹用于精确交接，
不代替 elaboration、有限证书、完整类型、公理或内核验证。

未运行 Lean/Lake/内核/CI，未使用用户 Codex 工具或本机，未创建定时任务。
所有提交带 [skip ci]。不标绿，也不把任何完整原黄色职责升蓝。
现有编译修复流程须按新精确源码 SHA、前轮清单和本轮清单串行验证；
若此前闭包已有运行，复用其匹配结果，不重复启动。

剩余主入口集中为 actual early 0/1/2 的完整前沿与保护/舍入控制，
以及最终这个 Q/rho 的 uniform signed PP。取得 early135 精确源码时须先复核，
不要重做已存在的历史积分 floor。Full hUpper 仍未闭合。
