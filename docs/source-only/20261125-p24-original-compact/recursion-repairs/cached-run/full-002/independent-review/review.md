# CachedRun full-002 独立静态审阅

审阅者：`/root/p24_scope_audit`。只读取本地源码、补丁和已保存的隔离任务收据；没有编译、远程任务、生产修改或发布。

## 结论与精确输入

未发现八个递归定义的数学语义、分支、顺序或原定理声明漂移。可以保持当前已实测候选，先交原 321 联合门控获取实际结果，再按真实错误作最小证明体调整。隔离通过不能作为新 Ledger、Adaptive、ConcreteRun 联合编译已经通过的依据。

- 原 CachedRun：`b97e7cf8d0be80ccc693db96497250223c7f3a8256726311a457c1be84ccd9b0`，22475 B。
- 本次 full-002：`80aab3eb9bda4146fa09ab0245a5bf93114dbf3f788175fb5ed868bfa8a330d4`，24343 B。
- Ledger：`11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c`。
- Adaptive：`e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6`。

`source-patches.json` 的 16 项替换已独立正向执行并反向恢复：正向结果精确等于本次文件，逆向结果精确等于原 b97e 文件，包括末尾 3 个 CRLF。27 个原 theorem 声明头逐字相同，20 个 def/abbrev 签名在仅规范空白后相同。修改局限于 8 个执行定义与 7 个定理内的 8 处证明调整；其余 12 个 def/abbrev 的 body、原 instance、imports、namespace、options、常量和闭合入口不变。

相对 full-001，本次只增加 `treeFold (β := List Bool → List Scheduled)` 的显式 β 参数，精确增加 37 个 UTF-8 字节。生产候选没有额外 `TreeFoldCandidate` import；该 import 只存在于隔离副本。

## 八个定义的语义核对

| 定义 | 保留的行为 |
|---|---|
| `cachedSeedForest` | 按原 seed 列表次序保留全部根；当前叶使用同一 `issueSerial`，尾部接收同一 `advance`，最终 serial 不变。 |
| `cachedSplitTreeAt` | 只有空路径与叶相遇时才按原 width assertion 分叉；false/true 分别走左/右，重建另一侧不变；父 entry、左右 serial 分配及所有 `none` 情形不变。 |
| `cachedSplitForestAt` | seed 0 选择头树，successor 进入尾 forest 并保留前面的根；空 forest 对任意 seed 都返回 `none`。 |
| `cachedTreeJobs` | 同一缓存 evaluator、seed、path；左地址追加 false，右地址追加 true，先左后右拼接。 |
| `cachedForestJobs` | 每个根从空路径开始，按原根顺序拼接；尾部 seed 恰加 1。 |
| `cachedRunFuel` | 0 分支仍区分 exhaustedFuel 与 stopResult；succ 分支保留原 keepRunning、错误 reason/state 及 next 递归调用；maxSplits、Q80、target、sticky assertions 不变。 |
| `cachedTreeEntries` | 每个叶的 cell、缓存 bounds、serial 全保留，左后右顺序不变；没有引入 heap/positive-error 过滤。 |
| `cachedEntries` | 完整叶列表按原根次序连接，完整有序 charge 数据未变。 |

树遍历使用的 `treeFold` 通过原 split 构造器中的 width 证明取得严格子预算下降，并提供 `treeFold_leaf`、`treeFold_split` 方程。未增加输入前提，也没有把执行 fuel 或 endpoint 条件换成新参数。Ledger 内对应 4421 字节 helper 段与已验隔离 helper 段相同，仅忽略段末空白；摘要为 `46443983f04248eca3ed212dcc0a6c8bdfcc1a03f5f7fcb66d4c9c8508e381c1`。

## Ledger 与 Adaptive 的边界

Ledger 第 216 行 `forest_integer_boxes` 的新证明是兼容的：在 `cons tree rest` 上，`eraseForest` 展开为 `eraseTree tree :: eraseForest rest`，`entries` 展开为 `treeEntries tree ++ entries rest`。Adaptive 第 110 行的新 `sourceIntegerForest` 对第一列表做 `List.rec`，消费这一个 cons 和对应 cell 后，尾部恰是 `sourceIntegerForest (eraseForest rest) cs`。

因此 Ledger 的 generic `change` 保留了与 IH 完全相同的尾函数头，随后 `rw [List.map_append, tree_integer_boxes, ih]` 的方向正确。这里的 forest、cell 和 rest 都是泛型变量，不会因这段 change 引入闭合 originalRun 或 initialSeeds 的计算。完整 ordered leaf identity 仍包括空叶和闭合切面的重复项，未改为 heap 投影。

## 联合门控应观察的证明展开点

以下是尚未编译的备用建议，不是已观察到的失败；当前源码保持冻结。

### `cachedForestJobs_eq`（第 160 行）

当前只在 IH 展开 cached 侧及 tree supplier，目标还展开 `forestJobs`。新 ConcreteRun 的 `forestJobs` 也是 `List.rec`，其右侧尾头可能与旧模式递归版本的 simp 行为不同。若原联合编译实际报错，保留原、未展开的 IH，将 cons 分支改为泛型命名尾式即可：

```lean
change
  cachedTreeJobs nodes seed [] tree ++
      cachedForestJobs nodes rest (seed + 1) =
    treeJobs seed [] tree ++ forestJobs rest (seed + 1)
rw [cachedTreeJobs_eq nodes hlookup, ih]
```

这只展开当前已知 cons 的一层，不要求遍历任意 rest。

### `cachedEntries_eq`（第 319 行）

同型风险出现在新 Ledger `entries` 的 raw `List.rec` 与当前单侧展开的 IH。若实际需要，可保留未展开 IH，使用：

```lean
change cachedTreeEntries nodes tree ++ cachedEntries nodes rest =
  treeEntries tree ++ entries rest
rw [cachedTreeEntries_eq nodes hlookup, ih]
```

### `cachedSeedForest_eq`（第 39 行）

应用已有 `he` 并展开现有 `OriginalForest` 别名后，两个新 `List.rec` body 定义相等；原归纳 IH 可能变得冗余，或与目标的另一侧展开程度不同。若联合编译报错，可考虑在原泛型目标上只用已有 `he` 与 `simp only [cachedSeedForest, seedForest, he]`。这是未经编译的证明体候选，无须预先替换当前已验文件。

### `cachedSplitForestAt_eq`（第 116 行）

zero 分支已经使用显式 generic change。若 succ 分支遇同根匹配错误，可保留未展开的 IH，change 成两个 `Option.map` 的等式，输入分别为同一 rest/seed/path 上的 cached 与 original split 调用，callback 都是保留当前 tree 的 `SourceForest.cons`，再 `rw [ih]`。

### `cachedRunFuel_eq`（第 252 行）

未发现新的同根缺口。现有 generic change 已统一两侧 `keepRunning` 条件，保留命名的 `cachedRunFuel` / `runFuel` 递归尾；成功分支直接 `exact ih next`。新 `Nat.rec` 只需展开一个 successor，不会让 IH 的函数头被 simp 改写。

### 两个树 fold 等式证明

`cachedTreeJobs_eq` 与 `cachedTreeEntries_eq` 明确使用 `treeFold_leaf` / `treeFold_split` 是必要的。split 方程涉及不同 child budget 之间的已证稳定性，不能把它误当成仅凭 `change` 就能获得的定义相等。当前方程用法没有新增数学前提；如果联合编译需要正规化，只调整泛型证明，不展开闭合 run。

## 实测范围与资源

已读取本地 `af16794dc5d34e17b425b4556fca60ca` 的实际 task/receipt：isolated compile、independent replay、原完整 owned 审计全部通过，99 owned，所有 postcheck 通过。收据 SHA 为 `c1333f9a85e937a7d6f0a18bcec99ed4afa1072e892e880affa36b6ffd03c3a8`。

这个隔离测试额外导入 `TreeFoldCandidate`，其余 lower 仍为 6e 原对象，并未同时导入新 Ledger11e2、Adaptivee948 和 ConcreteRun 替换。wrapper 的 Lean 参数与 full-001 完全相同：`-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000`；原 audit template 只替换两处目标名，仍校验完整 owned inventory、安全性、axioms 和完整 type。没有源码 options、生产写回、native requalification 或 A/B/W 执行。

上述 isolated 通过及本静态复核均不授予联合原 321 或完整 324 验收。下一步保持当前精确候选，使用原联合门控取得实际诊断。
