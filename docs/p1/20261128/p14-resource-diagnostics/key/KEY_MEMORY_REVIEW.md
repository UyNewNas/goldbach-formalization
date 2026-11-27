# Key 闭合唯一性证书：失败证据与 inverse-index 路线审查

## 1. 本次实际失败

完整只读导出任务 `job_c4cf0ce42d3849a480fed5f64ec4a7c0` 已读至 EOF：2 页、33977 B，SHA-256 `e40e69a75ed12b264b20e0431fcf57b8f1963d044e7822e0daba04fb2c73d7cc`。7 份原文件全部按长度与 SHA-256 恢复；没有重新运行原任务。

原 normal.log 为179880 B，SHA-256 `a43621ef5f2fb8a712c6df0853d3304675e02f4777a19c02dbb0baedcd7e83d6`。其2405行明确报告：

```text
ImbalancedChen/P1HistoricalFifthTypedKeyUniquenessCertificate.lean:16:2:
(kernel) excessive memory consumption detected
```

原 normal command 完成于48.59695251秒、exit1；built=[]。单stage RESULT和pipeline保存了失败，accepted_owners=[]，whole_P1_4_complete=false。源码部署与404模块只读检查均成功，它们不属于定理验收。source-only 没有编译或修改对象；原 checkout head/status 保持不变。

这是有完整失败终态的 kernel 内存诊断，与 Indexed 的外层 SIGKILL 且未写出normal-command不同。原guard保持 `-t0 -j2 -M12288` 的固定方案；本次导出没有新的per-PID runtime journal条目，因此不把pipeline里的资源预期冒充重新读取的实际注入argv。外层运行158.819秒、peak13609013248 B由root提供，未由本代理重复读取。

该报错定位在第16行开始的kernel诊断命令；它没有区分具体峰值来自map、mergeSort、decidable归约还是kernel缓存。不能只凭这一行称“纯排序开销”，也不能称证书为假。

## 2. 原数据的精确本地事实

纯Python逐字解析了原hub的全部143块、292633行和每行十个signed整数字段，未忽略payload行。143个数据源和hub的长度/SHA逐份匹配已经冻结的d14源闭包审查。解析器及全部源pins保存在 `analyze_key_blocks.py` / `KEY_BLOCK_DATA_ANALYSIS.json`。这不是Lean证明或原NPY字节真实性证明。

| 项目 | 全量观察 |
|---|---:|
| 原块数 | 143 = 142×2048行 + 1817行 |
| 原行数 | 292633 |
| 不同geometry keys | 292633 |
| 不同codes | 292633 |
| 块内不是严格递增的原块 | 143 / 143 |
| 满足max(block_i)<min(block_i+1)的相邻块对 | 0 / 142 |
| code区间相交的原块对 | 907 / 10153 |
| 区间相交连通分量 | 1，含全部143块 |

`rowKey raw = raw.lo`，`codeOfKey`只有五个lo坐标的base400编码，不含mask。block000前两code是795524330425、769860490425，已经给出原顺序不递增的具体见证。每个原块先排序，再直接按块拼接或仅重排整块，都不能用端点区间分离完成全表证明。

分桶的实际量级也已测得：`code / 400^4`有47个非空桶，最大16111行；`code / 400^3`有1106桶，最大790行。此方向需要完整覆盖和permutation证书，不能直接用Python桶作为前提。

## 3. 继续复用的可靠工作

- Key Core：源f475f4f9…，原RESULT ea85ed43…；原编码、`AdjacentStrict`、构造性Decidable及`adjacentStrict_nodup`均保留。
- Shape：源8e13f914…，原RESULT9e128dc7…；使用`rows_toList_order`、`block_order`、`block_sizes`和完整292633长度。它的block_order是原始顺序，不是key排序。
- Range aggregate：源609ba2dc…；checkpoint13原RESULT1042 B，SHA-256 `34122b8065bbac754be1923be112f4038e74150be6d4e1241cfc9fbf468ebcf4`，accepted owner确为TypedArchiveRange。其grid/mask/signed64范围不提供唯一性，也不是inverse路线需要新增的假设。
- StoredParentArchive：源88508e6e…，已有完整normal/kernel/13-owned验收。其72块sourceIndex合并方法可借鉴，不重编。

本地检索未找到已经为本题原typedCodes实现并验收的packed-code→原位置反函数/BST。P4上的HashMap lookup→位置唯一性只是其他数据的证明模式，不引入这些项目模块，也不把其验收当成本题证据。

StoredParent只有sourceIndex/oldQ80/newQ80，没有geometry keys；不能替代原typed source。特别是 `P5FullStoredParentSameOwnerBinding` 已经导入TypedKeyPartition，不能反向用于Key证书，否则形成循环。

## 4. 推荐先审查 inverse-index 证书

此路线逻辑上成立，而且无需全表filter/permutation归约：固定一个纯Lean、全定义的 `g : Nat → Nat`，把本题code查回原全局位置；未知code可返回0。g本身不需要单射、排序正确或全域查找正确的假设。

对全部143原块分别核验闭合等式：

```text
map g (originalBlockCodes b) = List.range' (2048*b) actualBlockLength
```

最后块长1817，其余2048。code必须仍由原block的五个lo字段和原 `codeOfKey` 计算，不能替换成外部输出的code表或跳过任何原位置。

这些局部等式经Shape的精确顺序桥与标准map/append组合，给出完整 `map g typedCodes = List.range 292633`，进而由range无重复和已经使用过的 `List.Nodup.of_map` 得到一个**独立**的 `typedCodes.Nodup` 辅助证书。

其可靠性很直接：如果两个原位置code相等，同一个总函数g必给相等结果；两条闭合证书却要求它们等于不同的原位置，于是至少一条证书无法通过。错误候选查找表、默认0或重复code不能绕过这个约束。既不需要证明codeOfKey全域单射，也不需要添加lo范围前提。

之后以泛型mergeSort排序性质、`mergeSort_perm`及Nodup推出原 `AdjacentStrict sortedCodes`，保留原三条public命题与原292633行对象。不能在第一条定理中引用现有 `actual_typed_codes_nodup`，因为现有证明方向正从第一条定理推出它；新辅助证书必须独立。

## 5. 已有API与避免全局归约的组合方式

本地实际使用已确认：`List.Nodup.of_map`、`List.map_append`、`List.map_flatMap`、`List.mergeSort_perm`、`List.pairwise_mergeSort'`，以及已验收StoredParent块中的 `List.getElem?_range' (s := …) (step := 1) bound`。

尚未核实当前固定库中range'拼接定理的准确名称和参数，不应凭名字写代码。可靠替代组织方式已有先例：StoredParent先把局部map=range'转成点态sourceIndex等式；其私有 `append_source_index` 使用 `Array.size_append` 与 `Array.getElem_append_left/right` 抽象组合，最终没有决定一个全局292633长range等式。它专用于StoredParent，不能直接当成本题泛型定理；需要一个小型g组合桥或相应标准List接口。

尚需新的技术性证明只有：本题g的总定义、143条真实闭合原块义务、抽象索引组合桥、以及“非严格有序＋Nodup⇒原AdjacentStrict”的标准列表桥。它们服务于同一个稿内闭合证书，不增添数据前提或稿外数论结论。

## 6. 资源风险与下一步边界

g不能在Lean内部通过整表排序/过滤临时构造，否则每个小证书仍可能隐藏原全表计算。候选查找结构应是固定的纯Lean字面量数据，以每条原块证书验证它在实际输入上的结果。

292633条目按中位数平衡时理论最大19层。可以考虑143个≤2048条目的sorted-key字面量分片，再用固定路由查找；没有生成这些Lean文件或证明。纯Python观测每个原source block会访问2–25个这种候选分片，block048访问25个，后续若资源允许可作为比仅测block000更有信息的诊断对象。

g的大常量、导入后的常驻内存、多个lookup路径以及kernel缓存仍可能占内存。Range/StoredParent说明“局部闭合检查＋抽象组合”的组织已有可靠先例，但不证明本方案必在12GiB内。应先固定g设计与原源绑定、核对精确API和泛型桥，再安排一个有明确诊断目标的小试；当前P1 lane busy，不执行基准，也不批量造143/1106份新证书。

组合层不得再对完整sort、完整map/range或全部字典执行一次大decide；那会重新形成同一峰值。保留原guard、serializer、资源参数和closed target；不使用native_decide、外部Boolean前提、sorry、axiom或内存加码。

## 7. 稿件范围和本轮状态

冻结1106稿件SHA-256 `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`，277–284行保留完整父/子规模，505–512行保留联合固定cap/branch/parent条件。以上路线保持全部原位置及原唯一性命题。当前没有由此失败展示的实质数学缺口，也尚未得到新的Lean验收。

本轮仅完整读取指定诊断任务、核对本地原文件和纯Python数据、准备这份审查。未提交远程任务、未编译、未修改仓库/Git、未生成g或批量证书，whole_P1_4_complete=false。
