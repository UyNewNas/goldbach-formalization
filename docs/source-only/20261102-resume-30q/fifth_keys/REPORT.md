# Q06 — fifth archive keys / original NPY：精确复用

状态：**源码供应已存在；本次不新增 Lean，不重复有限证书。P1.4.bytes / P1.4.keys 的 kernel 认证仍 OPEN。** `compiled=false`、`kernel_verified=false`、`formal_credit=0`；下述全部历史 finite guards 均 **UNEVALUATED**。交付仅为本目录 REPORT/REGISTRY；未编译、未跑 guard、未重生成或解析数据。

## 原始输入与生产段

先读 Q/BRIEF、q01_local_reuse、P/adopted87_policy 的 REPORT/REGISTRY、P/reviews/t26_review_policy_reserve 及 main.md 的 P1.4 黄叶。原稿 `manuscript-body.tex:367–374` 要求实际 prefix、祖先决策、successive replacements 与 same-stage 域分离；`:1328–1337` 明确四正项减真实 saving、同域改进不能重计。keys 认证只服务这一真实源银行，不供应动态 parent 或积分端点。

原 exporter `../goldbach-research/export_fifth_prefix_jensen_witness.py:9–25` 收集原 `exact_term` 调用，调用 `run(200,1,.8)`，保留原顺序，输出十列 `[n,l1,l2,l3,l4,l5,mask,vertex_gap_sum,A,B]`，mask 是原 zero-based slot 位编码。`:26–28` 对 locked gain/stream 的 assertions 是生产程序源码，**本次没有执行**。原 Jensen producer `certify_fifth_prefix_jensen.py:77–100` 生成初始有序 keys、选取 accepted cells，再将未接受父格作 `2*lo+BITS` 子分割；不能把阅读这段程序当作实际 archive 已通过去重检查。

独立 archive 为 `docs/source-only/20261028-paper-first/cohort04/upper/pure-data/d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7/cells.npy`，23410768 bytes，SHA256 `d6c59992f3f89d7ff30ad5b02e3f95f0d15205ed3446961862c0f126298f17b7`。L 保留 fixture 同尺寸同 raw hash。这里只重新核 metadata/hash，没有解 NPY payload、比较行、排序 keys 或计算 bounds。原文件和 typed literal 是两个独立输入，raw hash 不是 Lean 字节等式证明。

## 已有供应：精确调用，不再制造目标前提

| 所需接口 | 直接复用源码和声明 | 证明体 / 边界 |
| --- | --- | --- |
| 完整实际索引 | E `upper_mesh/P1HistoricalFifthIndexedOwnerArchive.lean:26–37`，`ArchiveIndex`、`archiveRow`、`archiveIndex_card`、`archiveRow_source_member` | 索引是原 hub 的 `Fin rows.toList.length`；全部 292633 源位置，保序与 multiplicity。不是任给的 row family。 |
| 五个 signed keys 正性 | F `upper_mesh/P1HistoricalFifthTypedBaseGeometry.lean:20–29,33–883,885–1178`，`LowerKeyBounds`、143 个 `blockNNN_lower_key_bounds`、`rows_lower_key_bounds` | `LowerKeyBounds row = ∀ k : Fin 5, 1 ≤ row.lo k ∧ row.lo k ≤ 77`；143 个闭 `by decide` 对原独立块，按原 hub `block_order` 合并。无 positive-key 输入前提。 |
| 实际每个索引正键 | 同文件 `:1181–1193`，`rows_baseGeometry`、`archiveRow_baseGeometry` | `(archiveRow_baseGeometry i).2.2.1 k` 直接给 `1 ≤ (archiveRow i).lo k`；或者 `rows_lower_key_bounds (archiveRow i) (archiveRow_source_member i) k` 给完整上下界。若消费者写 `0 < ...`，由整数 `0 < 1 ≤ ...` 即得，不是新数据证书缺口。 |
| 完整原 key 列表去重 | F `upper_mesh/P1HistoricalFifthTypedKeyPartition.lean:21–91`，`actual_sorted_codes_strict`、`actual_typed_codes_nodup`、`actual_typed_keys_nodup` | 对同一完整原列表的 Nat400 码排序，闭 `by decide` 断言相邻严格；实际归纳给 sorted Nodup，再由 permutation 回原序，`List.Nodup.of_map` 回五键。没有将目标 Nodup、checker flag 或 typed equality 当输入。码的逆向单射不是所需前提：相同 keys 必有相同码。 |
| 源索引与 key 唯一性 | 同文件 `:97–123`，`actual_records_key_injective`、`archiveIndex_eq_of_key_eq`、`archiveRow_injective`、`actual_records_card` | 先证明原 list 的 keys Nodup，再导出 Finset/card；没有先 toFinset 丢去重复。`:125–136` 给真实 half-open raw boxes 分离/共同点索引唯一。 |
| 独立原 bytes 构造 | L `original_npy_kernel/P1HistoricalFifthOriginalByteLiteral.lean` 与 `P1HistoricalFifthOriginalNpyKernel.lean:30–45` | `include_original_bytes%` 于用户编译时读取独立 fixture，透明 `ByteLiteral`；不是 `encodeFrame typedRows`。这里不执行 elaborator。 |
| 原 bytes → 全实际 typedRows | L 同 Kernel `:76–157`，`SameColumns`、`OrderedColumns`、`ParseColumns`、`original_complete_ordered_columns`、`original_complete_parse`、`original_complete_field_association` | full-compare 闭 `by decide` 对原 `decodeFrame originalBytes` 与实际 hub 全部十列、全部原顺序、精确 terminal length；不存在 agreement、parse success 或 typed-equality 假设。ordinary proof 把比较转成严格等式。 |
| 解析所得原 rows 的 keys / positivity | L 同 Kernel `:185–199`，`original_parsed_keys_nodup`、`original_parsed_baseGeometry` | 复用 F；参数 `h` 是要辨认所给 `parsed` 的解析关系，而实际源解析成功已由闭 `original_complete_parse` 供应。不是要求调用者证明原 archive 的目标认证。正性仍由 baseGeometry 字段投影获得。 |

表内 E/F/L 缩写分别指 `20261028-resume-30e`、`20261028-resume-30f`、`20261102-certificates-l`。每个完整路径、raw hash、直接 imports、intended module、声明和行号见 REGISTRY。

## 隐藏搜索与原表绑定

显式搜索全部 `docs/source-only` 和 `.lake/proof-continuation/source-reviews/drafts`，使用 `rg --hidden --no-ignore`，包含 `.lean` / `.txt`，并按 `typedRows`、archive/positive keys、`actual_typed_keys_nodup`、`rows_lower_key_bounds`、`original_complete_parse` 及真实模块名定向核查。实际 key/lower-bound 声明供应是上述 F；完整原字节比较是上述 L，J 的 `OriginalNpyAssociation` 仅是被 L 消费的旧 positional criterion。没有把隐藏 PhysicalRows/当前目标性质字段封装当作证书。

实际 hub 是隐藏 frozen `4590eb2a.../P1HistoricalFifthSavedTableData.lean`，引用 143 个独立原块；shape 来源为 frozen `9f9830bf.../20261028-Upper-Sol6-Phase3-TypedShapeCandidate.txt`；grid/mask/signed64 range 来源为原 `79445fb1.../20261028-Upper-Sol6-Phase5-TypedRangeCandidate.txt`。本次重新 hash 这 143 个源文件，全部与 L 的既存 pin 相同；未执行 literal 的数学断言。安装须沿既存 module targets 布置这些源文件，`.txt` 是可复用 Lean 源而非已安装模块，不能只安装最上层 F/L 文件。

L 的 source-relative fixture 必须安装到 `ImbalancedChen/provenance/original-fifth/cells.npy`；L/REGISTRY 已登记 J、F、E、hub/shape、143 块及解析器来源。本次登记补入 F 直接消费的 TypedArchiveRange 精确路径，作为复用定位，不复制或改写其证明体。

## 消除的排队项与保留的义务

**没有发现本任务范围内尚未写出的实际索引、正键、去重或 full bytes→typed rows 源码接口。** q01/main 所列黄叶不能再解释为“这些源码证明体不存在”。本次消除的是重复实现的工作项：原 143 块 positive-key 证书、完整 keys Nodup 证书和 L 的全比较证书均有闭源体，直接复用。新 Lean 声明数为 0；新增 guard 数为 0；不另写一个以相同目标为前提的 consumer。

尚未消除任何历史数据的 kernel 验证义务：F 的 143 lower-key guards、1 个 sorted-code guard，以及其依赖的 143 TypedValid guards 均未执行；L 的 literal length、128-byte header、完整 292633×10 signed-field comparison 同样未执行。Lean API/elaboration、巨量归约的时间/内存/栈可行性及全部 source-only imports 的安装仍未验证。精确失败或资源失败一旦出现，原目标仍保持 OPEN，不能以一般 Nodup 定理或部分比较替代。

同一 q 的完整 decoded gates、真实 Q3/Q4 parent、其他 75 eighth 域、完整 87 域历史/owner、逐 parent floor→实际总积分仍在本任务外，也不因 key 正性或 parse equality 得出。原 c/K、rho、mask、十字段、顺序、multiplicity 和所有边界约定均未改变。缺口分类是已有源码的安装/表达/API/有限认证待验；本次未发现可据以声称原稿数学错误的证据。

仅执行 read/search/hash/JSON 和本目录文档写入；没有 Lean/Lake/编译/CI/Git/数学重放/guard evaluation/数据再生成/子代理，也未修改任何旧文件。
