# P2.6 原字符紧凑表示：cell00 限定原型

## 已完成的范围

独立候选 `/workspace/p26-recovery-candidates/archive-packed-chars` 已完成四个 Lean 模块。通用字符/整树往返、长度与跳块正确性通过 normal 和独立 leanchecker；真实 geometry00 数据 normal、长度及前 20 字符 normal 和独立 leanchecker 均通过。生产 Core、原 SourceJson/typed decoder、此前成功的 CharList/前三字段对象均未修改；未提交远端任务。

这是输入表示原型。未运行完整 JSON parser、typed decoder 或其它 25 份输入；未证明旧 Core 的封闭 String 等式或旧 CharList 与新 packed 的整串封闭等式，不把此次长度/前缀验收当作上述义务的证明。

## 编码及已证正确性

`radix = UInt32.size = 2^32`。每个叶子存真实字符数与 Nat：`packWord (c :: cs) = c.toNat + radix * packWord cs`。解码严格由字符数控制；不会在 packed Nat 为 0 时提前停止，因此真实 NUL，包括末尾 NUL，均保留。Nat 无定宽溢出。`unpackWord_packWord` 逐个恢复原 `Char.toNat` 并使用同 pin 的 `Char.ofNat_toNat`；Unicode scalar 的正确性来自该往返证明，不以“数字小于基数”冒充排除 surrogate 的条件。

树按原列表 `take (length/2)` 和 `drop (length/2)` 保持左右顺序，目标叶大小为 256 字符。fuel 耗尽时将**全部**剩余列表打包为叶，绝不截断输入。已证明对任意 fuel、任意 Char 列表的整树往返，因此空输入、256/257 边界、余块、Unicode、CRLF 和 NUL 均无需附加 ASCII 假设。未把分块形状的复杂度性质作成额外数学断言。

核心公开接口：

```lean
unpackWord_packWord (cs : List Char) :
  unpackWord cs.length (packWord cs) = cs
unpack_packTreeGo (fuel : Nat) (cs : List Char) :
  (packTreeGo fuel cs).toList = cs
unpack_pack (cs : List Char) : (pack cs).toList = cs
Tree.length_toList (t : Tree) : t.toList.length = t.count
Tree.toList_drop (t : Tree) (skip : Nat) :
  (t.drop skip).toList = t.toList.drop skip
Tree.count_drop (t : Tree) (skip : Nat) :
  (t.drop skip).count = t.count - skip
```

树计数由 children/leaf count 直接推导，未另放未经证明的缓存长度。`drop` 在整个左子树被跳过时不解码左子树；叶子内以 `word / radix^skip` 跳过前缀。越过叶长度时返回空；以上行为与 `List.drop` 的关系均有泛型证明。

## 实际输入与引文边界

实际文件：`/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`。

- 原文件 195,134 bytes；本例全 ASCII，解码后 195,134 codepoints。
- SHA256：`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`。
- 原始换行是 CRLF。loader 使用 `IO.FS.readFile`，随后完整 `s.toList`，调用本模块已经证明的**同一个** `pack`，最后仅按 empty/leaf/branch 逐构造 quote。没有 Python/host JSON 解析、数值数学预检、截断或换行规范化。
- 独立 generator 只从原 `read_bytes().decode('utf-8')` 机械报价前 20 个字符，目标为 `[123,13,10,32,32,34,100,105,109,101,110,115,105,111,110,34,58,32,56,44]`；它保留了 CRLF、dimension 键、整数 8 及随后的逗号。
- 完整数据进入 Lean 的边界仍是可审查的原文件 quotation。通用 `unpack(pack cs)=cs` 已在内核证明；此次未另外构造并证明与旧 String/CharList 定义的整串闭合等式。SHA 只用于原件/源/对象溯源，不代替 Lean 字符等式。
- 当前是诊断 staging 路径。未来若采纳为生产输入，仍须保留原 `../goldbach-research/...` 两类 13 项映射；本原型不宣称已完成生产路径替换。

实际闭合定理：

```lean
geometryPacked00_count : geometryPacked00.count = 195134
geometryPackedChars00_length : geometryPackedChars00.length = 195134
geometryPackedChars00_take20 :
  geometryPackedChars00.take 20 = geometryPackedPrefix20
```

长度由小的结构计数闭合 guard 与泛型长度定理组合，不展开整串字符。前缀直接使用 `decide +kernel` 核验原 packed 解码得到的前 20 字符。上述定理均无假设。

## 实测

固定同 pin Lean 4.33.0-rc1（commit `62eed1db4d67327ec8120be05f1a1b0847d74561`），只导入 Lean，无 Mathlib。每个阶段原预算均为 4 GiB RSS / 180 秒，`maxRecDepth=1000000`、`maxHeartbeats=0`、单线程。RSS 为 20 ms 采样的进程树峰值。

| 阶段 | 状态 / exit | 秒 | peak RSS bytes |
| --- | --- | ---: | ---: |
| 通用 codec normal | succeeded / 0 | 2.384 | 1,645,133,824 |
| 通用 codec leanchecker | succeeded / 0 | 1.042 | 1,398,161,408 |
| 真实 cell00 数据 normal | succeeded / 0 | 1.410 | 1,637,732,352 |
| 长度 normal | succeeded / 0 | 1.236 | 1,637,838,848 |
| 长度 leanchecker | succeeded / 0 | 1.067 | 1,406,259,200 |
| 首 20 字符 normal | succeeded / 0 | 0.922 | 1,624,477,696 |
| 首 20 字符 leanchecker | succeeded / 0 | 0.844 | 1,398,923,264 |

唯一失败是 `core-v1` 的 `Tree.toList_drop` 空树分支 `rfl` 无法归约符号 `skip` 的 `List.drop skip []`，1.474 秒即报表达错误；源、日志保存在 `attempts/core-v1` 与 `logs/normal-core-v1*`。只将该证明分支改为 `simp only [Tree.drop, Tree.toList_empty, List.drop_nil]` 后通过。失败 elaboration 的 `sorryAx` 是错误占位传播，只存在失败日志，没有可接受对象；成功 10 项 `#print axioms` 结果仅为空、`[propext]` 或 `[propext, Quot.sound]`。实时成功源码无 sorry/admit/new axiom/native_decide/unsafe。

真实 packed 数据对象为 **1,201,072 B**，已有显式 CharList 数据对象为 **6,361,008 B**，本例对象缩小约 81.12%，约为旧对象 18.88%。两种 owner 的 imports/定义细节不同，时间和内存只能作为各自实测，不能当成一般性能倍率。整个 26 文件规模和最大 14 MB 输入尚未试验，未声称可扩展通过。

数据 owner 只按授权完成 normal，没有单独重放数据 owner 的 leanchecker；通用定理、长度、前缀 owner 均各自做了独立 leanchecker。这里的 kernel 结论限于这些实际重放的模块，不外推整个生产 Archive 闭包。

## 来源、复用和交付

参考 P1 checkout `298670f119d24874b719facb3ef756f1e01223a1` 的 `ImbalancedChen/P4AOriginalNewFifthArchiveReader.lean`（SHA `59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6`）：复用原始 Nat literal 叶、保持顺序的 balanced tree 与 prepend/list/length 证明思路。原 P4A 没有 Unicode `unpack(pack)=cs` 全树定理，所以本轮明确新增了输入表示正确性证明，没有继承不存在的验收信用。

- `ImbalancedChen/P2OriginalSaving19PackedChars.lean`：通用 codec 与全部正确性定理。
- `ImbalancedChen/P2OriginalSaving19PackedCharData00.lean`：真实原文件机械 loader。
- `ImbalancedChen/P2OriginalSaving19PackedCharLength00.lean`：真实长度 guard。
- `ImbalancedChen/P2OriginalSaving19PackedCharPrefix00.lean`：真实首 20 字符 guard。
- `generate_owners.py`、`run_check.py`：可重放生成与固定预算诊断（成功对象有防覆盖保护）。
- `RESULT.json`：全部 8 次尝试、完整 source/object/log SHA、原输入前后 hash、精确 axioms、旧对象未变记录。
- `SOURCE_ORIGIN.json`、`LOADER_MANIFEST.json`、`STATIC_AUDIT.json`：复用来源、引文边界与禁止构造扫描。

本轮停止于授权的有限原型。是否采用为新版本正式输入，由主线依据此次证据决策；完整原 parser/typed decode/Archive 语义目标仍待后续组合证明。
