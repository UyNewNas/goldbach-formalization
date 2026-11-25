from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'ImbalancedChen'
def fp(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
runs=[json.loads(p.read_text()) for p in sorted((ROOT/'logs').glob('*-result.json'))]
by={(r['mode'],r['tag']):r for r in runs}
expected=[('normal','core-v1'),('normal','core-v2'),('kernel','core-v2'),('normal','data-v1'),('normal','length-v1'),('kernel','length-v1'),('normal','prefix-v1'),('kernel','prefix-v1')]
assert set(by)==set(expected)
for k in expected:
 r=by[k]
 assert r['status']==('failed' if k==('normal','core-v1') else 'succeeded')
 assert r['source']==fp(Path(r['source']['path'])) or k==('normal','core-v1')
 if r['object']:
  assert r['object']==fp(Path(r['object']['path']))
 assert r['fixture_before']==r['fixture_after']
old=Path('/workspace/p26-recovery-candidates/archive-character-core')
invariants=[]
for rel,expected_sha in [
 ('objects/ImbalancedChen/P2OriginalSaving19CharacterCore00.olean','e8d785d76de156581dc5ae2c986d98bc7cc44387695ebb31f10110d0ea2719d9'),
 ('objects/ImbalancedChen/P2OriginalSaving19CharacterLength00.olean','4dcfa678dad2b10c69798981a79d40d2408c26671b4957b6882b459adea5e498'),
 ('objects/ImbalancedChen/P2OriginalSaving19DimensionPrefix00.olean','2792ba91cb949245fefb1cd11b21990399a6eb7e44359f9d95b95d4c28784304'),
 ('objects/ImbalancedChen/P2OriginalSaving19FirstThreeFields00.olean','1c49efaa3ffa5fac22e9906a8413036f7087e3ca74a979d08d123a2c8f337a79')]:
 v=fp(old/rel);assert v['sha256']==expected_sha;invariants.append(v)
for p in SOURCE.glob('*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\b',p.read_text(),re.M),p
axioms={}
for mode,tag in [('normal','core-v2'),('normal','length-v1'),('normal','prefix-v1')]:
 log=Path(by[(mode,tag)]['log']['path']).read_text()
 assert 'sorryAx' not in log
 for line in log.splitlines():
  m=re.match(r"'([^']+)' depends on axioms: \[(.*)\]",line)
  if m:axioms[m[1]]=[x.strip() for x in m[2].split(',') if x.strip()]
  m=re.match(r"'([^']+)' does not depend on any axioms",line)
  if m:axioms[m[1]]=[]
assert len(axioms)==10
assert all(set(v)<=set(['propext','Quot.sound','Classical.choice']) for v in axioms.values())
old_data=json.loads((old/'logs/normal-data-result.json').read_text())
new_data=by[('normal','data-v1')]
comparison={'old_data_object':old_data['object'],'packed_data_object':new_data['object'],'object_size_ratio_packed_over_list':new_data['object']['bytes']/old_data['object']['bytes'],'object_size_reduction_percent':100*(1-new_data['object']['bytes']/old_data['object']['bytes']),'old_data_normal_seconds':old_data['elapsed_seconds'],'packed_data_normal_seconds':new_data['elapsed_seconds'],'old_data_peak_rss_bytes':old_data['peak_rss_bytes'],'packed_data_peak_rss_bytes':new_data['peak_rss_bytes'],'scope':'Observed single geometry00 only; differing import closures and compilation details preclude a general runtime benchmark. No all26 scale claim.'}
result={'status':'scoped_prototype_passed','pin':{'lean':'4.33.0-rc1','lean_commit':'62eed1db4d67327ec8120be05f1a1b0847d74561','mathlib_imported':False},'limits':{'rss_bytes':4294967296,'wall_seconds':180,'maxRecDepth':1000000,'maxHeartbeats':0,'sampling_seconds':0.02},'results':[by[k] for k in expected],'axioms':axioms,'comparison':comparison,'original_input':json.loads((ROOT/'LOADER_MANIFEST.json').read_text()),'preserved_prior_objects':invariants,'acceptance':{'whole_unicode_pack_roundtrip':True,'tree_drop_correctness':True,'actual_cell00_data_normal':True,'actual_cell00_length_normal_and_independent_kernel':True,'actual_cell00_first20_normal_and_independent_kernel':True,'actual_data_owner_separate_kernel':False,'whole_json_parse':False,'typed_decoder':False,'old_Core_string_closed_equality':False,'old_CharList_whole_closed_equality':False,'all26_scale_verified':False,'production_modified':False,'remote_jobs_submitted':False}}
(ROOT/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
static={'live_lean_sources':[fp(p) for p in sorted(SOURCE.glob('*.lean'))],'forbidden_tokens_present':False,'audited_axioms':axioms,'data_loader':{'readFile':True,'complete_toList':True,'same_proved_pack':True,'constructor_preserving_quoteTree':True,'host_JSON_parse':False,'normalizes_CRLF':False},'preserved_prior_objects':invariants}
(ROOT/'STATIC_AUDIT.json').write_text(json.dumps(static,indent=2)+'\n')
rows=[]
for k,label in [(('normal','core-v2'),'通用 codec normal'),(('kernel','core-v2'),'通用 codec leanchecker'),(('normal','data-v1'),'真实 cell00 数据 normal'),(('normal','length-v1'),'长度 normal'),(('kernel','length-v1'),'长度 leanchecker'),(('normal','prefix-v1'),'首 20 字符 normal'),(('kernel','prefix-v1'),'首 20 字符 leanchecker')]:
 r=by[k];rows.append(f"| {label} | {r['status']} / {r['exit_code']} | {r['elapsed_seconds']:.3f} | {r['peak_rss_bytes']:,} |")
report='''# P2.6 原字符紧凑表示：cell00 限定原型

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
ROWS

唯一失败是 `core-v1` 的 `Tree.toList_drop` 空树分支 `rfl` 无法归约符号 `skip` 的 `List.drop skip []`，1.474 秒即报表达错误；源、日志保存在 `attempts/core-v1` 与 `logs/normal-core-v1*`。只将该证明分支改为 `simp only [Tree.drop, Tree.toList_empty, List.drop_nil]` 后通过。失败 elaboration 的 `sorryAx` 是错误占位传播，只存在失败日志，没有可接受对象；成功 10 项 `#print axioms` 结果仅为空、`[propext]` 或 `[propext, Quot.sound]`。实时成功源码无 sorry/admit/new axiom/native_decide/unsafe。

真实 packed 数据对象为 **1,201,072 B**，已有显式 CharList 数据对象为 **6,361,008 B**，本例对象缩小约 REDUCTION%，约为旧对象 RATIO%。两种 owner 的 imports/定义细节不同，时间和内存只能作为各自实测，不能当成一般性能倍率。整个 26 文件规模和最大 14 MB 输入尚未试验，未声称可扩展通过。

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
'''.replace('ROWS','\n'.join(rows)).replace('REDUCTION',f"{comparison['object_size_reduction_percent']:.2f}").replace('RATIO',f"{comparison['object_size_ratio_packed_over_list']*100:.2f}")
(ROOT/'REPORT.md').write_text(report)
files=[p for p in sorted(ROOT.rglob('*')) if p.is_file() and p.name!='MANIFEST.json']
manifest={'candidate_root':str(ROOT),'files':[fp(p) for p in files],'compiled_result_count':len(runs),'passed_result_count':sum(r['status']=='succeeded' for r in runs)}
(ROOT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'report':fp(ROOT/'REPORT.md'),'result':fp(ROOT/'RESULT.json'),'manifest':fp(ROOT/'MANIFEST.json'),'static':fp(ROOT/'STATIC_AUDIT.json'),'axioms':axioms,'comparison':comparison},indent=2))
