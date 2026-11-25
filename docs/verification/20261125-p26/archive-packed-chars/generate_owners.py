from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
RAW=Path('/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json')
raw=RAW.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691'
text=raw.decode('utf-8')
# This generator only quotes the first 20 original Unicode codepoints for a
# small closed guard. The complete packed payload is built by Lean's loader,
# IO.FS.readFile -> s.toList -> the proved pack, not by Python packing/parsing.
prefix='['+', '.join('Char.ofNat '+str(ord(c)) for c in text[:20])+']'
ns='ImbalancedChen.P2OriginalSaving19PackedChars'
base='''import ImbalancedChen.P2OriginalSaving19PackedChars

/-! Candidate input representation. Only geometry00 is loaded. No parser or
closed equality to the old Core String is asserted. The quotation runs the same
pure pack whose full Unicode/tree round-trip was kernel checked. -/
namespace ImbalancedChen.P2OriginalSaving19PackedChars

open Lean Elab Term
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

private def quoteTree : Tree → Expr
  | .empty => mkConst ``Tree.empty
  | .leaf n word => mkApp2 (mkConst ``Tree.leaf) (mkNatLit n) (mkNatLit word)
  | .branch l r => mkApp2 (mkConst ``Tree.branch) (quoteTree l) (quoteTree r)

elab "includeGeometryPacked00%" : term => do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 before_readFile"
  err.flush
  let s ← IO.FS.readFile "/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json"
  let chars := s.toList
  err.putStrLn s!"PACKED00 after_readFile codepoints={chars.length}"
  err.flush
  let packed := pack chars
  err.putStrLn s!"PACKED00 after_pack structural_count={packed.count}"
  err.flush
  let result := quoteTree packed
  err.putStrLn "PACKED00 after_quote"
  err.flush
  return result

noncomputable def geometryPacked00 : Tree := includeGeometryPacked00%
noncomputable def geometryPackedChars00 : List Char := geometryPacked00.toList

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 data_definitions_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19PackedChars
'''
length='''import ImbalancedChen.P2OriginalSaving19PackedCharData00

namespace ImbalancedChen.P2OriginalSaving19PackedChars
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 length_before_guard"
  err.flush

theorem geometryPacked00_count : geometryPacked00.count = 195134 := by
  decide +kernel

theorem geometryPackedChars00_length : geometryPackedChars00.length = 195134 := by
  rw [geometryPackedChars00, Tree.length_toList]
  exact geometryPacked00_count

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 length_after_guard"
  err.flush

#print axioms geometryPacked00_count
#print axioms geometryPackedChars00_length
end ImbalancedChen.P2OriginalSaving19PackedChars
'''
prefixsource='''import ImbalancedChen.P2OriginalSaving19PackedCharData00

namespace ImbalancedChen.P2OriginalSaving19PackedChars
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false

-- Mechanical quotation of the original first 20 UTF-8 decoded codepoints,
-- including CRLF. No line ending normalization or JSON parsing occurred.
def geometryPackedPrefix20 : List Char := PREFIX

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 prefix_before_guard"
  err.flush

theorem geometryPackedChars00_take20 :
    geometryPackedChars00.take 20 = geometryPackedPrefix20 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "PACKED00 prefix_after_guard"
  err.flush

#print axioms geometryPackedChars00_take20
end ImbalancedChen.P2OriginalSaving19PackedChars
'''.replace('PREFIX',prefix)
files={
 'P2OriginalSaving19PackedCharData00.lean':base,
 'P2OriginalSaving19PackedCharLength00.lean':length,
 'P2OriginalSaving19PackedCharPrefix00.lean':prefixsource}
for name,body in files.items():
 p=ROOT/'ImbalancedChen'/name
 assert not p.exists(), str(p)
 p.write_text(body)
manifest={'original_path':str(RAW),'bytes':len(raw),'codepoints':len(text),'ascii':raw.isascii(),'raw_sha256':hashlib.sha256(raw).hexdigest(),'prefix20_codepoints':[ord(c) for c in text[:20]],'prefix20_raw_hex':raw[:20].hex(),'generator_host_json_parse':False,'loader':'IO.FS.readFile -> s.toList -> proved pack -> constructor-preserving quoteTree','production_changed':False,'old_string_equality_asserted':False,'whole_parse_asserted':False,'files':{name:{'bytes':len(body.encode()),'sha256':hashlib.sha256(body.encode()).hexdigest()} for name,body in files.items()}}
(ROOT/'LOADER_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
