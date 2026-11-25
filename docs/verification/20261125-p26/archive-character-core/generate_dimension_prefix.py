from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parent
BASE=json.loads((ROOT/'MANIFEST.json').read_text())
FIXTURE=Path(BASE['fixture']['path'])
raw=FIXTURE.read_bytes()
assert len(raw)==195134 and hashlib.sha256(raw).hexdigest()==BASE['fixture']['sha256']
assert raw.isascii()
# Work from exact bytes. Path.read_text would normalize CRLF in Python.
prefix=raw[:20].decode('ascii')
assert prefix=='{\r\n  "dimension": 8,'
key=raw[6:15].decode('ascii')
number=raw[18:19].decode('ascii')
assert key=='dimension' and number=='8'
def quote_char(c):
    escaped={'\r':'\\r','\n':'\\n','\t':'\\t','\\':'\\\\',"'":"\\'"}.get(c,c)
    return "'"+escaped+"'"
def quote_list(s): return '['+', '.join(map(quote_char,s))+']'
def mark(s):
    return 'run_cmd do\n  let err ← IO.getStderr\n  err.putStrLn "P26_DIMENSION_PREFIX '+s+'"\n  err.flush\n'
ns='ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic'
source='''import ImbalancedChen.P2OriginalSaving19CharacterLength00
import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
One exact original field, with the original CRLF bytes and trailing comma.
The candidate prefix and expected AST data are mechanically quoted from raw
bytes. Their relationship to the actual reader is certified by Lean below.
No host JSON parser, replacement reader, copied whole tail, or whole parse guard
is used. The final theorem is a first-field transition on the complete input;
it deliberately does not assert that the remaining object parses successfully.
-/
namespace '''+ns+'''

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def dimensionPrefixChars00 : List Char := '''+quote_list(prefix)+'''

def dimensionKey00 : String := String.ofList '''+quote_list(key)+'''

def dimensionValue00 : SourceJson := .number (String.ofList '''+quote_list(number)+''')

'''+mark('before_actual_prefix_binding')+'''
theorem geometryChars00_dimension_prefix :
    geometryChars00.take 20 = dimensionPrefixChars00 := by
  rfl

'''+mark('after_actual_prefix_binding')+'''
/-- The comma is part of the checked prefix. The tail remains arbitrary.
The original object's empty-accumulator duplicate-key test is reduced here. -/
theorem value_dimension_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 12) (dimensionPrefixChars00 ++ tail) =
      SourceJson.object (fuel + 10) (SourceJson.white tail)
        [(dimensionKey00, dimensionValue00)] := by
  rfl

'''+mark('after_generic_reader_step')+'''
theorem geometryChars00_dimension_split :
    geometryChars00 = dimensionPrefixChars00 ++ geometryChars00.drop 20 := by
  exact (List.take_append_drop 20 geometryChars00).symm.trans
    (congrArg (fun p => p ++ geometryChars00.drop 20) geometryChars00_dimension_prefix)

'''+mark('after_complete_input_split')+'''
/-- Closed equality for the original reader on the complete original character
input. The remaining object call is retained, with its exact fuel and tail. -/
theorem geometryChars00_dimension_step :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195133 (SourceJson.white (geometryChars00.drop 20))
        [(dimensionKey00, dimensionValue00)] := by
  exact (congrArg (SourceJson.value 195135) geometryChars00_dimension_split).trans
    (value_dimension_prefix 195123 (geometryChars00.drop 20))

'''+mark('after_closed_original_reader_step')+'''
#print axioms geometryChars00_dimension_prefix
#print axioms value_dimension_prefix
#print axioms geometryChars00_dimension_split
#print axioms geometryChars00_dimension_step

end '''+ns+'\n'
p=ROOT/'ImbalancedChen/P2OriginalSaving19DimensionPrefix00.lean'
assert not p.exists(), 'Candidate is immutable per attempt; write a separately recorded revision.'
p.write_text(source)
def fingerprint(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
objects=[]
for name in ['P2OriginalSaving19CharacterCore00','P2OriginalSaving19CharacterLength00']:
 objects.append(fingerprint(ROOT/'objects/ImbalancedChen'/f'{name}.olean'))
manifest={**BASE,'status':'prepared_not_compiled','scope':'one first-field reader transition bound to full original geometry00 input; no whole-parse success',
 'files':[{'module':'ImbalancedChen.P2OriginalSaving19DimensionPrefix00','path':str(p.relative_to(ROOT)),'sha256':fingerprint(p)['sha256'],'bytes':fingerprint(p)['bytes']}],
 'reused_new_input_objects':objects,'prefix_bytes':20,'prefix_ascii_escaped':prefix,'prefix_sha256':hashlib.sha256(raw[:20]).hexdigest(),
 'prefix_key_byte_interval':[6,15],'prefix_number_byte_interval':[18,19],
 'line_endings_preserved':'CRLF','tail_representation':'geometryChars00.drop 20; no copied suffix',
 'generic_reader_step_fuel':'fuel+12 -> fuel+10','closed_reader_step_fuel':[195135,195133],
 'comma_preserved':True,'white_rule_preserved':True,'original_empty_acc_duplicate_check_preserved':True,
 'host_JSON_parser_used':False,'order':['dimension normal','dimension kernel only if normal succeeds'],
 'whole_parse_retried':False,'old_Core_equivalence_claimed':False}
(ROOT/'DIMENSION_PREFIX_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
