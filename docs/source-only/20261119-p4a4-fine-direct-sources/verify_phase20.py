"""Source identity and exact-statement comparison only; not a Lean check."""
import hashlib, re
from pathlib import Path
root = Path('/tmp/p4a4-phase20')
fine = (root/'P4AOriginalFiniteAll22FineCofinalCoefficient.lean').read_bytes()
changed = (root/'P4AOriginalFineWitnessChangedSupport.lean').read_bytes()
new = (root/'P4AOriginalFineSameWitnessChangedCoverage.lean').read_text()
assert hashlib.sha256(fine).hexdigest() == '74f2d4dc15e059f9ab197157ee9172808ddb34d2547dc85733eec878e1fbc3b6'
assert hashlib.sha256(changed).hexdigest() == '19556299fcbf01d7826c759d6c0bef8922adf40ff38100c0bfec680867959c25'
orig = fine.decode().split('theorem exists_fine_cofinal_same_coefficient_density_and_count',1)[1].split(' := by\n',1)[0]
candidate = new.split('theorem exists_fine_cofinal_same_witness_with_changed_coverage',1)[1].split(' := by\n',1)[0]
candidate = candidate.split('\n      ) ∧\n      ∀ (tags : ℕ → List Bool) (x : ℕ),',1)[0]
candidate = candidate.replace('      (P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms\n', '      P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms\n', 1)
assert candidate == orig
assert new.count('P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count') == 1
assert new.count('P4AOriginalFineWitnessChangedSupport.fine_witness_all_changed_seen') == 1
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',new)
assert 'exact ⟨hOriginal,hCoverage⟩' in new
print('prior_source_sha256_matches 2')
print('fine_statement_byte_identical_after_parenthesization yes')
print('one_call_to_each_existing_candidate yes')
print('forbidden_token_scan pass')
print('lean_elaboration_or_kernel false')
