"""Inspect exact source blobs and surface markers; never a Lean elaborator."""
import hashlib, re
from pathlib import Path

p=Path('/tmp/p4a4-phase22')
expected={
 'P4AOriginalFiniteFallbackActualChangedSupport.lean':'be14059cc960d861be48a445c748f95eaa63514b',
 'P4AOriginalFiniteFallbackWallRate.lean':'2a817dca158e647917b0cf355f47966565cf9659',
 'P4AFull87FiniteWallRate.lean':'c3f59dc3c639bbf1a50044f7e0c1b889e3fee51d',
 'P4AFull87MarkedPrimePayment.lean':'9c616579335ac0c223493ffbd005ea2e514e221f',
 'P4AUpperTaggedParityCompiler.lean':'2076b4a3e198f40f36ae5265e63f97c9dfce12e4',
 'P4AOriginalFiniteAll22FineCofinalCoefficient.lean':'eef0d3cc4864763b14037ed8bc58721f60170583',
}
for name,sha in expected.items():
 b=(p/name).read_bytes()
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha,name
s=(p/'P4AOriginalFiniteFallbackActualTaggedRate.lean').read_text()
finite=(p/'P4AFull87FiniteWallRate.lean').read_text()
marked=(p/'P4AFull87MarkedPrimePayment.lean').read_text()
compiler=(p/'P4AUpperTaggedParityCompiler.lean').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',s)
assert s.count('theorem actual_uniform_tagged_rate\n')==1
assert s.count('theorem actual_uniform_tagged_rate_eventually\n')==1
assert s.count('P4AFull87FiniteWallRate.exists_finite_rate')==1
assert s.count('P4AOriginalFiniteFallbackActualChangedSupport.actual_changed_seen')==1
first=s.split('theorem actual_uniform_tagged_rate\n',1)[1].split(' := by',1)[0]
assert first.index('∃ K E : ℝ')<first.index('∀ N cap : ℕ')<first.index('∀ tags : ℕ → List Bool')
assert 'changedMass (F T delta n D omega N) tags N cap' in first
assert 'cost (t : ℕ) : ℝ := 1 / (Nat.totient t : ℝ)' in marked
assert '(universe N cap w z).filter (changed retainOdd tag N cap w z tau)' in compiler
assert '1 / (Nat.totient d : ℝ)' in compiler
assert '∀ centres : ι → ℕ → ℕ → ℝ' in finite
assert 'original_positive' not in first
print('direct_and_referenced_git_blobs_verified',len(expected))
print('same_totient_weight_and_original_changed_filter confirmed_by_source_read')
print('constants_quantified_before_target_and_tags yes')
print('original_actual_changed_cover_and_finite_rate_invoked_once yes')
print('forbidden_token_scan pass')
print('Lean_elaboration_kernel_axioms_or_finite_evaluation false')
