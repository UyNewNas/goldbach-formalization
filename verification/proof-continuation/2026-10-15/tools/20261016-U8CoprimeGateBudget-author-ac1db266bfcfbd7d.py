from pathlib import Path
import hashlib
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
p=root/'ImbalancedChen/CurrentChenUpsilon8CoprimeGateBudget.lean'
assert not p.exists(), 'Do not replace an existing source.'
old=(root/'ImbalancedChen/CurrentChenUpsilon9CoprimeGateBudget.lean').read_text()
body=old[old.index('private theorem currentChenUpsilon9_prime_inverse_totient_le'):]
body=body.replace('currentChenUpsilon9', 'currentChenUpsilon8')
body=body.replace('currentChenUpsilon8_dvd_reciprocalTotient_sum_le','currentChenUpsilon9_dvd_reciprocalTotient_sum_le')
body=body.replace('currentChenUpsilon8_li_le_linear','currentChenUpsilon9_li_le_linear')
body=body.replace('(19 / 125 : ℝ)', '(417 / 5000 : ℝ)')
body=body.replace('(106 / 125 : ℝ)', '(4583 / 5000 : ℝ)')
body=body.replace('(106 / 125)', '(4583 / 5000)')
body=body.replace('= 1 - 19 / 125', '= 1 - 417 / 5000')
body=body.replace('The actual product label pays the whole non-coprime divisor mass.', 'The literal eighth product label pays the whole non-coprime divisor mass.')
start=body.index('theorem eventually_currentChenUpsilon8_li_arguments_two :')
end=body.index('/-- A crude proved main-mass bound', start)
body=body[:start]+'''theorem eventually_currentChenUpsilon8_li_arguments_two :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      2 ≤ (N : ℝ) / (a : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlarge hN
  intro a ha
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact hlarge.trans (currentChenUpsilon8_li_argument_power_lower hNr ha)

'''+body[end:]
body=body.replace('  obtain ⟨hp₁, hp₂, horder⟩ := chenY9PrimeSelector_ordered_prime_data ht',
'''  obtain ⟨hp₁, hp₂, horder⟩ := chenY9PrimeSelector_ordered_prime_data
    (show t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) from ht)''')
header='''import ImbalancedChen.CurrentChenUpsilon8ProductPan

/-!
# Paying the literal eighth coprimality gate

The actual eighth zero-one product coefficient is independent of the
sieve modulus. Its Pan main term keeps the true `Coprime a d` gate.
The two genuine prime factors are both at least N^(417/5000), so the
proved reciprocal-totient divisor estimate pays their non-coprime mass.
The cofactor need not be coprime to either prime.

The same signed upper Rosser coefficient is retained throughout. Its
absolute gate correction costs O(N^(4583/5000) (log N)^2), paid by the
existing power error budget. All li positivity and moving-argument
conditions are established from the actual eighth source before the
final threshold; they are not caller hypotheses. That threshold precedes
cap, z, L and the positive-modulus set chosen through N.

This leaf supplies no count majorant, density value, harmonic mean or
adopted upper constant. The already owned generic prime-divisor estimate
and the crude true-li bound are reused rather than reproved.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight

'''
text=header+body
assert '19 / 125' not in text and '106 / 125' not in text and '191 / 500' not in text and '309 / 500' not in text
assert text.count('import ')==1
p.write_text(text,encoding='utf-8',newline='\n')
print(hashlib.sha256(p.read_bytes()).hexdigest())
print('lines',len(text.splitlines()))