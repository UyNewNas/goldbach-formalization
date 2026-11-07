from pathlib import Path
import re,hashlib
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
p=root/'ImbalancedChen/CurrentChenUpsilon8FiniteMean.lean';assert not p.exists()
pan=(root/'ImbalancedChen/CurrentChenUpsilon9PanAggregate.lean').read_text();finite=(root/'ImbalancedChen/CurrentChenUpsilon9FiniteMean.lean').read_text()
def decl(text,name):
    matches=list(re.finditer(r'(?m)^(?:private\s+)?(?:theorem|def)\s+(\S+)',text))
    for i,m in enumerate(matches):
        if m[1]==name:
            end=matches[i+1].start() if i+1<len(matches) else len(text)
            segment=text[m.start():end]
            segment=re.split(r'(?m)^end(?:\s.*)?$',segment,maxsplit=1)[0]
            segment=re.sub(r'\n/--[\s\S]*?-/\s*$','',segment)
            return segment.rstrip()+'\n\n'
    raise AssertionError(name)
def eight(text):
    text=text.replace('currentChenUpsilon9','currentChenUpsilon8')
    for generic in ['PanActive','PanActive_subset','SwitchedUpperDensity','PrefixPrimeFibre','_prefix_sum_upperDivisorSum','_switchedPrimeFibre_card_le_upperDivisorSum_add_cap','SwitchedPrimeFibre','_primesInAPBelow_eq_zero_of_not_coprime']:
        text=text.replace('currentChenUpsilon8'+generic,'currentChenUpsilon9'+generic)
    return text
header='''import ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget
import ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget
import ImbalancedChen.CurrentChenUpsilon9FiniteMean

/-!
# The actual eighth count and its paid switched density main term

The original eighth product image, its modulus-independent zero-one
coefficient and its literal unit fibres are retained. The public generic
prime-fibre sieve and finite Fubini bridge are reused on each actual eighth
multiplier. Their native prime carrier has the closed endpoint a*q<=N,
including receiver zero; the strict original count is enlarged only by
the already proved nonnegativity of the complete divisor sum.

The AP identity below keeps the true multiplier coprimality gate and the
actual signed upper Rosser coefficient. The strict level Q+1 makes the
fullsupport-to-active restriction exact. The owned actual eighth Pan
majorant, its paid coprime gate and the literal finite source errors give
one B before every epsilon, and one threshold before every cap.

Only this finite main-and-error statement is proved. The density is the
same source-independent explicit sum already defined in the ninth finite
bridge. No density bound, true-li mean, harmonic mean or adopted constant
is assumed or asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

'''
chunks=[]
chunks.append('/-- The native closed AP count on the literal eighth product image. -/\n'+eight(decl(pan,'currentChenUpsilon9PrefixAPCount')))
chunks.append('/-- The actual eighth same-coefficient Pan error at the original target residue. -/\n'+eight(decl(pan,'currentChenUpsilon9PanError')))
chunks.append(eight(decl(pan,'currentChenUpsilon9_primesInAPBelow_target_mod')))
chunks.append('/-- Exact li main mass, genuine coprime defect and same-coefficient Pan error. -/\n'+eight(decl(pan,'currentChenUpsilon9_prefixAPCount_eq_main_sub_defect_add_error')))
chunks.append(eight(decl(finite,'currentChenUpsilon9_upper_sum_eq_active')))
chunks.append('/-- The same complete signed upper Rosser weight applied to the actual eighth error. -/\n'+eight(decl(pan,'currentChenUpsilon9PanRosserError')))
chunks.append('''/-- The strict level Q+1 pays every omitted modulus exactly. -/
theorem currentChenUpsilon8PanRosserError_eq_active (B : ℝ) (N cap : ℕ) (z : ℝ) :
    currentChenUpsilon8PanRosserError B N cap z =
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
          currentChenUpsilon8PanError N d := by
  exact currentChenUpsilon8_upper_sum_eq_active B N cap z _

''')
chunks.append(eight(decl(pan,'currentChenUpsilon9_abs_panError_le_MaxL')))
chunks.append('/-- No factor for the number of source labels or active moduli is inserted. -/\n'+eight(decl(pan,'currentChenUpsilon9_abs_panRosserError_le_MaxL_sum')))
paid=eight(decl(pan,'exists_currentChenUpsilon9_panRosserError_budget'))
paid=paid.replace('    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving 3 (by norm_num)', '    exists_currentChenUpsilon8_sameCoefficient_pan_majorant 3 (by norm_num)')
paid=paid.replace('  filter_upwards [eventually_currentChenUpsilon8_panLower_log_gate B,\n    eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ), hlarge, hlog]\n    with N hlower hN₀ hN hlarge hlog', '  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ), hlarge, hlog]\n    with N hN₀ hN hlarge hlog')
paid=paid.replace('  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN\n','')
paid=paid.replace('  have hdist := hagg N hN₀ (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N)\n    (currentChenUpsilon8ProductCoefficient N)\n    (currentChenUpsilon8_panUpper_le_two_thirds hNr) hlower\n    (abs_currentChenUpsilon8ProductCoefficient_le_one N)', '  have hdist := hagg N hN₀')
chunks.append('/-- The actual eighth majorant chooses B before epsilon, N, cap and z. -/\n'+paid)
chunks.append('/-- Generic finite Fubini, reindexed over the original eighth products. -/\n'+eight(decl(finite,'currentChenUpsilon9_product_sum_upperDivisorSum')))
chunks.append('/-- The same full actual coefficient supplies all three terms of this exact identity. -/\n'+eight(decl(finite,'currentChenUpsilon9_upper_AP_sum_eq_main_errors')))
chunks.append('/-- The literal eighth count, including its actual unit fibres and generic small-P loss. -/\n'+eight(decl(finite,'currentChenUpsilon9_le_upper_density_main_add_errors')))
chunks.append('''/-- The exact actual eighth product cardinal and the single receiver ceiling
have cost at most 2*N^(13/15). -/
theorem currentChenUpsilon8_small_prime_cost_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((currentChenUpsilon8PrefixProducts N).card : ℝ) *
      (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
        2 * (N : ℝ) ^ (13 / 15 : ℝ) := by
  have hNnat : 1 ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hcard : ((currentChenUpsilon8PrefixProducts N).card : ℝ) ≤
      (N : ℝ) ^ (2 / 3 : ℝ) :=
    (Nat.cast_le.mpr (currentChenUpsilon8_prefixProducts_card_le_panUpper hNnat)).trans
      (currentChenUpsilon8_panUpper_le_two_thirds hN)
  have hsmallOne : 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hsmallCeil : (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (1 / 5 : ℝ))
    linarith only [h, hsmallOne]
  calc
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (2 * (N : ℝ) ^ (1 / 5 : ℝ)) :=
      mul_le_mul hcard hsmallCeil (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
    _ = _ := by
      rw [show (13 / 15 : ℝ) = 2 / 3 + 1 / 5 by norm_num, Real.rpow_add hNp]
      ring

''')
chunks.append(eight(decl(finite,'eventually_currentChenUpsilon9_panLevel_sieveCutoff')))
final=eight(decl(finite,'exists_currentChenUpsilon9_le_switched_density_main'))
final=final.replace('eventually_powerLog_le_singularNormalization 4 (409 / 500) 0', 'eventually_powerLog_le_singularNormalization 2 (13 / 15) 0')
final=final.replace('eventually_currentChenUpsilon8_unitFibres_le_singularNormalization δ hδ,', 'eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization δ hδ,')
final=final.replace('with N hPanN hGateN hSmallN hUnitN hlevel hN', 'with N hPanN hGateN hSmallN hSourceN hlevel hN')
anchor='  have hfinite := currentChenUpsilon8_le_upper_density_main_add_errors B hNr cap z\n'
insert='''  have hUnit : ((currentChenUpsilon8UnitFibres N).card : ℝ) ≤
      δ * singularNormalization N := by
    have hSmallNonneg : (0 : ℝ) ≤
        ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := Nat.cast_nonneg _
    linarith only [hSourceN, hSmallNonneg]
'''
assert final.count(anchor)==1
final=final.replace(anchor,insert+anchor).replace('hSmall, hUnitN, htotal','hSmall, hUnit, htotal')
chunks.append('/-- Every actual error is paid before the cap is chosen; no main-term or distribution premise. -/\n'+final)
text=header+''.join(chunks)+'end\n\nend ImbalancedChen\n'
assert len(re.findall(r'(?m)^def ',text))==3
assert text.count('import ')==3
for unwanted in ['currentChenUpsilon8PanActive','currentChenUpsilon8SwitchedUpperDensity','currentChenUpsilon8PrefixPrimeFibre','currentChenUpsilon8_primesInAPBelow_eq_zero_of_not_coprime','409 / 500','309 / 500','191 / 500','19 / 125']:
    assert unwanted not in text, unwanted
p.write_text(text,encoding='utf8',newline='\n')
print(hashlib.sha256(p.read_bytes()).hexdigest());print('lines',len(text.splitlines()))