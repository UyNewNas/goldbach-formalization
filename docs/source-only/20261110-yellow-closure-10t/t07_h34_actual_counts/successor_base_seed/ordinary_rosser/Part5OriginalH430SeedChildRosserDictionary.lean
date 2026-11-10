import ImbalancedChen.Part5OriginalH430SeedUpperAnchorsAP
import ImbalancedChen.P4BCutoffRounding
import ImbalancedChen.CurrentChenRosserEndpointDictionary

/-! Strict real lower Rosser level and canonical natural level coincide at
the actual seed child because the fresh, target-coprime prime divides the
child prefix. The original old-mask sifting product remains unchanged. -/
namespace ImbalancedChen.Part5OriginalH430SeedChildRosserDictionary
noncomputable section
open Finset Real Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedNegativeChildRosser (childMean childResidualDensity childSupport childCoefficient childLevel
  childMean_eq_guarded_residual_density)
open P2SeedOmegaLiteralFibre (s0)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430StrictSeedCeiling (root_power_ne_coprime_multiple)
open Part5OriginalH430SameQCanonicalMains (model)
open scoped Classical BigOperators

theorem true_child_ceil {N n p d q : ℕ} (k : Root) (t : ℝ) (hq : q.Prime)
    (hcop : q.Coprime N) (hd : 0<d) (hQ : 0≤rootQ N n k t p) :
    ⌈childLevel (rootQ N n k t p) d q⌉₊ =
      P2ActualMarkedCountState.rootLevel (rootQ N n k t p) (d*q) := by
  let Q := rootQ N n k t p
  let R := Q/((d*q:ℕ):ℝ)
  have hdq : (0:ℝ)<(d*q:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hd hq.pos)
  have hR : 0≤R := div_nonneg hQ hdq.le
  have he : R≠(⌊R⌋₊:ℝ) := by
    intro heq
    let M := ⌊R⌋₊*(d*q)
    have hdiv : q∣M := dvd_mul_of_dvd_right (dvd_mul_left q d) _
    have h := root_power_ne_coprime_multiple (p:=p) n 1 k t hq hcop hdiv
    have hf : Q=(M:ℝ) := by
      have hh := (div_eq_iff hdq.ne').mp heq
      simpa only [M,Nat.cast_mul] using hh
    exact h (by simpa only [pow_one] using hf)
  exact P4BCutoffRounding.ceil_eq_floor_add_one_of_nonintegral hR he

private theorem old_product (M : ℕ) (z : ℝ) :
    actualSmallPrimeProduct M ⌈z⌉₊ z=ordinarySievePrimeProduct M z := by
  have hs : actualSmallPrimeFinset M ⌈z⌉₊ z=primeWindow M 0 z := by
    ext p
    rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil z),mem_primeWindow]
    constructor
    · rintro ⟨hp,hn,hz⟩
      exact ⟨hp,hp.coprime_iff_not_dvd.mpr hn,Nat.cast_nonneg _,hz⟩
    · rintro ⟨hp,hcop,_,hz⟩
      exact ⟨hp,hp.coprime_iff_not_dvd.mp hcop,hz⟩
  unfold actualSmallPrimeProduct ordinarySievePrimeProduct
  rw [hs] <;> rfl

/-- No replacement of a real strict-level endpoint is made for arbitrary Q.
The exact original frozen rational exponent supplies strictness here. -/
theorem true_child_mean_eq_model {N n p d q : ℕ} (k : Root) (t : ℝ)
    (hd : 0<d) (hcop : d.Coprime N) (hq : q.Prime) (hqN : q.Coprime N)
    (hQ : 0≤rootQ N n k t p) (hlo : cutoff (rootQ N n k t p) d s0≤(q:ℝ)) :
    childMean N (rootQ N n k t p) d q =
      model false N (rootQ N n k t p) (d*q) (cutoff (rootQ N n k t p) d s0) := by
  let Q := rootQ N n k t p
  let z := cutoff Q d s0
  have hprod : actualSmallPrimeProduct (d*N) ⌈z⌉₊ z = ordinarySievePrimeProduct ((d*q)*N) z := by
    rw [old_product]
    unfold ordinarySievePrimeProduct
    rw [show d*q*N=q*(d*N) by ring,primeWindow_mul_of_prime_above _ hq hlo]
  have hlevel := true_child_ceil k t hq hqN hd hQ
  rw [childMean_eq_guarded_residual_density hq hlo,if_pos (hcop.mul_left hqN)]
  apply congrArg (fun u : ℝ => AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N /
    (Nat.totient (d*q):ℝ)*u)
  change (∑ e∈(actualSmallPrimeProduct (d*N) ⌈z⌉₊ z).divisors,
    actualSmallRosserMinus (d*N) ⌈z⌉₊ z (childLevel Q d q) e/(Nat.totient e:ℝ))=
      ordinaryRosserMainSum false N (d*q) (P2ActualMarkedCountState.rootLevel Q (d*q)) z
  unfold actualSmallRosserMinus ActualSmallRosserProvider.lowerWeight ordinaryRosserMainSum ordinaryRosserWeight
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_eq_producer]
  simp only [hprod,hlevel,Bool.false_eq_true,if_false]

end
end ImbalancedChen.Part5OriginalH430SeedChildRosserDictionary
