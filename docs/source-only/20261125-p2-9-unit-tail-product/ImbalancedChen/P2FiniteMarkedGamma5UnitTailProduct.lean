import ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The unit rough cofactor has no tail coordinate. On the nonzero support
of the original smooth profile the two fresh upper gates bound the full
physical product below the global scale whenever R² ≤ N/d. All k old
coordinates stay in the profile and d is their product.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5UnitTailProduct

noncomputable section
open Finset Real
open P2SeedOmegaLiteralFibre (a2)
open P2FiniteMarkedGamma5LogExtension (Gate mem_program profile_nonzero_margin)
open P2FiniteMarkedGamma5PhysicalExtension
open scoped BigOperators

/-- The saving 38/29 is exactly 2 - 2*a2. The support statement
uses no primality, target exclusion, history weight or counting estimate. -/
theorem unit_tail_product_le {k : ℕ} {Q N width b : ℝ}
    {x : PhysicalPoint k 0} (hQ : 0 < Q) (hb : 0 < b) (hw : 0 < width)
    (hne : physicalProfile (log Q) N width b x ≠ 0)
    (hscale : (Q / (∏ i : Fin k, x (.inl i))) ^ (2 : ℕ) ≤
      N / (∏ i : Fin k, x (.inl i))) :
    physicalProduct x ≤ exp (2 * width) * N /
      (Q / (∏ i : Fin k, x (.inl i))) ^ (38 / 29 : ℝ) := by
  let d := ∏ i : Fin k, x (.inl i)
  let R := Q / d
  have hx (i : Slot k 0) : 0 < x i :=
    (half_pos hb).trans (physicalProfile_nonzero_lower hb hne i)
  have hd : 0 < d := prod_pos (fun i _ => hx (.inl i))
  have hR : 0 < R := div_pos hQ hd
  have hprefix : (logPoint x).1 = log d :=
    logPoint_prefix_eq_log_product (fun i => hx (.inl i))
  have hlogR : log R = log Q - log d := log_div hQ.ne' hd.ne'
  have hp := hne
  rw [physicalProfile_eq_floor_mul_original (log Q) N width hb x] at hp
  have hupper (i : Fin 2) : x (.inr (.inl i)) ≤ exp width * R ^ a2 := by
    have hm := profile_nonzero_margin hw (mul_ne_zero_iff.mp hp).2
      (Gate.upper i) (mem_program.mpr trivial)
    change -width < a2 * (log Q - (logPoint x).1) - log (x (.inr (.inl i))) at hm
    rw [hprefix, ← hlogR] at hm
    calc
      _ = exp (log (x (.inr (.inl i)))) := (exp_log (hx _)).symm
      _ ≤ exp (width + log R * a2) := exp_le_exp.mpr (by rw [mul_comm (log R) a2]; linarith only [hm])
      _ = _ := by rw [exp_add, rpow_def_of_pos hR]
  have hpair := mul_le_mul (hupper 0) (hupper 1) (hx _).le
    (mul_nonneg (exp_pos width).le (rpow_nonneg hR.le _))
  have hprod : physicalProduct x ≤ d * ((exp width * R ^ a2) * (exp width * R ^ a2)) := by
    rw [physicalProduct_eq]
    simpa [d, mul_assoc] using mul_le_mul_of_nonneg_left hpair hd.le
  have hpowers : (R ^ a2 * R ^ a2) * R ^ (38 / 29 : ℝ) = R ^ (2 : ℕ) := by
    rw [← rpow_add hR, ← rpow_add hR]
    norm_num [a2, rpow_two]
  have hexp : exp width * exp width = exp (2 * width) := by
    rw [← exp_add, two_mul]
  have hdR : d * R ^ (2 : ℕ) ≤ N := by
    have h : R ^ (2 : ℕ) ≤ N / d := hscale
    simpa only [mul_comm d] using (le_div_iff₀ hd).mp h
  change physicalProduct x ≤ exp (2 * width) * N / R ^ (38 / 29 : ℝ)
  apply (le_div_iff₀ (rpow_pos_of_pos hR _)).mpr
  calc
    _ ≤ (d * ((exp width * R ^ a2) * (exp width * R ^ a2))) * R ^ (38 / 29 : ℝ) :=
      mul_le_mul_of_nonneg_right hprod (rpow_nonneg hR.le _)
    _ = (exp width * exp width) * (d * ((R ^ a2 * R ^ a2) * R ^ (38 / 29 : ℝ))) := by ring
    _ = exp (2 * width) * (d * R ^ (2 : ℕ)) := by rw [hpowers, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdR (exp_pos _).le

end
end ImbalancedChen.P2FiniteMarkedGamma5UnitTailProduct
