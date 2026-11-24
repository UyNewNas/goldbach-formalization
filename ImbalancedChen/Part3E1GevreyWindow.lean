import ImbalancedChen.Part3E1MediumWindowBound
import ImbalancedChen.Part3GevreyCutoff

/-!
# The retained S2 estimate with one physical Gevrey cutoff

The real modulus weight and the Poisson Fourier factor are constructed
from the same function. The logarithmic and smooth-part thresholds are
chosen before the atom and all its finite data.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset Filter E1Finite
open scoped BigOperators SchwartzMap FourierTransform

private theorem eventually_e1_log_cutoff_le_scale {Ccut : ℝ} (hCcut : 0 ≤ Ccut) :
    ∀ᶠ X : ℝ in atTop, 2 ≤ X ∧ (4 * Ccut) * (Real.log X)^5 ≤ X := by
  let A := 4 * Ccut * (10 : ℝ)^5
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  filter_upwards [eventually_ge_atTop (max (2 : ℝ) (A^2))] with X hX
  have hX2 := (le_max_left _ _).trans hX
  have hX1 : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans hX2
  have hX0 : 0 ≤ X := zero_le_one.trans hX1
  refine ⟨hX2, ?_⟩
  have hl := Real.log_le_rpow_div hX0 (show (0 : ℝ) < 1 / 10 by norm_num)
  have hl' : Real.log X ≤ 10 * X ^ (1 / 10 : ℝ) := by
    convert hl using 1
    ring
  have hp : (Real.log X)^5 ≤ 10^5 * Real.sqrt X := by
    calc
      _ ≤ (10 * X ^ (1 / 10 : ℝ)) ^ 5 := pow_le_pow_left₀ (Real.log_nonneg hX1) hl' 5
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hX0, Nat.cast_ofNat, Real.sqrt_eq_rpow]; norm_num
  have hs : A ≤ Real.sqrt X := by
    simpa only [Real.sqrt_sq hA] using Real.sqrt_le_sqrt ((le_max_right _ _).trans hX)
  calc
    _ ≤ (4 * Ccut) * (10^5 * Real.sqrt X) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = A * Real.sqrt X := by dsimp only [A]; ring
    _ ≤ Real.sqrt X * Real.sqrt X := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = X := Real.mul_self_sqrt hX0

/-- Retained S2 for the actual real plateau window, with the Fourier
transform of precisely that same plateau at all physical moduli. -/
theorem exists_retainedS2_medium_gevreyWindow {σ c0 Ccut : ℝ}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hCcut : 0 ≤ Ccut) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ (B : ℕ) (κ : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → X₀ ≤ d.scale →
      ∀ (D : ℝ), 1 ≤ D → D ≤ (d.scale ^ (1 / Real.log (Real.log d.scale)))^2 →
      ∀ (Q : Finset ℕ) (R H : ℕ → ℝ) (Rs : ℕ → Finset ℕ) (lambdaTrim : ℕ → ℕ → ℂ),
        (∀ k ∈ factorCarrier D, (Rs k).Nonempty →
          1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3 ∧ Rs k ⊆ factorCarrier (R k)) →
        (∀ k ∈ factorCarrier D, 0 ≤ H k ∧
          H k ≤ (Ccut * Real.log d.scale ^ 5) * ((D * d.Q1) * R k / d.V)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, ‖lambdaTrim k r‖ ≤ ((k * r).divisors.card : ℝ)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, lambdaTrim k r ≠ 0 → (k * r).Coprime d.residue.natAbs) →
        ‖∑ k ∈ factorCarrier D,
          retainedS2FixedD Q (Rs k) d.alphaCarrier ⌊H k⌋₊ k d.residue d.V
            (⇑(𝓕 GevreyCutoff.cutoffSchwartz : 𝓢(ℝ, ℂ)))
            (fun q => GevreyCutoff.cutoff ((q : ℝ) / d.Q1)) (lambdaTrim k) d.alpha‖ / d.V ≤
          C * (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_retainedS2_medium_smoothWindow hσ hc0 hCcut GevreyCutoff.cutoffSchwartz
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_e1_log_cutoff_le_scale hCcut).and (eventually_e1SplitScale_reserve hσ))
  refine ⟨C, hC, X₀, ?_⟩
  intro B κ d hd hX D hD hDsmall Q R H Rs lambdaTrim hR hH hτ hprimitive
  obtain ⟨⟨hX2, hLog⟩, hDsub, hXlarge⟩ := hX₀ d.scale hX
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hsupport (q : ℕ) (_hq : q ∈ Q)
      (hqn : GevreyCutoff.cutoff ((q : ℝ) / d.Q1) ≠ 0) :
      d.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * d.Q1 / 2 := by
    have h := GevreyCutoff.cutoff_tsupport_subset (subset_closure hqn)
    have hlo := (le_div_iff₀ hQ).mp h.1
    have hhi := (div_le_iff₀ hQ).mp h.2
    exact ⟨by linarith, by linarith⟩
  exact hbound B κ d hd hX2 hLog D hD (hDsmall.trans hDsub) hXlarge Q R H Rs
    (fun q => GevreyCutoff.cutoff ((q : ℝ) / d.Q1)) lambdaTrim hsupport hR hH
    (fun _ _ => GevreyCutoff.cutoff_mem_Icc _) hτ hprimitive

end

end ImbalancedChen.Part3
