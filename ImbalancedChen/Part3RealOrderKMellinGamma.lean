import ImbalancedChen.Part3RealOrderKMellinBetaTail
import ImbalancedChen.Part3RealBetaHalfLineGamma
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The reciprocal substitution t->1/t glues the actual paired Euler tail
to one full positive Euler integral. The separately constructed concrete
half-line Beta/Gamma theorem then evaluates it, yielding the Gamma-product
Mellin formula for literal realOrderK at every real s>|alpha|.

The Beta/Gamma theorem is imported as proved source, not taken as a premise.
This does not prove the complex-order Mellin identity, KL Plancherel,
automorphic spectral normalization or the original manuscript theorem.
-/

namespace ImbalancedChen.Part3.RealOrderKMellinGamma20261025a

noncomputable section
open Set MeasureTheory Filter
open RealOrderKExceptionalSourceOnly
open RealOrderKMellinBetaTail20261025a

private def eulerDensity (a b t : ℝ) : ℝ :=
  t ^ (a - 1) / (1 + t) ^ (a + b)

/-- The exact reciprocal Jacobian identity for the actual Euler kernel. -/
private theorem eulerDensity_reciprocal (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    (t ^ 2)⁻¹ * eulerDensity a b t⁻¹ = eulerDensity b a t := by
  have htne := ht.ne'
  have hplus : 0 < 1 + t := by linarith
  have hinv : 1 + t⁻¹ = (1 + t) / t := by field_simp [htne] <;> ring
  have hp : t ^ (a + b) = t ^ (a - 1) * t ^ (b - 1) * t ^ 2 := by
    calc
      t ^ (a + b) = t ^ ((a - 1) + (b - 1) + (2 : ℝ)) := by congr 1; ring
      _ = t ^ (a - 1) * t ^ (b - 1) * t ^ (2 : ℝ) := by
        rw [Real.rpow_add ht, Real.rpow_add ht]
      _ = t ^ (a - 1) * t ^ (b - 1) * t ^ 2 := by rw [Real.rpow_two]
  dsimp only [eulerDensity]
  rw [hinv, Real.inv_rpow ht.le,
    Real.div_rpow hplus.le ht.le (a + b), add_comm b a, hp]
  field_simp [htne, (Real.rpow_pos_of_pos ht (a - 1)).ne',
    (Real.rpow_pos_of_pos ht (b - 1)).ne',
    (Real.rpow_pos_of_pos hplus (a + b)).ne'] <;> ring

/-- Reciprocal substitution identifies the small Euler interval with the
opposite-order tail. No integral evaluation is a premise. -/
private theorem eulerDensity_small_integral_eq_swapped_tail (a b : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, eulerDensity a b t) =
      ∫ t in Ioi (1 : ℝ), eulerDensity b a t := by
  have himage : (fun t : ℝ => t⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) 1 := by
    rw [image_inv_eq_inv, inv_Ioi₀ (by norm_num : (0 : ℝ) < 1), inv_one]
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => t⁻¹) (f' := fun t : ℝ => -(t ^ 2)⁻¹)
    measurableSet_Ioi
    (fun t ht =>
      (hasDerivAt_inv (lt_trans (by norm_num : (0 : ℝ) < 1) ht).ne').hasDerivWithinAt)
    (fun x _ y _ hxy => inv_injective hxy) (eulerDensity a b)
  rw [himage] at h
  refine h.trans ?_
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  simp only [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)), smul_eq_mul]
  exact eulerDensity_reciprocal a b htpos

private theorem eulerDensity_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (eulerDensity a b) (Ioi (0 : ℝ)) :=
  ImbalancedChen.Part3RealBetaHalfLineGamma.integrableOn_beta_halfline ha hb

/-- Positive and reciprocal tails reconstruct the full Euler integral. -/
private theorem eulerDensity_paired_tail_eq_full {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (1 : ℝ), eulerDensity a b t + eulerDensity b a t) =
      ∫ t in Ioi (0 : ℝ), eulerDensity a b t := by
  have hfull := eulerDensity_integrable ha hb
  have htail : IntegrableOn (eulerDensity a b) (Ioi (1 : ℝ)) :=
    hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have htailSwap : IntegrableOn (eulerDensity b a) (Ioi (1 : ℝ)) :=
    (eulerDensity_integrable hb ha).mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit : (∫ t in Ioi (0 : ℝ), eulerDensity a b t) =
      (∫ t in Ioo (0 : ℝ) 1, eulerDensity a b t) +
        ∫ t in Ioi (1 : ℝ), eulerDensity a b t := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hfull.mono_set Ioc_subset_Ioi_self) htail,
      integral_Ioc_eq_integral_Ioo]
  rw [integral_add htail htailSwap,
    ← eulerDensity_small_integral_eq_swapped_tail a b, add_comm]
  exact hsplit.symm

/-- The actual paired tail produced by exp(2u) is now evaluated. -/
theorem betaTailDensity_integral_eq_gamma {α s : ℝ} (hs : |α| < s) :
    (∫ t in Ioi (1 : ℝ), betaTailDensity α s t) =
      Real.Gamma ((s + α) / 2) * Real.Gamma ((s - α) / 2) / Real.Gamma s := by
  let a : ℝ := (s + α) / 2
  let b : ℝ := (s - α) / 2
  have ha : 0 < a := by dsimp [a]; linarith [neg_le_abs α]
  have hb : 0 < b := by dsimp [b]; linarith [le_abs_self α]
  have hab : a + b = s := by dsimp [a, b]; ring
  calc
    (∫ t in Ioi (1 : ℝ), betaTailDensity α s t) =
        ∫ t in Ioi (1 : ℝ), eulerDensity a b t + eulerDensity b a t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        dsimp only [betaTailDensity, eulerDensity, a, b]
        have hsum : (s + α) / 2 + (s - α) / 2 = s := by ring
        have hswap : (s - α) / 2 + (s + α) / 2 = s := by ring
        rw [hsum, hswap]
        ring)
    _ = ∫ t in Ioi (0 : ℝ), eulerDensity a b t :=
      eulerDensity_paired_tail_eq_full ha hb
    _ = Real.Gamma ((s + α) / 2) * Real.Gamma ((s - α) / 2) / Real.Gamma s := by
      have h := ImbalancedChen.Part3RealBetaHalfLineGamma.integral_beta_halfline_eq_gamma ha hb
      change (∫ t in Ioi (0 : ℝ), eulerDensity a b t) =
        Real.Gamma a * Real.Gamma b / Real.Gamma s
      simpa only [eulerDensity, hab] using h

/-- Gamma-product Mellin normalization of the literal real-order K
integral, proved throughout s>|alpha| with no normalization hypothesis. -/
theorem realOrderK_mellin_eq_gamma {α s : ℝ} (hs : |α| < s) :
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * realOrderK α q) =
      (2 : ℝ) ^ (s - 2) * Real.Gamma ((s + α) / 2) *
        Real.Gamma ((s - α) / 2) := by
  have hs0 : 0 < s := lt_of_le_of_lt (abs_nonneg α) hs
  have hgamma : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs0).ne'
  have htwo : (2 : ℝ) ^ (s - 2) = (2 : ℝ) ^ s / 4 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_two]
    norm_num
  rw [realOrderK_mellin_eq_betaTail hs, betaTailDensity_integral_eq_gamma hs, htwo]
  field_simp [hgamma] <;> ring

end
end ImbalancedChen.Part3.RealOrderKMellinGamma20261025a
