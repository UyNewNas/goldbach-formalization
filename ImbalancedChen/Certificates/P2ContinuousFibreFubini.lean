import ImbalancedChen.Certificates.P2PairedSupportFubini

/-!
SOURCE ONLY / UNCOMPILED. The import names the intended installation of
the adjacent P2PairedSupportFubini.lean candidate.

Nonseparable Fubini on the actual adopted fibres. The main theorem assumes
only actual integrability of F on the support, not a target integral
identity or a numerical enclosure. Continuous kernels on the actual compact
fibre box receive integrability from compactness in the final adapters.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2ContinuousFibreFubini

open MeasureTheory Set
open scoped BigOperators Interval
open P2AdoptedUnion P2PairedSupportFubini

noncomputable section

/-- Genuine Fubini on two coordinates, with the actual coordinate map. -/
theorem integral_fin_two (F : Point2 → ℝ) (hF : Integrable F) :
    (∫ x : Point2, F x) = ∫ z : ℝ, ∫ w : ℝ, F ![z, w] := by
  have hi : Integrable (fun p : ℝ × ℝ => F (split2.symm p)) :=
    split2_preserving.symm.integrable_comp_of_integrable hF
  calc
    _ = ∫ p : ℝ × ℝ, F (split2.symm p) :=
      (split2_preserving.symm.integral_comp' F).symm
    _ = _ := by
      simpa only [split2_symm] using
        integral_prod (fun p : ℝ × ℝ => F (split2.symm p)) hi

/-- A.e. integrable slices, rather than an assumed pointwise Fubini
identity, justify the third coordinate. -/
theorem integral_fin_three (F : Point3 → ℝ) (hF : Integrable F) :
    (∫ x : Point3, F x) = ∫ u : ℝ, ∫ z : ℝ, ∫ w : ℝ, F ![u, z, w] := by
  have hi : Integrable (fun p : ℝ × Point2 => F (split3.symm p)) :=
    split3_preserving.symm.integrable_comp_of_integrable hF
  calc
    _ = ∫ p : ℝ × Point2, F (split3.symm p) :=
      (split3_preserving.symm.integral_comp' F).symm
    _ = ∫ u : ℝ, ∫ v : Point2, F (split3.symm (u, v)) :=
      integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with u hu
      simpa only [split3_symm] using
        integral_fin_two (fun v : Point2 => F (split3.symm (u, v))) hu

/-- Complete four-coordinate Fubini for arbitrary integrable real kernels.
No separation into products of one-variable functions is required. -/
theorem integral_fin_four (F : Point → ℝ) (hF : Integrable F) :
    (∫ x : Point, F x) =
      ∫ t : ℝ, ∫ u : ℝ, ∫ z : ℝ, ∫ w : ℝ, F ![t, u, z, w] := by
  have hi : Integrable (fun p : ℝ × Point3 => F (split4.symm p)) :=
    split4_preserving.symm.integrable_comp_of_integrable hF
  calc
    _ = ∫ p : ℝ × Point3, F (split4.symm p) :=
      (split4_preserving.symm.integral_comp' F).symm
    _ = ∫ t : ℝ, ∫ v : Point3, F (split4.symm (t, v)) :=
      integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with t ht
      simpa only [split4_symm] using
        integral_fin_three (fun v : Point3 => F (split4.symm (t, v))) ht

/-- An indicator in a fixed outer parameter commutes with inner integration.
This identity requires no integrability assumption or boundary convention. -/
theorem integral_fixed_indicator (s : Set ℝ) (t : ℝ) (F : ℝ → ℝ → ℝ) :
    (∫ x : ℝ, s.indicator (fun t => F t x) t) =
      s.indicator (fun t => ∫ x : ℝ, F t x) t := by
  by_cases ht : t ∈ s <;> simp [ht]

theorem support_indicator_vector (r : Row) (F : Point → ℝ) (t u z w : ℝ) :
    (support r).indicator F ![t, u, z, w] =
      (tInterval r).indicator (fun t =>
        (uInterval r).indicator (fun u =>
          (Ioo (a : ℝ) (cutoff r : ℝ)).indicator (fun z =>
            (Ioo (a : ℝ) z).indicator (fun w => F ![t, u, z, w]) w) z) u) t := by
  have hm : ![t, u, z, w] ∈ support r ↔
      t ∈ tInterval r ∧ u ∈ uInterval r ∧
        z ∈ Ioo (a : ℝ) (cutoff r : ℝ) ∧ w ∈ Ioo (a : ℝ) z := by
    change
      ((tLower (indices r).1 : ℝ) < t ∧
        t < (tUpper (indices r).1 : ℝ) ∧
        (uLower (indices r).2 : ℝ) < u ∧
        u < (uUpper (indices r).2 : ℝ) ∧
        (a : ℝ) < w ∧ w < z ∧ z < (cutoff r : ℝ)) ↔
      (((tLower (indices r).1 : ℝ) < t ∧
        t < (tUpper (indices r).1 : ℝ)) ∧
        ((uLower (indices r).2 : ℝ) < u ∧
          u < (uUpper (indices r).2 : ℝ)) ∧
        ((a : ℝ) < z ∧ z < (cutoff r : ℝ)) ∧
        (a : ℝ) < w ∧ w < z)
    constructor
    · rintro ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
      exact ⟨⟨htl, htr⟩, ⟨hul, hur⟩, ⟨haw.trans hwz, hzZ⟩, haw, hwz⟩
    · rintro ⟨⟨htl, htr⟩, ⟨hul, hur⟩, ⟨_, hzZ⟩, haw, hwz⟩
      exact ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
  by_cases ht : t ∈ tInterval r <;>
    by_cases hu : u ∈ uInterval r <;>
    by_cases hz : z ∈ Ioo (a : ℝ) (cutoff r : ℝ) <;>
    by_cases hw : w ∈ Ioo (a : ℝ) z <;>
      simp [Set.indicator_apply, hm, ht, hu, hz, hw]

/-- Fubini restricted to the actual nonrectangular open fibre. -/
theorem support_setIntegral_eq_Ioo (r : Row) (F : Point → ℝ)
    (hF : IntegrableOn F (support r)) :
    (∫ x : Point in support r, F x) =
      ∫ t in tInterval r, ∫ u in uInterval r,
      ∫ z in Ioo (a : ℝ) (cutoff r : ℝ),
      ∫ w in Ioo (a : ℝ) z, F ![t, u, z, w] := by
  have hG : Integrable ((support r).indicator F) :=
    hF.integrable_indicator (support_measurable r)
  calc
    _ = ∫ x : Point, (support r).indicator F x :=
      (integral_indicator (support_measurable r)).symm
    _ = ∫ t : ℝ, ∫ u : ℝ, ∫ z : ℝ, ∫ w : ℝ,
        (support r).indicator F ![t, u, z, w] :=
      integral_fin_four _ hG
    _ = _ := by
      simp_rw [support_indicator_vector, integral_fixed_indicator]
      simp only [tInterval, uInterval, integral_indicator measurableSet_Ioo]

theorem setIntegral_Ioo_eq_interval {l u : ℝ} (hlu : l ≤ u) (F : ℝ → ℝ) :
    (∫ x in Ioo l u, F x) = ∫ x in l..u, F x := by
  rw [intervalIntegral.integral_of_le hlu, integral_Ioc_eq_integral_Ioo]

/-- Generic nonseparable per-row API. Actual integrability is sufficient;
the literal fourfold interval integral is the conclusion. -/
theorem support_setIntegral_eq_fourfold (r : Row) (F : Point → ℝ)
    (hF : IntegrableOn F (support r)) :
    (∫ x : Point in support r, F x) =
      ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
      ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
      ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
        F ![t, u, z, w] := by
  have htu : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) :=
    Rat.cast_le.mpr (row_endpoint_bounds r).2.2.2.2.2.1.le
  have huu : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) :=
    Rat.cast_le.mpr (row_endpoint_bounds r).2.2.1.le
  have haZ : (a : ℝ) ≤ (cutoff r : ℝ) :=
    Rat.cast_le.mpr (row_endpoint_bounds r).1.le
  rw [support_setIntegral_eq_Ioo r F hF]
  change (∫ t in Ioo (tLower (indices r).1 : ℝ) (tUpper (indices r).1 : ℝ),
    ∫ u in Ioo (uLower (indices r).2 : ℝ) (uUpper (indices r).2 : ℝ),
    ∫ z in Ioo (a : ℝ) (cutoff r : ℝ), ∫ w in Ioo (a : ℝ) z,
      F ![t, u, z, w]) = _
  rw [setIntegral_Ioo_eq_interval htu]
  apply intervalIntegral.integral_congr
  intro t _
  rw [setIntegral_Ioo_eq_interval huu]
  apply intervalIntegral.integral_congr
  intro u _
  rw [setIntegral_Ioo_eq_interval haZ]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le haZ] at hz
  exact setIntegral_Ioo_eq_interval hz.1 _

/-- The actual compact rectangular closure of one triangular fibre. -/
def fibreBox (r : Row) : Set Point :=
  Icc ![(tLower (indices r).1 : ℝ), (uLower (indices r).2 : ℝ), (a : ℝ), (a : ℝ)]
    ![(tUpper (indices r).1 : ℝ), (uUpper (indices r).2 : ℝ),
      (cutoff r : ℝ), (cutoff r : ℝ)]

theorem support_subset_fibreBox (r : Row) : support r ⊆ fibreBox r := by
  intro x hx
  rcases hx with ⟨htl, htr, hul, hur, haw, hwz, hzZ⟩
  constructor
  · intro i
    fin_cases i
    · exact htl.le
    · exact hul.le
    · exact haw.le.trans hwz.le
    · exact haw.le
  · intro i
    fin_cases i
    · exact htr.le
    · exact hur.le
    · exact hzZ.le
    · exact hwz.le.trans hzZ.le

/-- Continuity on the genuine compact fibre box pays the integrability
premise of the generic API. -/
theorem support_setIntegral_eq_fourfold_of_continuousOn (r : Row) (F : Point → ℝ)
    (hF : ContinuousOn F (fibreBox r)) :
    (∫ x : Point in support r, F x) =
      ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
      ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
      ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
        F ![t, u, z, w] := by
  exact support_setIntegral_eq_fourfold r F
    ((hF.integrableOn_compact isCompact_Icc).mono_set (support_subset_fibreBox r))

/-- Global positive-box continuity is a convenient uniform supplier for
all 17572 actual row applications, including nonseparable Buchstab kernels. -/
theorem support_setIntegral_eq_fourfold_of_continuousOn_box
    (r : Row) (F : Point → ℝ) (hF : ContinuousOn F P2AdoptedUnion.box) :
    (∫ x : Point in support r, F x) =
      ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
      ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
      ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
        F ![t, u, z, w] := by
  exact support_setIntegral_eq_fourfold r F
    ((hF.integrableOn_compact isCompact_Icc).mono_set (support_subset_box r))

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2ContinuousFibreFubini
