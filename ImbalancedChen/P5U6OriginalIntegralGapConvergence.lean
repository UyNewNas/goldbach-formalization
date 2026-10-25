import ImbalancedChen.P5U6OriginalUniformEnvelopeBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Genuine diagonal convergence of the ORIGINAL corrected Runbo U6 rational
enclosure gap. The actual LOWER h248 array, true R denominator, generated
Ico owner, proper affine profile/product walls, moving rational log tails,
and explicit integrable dominator are all supplied by source proofs.
No gap, continuity, wall-nullity, domination or mean premise is supplied.
No concrete finite check is evaluated and no saved endpoint is asserted.
-/

namespace ImbalancedChen.P5U6OriginalIntegralGapConvergence

noncomputable section

open Set MeasureTheory Filter Topology Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6OriginalRationalIntegralCertificates P5U6OriginalOwnerKernelConvergence
open P5U6OriginalUniformEnvelopeBounds
open P5U6AdoptedH248BindingSourceOnly
open scoped BigOperators

def sampleGap (n : ℕ) (x : Fin 2 → ℝ) : ℝ :=
  sample n (outer n) (densityUpper n n) x - sample n (inner n) (densityLower n n) x

theorem eventually_owner_inner {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (hcap : x 0 + x 1 < 833 / 2500) :
    ∀ᶠ n in atTop, owner n x hx ∈ inner n := by
  have h0 := (corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 0).2
  have h1 := (corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 1).2
  filter_upwards [(h0.add h1).eventually (Iio_mem_nhds hcap)] with n hn
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hQ : upperCorner n (owner n x hx) 0 + upperCorner n (owner n x hx) 1 ≤ 833 / 2500 := by
    exact_mod_cast hn.le
  exact hQ

theorem eventually_owner_not_outer {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) (hcap : (833 / 2500 : ℝ) < x 0 + x 1) :
    ∀ᶠ n in atTop, owner n x hx ∉ outer n := by
  have h0 := (corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 0).1
  have h1 := (corner_tendsto (fun n => owner n x hx) (fun n => owner_mem n x hx) 1).1
  filter_upwards [(h0.add h1).eventually (Ioi_mem_nhds hcap)] with n hn
  intro ho
  have hQ := (Finset.mem_filter.mp ho).2
  have hR : (lowerCorner n (owner n x hx) 0 : ℝ) + lowerCorner n (owner n x hx) 1 ≤ 833 / 2500 := by
    exact_mod_cast hQ
  exact (not_lt_of_ge hR) hn

theorem sampleGap_tendsto_zero (x : Fin 2 → ℝ)
    (hne : ∀ k : Fin 201, currentChenUpsilon6OrdinaryProfile x ≠ floorGrid k.val)
    (hproduct : x 0 + x 1 ≠ (833 / 2500 : ℝ)) :
    Tendsto (fun n => sampleGap n x) atTop (𝓝 0) := by
  by_cases hx : x ∈ currentChenUpsilon6LogRectangle
  · by_cases hD : x ∈ currentChenUpsilon6LogDomain 0
    · have hcap : x 0 + x 1 < (833 / 2500 : ℝ) :=
        lt_of_le_of_ne (by simpa only [sub_zero] using hD.2) hproduct
      have hlims := generated_density_bounds_tendsto hD hne
      have ht : Tendsto (fun n => (densityUpper n n (owner n x hx) : ℝ) -
          (densityLower n n (owner n x hx) : ℝ)) atTop (𝓝 0) := by
        simpa only [sub_self] using hlims.2.sub hlims.1
      apply ht.congr'
      filter_upwards [eventually_owner_inner hx hcap] with n hn
      have ho := domain_cell_is_outer n hD (owner_mem n x hx)
      rw [sampleGap, sample_eq_owner n (outer n) _ hx, sample_eq_owner n (inner n) _ hx,
        if_pos ho, if_pos hn]
    · have hcap : (833 / 2500 : ℝ) < x 0 + x 1 := by
        apply lt_of_not_ge
        intro hc
        exact hD ⟨hx, by simpa only [sub_zero] using hc⟩
      have hni (n : ℕ) : owner n x hx ∉ inner n := fun hi =>
        hD (inner_cell_subset_domain n hi (owner_mem n x hx))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_owner_not_outer hx hcap] with n hn
      rw [sampleGap, sample_eq_owner n (outer n) _ hx, sample_eq_owner n (inner n) _ hx,
        if_neg hn, if_neg (hni n), sub_self]
  · apply tendsto_const_nhds.congr
    intro n
    rw [sampleGap, sample_eq_zero_outside n (outer n) _ hx,
      sample_eq_zero_outside n (inner n) _ hx, sub_self]

theorem ae_sampleGap_tendsto_zero :
    ∀ᵐ x : Fin 2 → ℝ ∂volume, Tendsto (fun n => sampleGap n x) atTop (𝓝 0) := by
  have hp : ∀ᵐ x : Fin 2 → ℝ ∂volume, x 0 + x 1 ≠ (833 / 2500 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using currentChenUpsilon6_productWall_volume_zero (833 / 2500 : ℝ)
  filter_upwards [ae_profile_ne_all_knots, hp] with x hk hc
  exact sampleGap_tendsto_zero x hk hc

theorem sampleGap_integrable (n : ℕ) : Integrable (sampleGap n) :=
  (sample_integrable n (outer n) _).sub (sample_integrable n (inner n) _)

theorem integral_sampleGap_eq (n : ℕ) :
    (∫ x, sampleGap n x) = ((rationalUpper n n - rationalLower n n : ℚ) : ℝ) := by
  rw [sampleGap, integral_sub (sample_integrable n (outer n) _) (sample_integrable n (inner n) _),
    sample_integral, sample_integral]
  simp only [rationalUpper, rationalLower, Rat.cast_sub]

/-- True original U6 diagonal enclosure-gap limit. Every real analytic
and actual geometric supplier is discharged above, before applying DCT. -/
theorem tendsto_diagonal_rational_enclosure_gap :
    Tendsto (fun n : ℕ => ((rationalUpper n n - rationalLower n n : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence domination
    (fun n => (sampleGap_integrable n).aestronglyMeasurable) domination_integrable
    (fun n => Eventually.of_forall
      (sample_difference_dominated n n (inner n) (outer n) (fun _ hj => hj) (fun _ hj => hj)))
    ae_sampleGap_tendsto_zero
  simpa only [integral_sampleGap_eq, integral_zero] using ht

end

end ImbalancedChen.P5U6OriginalIntegralGapConvergence
