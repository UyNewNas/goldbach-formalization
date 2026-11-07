import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The real-parameter nonholomorphic Eisenstein seed is the literal upper-half-plane
lattice summand `Im(z)^s / |c*z+d|^(2*s)`. For `s > 1` this file proves absolute
summability on all integer pairs, hence on primitive pairs, and uniform convergence
on bounded-height portions of vertical strips and on compact subsets of `ℍ`.

The only external analytic inputs are the pinned Mathlib lemmas
`EisensteinSeries.summand_bound_of_mem_verticalStrip` and
`EisensteinSeries.summable_one_div_norm_rpow`. There is no spectral continuation,
Fourier expansion, functional equation, or Kuznetsov assertion.
-/

namespace ImbalancedChen.Part3.RealEisensteinSeedConvergence

noncomputable section

open Complex UpperHalfPlane EisensteinSeries Set Topology
open scoped UpperHalfPlane

/-- The actual real-parameter seed indexed by the integer vector `(c,d)`.
The zero vector contributes zero, as appropriate for the all-pairs majorant. -/
def seed (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) : ℝ :=
  z.im ^ s * ‖(v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)‖ ^ (-(2 * s))

/-- Literal quotient form of the nonholomorphic seed. -/
theorem seed_eq_quotient (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) :
    seed s z v = z.im ^ s /
      ‖(v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)‖ ^ (2 * s) := by
  rw [seed, Real.rpow_neg (norm_nonneg _) (2 * s)]
  exact (div_eq_mul_inv _ _).symm

/-- The lattice norm majorant is summable exactly in the range used by the
nonholomorphic seed: `2*s > 2`. -/
private theorem latticeMajorant_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun v : Fin 2 → ℤ => ‖v‖ ^ (-(2 * s))) := by
  exact EisensteinSeries.summable_one_div_norm_rpow (by linarith : 2 < 2 * s)

/-- Absolute convergence of the genuine all-pairs seed for each `z ∈ ℍ`.
This immediately controls every primitive or congruence-restricted subseries. -/
theorem seed_summable (s : ℝ) (hs : 1 < s) (z : ℍ) :
    Summable (seed s z) := by
  let C : ℝ := z.im ^ s * EisensteinSeries.r z ^ (-(2 * s))
  have hmaj : Summable (fun v : Fin 2 → ℤ => C * ‖v‖ ^ (-(2 * s))) :=
    (latticeMajorant_summable s hs).mul_left C
  apply hmaj.of_nonneg_of_le (fun v => by unfold seed; positivity)
  intro v
  have hb := EisensteinSeries.summand_bound z
    (show 0 ≤ 2 * s by linarith) v
  calc
    seed s z v ≤ z.im ^ s *
        (EisensteinSeries.r z ^ (-(2 * s)) * ‖v‖ ^ (-(2 * s))) := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * ‖v‖ ^ (-(2 * s)) := by simp [C, mul_assoc]

/-- Absolute convergence on the actual primitive-pair type from pinned Mathlib. -/
theorem primitiveSeed_summable (s : ℝ) (hs : 1 < s) (z : ℍ) :
    Summable (fun v : EisensteinSeries.gammaSet 1 1 0 => seed s z v.1) :=
  (seed_summable s hs z).subtype _

/-- An explicit positive lower bound for every nonzero lattice denominator
on a compact subset of the actual upper half plane. The constant is Mathlib's
`r` evaluated at a strip enclosing the compact set. -/
theorem compact_denominator_lower_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ v : Fin 2 → ℤ, v ≠ 0 →
      C * ‖v‖ ≤ ‖(v 0 : ℂ) * (z : ℂ) + (v 1 : ℂ)‖ := by
  obtain ⟨A, B, hB, hstrip⟩ := subset_verticalStrip_of_isCompact hK
  refine ⟨EisensteinSeries.r ⟨⟨A, B⟩, hB⟩,
    EisensteinSeries.r_pos _, ?_⟩
  intro z hz v hv
  exact (mul_le_mul_of_nonneg_right
    (EisensteinSeries.r_lower_bound_on_verticalStrip z hB (hstrip hz))
    (norm_nonneg v)).trans (EisensteinSeries.r_mul_max_le z hv)

/-- Explicit summable majorant on a vertical strip with an upper height bound.
The strip lower height `B` makes the denominator bound uniform; `Y` controls
the numerator `Im(z)^s`. -/
theorem seed_bound_on_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y : ℝ) (hB : 0 < B) (v : Fin 2 → ℤ) (z : ℍ)
    (hz : z ∈ verticalStrip A B) (hY : z.im ≤ Y) :
    seed s z v ≤
      (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s))) *
        ‖v‖ ^ (-(2 * s)) := by
  have hden := EisensteinSeries.summand_bound_of_mem_verticalStrip
    (z := z) (show 0 ≤ 2 * s by linarith) v hB hz
  have hnum : z.im ^ s ≤ Y ^ s := by
    exact Real.rpow_le_rpow z.im_pos.le hY (by linarith)
  calc
    seed s z v ≤ z.im ^ s *
        (EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)) *
          ‖v‖ ^ (-(2 * s))) := by
            exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ Y ^ s *
        (EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s)) *
          ‖v‖ ^ (-(2 * s))) := by
            exact mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s))) *
          ‖v‖ ^ (-(2 * s)) := by ring

/-- Uniform convergence of finite seed sums on a bounded-height vertical strip. -/
theorem seed_tendstoUniformlyOn_boundedStrip (s : ℝ) (hs : 1 < s)
    (A B Y : ℝ) (hB : 0 < B) :
    TendstoUniformlyOn
      (fun F : Finset (Fin 2 → ℤ) => fun z : ℍ => ∑ v ∈ F, seed s z v)
      (fun z : ℍ => ∑' v : Fin 2 → ℤ, seed s z v) Filter.atTop
      (verticalStrip A B ∩ {z : ℍ | z.im ≤ Y}) := by
  let C : ℝ := Y ^ s * EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * s))
  apply tendstoUniformlyOn_tsum ((latticeMajorant_summable s hs).mul_left C)
  intro v z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold seed; positivity)]
  exact seed_bound_on_boundedStrip s hs A B Y hB v z hz.1 hz.2

/-- The genuine all-pairs seed sum converges locally uniformly on the actual
upper half plane for every real `s > 1`. -/
theorem seed_tendstoLocallyUniformly (s : ℝ) (hs : 1 < s) :
    TendstoLocallyUniformly
      (fun F : Finset (Fin 2 → ℤ) => fun z : ℍ => ∑ v ∈ F, seed s z v)
      (fun z : ℍ => ∑' v : Fin 2 → ℤ, seed s z v) Filter.atTop := by
  simp only [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨A, B, hB, hstrip⟩ := subset_verticalStrip_of_isCompact hK
  have hheight : ∃ Y : ℝ, ∀ z ∈ K, z.im ≤ Y := by
    rcases K.eq_empty_or_nonempty with h | h
    · refine ⟨1, ?_⟩
      simpa [h]
    · obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn h continuous_im.continuousOn
      exact ⟨u.im, fun z hz => isMaxOn_iff.mp hu z hz⟩
  obtain ⟨Y, hY⟩ := hheight
  exact (seed_tendstoUniformlyOn_boundedStrip s hs A B Y hB).mono
    (fun z hz => ⟨hstrip hz, hY z hz⟩)

end

end ImbalancedChen.Part3.RealEisensteinSeedConvergence
