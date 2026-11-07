import ImbalancedChen.Part3IndicatorInvariantCyclicDensity
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Closed scalar L2 submodules invariant under the actual real coordinate
multiplier on a compact subset of R are invariant under every measurable
indicator. Stone--Weierstrass first gives invariance under all continuous
real multipliers. An integrable L2 pairing is then extended to R, where
the pinned continuous-test uniqueness theorem proves local annihilation.
This argument works for arbitrary measures on the compact coordinate
space; it never assumes that the constant function lies in L2.
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.CompactCoordinateIndicatorInvariance20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a

variable {s : Set ℝ} [CompactSpace s] (μ : Measure s)

private theorem multiply_memLp (φ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    MemLp (fun x : s => φ x • u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul
    (φ.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact Eventually.of_forall fun x => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)

def continuousMultiply (φ : C(s, ℝ)) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (multiply_memLp μ φ u).toLp (fun x => φ x • u x)

theorem continuousMultiply_coe_ae (φ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    continuousMultiply μ φ u =ᵐ[μ] (fun x => φ x • u x) :=
  (multiply_memLp μ φ u).coeFn_toLp

theorem continuousMultiply_norm_le (φ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    ‖continuousMultiply μ φ u‖ ≤ ‖φ‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousMultiply_coe_ae μ φ u] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)

theorem continuousMultiply_const (c : ℝ) (u : Lp ℂ 2 μ) :
    continuousMultiply μ (ContinuousMap.const s c) u = c • u := by
  apply Lp.ext
  filter_upwards [continuousMultiply_coe_ae μ (ContinuousMap.const s c) u,
    Lp.coeFn_smul c u] with x hx hy
  exact hx.trans hy.symm

theorem continuousMultiply_add (φ ψ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    continuousMultiply μ (φ + ψ) u = continuousMultiply μ φ u + continuousMultiply μ ψ u := by
  apply Lp.ext
  filter_upwards [continuousMultiply_coe_ae μ (φ + ψ) u,
    continuousMultiply_coe_ae μ φ u, continuousMultiply_coe_ae μ ψ u,
    Lp.coeFn_add (continuousMultiply μ φ u) (continuousMultiply μ ψ u)] with x hxy hx hy hadd
  rw [hxy, hadd, hx, hy]
  exact add_smul _ _ _

theorem continuousMultiply_smul (c : ℝ) (φ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    continuousMultiply μ (c • φ) u = c • continuousMultiply μ φ u := by
  apply Lp.ext
  filter_upwards [continuousMultiply_coe_ae μ (c • φ) u,
    continuousMultiply_coe_ae μ φ u, Lp.coeFn_smul c (continuousMultiply μ φ u)] with x hleft hx hright
  rw [hleft, hright, hx]
  exact mul_smul _ _ _

theorem continuousMultiply_mul (φ ψ : C(s, ℝ)) (u : Lp ℂ 2 μ) :
    continuousMultiply μ (φ * ψ) u = continuousMultiply μ φ (continuousMultiply μ ψ u) := by
  apply Lp.ext
  filter_upwards [continuousMultiply_coe_ae μ (φ * ψ) u,
    continuousMultiply_coe_ae μ φ (continuousMultiply μ ψ u),
    continuousMultiply_coe_ae μ ψ u] with x hleft hright hinner
  rw [hleft, hright, hinner]
  exact mul_smul _ _ _

def continuousOrbit (u : Lp ℂ 2 μ) : C(s, ℝ) →L[ℝ] Lp ℂ 2 μ :=
  ({ toFun := fun φ => continuousMultiply μ φ u
     map_add' := fun φ ψ => continuousMultiply_add μ φ ψ u
     map_smul' := fun c φ => continuousMultiply_smul μ c φ u } :
    C(s, ℝ) →ₗ[ℝ] Lp ℂ 2 μ).mkContinuous ‖u‖ (fun φ => by
      simpa only [mul_comm] using continuousMultiply_norm_le μ φ u)

def coordinate : C(s, ℝ) := (ContinuousMap.id ℝ).restrict s

def coordinateMultiply (u : Lp ℂ 2 μ) : Lp ℂ 2 μ := continuousMultiply μ coordinate u

theorem coordinateMultiply_coe_ae (u : Lp ℂ 2 μ) :
    coordinateMultiply μ u =ᵐ[μ] (fun x : s => (x : ℝ) • u x) :=
  continuousMultiply_coe_ae μ coordinate u

/-- Stone--Weierstrass supplies every continuous real multiplier from
literal invariance under the single real coordinate. -/
theorem continuousMultiply_mem (S : Submodule ℂ (Lp ℂ 2 μ))
    (hclosed : IsClosed (S : Set (Lp ℂ 2 μ)))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiply μ u ∈ S)
    (φ : C(s, ℝ)) : ∀ u, u ∈ S → continuousMultiply μ φ u ∈ S := by
  apply ContinuousMap.induction_on_of_compact
    (p := fun ψ : C(s, ℝ) => ∀ u, u ∈ S → continuousMultiply μ ψ u ∈ S)
    (f := φ)
  · intro c u hu
    rw [continuousMultiply_const, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact S.smul_mem (c : ℂ) hu
  · exact hcoordinate
  · simpa only [star_trivial] using hcoordinate
  · intro ψ χ hψ hχ u hu
    rw [continuousMultiply_add]
    exact S.add_mem (hψ u hu) (hχ u hu)
  · intro ψ χ hψ hχ u hu
    rw [continuousMultiply_mul]
    exact hψ _ (hχ u hu)
  · intro ψ hfreq u hu
    exact hclosed.mem_of_frequently_of_tendsto
      (hfreq.mono (fun χ hχ => hχ u hu)) ((continuousOrbit μ u).continuous.tendsto ψ)

theorem continuousMultiply_inner (φ : C(s, ℝ)) (u v : Lp ℂ 2 μ) :
    inner ℂ (continuousMultiply μ φ u) v =
      ∫ x : s, φ x • inner ℂ (u x) (v x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousMultiply_coe_ae μ φ u] with x hx
  rw [hx]
  exact inner_smul_left_eq_smul _ _ _

/-- Testing a compact-coordinate integrable function against all real
continuous functions determines it. The pinned distribution uniqueness
theorem is applied after an actual measurable embedding into R. -/
theorem ae_eq_zero_of_continuous_tests (q : s → ℂ) (hq : Integrable q μ)
    (htest : ∀ φ : C(s, ℝ), (∫ x : s, φ x • q x ∂μ) = 0) : q =ᵐ[μ] 0 := by
  classical
  have hs : IsClosed s := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have he : MeasurableEmbedding (Subtype.val : s → ℝ) :=
    MeasurableEmbedding.subtype_coe hs.measurableSet
  let Q : ℝ → ℂ := fun x => if hx : x ∈ s then q ⟨x, hx⟩ else 0
  have hQ (x : s) : Q (x : ℝ) = q x := by simp only [Q, dif_pos x.property]
  have hQmeas : AEStronglyMeasurable Q (μ.map (Subtype.val : s → ℝ)) := by
    apply he.aestronglyMeasurable_map_iff.2
    simpa only [Function.comp_apply, hQ] using hq.aestronglyMeasurable
  have hQint : Integrable Q (μ.map (Subtype.val : s → ℝ)) := by
    apply (integrable_map_measure hQmeas he.measurable.aemeasurable).2
    simpa only [Function.comp_apply, hQ] using hq
  have hzero : ∀ᵐ x : ℝ ∂μ.map (Subtype.val : s → ℝ), Q x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hQint.locallyIntegrable
    intro g hg _hgcompact
    rw [integral_map he.measurable.aemeasurable
      (hg.continuous.aestronglyMeasurable.smul hQmeas)]
    simpa only [hQ] using htest ⟨fun x : s => g (x : ℝ),
      hg.continuous.comp continuous_subtype_val⟩
  simpa only [hQ] using ae_of_ae_map he.measurable.aemeasurable hzero

/-- A real coordinate is symmetric, so its invariant submodule has an
invariant orthogonal complement. This is derived, not supplied. -/
theorem orthogonal_coordinate_invariant (S : Submodule ℂ (Lp ℂ 2 μ))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiply μ u ∈ S)
    {v : Lp ℂ 2 μ} (hv : v ∈ Sᗮ) : coordinateMultiply μ v ∈ Sᗮ := by
  apply (S.mem_orthogonal _).2
  intro u hu
  have hsym : inner ℂ u (coordinateMultiply μ v) = inner ℂ (coordinateMultiply μ u) v := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coordinateMultiply_coe_ae μ u, coordinateMultiply_coe_ae μ v] with x hxu hxv
    rw [hxu, hxv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  rw [hsym]
  exact (S.mem_orthogonal v).mp hv _ (hcoordinate u hu)

/-- The main new implication has only closedness and coordinate invariance
as subspace inputs; no indicator or density premise occurs. -/
theorem indicatorMultiplier_mem (S : Submodule ℂ (Lp ℂ 2 μ))
    (hclosed : IsClosed (S : Set (Lp ℂ 2 μ)))
    (hcoordinate : ∀ u, u ∈ S → coordinateMultiply μ u ∈ S)
    (B : Set s) (hB : MeasurableSet B) (u : Lp ℂ 2 μ) (hu : u ∈ S) :
    indicatorMultiplier μ B hB u ∈ S := by
  have hdouble : indicatorMultiplier μ B hB u ∈ Sᗮᗮ := by
    apply (Sᗮ.mem_orthogonal _).2
    intro v hv
    have hq : Integrable (fun x : s => inner ℂ (u x) (v x)) μ := L2.integrable_inner u v
    have hqzero : (fun x : s => inner ℂ (u x) (v x)) =ᵐ[μ] 0 := by
      apply ae_eq_zero_of_continuous_tests μ _ hq
      intro φ
      rw [← continuousMultiply_inner]
      exact (S.mem_orthogonal v).mp hv _ (continuousMultiply_mem μ S hclosed hcoordinate φ u hu)
    have hinner : inner ℂ (indicatorMultiplier μ B hB u) v = 0 := by
      rw [indicatorMultiplier_inner]
      exact integral_eq_zero_of_ae (ae_restrict_of_ae hqzero)
    exact (inner_eq_zero_symm).mp hinner
  rw [S.orthogonal_orthogonal_eq_closure, hclosed.submodule_topologicalClosure_eq] at hdouble
  exact hdouble

end

end ImbalancedChen.Part3.CompactCoordinateIndicatorInvariance20261025a
