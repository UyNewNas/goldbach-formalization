import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier
import ImbalancedChen.Part3Gamma0EffectiveActionKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / no acceptance credit, 2026-10-24.

This upgrades the finite Gamma0 carrier from a finite-volume *cover* to
an exact measured modular cell carrier.  The new input is proved here:
the boundary of Mathlib's classical modular domain has zero canonical
hyperbolic volume.  Its circular part is a Euclidean sphere and its two
straight parts are planar vertical lines.  Mathlib's second fundamental
domain lemma then makes distinct finite Gamma0 coset cells almost-everywhere
disjoint: an overlap with one point in the open modular cell would force
the relative matrix to be ±1, whose central sign lies in Gamma0.

This is an exact volume statement for the concrete finite union of cells.
No abstract orbit quotient, quotient measure, or Plancherel theorem is
asserted.
-/

namespace ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z

private instance : MeasurableConstSMul SL(2, ℤ) UpperHalfPlane where
  measurable_const_smul g := by
    change Measurable (fun z : UpperHalfPlane =>
      (SpecialLinearGroup.mapGL ℝ g) • z)
    exact (continuous_const_smul _).measurable

private instance : SMulInvariantMeasure SL(2, ℤ) UpperHalfPlane
    (volume : Measure UpperHalfPlane) where
  measure_preimage_smul g s hs := by
    change (volume : Measure UpperHalfPlane)
        ((fun z : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ g) • z) ⁻¹' s) =
      (volume : Measure UpperHalfPlane) s
    exact SMulInvariantMeasure.measure_preimage_smul
      (SpecialLinearGroup.mapGL ℝ g) hs

/-- A fixed real-coordinate line is planar Lebesgue-null.  The factor
`{a}` is null even though the second factor is unbounded. -/
private theorem complex_vertical_null (a : ℝ) :
    (volume : Measure ℂ) {w : ℂ | w.re = a} = 0 := by
  have hpre : {w : ℂ | w.re = a} =
      Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (univ : Set ℝ)) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply]
  rw [hpre]
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.singleton.prod MeasurableSet.univ)]
  simp [Measure.volume_eq_prod, Measure.prod_prod]

/-- Pulling a planar vertical line back to the upper half-plane keeps it
null for the density-weighted hyperbolic measure. -/
private theorem upper_vertical_null (a : ℝ) :
    (volume : Measure UpperHalfPlane) {z : UpperHalfPlane | z.re = a} = 0 := by
  have hcoord : coordinateMeasure {z : UpperHalfPlane | z.re = a} = 0 := by
    rw [coordinateMeasure,
      UpperHalfPlane.measurableEmbedding_coe.comap_apply]
    apply measure_mono_null (t := {w : ℂ | w.re = a})
    · rintro w ⟨z, hz, rfl⟩
      exact hz
    · exact complex_vertical_null a
  exact hyperbolicMeasure_absolutelyContinuous_coordinate hcoord

/-- The circular part of Mathlib's modular boundary is planar-null. -/
private theorem upper_unit_circle_null :
    (volume : Measure UpperHalfPlane)
      {z : UpperHalfPlane | Complex.normSq (z : ℂ) = 1} = 0 := by
  have hcoord : coordinateMeasure
      {z : UpperHalfPlane | Complex.normSq (z : ℂ) = 1} = 0 := by
    rw [coordinateMeasure,
      UpperHalfPlane.measurableEmbedding_coe.comap_apply]
    apply measure_mono_null (t := Metric.sphere (0 : ℂ) 1)
    · rintro w ⟨z, hz, rfl⟩
      have hn : ‖(z : ℂ)‖ = 1 := by
        rw [Complex.normSq_eq_norm_sq] at hz
        nlinarith [norm_nonneg (z : ℂ)]
      simpa [Metric.mem_sphere, dist_eq_norm] using hn
    · exact Measure.addHaar_sphere (volume : Measure ℂ) 0 1
  exact hyperbolicMeasure_absolutelyContinuous_coordinate hcoord

/-- The closed classical cell minus its open interior. -/
def modularFDBoundary : Set UpperHalfPlane :=
  modularFD \ ModularGroup.fdo

private theorem modularFDBoundary_subset_null_parts :
    modularFDBoundary ⊆
      {z : UpperHalfPlane | Complex.normSq (z : ℂ) = 1} ∪
      {z : UpperHalfPlane | z.re = (1 : ℝ) / 2} ∪
      {z : UpperHalfPlane | z.re = -(1 : ℝ) / 2} := by
  intro z hz
  rcases hz with ⟨hfd, hnot⟩
  change (1 : ℝ) ≤ Complex.normSq (z : ℂ) ∧
    |z.re| ≤ (1 : ℝ) / 2 at hfd
  change ¬ ((1 : ℝ) < Complex.normSq (z : ℂ) ∧
    |z.re| < (1 : ℝ) / 2) at hnot
  by_cases hnorm : (1 : ℝ) < Complex.normSq (z : ℂ)
  · have heq : |z.re| = (1 : ℝ) / 2 :=
      le_antisymm hfd.2 (le_of_not_gt (fun hh => hnot ⟨hnorm, hh⟩))
    rcases le_total 0 z.re with hpos | hneg
    · exact Or.inr (Or.inl (by simpa [abs_of_nonneg hpos] using heq))
    · exact Or.inr (Or.inr (by
        rw [abs_of_nonpos hneg] at heq
        linarith))
  · exact Or.inl (le_antisymm (le_of_not_gt hnorm) hfd.1)

/-- Mathlib's actual modular-domain boundary has zero hyperbolic measure. -/
theorem modularFDBoundary_null :
    (volume : Measure UpperHalfPlane) modularFDBoundary = 0 := by
  apply measure_mono_null modularFDBoundary_subset_null_parts
  exact measure_union_null upper_unit_circle_null
    (measure_union_null
      (upper_vertical_null ((1 : ℝ) / 2))
      (upper_vertical_null (-(1 : ℝ) / 2)))

private theorem translated_boundary_null (g : SL(2, ℤ)) :
    (volume : Measure UpperHalfPlane) (g • modularFDBoundary) = 0 := by
  rw [measure_smul]
  exact modularFDBoundary_null

/-- If two chosen inverse representatives differ projectively only by the
central sign, their original right Gamma0 classes coincide. -/
private theorem classes_eq_of_relative_center (N : ℕ) [NeZero N]
    (q r : gamma0Classes N)
    (hc : (inverseClassRep N r)⁻¹ * inverseClassRep N q = 1 ∨
      (inverseClassRep N r)⁻¹ * inverseClassRep N q = -1) : q = r := by
  let a : SL(2, ℤ) := Quotient.out q
  let b : SL(2, ℤ) := Quotient.out r
  have hcenter : b * a⁻¹ = 1 ∨ b * a⁻¹ = -1 := by
    simpa only [inverseClassRep, inv_inv, a, b] using hc
  have hright : ∃ k ∈ CongruenceSubgroup.Gamma0 N, a * k = b := by
    rcases hcenter with h | h
    · refine ⟨1, (CongruenceSubgroup.Gamma0 N).one_mem, ?_⟩
      have hab : b = a := by calc
        b = (b * a⁻¹) * a := by group
        _ = a := by rw [h]; simp
      simpa [hab]
    · refine ⟨-1, neg_one_mem_gamma0 N, ?_⟩
      have hab : b = (-1 : SL(2, ℤ)) * a := by calc
        b = (b * a⁻¹) * a := by group
        _ = (-1 : SL(2, ℤ)) * a := by rw [h]
      have hcentral : (-1 : SL(2, ℤ)) * a = a * (-1 : SL(2, ℤ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [hab, hcentral]
  obtain ⟨k, hk, hak⟩ := hright
  have hmem : a⁻¹ * b ∈ CongruenceSubgroup.Gamma0 N := by
    have heq : a⁻¹ * b = k := by rw [← hak]; group
    rw [heq]
    exact hk
  have hclass : (a : gamma0Classes N) = b :=
    QuotientGroup.eq.mpr hmem
  calc
    q = (a : gamma0Classes N) := (Quotient.out_eq' q).symm
    _ = b := hclass
    _ = r := Quotient.out_eq' r

/-- Distinct actual Gamma0 coset cells overlap only on a translated
modular-domain boundary.  The second FD lemma is the uniqueness input. -/
theorem distinct_coset_cells_aeDisjoint (N : ℕ) [NeZero N] :
    Pairwise (AEDisjoint (volume : Measure UpperHalfPlane) on
      fun q : gamma0Classes N => inverseClassRep N q • modularFD) := by
  intro q r hqr
  let g := inverseClassRep N q
  let h := inverseClassRep N r
  have hsubset :
      (g • modularFD) ∩ (h • modularFD) ⊆
        g • modularFDBoundary := by
    intro z hz
    have hgz : g⁻¹ • z ∈ modularFD :=
      (mem_smul_set_iff_inv_smul_mem).mp hz.1
    have hrz : h⁻¹ • z ∈ modularFD :=
      (mem_smul_set_iff_inv_smul_mem).mp hz.2
    have hnotopen : g⁻¹ • z ∉ ModularGroup.fdo := by
      intro hopen
      have hrelative : (h⁻¹ * g) • (g⁻¹ • z) ∈ ModularGroup.fd := by
        simpa [mul_smul, h, g, modularFD] using hrz
      have hc := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd
        hopen hrelative
      exact hqr (classes_eq_of_relative_center N q r (by simpa [g, h] using hc))
    rw [mem_smul_set_iff_inv_smul_mem]
    exact ⟨hgz, hnotopen⟩
  change (volume : Measure UpperHalfPlane)
    ((g • modularFD) ∩ (h • modularFD)) = 0
  exact measure_mono_null hsubset (translated_boundary_null g)

/-- Exact volume of the concrete finite Γ0 carrier.  The multiplier is
the actual subgroup index and the base volume is Mathlib's own fd volume. -/
theorem gamma0Carrier_measure_eq_index (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
        (volume : Measure UpperHalfPlane) modularFD := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  calc
    (volume : Measure UpperHalfPlane) (gamma0Carrier N) =
        ∑' q : gamma0Classes N,
          (volume : Measure UpperHalfPlane) (inverseClassRep N q • modularFD) := by
      unfold gamma0Carrier
      exact measure_iUnion₀ (distinct_coset_cells_aeDisjoint N)
        (fun q => (modularFD_measurable.const_smul _).nullMeasurableSet)
    _ = ∑ q : gamma0Classes N,
          (volume : Measure UpperHalfPlane) modularFD := by
      rw [tsum_fintype]
      simp only [measure_smul]
    _ = ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
          (volume : Measure UpperHalfPlane) modularFD := by
      rw [← gamma0Classes_card_eq_index N]
      simp [Finset.sum_const, nsmul_eq_mul]

end
end ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
