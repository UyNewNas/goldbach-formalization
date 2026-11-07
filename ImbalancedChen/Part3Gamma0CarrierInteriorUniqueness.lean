import ImbalancedChen.Part3Gamma0FiniteCarrierExactMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The genuine second modular fundamental-domain lemma implies that two
points in the finite Gamma0 carrier, one in its open-cell part, can differ
by Gamma0 only through the scalar kernel {1,-1}. The exceptional points
for noncentral collisions lie in the finite union of translated modular
boundaries and hence have zero canonical hyperbolic volume. No abstract
fundamental-domain or spectral theorem is a hypothesis.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z

/-- The union of the actual translated open modular cells. -/
def gamma0OpenCarrier (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ q : gamma0Classes N, inverseClassRep N q • ModularGroup.fdo

private theorem conjugate_neg_one (a : SL(2, ℤ)) :
    a⁻¹ * (-1 : SL(2, ℤ)) * a = -1 := by
  have hc : (-1 : SL(2, ℤ)) * a = a * (-1 : SL(2, ℤ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    a⁻¹ * (-1 : SL(2, ℤ)) * a = a⁻¹ * ((-1 : SL(2, ℤ)) * a) := by group
    _ = a⁻¹ * (a * (-1 : SL(2, ℤ))) := by rw [hc]
    _ = -1 := by group

/-- A relative central matrix forces equality of the original right
Gamma0 cosets, even though Gamma0 is not assumed normal. -/
private theorem cosets_eq_of_gamma0_relative_center (N : ℕ) [NeZero N]
    (q r : gamma0Classes N) (γ : CongruenceSubgroup.Gamma0 N)
    (hc : (inverseClassRep N r)⁻¹ * (γ : SL(2, ℤ)) * inverseClassRep N q = 1 ∨
      (inverseClassRep N r)⁻¹ * (γ : SL(2, ℤ)) * inverseClassRep N q = -1) :
    q = r := by
  let a : SL(2, ℤ) := Quotient.out q
  let b : SL(2, ℤ) := Quotient.out r
  have hc' : b * (γ : SL(2, ℤ)) * a⁻¹ = 1 ∨
      b * (γ : SL(2, ℤ)) * a⁻¹ = -1 := by
    simpa only [inverseClassRep, inv_inv, a, b] using hc
  have hrewrite : a⁻¹ * b =
      (a⁻¹ * (b * (γ : SL(2, ℤ)) * a⁻¹) * a) * (γ : SL(2, ℤ))⁻¹ := by
    group
  have hmem : a⁻¹ * b ∈ CongruenceSubgroup.Gamma0 N := by
    rcases hc' with hc' | hc'
    · rw [hrewrite, hc']
      simpa using (CongruenceSubgroup.Gamma0 N).inv_mem γ.property
    · rw [hrewrite, hc', conjugate_neg_one]
      exact (CongruenceSubgroup.Gamma0 N).mul_mem
        (neg_one_mem_gamma0 N) ((CongruenceSubgroup.Gamma0 N).inv_mem γ.property)
  have hclass : (a : gamma0Classes N) = b := QuotientGroup.eq.mpr hmem
  calc
    q = (a : gamma0Classes N) := (Quotient.out_eq' q).symm
    _ = b := hclass
    _ = r := Quotient.out_eq' r

/-- The original modular-domain theorem computes the relative matrix,
then the actual Gamma0 condition makes the cell labels equal. -/
theorem gamma0_between_open_closed_cells (N : ℕ) [NeZero N]
    (q r : gamma0Classes N) (γ : CongruenceSubgroup.Gamma0 N)
    {z : UpperHalfPlane}
    (hq : z ∈ inverseClassRep N q • ModularGroup.fdo)
    (hr : γ • z ∈ inverseClassRep N r • modularFD) :
    q = r ∧ ((γ : SL(2, ℤ)) = 1 ∨ (γ : SL(2, ℤ)) = -1) := by
  let g := inverseClassRep N q
  let h := inverseClassRep N r
  have hz : g⁻¹ • z ∈ ModularGroup.fdo :=
    mem_smul_set_iff_inv_smul_mem.mp hq
  have hclosed : h⁻¹ • (γ • z) ∈ modularFD :=
    mem_smul_set_iff_inv_smul_mem.mp hr
  have hrelative :
      (h⁻¹ * (γ : SL(2, ℤ)) * g) • (g⁻¹ • z) ∈ ModularGroup.fd := by
    simpa [mul_smul, modularFD] using hclosed
  have hc := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hz hrelative
  have hqr : q = r :=
    cosets_eq_of_gamma0_relative_center N q r γ (by simpa [g, h] using hc)
  refine ⟨hqr, ?_⟩
  have hcself : g⁻¹ * (γ : SL(2, ℤ)) * g = 1 ∨
      g⁻¹ * (γ : SL(2, ℤ)) * g = -1 := by
    simpa [h, g, ← hqr] using hc
  apply (sl2_fixed_all_iff (γ : SL(2, ℤ))).mp
  intro w
  have hfix :=
    (sl2_fixed_all_iff (g⁻¹ * (γ : SL(2, ℤ)) * g)).mpr hcself (g⁻¹ • w)
  simpa [mul_smul] using congrArg (fun u : UpperHalfPlane => g • u) hfix

/-- Open-carrier representatives are unique modulo the genuine scalar
kernel of the integral Gamma0 action. -/
theorem gamma0_open_to_closed_center (N : ℕ) [NeZero N]
    (γ : CongruenceSubgroup.Gamma0 N) {z : UpperHalfPlane}
    (hz : z ∈ gamma0OpenCarrier N) (hγz : γ • z ∈ gamma0Carrier N) :
    (γ : SL(2, ℤ)) = 1 ∨ (γ : SL(2, ℤ)) = -1 := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  obtain ⟨r, hr⟩ := mem_iUnion.mp hγz
  exact (gamma0_between_open_closed_cells N q r γ hq hr).2

/-- The same conclusion in the existing effective-action kernel. -/
theorem gamma0_open_to_closed_mem_kernel (N : ℕ) [NeZero N]
    (γ : CongruenceSubgroup.Gamma0 N) {z : UpperHalfPlane}
    (hz : z ∈ gamma0OpenCarrier N) (hγz : γ • z ∈ gamma0Carrier N) :
    γ ∈ gamma0ActionKernel N :=
  (gamma0_actionKernel_iff N γ).mpr (gamma0_open_to_closed_center N γ hz hγz)

/-- The precise exceptional boundary carrier; no topological boundary
of a finite union has to be computed. -/
def gamma0BoundaryCarrier (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ q : gamma0Classes N, inverseClassRep N q • modularFDBoundary

/-- The closed-minus-open carrier is explicitly covered by translated
null modular boundaries. -/
theorem carrier_sdiff_open_subset_boundary (N : ℕ) [NeZero N] :
    gamma0Carrier N \ gamma0OpenCarrier N ⊆ gamma0BoundaryCarrier N := by
  intro z hz
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz.1
  refine mem_iUnion.mpr ⟨q, ?_⟩
  rw [mem_smul_set_iff_inv_smul_mem]
  refine ⟨mem_smul_set_iff_inv_smul_mem.mp hq, ?_⟩
  intro hopen
  apply hz.2
  exact mem_iUnion.mpr ⟨q, mem_smul_set_iff_inv_smul_mem.mpr hopen⟩

theorem gamma0BoundaryCarrier_null (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (gamma0BoundaryCarrier N) = 0 := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  unfold gamma0BoundaryCarrier
  apply measure_iUnion_null
  intro q
  change (volume : Measure UpperHalfPlane)
    ((SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • modularFDBoundary) = 0
  rw [measure_smul]
  exact modularFDBoundary_null

theorem carrier_sdiff_open_null (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane)
      (gamma0Carrier N \ gamma0OpenCarrier N) = 0 :=
  measure_mono_null (carrier_sdiff_open_subset_boundary N) (gamma0BoundaryCarrier_null N)

/-- Points at which distinct effective Gamma0 translates can both return
to the carrier. The group quantifier is over actual integral matrices. -/
def noncentralCollisionPoints (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  {z | z ∈ gamma0Carrier N ∧
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      γ ∉ gamma0ActionKernel N ∧ γ • z ∈ gamma0Carrier N}

theorem noncentralCollisionPoints_subset_boundary (N : ℕ) [NeZero N] :
    noncentralCollisionPoints N ⊆ gamma0BoundaryCarrier N := by
  apply Subset.trans (t := gamma0Carrier N \ gamma0OpenCarrier N)
  · rintro z ⟨hz, γ, hγ, hγz⟩
    refine ⟨hz, ?_⟩
    intro hopen
    exact hγ (gamma0_open_to_closed_mem_kernel N γ hopen hγz)
  · exact carrier_sdiff_open_subset_boundary N

/-- Noncentral repetitions in the actual Gamma0 carrier have zero
canonical hyperbolic volume. This closes the boundary-null reduction. -/
theorem noncentralCollisionPoints_null (N : ℕ) [NeZero N] :
    (volume : Measure UpperHalfPlane) (noncentralCollisionPoints N) = 0 :=
  measure_mono_null (noncentralCollisionPoints_subset_boundary N) (gamma0BoundaryCarrier_null N)

end
end ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a

