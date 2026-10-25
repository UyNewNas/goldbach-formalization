import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import ImbalancedChen.Part3Gamma0CarrierInteriorUniqueness

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The spatial quotient measure obtained from the actual finite modular-cell
carrier is independent of the choice of representatives of SL(2,Z)/Gamma0.
A legal section is the only new input. Its inverse cell is proved to be an
actual Gamma0 translate of the corresponding previously chosen inverse
cell. Arbitrary-section cells are a.e. disjoint by the proved true
open-to-closed Gamma0 cell uniqueness and the null modular boundary.
Finite additivity and the actual Gamma0 change-of-cell identity then give
equality of quotient measures. No measure equality or FD theorem is input.
-/

namespace ImbalancedChen.Part3.Gamma0CosetSectionIndependence20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a

/-- The inverse cell for an arbitrary integral representative section. -/
def sectionCell (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ)) (q : gamma0Classes N) : Set UpperHalfPlane :=
  (σ q)⁻¹ • modularFD

def sectionCarrier (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ)) : Set UpperHalfPlane :=
  ⋃ q : gamma0Classes N, sectionCell N σ q

/-- The change from the old representative to the new one is a matrix
of the actual Gamma0 subgroup, with its membership proved by right-coset equality. -/
def sectionChangeGamma (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q) (q : gamma0Classes N) :
    CongruenceSubgroup.Gamma0 N :=
  ⟨(σ q)⁻¹ * Quotient.out q, QuotientGroup.eq.mp
    ((hσ q).trans (Quotient.out_eq' q).symm)⟩

/-- Pointwise matrix relation underlying representative independence. -/
theorem sectionChangeGamma_mul_inverseClassRep (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q) (q : gamma0Classes N) :
    (sectionChangeGamma N σ hσ q : SL(2, ℤ)) * inverseClassRep N q = (σ q)⁻¹ := by
  change ((σ q)⁻¹ * Quotient.out q) * (Quotient.out q)⁻¹ = (σ q)⁻¹
  group

/-- The actual translate relation holds for every set, in particular for
the closed, open, and boundary modular cells. -/
theorem section_inverse_translate (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q)
    (q : gamma0Classes N) (D : Set UpperHalfPlane) :
    (σ q)⁻¹ • D = sectionChangeGamma N σ hσ q • (inverseClassRep N q • D) := by
  change (σ q)⁻¹ • D =
    (sectionChangeGamma N σ hσ q : SL(2, ℤ)) • (inverseClassRep N q • D)
  rw [smul_smul, sectionChangeGamma_mul_inverseClassRep]

/-- Each new cell has the identical quotient pushforward measure. -/
theorem sectionCell_pushforward_eq (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q) (q : gamma0Classes N) :
    cellPushforward N (sectionCell N σ q) =
      cellPushforward N (inverseClassRep N q • modularFD) := by
  unfold sectionCell
  rw [section_inverse_translate N σ hσ q modularFD]
  exact cellPushforward_gamma0_translate N (sectionChangeGamma N σ hσ q) _

theorem sectionCell_measurable (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ)) (q : gamma0Classes N) :
    MeasurableSet (sectionCell N σ q) := by
  change MeasurableSet ((SpecialLinearGroup.mapGL ℝ ((σ q)⁻¹)) • modularFD)
  exact modularFD_measurable.const_smul _

/-- New section cells cannot overlap away from a translated modular
boundary: an open overlap would violate actual Gamma0 cell uniqueness. -/
theorem sectionCells_aeDisjoint (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q) :
    Pairwise (AEDisjoint (volume : Measure UpperHalfPlane) on sectionCell N σ) := by
  intro q r hqr
  have hsubset : sectionCell N σ q ∩ sectionCell N σ r ⊆
      (σ q)⁻¹ • modularFDBoundary := by
    intro z hz
    have hqclosed : σ q • z ∈ modularFD := by
      simpa only [sectionCell, mem_smul_set_iff_inv_smul_mem, inv_inv] using hz.1
    have hnotopen : σ q • z ∉ ModularGroup.fdo := by
      intro hopen
      have hqnew : z ∈ (σ q)⁻¹ • ModularGroup.fdo := by
        rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact hopen
      have hrnew : z ∈ (σ r)⁻¹ • modularFD := hz.2
      rw [section_inverse_translate N σ hσ q ModularGroup.fdo] at hqnew
      rw [section_inverse_translate N σ hσ r modularFD] at hrnew
      have hqold := mem_smul_set_iff_inv_smul_mem.mp hqnew
      have hrold := mem_smul_set_iff_inv_smul_mem.mp hrnew
      let δ : CongruenceSubgroup.Gamma0 N :=
        (sectionChangeGamma N σ hσ r)⁻¹ * sectionChangeGamma N σ hσ q
      have hδ : δ • ((sectionChangeGamma N σ hσ q)⁻¹ • z) ∈
          inverseClassRep N r • modularFD := by
        simpa [δ, mul_smul] using hrold
      exact hqr (gamma0_between_open_closed_cells N q r δ hqold hδ).1
    rw [mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact ⟨hqclosed, hnotopen⟩
  change (volume : Measure UpperHalfPlane) (sectionCell N σ q ∩ sectionCell N σ r) = 0
  apply measure_mono_null hsubset
  change (volume : Measure UpperHalfPlane)
    ((SpecialLinearGroup.mapGL ℝ ((σ q)⁻¹)) • modularFDBoundary) = 0
  rw [measure_smul]
  exact modularFDBoundary_null

/-- Exact decomposition of the arbitrary-section carrier on every
measurable quotient test set. -/
theorem sectionCarrier_pushforward_apply (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q)
    {A : Set (Gamma0OrbitSpace N)} (hA : MeasurableSet A) :
    cellPushforward N (sectionCarrier N σ) A =
      ∑' q : gamma0Classes N, cellPushforward N (sectionCell N σ q) A := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  rw [cellPushforward_apply N (sectionCarrier N σ) hA]
  simp_rw [cellPushforward_apply N _ hA]
  unfold sectionCarrier
  rw [inter_iUnion]
  exact measure_iUnion₀
    ((sectionCells_aeDisjoint N σ hσ).mono fun i j hij =>
      hij.mono inter_subset_right inter_subset_right)
    (fun q => (((orbitProjection_measurable N) hA).inter
      (sectionCell_measurable N σ q)).nullMeasurableSet)

/-- The actual finite-cell quotient measure is independent of any legal
choice of right-coset representative section. -/
theorem sectionCarrier_pushforward_eq_canonical (N : ℕ) [NeZero N]
    (σ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q) :
    cellPushforward N (sectionCarrier N σ) = carrierPushforward N := by
  ext A hA
  have hcanonical := sectionCarrier_pushforward_apply N
    (fun q : gamma0Classes N => Quotient.out q)
    (fun q => Quotient.out_eq' q) hA
  change carrierPushforward N A =
    ∑' q : gamma0Classes N,
      cellPushforward N (inverseClassRep N q • modularFD) A at hcanonical
  rw [sectionCarrier_pushforward_apply N σ hσ hA, hcanonical]
  apply tsum_congr
  intro q
  rw [sectionCell_pushforward_eq N σ hσ q]

/-- Two arbitrary legal representative choices induce identical measures. -/
theorem sectionCarrier_pushforward_independent (N : ℕ) [NeZero N]
    (σ τ : gamma0Classes N → SL(2, ℤ))
    (hσ : ∀ q, (σ q : gamma0Classes N) = q)
    (hτ : ∀ q, (τ q : gamma0Classes N) = q) :
    cellPushforward N (sectionCarrier N σ) =
      cellPushforward N (sectionCarrier N τ) := by
  rw [sectionCarrier_pushforward_eq_canonical N σ hσ,
    sectionCarrier_pushforward_eq_canonical N τ hτ]

end
end ImbalancedChen.Part3.Gamma0CosetSectionIndependence20261025a


