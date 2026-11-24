import ImbalancedChen.P1OriginalThirdGammaMeshSectionBridge
import ImbalancedChen.P1FifthUnitBoxGainDecomposition
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- Genuine product-measure Fubini bridge for the actual Ico raw-owner union.
-- The exact section bound is an explicit remaining premise, not a hidden
-- whole-volume target. No all-archive selection assertion is made.
namespace ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P1OriginalPrefixRowDecodeSoundness
open P1FifthUnitBoxGainDecomposition

private abbrev Point := Fin 5 → ℝ
private abbrev Base := Fin 4 → ℝ

def baseBox (raw : FifthWireRow) : Set Base :=
  univ.pi (fun i => Icc (raw.lower ((0 : Fin 5).succAbove i) : ℝ)
    (raw.upper ((0 : Fin 5).succAbove i) : ℝ))

theorem baseBox_measurable (raw : FifthWireRow) : MeasurableSet (baseBox raw) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem baseBox_volume (raw : FifthWireRow) (hg : raw.grid = 400) :
    volume (baseBox raw) = (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
  have hw (i : Fin 4) :
      (raw.upper ((0 : Fin 5).succAbove i) : ℝ) -
        (raw.lower ((0 : Fin 5).succAbove i) : ℝ) = 1 / 400 := by
    simp only [FifthWireRow.upper, FifthWireRow.lower, hg]
    push_cast
    ring
  rw [baseBox, volume_pi_pi]
  simp_rw [Real.volume_Icc, hw]
  simp

def ownerUnion (raw : FifthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) : Set Point :=
  ⋃ j ∈ J, rawOwnerDomain raw e chi m omega j

theorem ownerUnion_measurable (raw : FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) :
    MeasurableSet (ownerUnion raw e chi m omega J) := by
  dsimp [ownerUnion]
  exact MeasurableSet.biUnion (fun j _ => rawOwnerDomain_measurable raw e chi m omega j)

theorem ownerUnion_subset_raw (raw : FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) :
    ownerUnion raw e chi m omega J ⊆ raw.originalBox := by
  intro t ht
  obtain ⟨j, _hj, htj⟩ := mem_iUnion₂.mp ht
  exact htj.1

def ownerSymmDiff (raw : FifthWireRow)
    (e₀ e₁ : ℚ) (chi₀ chi₁ : ℝ) (m : ℕ)
    (omega₀ omega₁ : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) : Set Point :=
  (ownerUnion raw e₀ chi₀ m omega₀ J \
      ownerUnion raw e₁ chi₁ m omega₁ J) ∪
    (ownerUnion raw e₁ chi₁ m omega₁ J \
      ownerUnion raw e₀ chi₀ m omega₀ J)

theorem ownerSymmDiff_measurable (raw : FifthWireRow)
    (e₀ e₁ : ℚ) (chi₀ chi₁ : ℝ) (m : ℕ)
    (omega₀ omega₁ : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) :
    MeasurableSet (ownerSymmDiff raw e₀ e₁ chi₀ chi₁ m omega₀ omega₁ J) := by
  dsimp [ownerSymmDiff]
  exact ((ownerUnion_measurable raw e₀ chi₀ m omega₀ J).diff
    (ownerUnion_measurable raw e₁ chi₁ m omega₁ J)).union
      ((ownerUnion_measurable raw e₁ chi₁ m omega₁ J).diff
        (ownerUnion_measurable raw e₀ chi₀ m omega₀ J))

theorem ownerSymmDiff_subset_raw (raw : FifthWireRow)
    (e₀ e₁ : ℚ) (chi₀ chi₁ : ℝ) (m : ℕ)
    (omega₀ omega₁ : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) :
    ownerSymmDiff raw e₀ e₁ chi₀ chi₁ m omega₀ omega₁ J ⊆ raw.originalBox := by
  intro t ht
  rcases ht with ht | ht
  · exact ownerUnion_subset_raw raw e₀ chi₀ m omega₀ J ht.1
  · exact ownerUnion_subset_raw raw e₁ chi₁ m omega₁ J ht.1

-- This is a standard Fubini bound. The fiber premise is genuinely
-- one-dimensional; it is not the desired five-dimensional volume bound.
theorem product_volume_le_of_fiber_bound
    (T : Set (ℝ × Base)) (B : Set Base) (L : ℝ)
    (hT : MeasurableSet T) (hB : MeasurableSet B)
    (hsupport : T ⊆ {p | p.2 ∈ B})
    (hfiber : ∀ y ∈ B,
      volume ((fun x : ℝ => (x, y)) ⁻¹' T) ≤ ENNReal.ofReal L) :
    (volume.prod volume) T ≤ ENNReal.ofReal L * volume B := by
  rw [Measure.prod_apply_symm hT]
  have hpoint (y : Base) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' T) ≤
        B.indicator (fun _ => ENNReal.ofReal L) y := by
    by_cases hy : y ∈ B
    · simpa [indicator_of_mem hy] using hfiber y hy
    · have hempty : ((fun x : ℝ => (x, y)) ⁻¹' T) = ∅ := by
        ext x
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro ht
        exact hy (hsupport ht)
      simp [hempty, indicator_of_notMem hy]
  calc
    ∫⁻ y, volume ((fun x : ℝ => (x, y)) ⁻¹' T) ∂volume ≤
        ∫⁻ y, B.indicator (fun _ => ENNReal.ofReal L) y ∂volume :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal L * volume B := by
      rw [lintegral_indicator hB]
      simp only [lintegral_const, Measure.restrict_apply_univ]

-- This binds the product Fubini lemma to the ACTUAL five-dimensional raw
-- box using the same measure-preserving equivalence as the Phase5 slab.
-- Its only quantitative premise is a one-dimensional fiber bound.
theorem raw_volume_le_of_fiber_bound (raw : FifthWireRow) (hg : raw.grid = 400)
    (S : Set Point) (L : ℝ) (hS : MeasurableSet S)
    (hraw : S ⊆ raw.originalBox)
    (hfiber : ∀ y ∈ baseBox raw,
      volume ((fun x : ℝ =>
        (x, y)) ⁻¹' ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin 5 => ℝ) (0 : Fin 5)).symm ⁻¹' S)) ≤ ENNReal.ofReal L) :
    volume S ≤ ENNReal.ofReal L * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (0 : Fin 5)
  let T : Set (ℝ × Base) := E.symm ⁻¹' S
  have hT : MeasurableSet T := hS.preimage E.symm.measurable
  have hsupp : T ⊆ {p | p.2 ∈ baseBox raw} := by
    intro p hp
    have hpraw : E.symm p ∈ raw.originalBox := hraw hp
    intro i _hi
    have hcoord : E.symm p ((0 : Fin 5).succAbove i) = p.2 i := by
      have heq := congrArg (fun z : ℝ × Base => z.2 i) (E.apply_symm_apply p)
      exact heq
    rw [← hcoord]
    exact ⟨(hpraw ((0 : Fin 5).succAbove i)).1,
      (hpraw ((0 : Fin 5).succAbove i)).2.le⟩
  have hvol : volume S = (volume.prod volume) T := by
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) (0 : Fin 5)
    calc
      volume S = (volume.map E) T := by
        rw [Measure.map_apply E.measurable hT]
        simp [T]
      _ = (volume.prod volume) T :=
        congrArg (fun μ => μ T) hmp.map_eq
  rw [hvol]
  have hf : ∀ y ∈ baseBox raw,
      volume ((fun x : ℝ => (x,y)) ⁻¹' T) ≤ ENNReal.ofReal L := hfiber
  calc
    (volume.prod volume) T ≤ ENNReal.ofReal L * volume (baseBox raw) :=
      product_volume_le_of_fiber_bound T (baseBox raw) L hT
        (baseBox_measurable raw) hsupp hf
    _ = ENNReal.ofReal L * (ENNReal.ofReal (1 / 400 : ℝ)) ^ 4 := by
      rw [baseBox_volume raw hg]

-- Remaining exact section lemma for S=ownerSymmDiff raw 0 e ... J:
-- for every y in baseBox raw, the fiber in raw_volume_le_of_fiber_bound
-- has measure <= ofReal((428/75)*(e:ℝ)). Its proof must use the literal
-- selectedFifthCells and firstStop=true guards, the Phase4 seven-gate
-- crossing inclusion, Phase8 Gamma VALUE rate, unique decoded Ico owner,
-- gamma_mesh_first_rise and the two section spans. No whole volume bound
-- is an input. This source does not assert that section lemma is proved.

end
end ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge
