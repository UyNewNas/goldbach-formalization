import ImbalancedChen.Part3Gamma0ParabolicCosetRows
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The literal half-open strip 0 <= Re(z) < 1 is an exact transversal for the
ACTUAL GammaInfinity(N) action on H. All its integral translates are
pairwise disjoint, canonically measure-preserving, and tile all of H.
The actual parabolic subgroup includes +/-T^k; its central sign acts
trivially and is not counted twice. The quotient measure is the pushforward
of canonical hyperbolic volume restricted to this exact strip.

Periodic measurable functions descend to the true parabolic orbit quotient.
Their quotient integrals are their strip integrals; complex L1 requires
only strip integrability here, never integrability of a periodic seed on H.
This infinite-height strip measure is not asserted finite.
-/

namespace ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a

/-- Actual determinant-one integral translation by k. -/
def translate (k : ℤ) (z : UpperHalfPlane) : UpperHalfPlane := ModularGroup.T ^ k • z

theorem translate_eq_vadd (k : ℤ) (z : UpperHalfPlane) :
    translate k z = (k : ℝ) +ᵥ z := UpperHalfPlane.modular_T_zpow_smul z k

@[simp] theorem translate_zero (z : UpperHalfPlane) : translate 0 z = z := by
  simp [translate]

theorem translate_add (j k : ℤ) (z : UpperHalfPlane) :
    translate (j + k) z = translate j (translate k z) := by
  simp [translate, zpow_add, mul_smul]

@[simp] theorem translate_re (k : ℤ) (z : UpperHalfPlane) :
    (translate k z).re = (k : ℝ) + z.re := by
  rw [translate_eq_vadd, UpperHalfPlane.vadd_re]

/-- The full positive-height, half-open width-one strip. -/
def strip : Set UpperHalfPlane := {z | z.re ∈ Ico (0 : ℝ) 1}

theorem strip_measurable : MeasurableSet strip :=
  UpperHalfPlane.continuous_re.measurable measurableSet_Ico

def stripCell (k : ℤ) : Set UpperHalfPlane := translate k '' strip

theorem translate_measurePreserving (k : ℤ) :
    MeasurePreserving (translate k) (volume : Measure UpperHalfPlane)
      (volume : Measure UpperHalfPlane) := by
  change MeasurePreserving (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ k)) • z) _ _
  exact measurePreserving_smul _ _

theorem translate_measurableEmbedding (k : ℤ) : MeasurableEmbedding (translate k) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ k)) • z)
  exact (MeasurableEquiv.smul _).measurableEmbedding

theorem stripCell_measurable (k : ℤ) : MeasurableSet (stripCell k) :=
  (translate_measurableEmbedding k).measurableSet_image.mpr strip_measurable

/-- This unique integer shift uses the genuine half-open real interval. -/
theorem unique_horizontal_period (z : UpperHalfPlane) :
    ∃! k : ℤ, z.re - (k : ℝ) ∈ Ico (0 : ℝ) 1 := by
  simpa only [zsmul_eq_mul, zero_add, mul_one] using
    existsUnique_sub_zsmul_mem_Ico (show (0 : ℝ) < 1 by norm_num) z.re (0 : ℝ)

theorem mem_stripCell_iff (k : ℤ) (z : UpperHalfPlane) :
    z ∈ stripCell k ↔ z.re - (k : ℝ) ∈ Ico (0 : ℝ) 1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [translate_re, add_sub_cancel_left] using hw
  · intro hz
    refine ⟨translate (-k) z, ?_, ?_⟩
    · simpa only [strip, mem_setOf_eq, translate_re, Int.cast_neg, neg_add_eq_sub] using hz
    · rw [← translate_add]
      simp

theorem stripCell_pairwise_disjoint : Pairwise (Disjoint on stripCell) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro z hzj hzk
  obtain ⟨n, _hn, hunique⟩ := unique_horizontal_period z
  exact hjk ((hunique j ((mem_stripCell_iff j z).mp hzj)).trans
    (hunique k ((mem_stripCell_iff k z).mp hzk)).symm)

/-- A genuine all-H disjoint tiling; no hTiling field occurs. -/
theorem iUnion_stripCell : (⋃ k : ℤ, stripCell k) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨k, hk, _⟩ := unique_horizontal_period z
  exact mem_iUnion.mpr ⟨k, (mem_stripCell_iff k z).mpr hk⟩

/-- The actual translation element inside the actual parabolic subgroup. -/
def infinityTranslation (N : ℕ) (k : ℤ) : gammaInfinity N :=
  ⟨⟨ModularGroup.T ^ k, translation_mem_gamma0 N k⟩, by
    change (ModularGroup.T ^ k) 1 0 = 0
    simp [ModularGroup.coe_T_zpow]⟩

/-- Every actual parabolic matrix acts as one integer translation; the
negative matrix has the identical action, so no factor two is introduced. -/
theorem parabolic_action_integer (N : ℕ) (γ : gammaInfinity N) :
    ∃ k : ℤ, ∀ z : UpperHalfPlane, γ • z = translate k z := by
  obtain ⟨k, hk | hk⟩ := (gammaInfinity_mem_iff N γ.val).mp γ.property
  · refine ⟨k, ?_⟩
    intro z
    change ((γ.val : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z = _
    rw [hk]
    rfl
  · refine ⟨k, ?_⟩
    intro z
    change ((γ.val : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • z = _
    rw [hk, UpperHalfPlane.SL_neg_smul]
    rfl

abbrev InfinityOrbitSpace (N : ℕ) :=
  Quotient (MulAction.orbitRel (gammaInfinity N) UpperHalfPlane)

def infinityProjection (N : ℕ) : UpperHalfPlane → InfinityOrbitSpace N := Quotient.mk''

theorem infinityProjection_measurable (N : ℕ) : Measurable (infinityProjection N) :=
  measurable_quotient_mk''

@[simp] theorem infinityProjection_translate (N : ℕ) (k : ℤ) (z : UpperHalfPlane) :
    infinityProjection N (translate k z) = infinityProjection N z := by
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨infinityTranslation N k, rfl⟩

/-- Every actual parabolic orbit has a representative in the literal strip. -/
theorem infinityProjection_strip_surjective (N : ℕ) (q : InfinityOrbitSpace N) :
    ∃ z ∈ strip, infinityProjection N z = q := by
  refine Quotient.inductionOn q (fun z => ?_)
  obtain ⟨k, hk, _⟩ := unique_horizontal_period z
  refine ⟨translate (-k) z, ?_, infinityProjection_translate N (-k) z⟩
  simpa only [strip, mem_setOf_eq, translate_re, Int.cast_neg, neg_add_eq_sub] using hk

/-- No two different strip points represent the same true parabolic orbit. -/
theorem infinityProjection_injOn_strip (N : ℕ) : InjOn (infinityProjection N) strip := by
  intro z hz w hw hq
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
  obtain ⟨k, hk⟩ := parabolic_action_integer N γ
  have htrans : translate k w = z := (hk w).symm.trans hγ
  have hkcell : z ∈ stripCell k := ⟨w, hw, htrans⟩
  obtain ⟨n, _hn, hunique⟩ := unique_horizontal_period z
  have hzero : z.re - ((0 : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa using hz
  have hkzero : k = 0 := ((hunique k ((mem_stripCell_iff k z).mp hkcell)).trans
    (hunique 0 hzero).symm)
  rw [hkzero, translate_zero] at htrans
  exact htrans.symm

/-- Canonical quotient measure from the actual exact translation strip.
Its full height range is not asserted to have finite mass. -/
def infinityQuotientMeasure (N : ℕ) : Measure (InfinityOrbitSpace N) :=
  ((volume : Measure UpperHalfPlane).restrict strip).map (infinityProjection N)

/-- A genuinely periodic seed descends without any integrability on H. -/
def periodicLift {A : Type*} (N : ℕ) (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) : InfinityOrbitSpace N → A :=
  Quotient.lift F (by
    intro z w hzw
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp hzw
    obtain ⟨k, hk⟩ := parabolic_action_integer N γ
    calc
      F z = F (γ • w) := congrArg F hγ.symm
      _ = F (translate k w) := congrArg F (hk w)
      _ = F w := hperiod k w)

@[simp] theorem periodicLift_projection {A : Type*} (N : ℕ) (F : UpperHalfPlane → A)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (z : UpperHalfPlane) :
    periodicLift N F hperiod (infinityProjection N z) = F z := rfl

theorem periodicLift_measurable {A : Type*} [MeasurableSpace A] (N : ℕ)
    (F : UpperHalfPlane → A) (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) : Measurable (periodicLift N F hperiod) := by
  apply measurable_from_quotient.mpr
  exact hF

theorem lintegral_periodicLift (N : ℕ) (F : UpperHalfPlane → ℝ≥0∞)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z) (hF : Measurable F) :
    (∫⁻ q, periodicLift N F hperiod q ∂infinityQuotientMeasure N) =
      ∫⁻ z in strip, F z :=
  lintegral_map (periodicLift_measurable N F hperiod hF) (infinityProjection_measurable N)

/-- Strip integrability is the exact analytic premise for a periodic
complex seed on the parabolic quotient, with no H-L1 substitution. -/
theorem periodicLift_integrable (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    Integrable (periodicLift N F hperiod) (infinityQuotientMeasure N) :=
  (integrable_map_measure (periodicLift_measurable N F hperiod hF).aestronglyMeasurable
    (infinityProjection_measurable N).aemeasurable).mpr hstrip

theorem integral_periodicLift (N : ℕ) (F : UpperHalfPlane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ z, F (translate k z) = F z)
    (hF : Measurable F) (hstrip : IntegrableOn F strip) :
    (∫ q, periodicLift N F hperiod q ∂infinityQuotientMeasure N) =
      ∫ z in strip, F z :=
  integral_map (infinityProjection_measurable N).aemeasurable
    (periodicLift_measurable N F hperiod hF).aestronglyMeasurable

end
end ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a

