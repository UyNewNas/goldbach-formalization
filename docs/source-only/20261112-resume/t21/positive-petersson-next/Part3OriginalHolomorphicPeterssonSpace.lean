import ImbalancedChen.Part3OriginalHolomorphicFiniteDimension
import ImbalancedChen.Part3Gamma0QuotientCoreRepresentativeFaithfulness
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

namespace ImbalancedChen.Part3.OriginalHolomorphicPeterssonSpace20261112

noncomputable section
open MeasureTheory Filter Set UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ModularForm ComplexConjugate InnerProductSpace
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicFiniteDimension20261112
open Gamma0FiniteMeasureCarrier20261024z Gamma0QuotientCellPushforward20261025a
open Gamma0QuotientCoreRepresentativeFaithfulness20261025a

abbrev Forms (N r : ℕ) := CuspForm (levelGroup N) (2*(r : ℤ))
abbrev carrierMeasure (N : ℕ) [NeZero N] : Measure ℍ := volume.restrict (gamma0Carrier N)

/-- The actual weight section on the chosen fundamental carrier. -/
def sectionValue {N r : ℕ} (f : Forms N r) (w : ℍ) : ℂ := (w.im : ℂ)^r * f w

theorem section_continuous {N r : ℕ} (f : Forms N r) : Continuous (sectionValue f) :=
  ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow _).mul
    (ModularFormClass.holo f).continuous

theorem section_bound {N r : ℕ} [NeZero N] (f : Forms N r) :
    ∃ C : ℝ, ∀ w, ‖sectionValue f w‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun w => ?_⟩
  have he : (((2*(r : ℤ) : ℤ) : ℝ)/2) = (r : ℝ) := by push_cast; ring
  have h := hC w
  rw [he, Real.rpow_natCast, le_div_iff₀ (pow_pos w.im_pos _)] at h
  simpa [sectionValue, norm_mul, norm_pow, Real.norm_of_nonneg w.im_pos.le, mul_comm] using h

theorem section_memLp {N r : ℕ} [NeZero N] (f : Forms N r) :
    MemLp (sectionValue f) 2 (carrierMeasure N) := by
  letI : IsFiniteMeasure (carrierMeasure N) :=
    ⟨by simpa [carrierMeasure] using gamma0Carrier_finite N⟩
  obtain ⟨C,hC⟩ := section_bound f
  exact MemLp.of_bound (section_continuous f).aestronglyMeasurable C (.of_forall hC)

def sectionMap (N r : ℕ) [NeZero N] : Forms N r →ₗ[ℂ] Lp ℂ 2 (carrierMeasure N) where
  toFun f := (section_memLp f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(section_memLp (f+g)).coeFn_toLp,
      Lp.coeFn_add ((section_memLp f).toLp _) ((section_memLp g).toLp _),
      (section_memLp f).coeFn_toLp, (section_memLp g).coeFn_toLp] with w h hfg hf hg
    simpa [h, hfg, Pi.add_apply, hf, hg, sectionValue, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(section_memLp (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((section_memLp f).toLp _), (section_memLp f).coeFn_toLp] with w h hcf hf
    simp [h, hcf, Pi.smul_apply, hf, sectionValue, mul_left_comm]

def quotientSquare {N r : ℕ} (f : Forms N r) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (petersson (2*(r : ℤ)) f f) (by
    intro x y h
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    rw [← hg]
    exact SlashInvariantFormClass.petersson_smul
      (show Matrix.SpecialLinearGroup.mapGL ℝ (g.val) ∈ levelGroup N from
        Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩))

theorem section_inner {N r : ℕ} (f g : Forms N r) (w : ℍ) :
    inner ℂ (sectionValue f w) (sectionValue g w) = petersson (2*(r : ℤ)) f g w := by
  rw [show 2*(r : ℤ) = ((r+r : ℕ) : ℤ) by omega]
  simp only [sectionValue, RCLike.inner_apply, petersson, zpow_natCast, map_mul, map_pow,
    Complex.conj_ofReal, pow_add]
  ring

theorem section_injective (N r : ℕ) [NeZero N] : Function.Injective (sectionMap N r) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hz : (section_memLp f).toLp _ = 0 := hf
  have hsec := (section_memLp f).coeFn_toLp.symm
  rw [hz] at hsec
  have h0 := hsec.trans (Lp.coeFn_zero ℂ 2 (carrierMeasure N))
  have hc : Continuous (petersson (2*(r : ℤ)) f f) :=
    petersson_continuous _ (ModularFormClass.holo f).continuous (ModularFormClass.holo f).continuous
  have hq : quotientSquare f =ᵐ[carrierPushforward N] (fun _ => (0:ℂ)) := by
    apply (ae_map_iff (orbitProjection_measurable N).aemeasurable ?_).mpr
    · filter_upwards [h0] with w hw
      change petersson (2*(r : ℤ)) f f w = 0
      rw [← section_inner]
      change sectionValue f w = 0 at hw
      simp [hw]
    · apply measurableSet_quotient.mpr
      exact measurableSet_eq_fun hc.measurable measurable_const
  have hid := quotient_ae_continuous_pullback_eq N hq hc continuous_const
  ext w
  have h : inner ℂ (sectionValue f w) (sectionValue f w) = 0 :=
    (section_inner f f w).trans (congrFun hid w)
  have hw := inner_self_eq_zero.mp h
  exact (mul_eq_zero.mp hw).resolve_left
    (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr w.im_ne_zero))

def peterssonNorm (N r : ℕ) [NeZero N] : NormedAddCommGroup (Forms N r) :=
  NormedAddCommGroup.induced (Forms N r) _ (sectionMap N r) (section_injective N r)

scoped instance (N r : ℕ) [NeZero N] : NormedAddCommGroup (Forms N r) := peterssonNorm N r

open scoped OriginalHolomorphicPeterssonSpace20261112

scoped instance (N r : ℕ) [NeZero N] : InnerProductSpace ℂ (Forms N r) :=
  InnerProductSpace.induced (sectionMap N r)

scoped instance (N r : ℕ) [NeZero N] : FiniteDimensional ℂ (Forms N r) :=
  finite_forms N _

/-- Petersson inner product with the unscaled canonical hyperbolic volume. -/
theorem inner_integral (N r : ℕ) [NeZero N] (f g : Forms N r) :
    inner ℂ f g = ∫ w in gamma0Carrier N, petersson (2*(r : ℤ)) f g w := by
  change inner ℂ (sectionMap N r f) (sectionMap N r g) = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(section_memLp f).coeFn_toLp, (section_memLp g).coeFn_toLp] with w hf hg
  change inner ℂ ((section_memLp f).toLp _ w) ((section_memLp g).toLp _ w) = _
  rw [hf,hg,section_inner]

abbrev BasisIndex (N r : ℕ) [NeZero N] := Fin (Module.finrank ℂ (Forms N r))

def formsBasis (N r : ℕ) [NeZero N] : OrthonormalBasis (BasisIndex N r) ℂ (Forms N r) :=
  stdOrthonormalBasis ℂ (Forms N r)

theorem basis_integral (N r : ℕ) [NeZero N] (i j : BasisIndex N r) :
    (∫ w in gamma0Carrier N, petersson (2*(r : ℤ)) (formsBasis N r i) (formsBasis N r j) w) =
      if i=j then 1 else 0 := by
  rw [← inner_integral]
  exact orthonormal_iff_ite.mp (formsBasis N r).orthonormal i j

theorem basis_complete (N r : ℕ) [NeZero N] (f : Forms N r) :
    ∑ i, inner ℂ (formsBasis N r i) f • formsBasis N r i = f :=
  (formsBasis N r).sum_repr' f

end
end ImbalancedChen.Part3.OriginalHolomorphicPeterssonSpace20261112
