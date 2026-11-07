import ImbalancedChen.Part3Gamma0FiniteCarrierExactMeasure
import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import ImbalancedChen.Part3Gamma0ActualParabolicUnfolding
import ImbalancedChen.Part3ActualInfinityKloostermanSeed
import ImbalancedChen.Part3MaassWeakOperatorCore
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Fourier.AddCircle

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The genuine constant mode in the actual finite-volume Gamma0 quotient L2.
The original quotient pushforward has positive finite mass, equal to the
actual subgroup index times the actual modular fundamental-domain volume.
The constant function belongs to L2, is nonzero, and has squared norm equal
to that physical quotient volume.

The strip integral of a nonzero integer Fourier-radial seed vanishes by
the actual H-to-chart measure formula and product integration. Combining
this with genuine GammaInfinity\Gamma0 unfolding proves the actual quotient
parabolic series has integral zero. No arbitrary Fourier/spectral label is
declared orthogonal. Membership of the constant in the energy form domain,
and a Laplacian-kernel assertion, require genuine cusp cutoffs and are NOT
claimed here.
-/

namespace ImbalancedChen.Part3.Gamma0ActualConstantMode20261025a

noncomputable section
open Set MeasureTheory
open scoped ENNReal UpperHalfPlane
open Gamma0FiniteMeasureCarrier20261024z Gamma0FiniteCarrierExactMeasure20261024zz
open ModularFundamentalFiniteMeasure20261024z Gamma0QuotientCellPushforward20261025a
open GammaInfinityTranslationStrip20261025a Gamma0ActualParabolicUnfolding20261025a
open ActualInfinityKloostermanSeed20261025a
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeakOperatorCore20261024zz

local instance periodOne_pos : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

abbrev QuotientL2 (N : ℕ) [NeZero N] := Lp ℂ 2 (carrierPushforward N)

theorem quotient_mass_exact (N : ℕ) [NeZero N] :
    carrierPushforward N univ=((CongruenceSubgroup.Gamma0 N).index:ℝ≥0∞)*
      (volume : Measure UpperHalfPlane) modularFD := by
  rw [carrierPushforward,cellPushforward_univ,gamma0Carrier_measure_eq_index]

theorem quotient_mass_pos (N : ℕ) [NeZero N] : 0<carrierPushforward N univ := by
  have hi : 0<(CongruenceSubgroup.Gamma0 N).index :=
    Nat.pos_of_ne_zero (CongruenceSubgroup.Gamma0 N).index_ne_zero_of_finite
  have hiE : (0:ℝ≥0∞)<((CongruenceSubgroup.Gamma0 N).index:ℝ≥0∞) := by exact_mod_cast hi
  rw [quotient_mass_exact]
  exact mul_pos hiE modularFD_pos

def actualVolume (N : ℕ) [NeZero N] : ℝ := (carrierPushforward N).real univ

theorem actualVolume_pos (N : ℕ) [NeZero N] : 0<actualVolume N :=
  ENNReal.toReal_pos (quotient_mass_pos N).ne' (carrierPushforward_finite N).ne

local instance quotientFiniteMeasure (N : ℕ) [NeZero N] : IsFiniteMeasure (carrierPushforward N) where
  measure_univ_lt_top := carrierPushforward_finite N

theorem constant_memLp_two (N : ℕ) [NeZero N] :
    MemLp (fun _ : Gamma0OrbitSpace N => (1:ℂ)) 2 (carrierPushforward N) := memLp_const 1

/-- The literal constant one, represented canonically in the actual L2. -/
def constantL2 (N : ℕ) [NeZero N] : QuotientL2 N :=
  indicatorConstLp 2 measurableSet_univ (carrierPushforward_finite N).ne (1:ℂ)

theorem constantL2_ae (N : ℕ) [NeZero N] :
    (constantL2 N : Gamma0OrbitSpace N → ℂ)=ᵐ[carrierPushforward N] (fun _ => 1) := by
  simpa only [constantL2,Set.indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (μ := carrierPushforward N)
      (s := Set.univ) (c := (1:ℂ)) (hs := measurableSet_univ)
      (hμs := (carrierPushforward_finite N).ne))

theorem constantL2_eq_toLp (N : ℕ) [NeZero N] :
    constantL2 N=(constant_memLp_two N).toLp (fun _ => (1:ℂ)) :=
  Lp.ext ((constantL2_ae N).trans (constant_memLp_two N).coeFn_toLp.symm)

theorem constantL2_inner (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    inner ℂ (constantL2 N) f=∫ q,f q ∂carrierPushforward N := by
  simpa only [constantL2,Measure.restrict_univ] using
    (L2.inner_indicatorConstLp_one measurableSet_univ (carrierPushforward_finite N).ne f)

theorem constantL2_inner_self (N : ℕ) [NeZero N] :
    inner ℂ (constantL2 N) (constantL2 N)=(actualVolume N:ℂ) := by
  simpa only [constantL2,Set.univ_inter,actualVolume] using
    (L2.inner_indicatorConstLp_one_indicatorConstLp_one (𝕜 := ℂ)
      (μ := carrierPushforward N) measurableSet_univ measurableSet_univ
      (carrierPushforward_finite N).ne (carrierPushforward_finite N).ne)

theorem constantL2_norm_sq (N : ℕ) [NeZero N] : ‖constantL2 N‖^2=actualVolume N := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),constantL2_inner_self,Complex.ofReal_re]

theorem constantL2_ne_zero (N : ℕ) [NeZero N] : constantL2 N≠0 := by
  intro hz
  have hpos := actualVolume_pos N
  rw [← constantL2_norm_sq N,hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] at hpos
  exact (lt_irrefl (0:ℝ)) hpos

private theorem phase_integral_zero (m : ℤ) (hm : m≠0) :
    (∫ x in Ico (0:ℝ) 1,AddCircle.fourier m (x:UnitAddCircle))=0 := by
  have hz : AddCircle.fourierCoeff (AddCircle.fourier (T := (1:ℝ)) m) 0=0 := by
    simpa [Pi.single_apply,hm,Ne.symm hm] using
      congrFun (AddCircle.fourierCoeff_fourier (T := (1:ℝ)) m) 0
  have hi := AddCircle.fourierCoeff_eq_intervalIntegral
    (AddCircle.fourier (T := (1:ℝ)) m) 0 (0:ℝ)
  have hint : (∫ x in (0:ℝ)..1,AddCircle.fourier m (x:UnitAddCircle))=0 := by
    simpa only [hz,neg_zero,AddCircle.fourier_zero,one_smul,zero_add,
      one_div_one] using hi.symm
  calc
    (∫ x in Ico (0:ℝ) 1,AddCircle.fourier m (x:UnitAddCircle))=
        ∫ x in Ioc (0:ℝ) 1,AddCircle.fourier m (x:UnitAddCircle) := integral_Ico_eq_integral_Ioc
    _ = ∫ x in (0:ℝ)..1,AddCircle.fourier m (x:UnitAddCircle) :=
      (intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)).symm
    _ = 0 := hint

/-- This is the literal hyperbolic strip integral of the genuine radial
seed. The x character integral vanishes before any quotient series claim. -/
theorem fourierRadialSeed_strip_integral_zero (m : ℤ) (hm : m≠0) (ψ : ℝ → ℂ) :
    (∫ z in strip,fourierRadialSeed m ψ z)=0 := by
  let a : ℝ → ℂ := (Ico (0:ℝ) 1).indicator (fun x => AddCircle.fourier m (x:UnitAddCircle))
  let F : ℝ × ℝ → ℂ := fun p => a p.1*ψ p.2
  let b : ℝ → ℂ := fun y => ((chartWeight (0,y):ℝ):ℂ)*ψ y
  have hind (z : UpperHalfPlane) :
      strip.indicator (fourierRadialSeed m ψ) z=F (Complex.measurableEquivRealProd (z:ℂ)) := by
    change strip.indicator (fourierRadialSeed m ψ) z=a z.re*ψ z.im
    by_cases hx : z.re∈Ico (0:ℝ) 1 <;> simp [strip,a,hx,fourierRadialSeed]
  have hupper : upperChart=(Set.univ : Set ℝ) ×ˢ Ioi (0:ℝ) := by ext p; simp [upperChart]
  have ha : (∫ x : ℝ,a x)=0 := by
    rw [a,integral_indicator measurableSet_Ico]
    exact phase_integral_zero m hm
  calc
    (∫ z in strip,fourierRadialSeed m ψ z)=
        ∫ z : UpperHalfPlane,strip.indicator (fourierRadialSeed m ψ) z :=
      (integral_indicator strip_measurable).symm
    _ = ∫ z : UpperHalfPlane,F (Complex.measurableEquivRealProd (z:ℂ)) :=
      integral_congr_ae (Filter.Eventually.of_forall hind)
    _ = ∫ p : ℝ × ℝ,F p ∂chartMeasure := canonical_integral_eq_chart_integral F
    _ = ∫ p : ℝ × ℝ,a p.1*b p.2
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi (0:ℝ)))) := by
      rw [chartMeasure,integral_withDensity_eq_integral_smul chartWeight_measurable,
        hupper,Measure.volume_eq_prod,← Measure.prod_restrict,Measure.restrict_univ]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      dsimp [F,b]
      simp only [NNReal.smul_def,Complex.real_smul]
      change ((chartWeight p:ℝ):ℂ)*(a p.1*ψ p.2)=
        a p.1*(((chartWeight (0,p.2):ℝ):ℂ)*ψ p.2)
      change (((p.2⁻¹)^2:ℝ):ℂ)*(a p.1*ψ p.2)=
        a p.1*((((p.2⁻¹)^2:ℝ):ℂ)*ψ p.2)
      ring
    _ = (∫ x : ℝ,a x)*(∫ y in Ioi (0:ℝ),b y) := integral_prod_mul a b
    _ = 0 := by rw [ha,zero_mul]

/-- Actual parabolic unfolding turns the computed strip integral into the
zero quotient mean of the actual GammaInfinity\Gamma0 series. The explicit
inputs are primitive strip-integrability/periodicity, not orthogonality. -/
theorem parabolic_fourier_mean_zero (N : ℕ) [NeZero N]
    (m : ℤ) (hm : m≠0) (ψ : ℝ → ℂ)
    (hperiod : ∀ k : ℤ,∀ z,fourierRadialSeed m ψ (translate k z)=fourierRadialSeed m ψ z)
    (hF : Measurable (fourierRadialSeed m ψ))
    (hstrip : IntegrableOn (fourierRadialSeed m ψ) strip) :
    (∫ q,parabolicComplexPoincare N (fourierRadialSeed m ψ) q ∂carrierPushforward N)=0 := by
  rw [complex_parabolic_quotient_unfolding N _ hperiod hF hstrip]
  exact fourierRadialSeed_strip_integral_zero m hm ψ

end
end ImbalancedChen.Part3.Gamma0ActualConstantMode20261025a
