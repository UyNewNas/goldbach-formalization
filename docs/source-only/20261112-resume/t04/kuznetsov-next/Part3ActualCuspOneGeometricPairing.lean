import ImbalancedChen.Part3ActualContinuousPoincarePairing
import ImbalancedChen.Part3ActualFrickeQuotientMeasure
import ImbalancedChen.Part3InfinityZeroActualQuotientL2
import ImbalancedChen.Part3OriginalNonzeroCuspOneSource
import ImbalancedChen.Part3KloostermanConjugation
import Batteries.Tactic.OpenPrivate

/-! The geometric pairing in the manuscript's oriented infinity/one
frames, including the level-one diagonal and the signed second index. -/
namespace ImbalancedChen.Part3.ActualCuspOneGeometricPairing20261112

noncomputable section
open Set Filter MeasureTheory Matrix Complex UpperHalfPlane AddCircle
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualContinuousPoincarePairing20261110 ActualFrickeCuspPhase20261025a
open ActualFrickeQuotientMeasure20261026b FrickeNormalizer
open Gamma0ActualCuspsSourceOnly Gamma0GeneralCuspWidth20261025a
open Gamma0GeneralCuspUnitPeriod20261025a ActualCuspFourierSectionSourceOnly
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0ActualParabolicUnfolding20261025a Gamma0ParabolicCosetRows20261025a
open ActualPoincareSpectralCoefficient20261026a NormalizedCuspCompactPoincare20261026b
open NormalizedCuspCompactFourierFubini20261026b NormalizedCuspCompactQuotientLp20261026b
open InfinityZeroActualQuotientGeometricAssembly20261026b InfinityZeroActualQuotientL220261026b
open InfinityZeroActualFiberGeometricPair20261026a InfinityZeroArithmetic20261025a
open InfinityZeroActualFiniteGeometricAssembly20261026b ActualCompactBruhatAllModuli20261025a
open ActualCompactBruhatKernel20261025a CompactCuspFiniteGeometricIntegral20261025a
open CompactCuspParabolicL220261025a CompactCuspQuotientGeometricPairing20261025a
open ActualInfinityKloostermanSeed20261025a CompactCuspGeometricFubini20261025a
open OriginalNonzeroCuspOneSource20261102 OriginalSmoothPoissonTail KloostermanConjugation
open P3Period64NativeReconstructionSourceOnly (e)
open private scaling_infty from ImbalancedChen.Part3ActualContinuousPoincarePairing

private theorem frame_modes (N : ℕ) [NeZero N] (F : Gamma0OrbitSpace N → ℂ) (n : ℤ)
    {y : ℝ} (hy : 0<y) :
    frameFourier N (NeZero.pos N) cuspOneMatrix F n y =
      e ((n : ℝ)/(N : ℝ)) *
        frameFourier N (NeZero.pos N) 1 (F ∘ quotientFricke N (NeZero.pos N)) n y := by
  let hN := NeZero.pos N
  let L := fun z : ℍ => F (orbitProjection N z)
  have hL (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) : L (g • z)=L z :=
    congrArg F (orbitProjection_smul N ⟨g,hg⟩ z)
  have point (x : ℝ) : (⟨⟨x,y⟩,hy⟩ : ℍ)=horizontal y hy x := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [horizontal]
  have one : frameFourier N hN cuspOneMatrix F n y = fourierCoeff (sigmaOneSection N hN L hL y hy) n := by
    rw [frameFourier_positive_height N hN _ _ n hy,integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
    simp only [div_one,one_smul,zero_add,smul_eq_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change fourier (-n) (x : UnitAddCircle) * F (orbitProjection N (normalizedScaling N hN cuspOneMatrix • _)) =
      fourier (-n) (x : UnitAddCircle) * F (orbitProjection N (normalizedScaling N hN cuspOneMatrix • horizontal y hy x))
    rw [point]
  have zero : frameFourier N hN 1 (F ∘ quotientFricke N hN) n y = frickeFourierCoeff N hN L hL y hy n := by
    rw [frameFourier_positive_height N hN _ _ n hy,integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,frickeFourierCoeff,fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
    simp only [div_one,one_smul,zero_add,smul_eq_mul,frameAction,scaling_infty,Function.comp_apply,
      quotientFricke_projection]
    apply intervalIntegral.integral_congr
    intro x _
    change fourier (-n) (x : UnitAddCircle) * F (orbitProjection N (frickeSL N hN • _)) =
      fourier (-n) (x : UnitAddCircle) * F (orbitProjection N (frickeSL N hN • horizontal y hy x))
    rw [point]
  rw [one,zero,sigmaOne_fourierCoeff_fricke_phase]
  congr 1
  unfold e
  push_cast
  congr 1
  ring

private theorem fricke_measure (N : ℕ) [NeZero N] :
    MeasurePreserving (quotientFricke N (NeZero.pos N)) (carrierPushforward N) (carrierPushforward N) :=
  ⟨quotientFricke_measurable _ _,quotientFricke_map_measure _ _⟩

private theorem pulled_infinity (N : ℕ) [NeZero N] (n : ℤ) (φ : ℝ → ℂ)
    (hc : HasCompactSupport φ) (hp : tsupport φ ⊆ Ioi (0 : ℝ)) :
    originalPoincare N false n φ ∘ quotientFricke N (NeZero.pos N) =ᵐ[carrierPushforward N]
      zeroCuspPoincare N (NeZero.pos N) n φ hc hp := by
  let W := quotientFricke N (NeZero.pos N)
  let Z := zeroCuspPoincare N (NeZero.pos N) n φ hc hp
  have H : originalPoincare N false n φ =ᵐ[carrierPushforward N] Z ∘ W := by
    filter_upwards [reducedProjection_range_ae N] with q hq
    obtain ⟨z,rfl⟩ := hq
    change parabolicComplexPoincare N (fourierRadialSeed n φ) (reducedProjection N z) =
      Z (quotientFricke N (NeZero.pos N) (orbitProjection N z))
    rw [parabolicComplexPoincare_projection,quotientFricke_projection]
    simp only [Z,zeroCuspPoincare_orbitProjection,zeroChartTrace,zeroSL_eq_frickeSL,
      frickeSL_action_involutive,actualCompactPoincare_eq_parabolicTrace]
  filter_upwards [(fricke_measure N).quasiMeasurePreserving.ae_eq_comp H] with q hq
  exact hq.trans (congrArg Z (quotientFricke_involutive N (NeZero.pos N) q))

/-- This chart identity is tested against an arbitrary actual spatial
`L²` function. Its phase appears in the conjugate-linear vector. -/
theorem one_zero_pair (N : ℕ) [NeZero N] (n : ℤ) (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hp : tsupport φ ⊆ Ioi (0 : ℝ))
    (F : Gamma0OrbitSpace N → ℂ) (hF : MemLp F 2 (carrierPushforward N)) :
    (∫ q, star (originalPoincare N true n φ q)*F q ∂carrierPushforward N) =
      e ((n : ℝ)/(N : ℝ)) * ∫ q, star (zeroCuspPoincare N (NeZero.pos N) n φ hc hp q)*F q ∂carrierPushforward N := by
  let hN := NeZero.pos N
  let W := quotientFricke N hN
  let E : Gamma0OrbitSpace N ≃ᵐ Gamma0OrbitSpace N :=
    { toEquiv := (quotientFricke_involutive N hN).toPerm W
      measurable_toFun := quotientFricke_measurable N hN
      measurable_invFun := quotientFricke_measurable N hN }
  have hW : MeasurePreserving E (carrierPushforward N) (carrierPushforward N) := fricke_measure N
  have A := framePoincare_pairing_eq_fourier N hN cuspOneMatrix n φ hφ hc hp F hF
  have B := framePoincare_pairing_eq_fourier N hN 1 n φ hφ hc hp (F ∘ W) (hF.comp_measurePreserving hW)
  have HB := original_eq_framed N false n φ hc hp
  change originalPoincare N false n φ = _ at HB
  let P := originalPoincare N false n φ
  have changeW : (∫ q,star (P q)*(F ∘ W) q ∂carrierPushforward N) =
      ∫ q,star (zeroCuspPoincare N hN n φ hc hp q)*F q ∂carrierPushforward N := by
    rw [← hW.integral_comp' (fun q => star (P q)*(F ∘ W) q)]
    apply integral_congr_ae
    filter_upwards [pulled_infinity N n φ hc hp] with q hq
    change star (P (W q))*F (W (W q)) = _
    rw [quotientFricke_involutive N hN q,show P (W q)=_ from hq]
  calc
    _ = _ := A
    _ = e ((n : ℝ)/(N : ℝ)) * ∫ y in Ioi (0 : ℝ), ((y⁻¹)^2 : ℝ) •
        (star (φ y)*frameFourier N hN 1 (F ∘ W) n y) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      rw [frame_modes N F n hy]
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [← B,← HB]
      exact congrArg (fun z => e ((n : ℝ)/(N : ℝ))*z) changeW

def sourceDiagonal (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) : ℂ :=
  e ((n : ℝ)/(N : ℝ))*star (if N=1 ∧ m=n then ∫ y : ℝ,radialWeight ψ y*φ y else 0)

def sourceOrbit (N : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (d : ℕ+) : ℂ :=
  (if hd : N.Coprime (d : ℕ) then cuspOneMatrixSum N d hd m n else 0) *
    star (∫ x : ℝ,∫ y : ℝ,mixedOrbitKernel N d m n ψ φ (x,y))

/-- The complete positive-modulus series in the original orientation.
Compact height support supplies a common physical cutoff for the
denominator fibers before the horizontal and vertical integrations. -/
theorem signed_geometric_pair (N : ℕ) [NeZero N] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Summable (sourceOrbit N m n ψ φ) ∧
      (∫ q,star (originalPoincare N true n φ q)*originalPoincare N false m ψ q ∂carrierPushforward N) =
        sourceDiagonal N m n ψ φ + ∑' d : ℕ+,sourceOrbit N m n ψ φ d := by
  classical
  let hN := NeZero.pos N
  let E := e ((n : ℝ)/(N : ℝ))
  let R := fun d : ℕ+ => ∫ y,mixedFiberPairSlice N hN d m n ψ φ y
  have orient (d : ℕ+) : E*star (R d)=sourceOrbit N m n ψ φ d := by
    dsimp only [R,sourceOrbit]
    rw [integrated_actualMixedFiber_eq_geometric N hN d m n ψ φ hψ hcψ hpψ hφ hcφ hpφ]
    by_cases hd : N.Coprime (d : ℕ)
    · rw [if_pos hd,dif_pos hd,star_mul,star_kloosterman_eq,
        show -m*inverseResidue d (N : ℤ) = -(m*inverseResidue d (N : ℤ)) by ring,
        ActualReciprocalSquarePoissonSourceOnly.kloosterman_both_negative,
        cuspOneMatrixSum_eq_phase_mul_kloosterman N d hN hd m n]
      dsimp only [E]
      ring
    · simp only [if_neg hd,dif_neg hd,zero_mul,star_zero,mul_zero]
  obtain ⟨a,ha,hfloorφ⟩ := radial_support_positive_floor φ hcφ hpφ
  obtain ⟨b,hb,hfloorψ⟩ := radial_support_positive_floor ψ hcψ hpψ
  obtain ⟨C,hC⟩ := exists_positive_modulus_cutoff a b ha hb
  let S := Finset.Icc (1 : ℕ+) C
  have finite : HasSum (sourceOrbit N m n ψ φ) (∑ d ∈ S,sourceOrbit N m n ψ φ d) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd
    have hCd : C<d := lt_of_not_ge (fun h => hd (Finset.mem_Icc.mpr ⟨d.property,h⟩))
    have Z := mixedFiberPairSlice_zero_of_large N hN d m n ψ φ a b ha hb hfloorφ hfloorψ
      (mixed_large_of_cutoff N hN a b ha hb C d hC hCd)
    rw [← orient]
    simp only [R,Z,integral_zero,star_zero,mul_zero]
  refine ⟨finite.summable,?_⟩
  have hd : Integrable (fun y => if N=1 ∧ m=n then radialWeight ψ y*φ y else 0) := by
    by_cases h : N=1 ∧ m=n
    · simpa only [if_pos h] using radial_diagonal_integrable ψ φ hψ hcψ hpψ hφ
    · simp only [if_neg h]
      exact integrable_zero _ _ _
  have H : (∫ q,star (parabolicComplexPoincare N (fourierRadialSeed m ψ) q)*
      zeroCuspPoincare N hN n φ hcφ hpφ q ∂carrierPushforward N) =
      (if N=1 ∧ m=n then ∫ y : ℝ,radialWeight ψ y*φ y else 0)+∑ d ∈ S,R d := by
    rw [mixed_quotient_pairing_unfolding N hN m n ψ φ hψ hcψ hpψ hφ hcφ hpφ,
      mixed_strip_pairing_eq_integrated_slices N hN m n ψ φ hψ hcψ hpψ hφ hcφ hpφ,
      funext (mixedActualPairSlice_eq_finite N hN m n ψ φ hpψ hφ hcφ hpφ a b ha hb hfloorφ hfloorψ C hC)]
    have I (d : ℕ+) := mixedFiberPairSlice_integrable N hN d m n ψ φ hψ hcψ hpψ hφ hcφ hpφ
    rw [integral_add hd (integrable_finsetSum _ (fun d _ => I d)),integral_finsetSum _ (fun d _ => I d)]
    by_cases h : N=1 ∧ m=n <;> simp only [h,if_true,if_false,integral_zero,R,S]
  have swap : (∫ q,star (zeroCuspPoincare N hN n φ hcφ hpφ q)*originalPoincare N false m ψ q
      ∂carrierPushforward N) = star (∫ q,star (parabolicComplexPoincare N (fourierRadialSeed m ψ) q)*
        zeroCuspPoincare N hN n φ hcφ hpφ q ∂carrierPushforward N) := by
    rw [← integral_conj]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => by simp only [← Complex.star_def,star_mul,star_star] <;> rfl)
  rw [one_zero_pair N n φ hφ hcφ hpφ _ (compactCuspPoincare_memLp_two N m ψ hψ hcψ hpψ),
    swap,H,star_add,mul_add,star_sum,Finset.mul_sum,finite.tsum_eq]
  exact congrArg (fun z => sourceDiagonal N m n ψ φ+z) (Finset.sum_congr rfl (fun d _ => orient d))

end
end ImbalancedChen.Part3.ActualCuspOneGeometricPairing20261112

