import ImbalancedChen.Part3LocalSmoothWeakDerivativeUniqueness
import ImbalancedChen.Part3Gamma0ArbitrarySmoothWeakGradient
import ImbalancedChen.Part3CanonicalPlanarL2Unitary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The represented gradient of an actual energy vector is identified with the
literal derivative of any independently supplied smooth physical chart
representative. Each compact local component is zero-extended and passed
through the TRUE canonical hyperbolic-to-planar L2 unitary. Division by y
therefore yields an ordinary planar L2 derivative. Actual arbitrary smooth
testing and local distribution uniqueness identify it with the classical
derivative. No gradient equality, C1 approximation, or adjoint H1 premise
is supplied. The sole representation hypothesis is an AE VALUE equality.
-/

namespace ImbalancedChen.Part3.GammaCompletedGradientClassicalRepresentative20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a MaassWeakOperatorCore20261024zz
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CompactCoreGradient20261025a Gamma0EnergyCompactGradientExtension20261025a
open Gamma0EnergyGeometricWeakGradient20261025a Gamma0ArbitrarySmoothWeakGradient20261026b
open CompactC2ProductMollifier20261026a ArbitraryCompactFirstGradientIBP20261026b
open LocalSmoothWeakDerivativeUniqueness20261026b CanonicalPlanarL2UnitarySourceOnly
open CanonicalTensorHyperbolicLaplacianForm20261024z
open OneCompactFirstGradientIBP20261025a

/-- Ordinary coordinate derivative candidate: the native vector component,
zero-extended from K, then divided by y through the actual L2 unitary. -/
def planarCompletedPartial (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N) : Plane → ℂ :=
  forwardFunction (K.indicator (fun z =>
    (completedCompactGradient N hK e) z (firstCoordinate vertical)))

theorem planarCompletedPartial_memLp (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N) :
    MemLp (planarCompletedPartial N hK vertical e) 2 (volume : Measure Plane) := by
  have hc : MemLp (fun z => (completedCompactGradient N hK e) z (firstCoordinate vertical))
      2 ((volume : Measure UpperHalfPlane).restrict K) := by
    exact (EuclideanSpace.proj (𝕜 := ℂ) (firstCoordinate vertical)).comp_memLp
      (completedCompactGradient N hK e)
  exact forwardFunction_memLp ((memLp_indicator_iff_restrict hK.measurableSet).2 hc)

theorem planarCompletedPartial_at_upper (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N) (z : UpperHalfPlane) :
    planarCompletedPartial N hK vertical e (z.re,z.im) =
      (z.im⁻¹ : ℝ) • K.indicator
        (fun w => (completedCompactGradient N hK e) w (firstCoordinate vertical)) z :=
  forwardFunction_at_upper _ z

theorem planarCompletedPartial_test_pairing (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    (∫ z in K, star (ψ (z.re,z.im)) *
      (completedCompactGradient N hK e) z (firstCoordinate vertical) * (z.im : ℂ)) =
      ∫ p : Plane, star (ψ p) * planarCompletedPartial N hK vertical e p := by
  rw [← canonical_ySq_integral _ (fun p hp => by
    simp only [planarCompletedPartial,forwardFunction_zero_outside _ p hp,mul_zero])]
  rw [← integral_indicator hK.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    rw [planarCompletedPartial_at_upper]
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz]
      simp only [Complex.real_smul,Complex.ofReal_inv]
      have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos)
      field_simp [hy] <;> ring
    · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem hz]
      simp only [smul_zero,mul_zero])

/-- The actual weak derivative identity, with only an independently
verified physical VALUE representative substituted into the mass term. -/
theorem planarCompletedPartial_weak_for_representative (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N)
    {U : Set Plane} (hUp : U ⊆ positiveChart)
    (hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ U → z ∈ K)
    (F : Plane → ℂ)
    (hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      (physicalProjection N e) (orbitProjection N z) = F (z.re,z.im))
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) :
    (∫ p : Plane, star (ψ p) * planarCompletedPartial N hK vertical e p) =
      -(∫ p : Plane, star (directional (coordinateDirection vertical) ψ p) * F p) := by
  have hTK : chartTestSupport ψ ⊆ K := fun z hz => hUK z (hs hz)
  have ht := completed_arbitrary_smooth_weak_derivative N hK vertical hψ hc
    (hs.trans hUp) hTK e
  have hmass : (∫ z in K, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (physicalProjection N e) (orbitProjection N z) * (z.im : ℂ)^2) =
      ∫ p : Plane, star (directional (coordinateDirection vertical) ψ p) * F p := by
    calc
      _ = ∫ z in K, (z.im : ℂ)^2 *
          (star (directional (coordinateDirection vertical) ψ (z.re,z.im)) * F (z.re,z.im)) := by
        apply integral_congr_ae
        filter_upwards [hrep] with z hz
        rw [hz]
        ring
      _ = ∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
          (star (directional (coordinateDirection vertical) ψ (z.re,z.im)) * F (z.re,z.im)) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
          have hn : (z.re,z.im) ∉ tsupport ψ := fun hp => hz (hUK z (hs hp))
          have hd : directional (coordinateDirection vertical) ψ (z.re,z.im) = 0 := by
            simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
          simp only [hd,star_zero,zero_mul,mul_zero])
      _ = _ := canonical_ySq_integral _ (fun p hp => by
        have hn : p ∉ tsupport ψ := fun ht => hp (hUp (hs ht))
        have hd : directional (coordinateDirection vertical) ψ p = 0 := by
          simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
        simp only [hd,star_zero,zero_mul])
  rw [hmass,planarCompletedPartial_test_pairing N hK vertical e hψ] at ht
  simpa only [neg_neg] using congrArg Neg.neg ht.symm

/-- The planar native L2 derivative is the classical real derivative on
every open chart whose upper lift lies in the compact local gradient set. -/
theorem planarCompletedPartial_eq_classical (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N)
    {U : Set Plane} (hU : IsOpen U) (hUp : U ⊆ positiveChart)
    (hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ U → z ∈ K)
    (F : Plane → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      (physicalProjection N e) (orbitProjection N z) = F (z.re,z.im)) :
    ∀ᵐ p ∂(volume : Measure Plane), p ∈ U →
      planarCompletedPartial N hK vertical e p = directional (coordinateDirection vertical) F p := by
  apply local_weak_derivative_eq_classical hU hUp _ hF
    (((planarCompletedPartial_memLp N hK vertical e).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
  intro ψ hψ hc hs
  exact planarCompletedPartial_weak_for_representative N hK vertical e hUp hUK F hrep hψ hc hs

/-- Literal weighted classical gradient identification in canonical H
volume. The proof transports the planar AE equality back through the
genuine quasi-measure-preserving chart, then cancels positive height. -/
theorem completedCompactGradient_eq_classical_component (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N)
    {U : Set Plane} (hU : IsOpen U) (hUp : U ⊆ positiveChart)
    (hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ U → z ∈ K)
    (F : Plane → ℂ) (hF : ContDiffOn ℝ 2 F positiveChart)
    (hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      (physicalProjection N e) (orbitProjection N z) = F (z.re,z.im)) :
    ∀ᵐ z ∂(volume : Measure UpperHalfPlane), (z.re,z.im) ∈ U →
      (completedCompactGradient N hK e) z (firstCoordinate vertical) =
        (z.im : ℂ) * directional (coordinateDirection vertical) F (z.re,z.im) := by
  have hp := planarCompletedPartial_eq_classical N hK vertical e hU hUp hUK F hF hrep
  filter_upwards [chartMap_quasiMeasurePreserving.ae hp] with z hz
  intro hzU
  have he := hz hzU
  rw [planarCompletedPartial_at_upper,Set.indicator_of_mem (hUK z hzU)] at he
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt z.im_pos)
  have he' : (z.im : ℂ)⁻¹ * (completedCompactGradient N hK e) z (firstCoordinate vertical) =
      directional (coordinateDirection vertical) F (z.re,z.im) := by
    simpa only [Complex.real_smul,Complex.ofReal_inv] using he
  have hm := congrArg (fun w : ℂ => (z.im : ℂ) * w) he'
  simpa only [← mul_assoc,mul_inv_cancel₀ hy,one_mul] using hm

end
end ImbalancedChen.Part3.GammaCompletedGradientClassicalRepresentative20261026b
