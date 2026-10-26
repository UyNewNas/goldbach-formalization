import ImbalancedChen.Part3ActualPhysicalHeckeL2
import ImbalancedChen.Part3ActualHeckeComplexCoverIntegral

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual physical normalized Hecke trace is identified with the genuine
finite correspondence pairing. The original quotient L2 hypotheses pay
both product integrals; actual covering integration pays the p+1 branches.
The resulting native L2 identity is <P1 U,P2 V> = sqrt(p)<U,Tp V>.
Neither an abstract trace-adjoint premise nor selfadjointness is assumed.
-/

namespace ImbalancedChen.Part3.ActualHeckeCorrespondencePairing20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeQuotientDescent20261026b
open ActualHeckeFiniteCover20261026b ActualHeckeCorrespondenceCarrier20261026b
open ActualHeckeSecondProjection20261026b ActualHeckeComplexCoverIntegral20261026b
open ActualHeckeForgetCoverMeasure20261026b ActualHeckeForgetL220261026b
open ActualHeckeSecondL220261026b ActualPhysicalHeckeL220261026b
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open ActualPoincareSpectralCoefficient20261026a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

theorem correspondence_pairing_integrable {U V : Gamma0OrbitSpace N → ℂ}
    (hU : MemLp U 2 (carrierPushforward N)) (hV : MemLp V 2 (carrierPushforward N)) :
    Integrable (fun q => star (U (forgetPrimeLevel N p q)) *
      V (secondProjection N p hp hpN q)) (carrierPushforward (N*p)) :=
  (forgetPrimeLevel_memLp N p hp hpN hU).star.integrable_mul
    (secondProjection_memLp N p hN hp hpN hV)

private theorem integral_on_reducedCarrier (F : Gamma0OrbitSpace N → ℂ)
    (hF : Integrable F (carrierPushforward N)) :
    (∫ q, F q ∂carrierPushforward N) = ∫ z in reducedCarrier N, F (orbitProjection N z) := by
  have hm : AEStronglyMeasurable F
      (((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)).map (orbitProjection N)) := by
    change AEStronglyMeasurable F (cellPushforward N (reducedCarrier N))
    rw [reducedCarrier_pushforward_eq N]
    exact hF.aestronglyMeasurable
  have heq := integral_map (orbitProjection_measurable N).aemeasurable hm
  change (∫ q, F q ∂cellPushforward N (reducedCarrier N)) = _ at heq
  rw [reducedCarrier_pushforward_eq N] at heq
  exact heq

/-- Exact physical Hecke pairing for original quotient observables.
Only original V is required measurable; original U only needs native L2. -/
theorem physicalHecke_correspondence_pairing (U V : Gamma0OrbitSpace N → ℂ)
    (hU : MemLp U 2 (carrierPushforward N)) (hVm : Measurable V)
    (hV : MemLp V 2 (carrierPushforward N)) :
    (∫ q, star (U (forgetPrimeLevel N p q)) * V (secondProjection N p hp hpN q)
      ∂carrierPushforward (N*p)) =
      (Real.sqrt (p : ℝ) : ℂ) * ∫ q, star (U q) * quotientHecke N p hp hpN V q
        ∂carrierPushforward N := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast hp.pos)).ne'
  let G : Gamma0OrbitSpace (N*p) → ℂ := fun q =>
    star (U (forgetPrimeLevel N p q)) * V (secondProjection N p hp hpN q)
  have hG : Integrable G (carrierPushforward (N*p)) :=
    correspondence_pairing_integrable N p hN hp hpN hU hV
  have hpair : Integrable (fun q => star (U q) * quotientHecke N p hp hpN V q)
      (carrierPushforward N) :=
    hU.star.integrable_mul (quotientHecke_memLp N p hN hp hpN V hVm hV)
  have hsum (z : UpperHalfPlane) :
      (∑ j : Branch p, G (orbitProjection (N*p) (coverAction N p hp hpN j z))) =
      (Real.sqrt (p : ℝ) : ℂ) *
        (star (U (orbitProjection N z)) * quotientHecke N p hp hpN V (orbitProjection N z)) := by
    have hfirst (j : Branch p) :
        forgetPrimeLevel N p (orbitProjection (N*p) (coverAction N p hp hpN j z)) =
          orbitProjection N z := by
      rw [forgetPrimeLevel_projection]
      exact orbitProjection_smul N (coverRepresentative N p hp hpN j) z
    have htrace : quotientHecke N p hp hpN V (orbitProjection N z) =
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ * ∑ j : Branch p,
          V (secondProjection N p hp hpN (orbitProjection (N*p) (coverAction N p hp hpN j z))) :=
      nativeHecke_correspondence N p hp hpN V z
    change (∑ j : Branch p, star (U (forgetPrimeLevel N p
      (orbitProjection (N*p) (coverAction N p hp hpN j z)))) *
        V (secondProjection N p hp hpN (orbitProjection (N*p) (coverAction N p hp hpN j z)))) = _
    simp_rw [hfirst]
    rw [← Finset.mul_sum, htrace]
    field_simp [hs] <;> ring
  calc
    _ = ∫ z in reducedCarrier N, ∑ j : Branch p,
        G (orbitProjection (N*p) (coverAction N p hp hpN j z)) :=
      canonical_cover_integral N p hp hpN G hG
    _ = ∫ z in reducedCarrier N, (Real.sqrt (p : ℝ) : ℂ) *
        (star (U (orbitProjection N z)) * quotientHecke N p hp hpN V (orbitProjection N z)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hsum
    _ = (Real.sqrt (p : ℝ) : ℂ) * ∫ z in reducedCarrier N,
        star (U (orbitProjection N z)) * quotientHecke N p hp hpN V (orbitProjection N z) :=
      integral_const_mul _ _
    _ = _ := congrArg (fun a : ℂ => (Real.sqrt (p : ℝ) : ℂ)*a)
      (integral_on_reducedCarrier N _ hpair).symm

/-- The actual physical quotient trace, now as a native L2 vector. -/
def physicalHeckeLp (V : Lp ℂ 2 (carrierPushforward N)) : Lp ℂ 2 (carrierPushforward N) :=
  (quotientHecke_memLp N p hN hp hpN V V.stronglyMeasurable.measurable (Lp.memLp V)).toLp
    (quotientHecke N p hp hpN V)

theorem physicalHeckeLp_coe (V : Lp ℂ 2 (carrierPushforward N)) :
    (physicalHeckeLp N p hN hp hpN V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientHecke N p hp hpN V :=
  (quotientHecke_memLp N p hN hp hpN V V.stronglyMeasurable.measurable (Lp.memLp V)).coeFn_toLp

/-- Native Hilbert pairing with both ACTUAL pullback representatives. -/
theorem rawPullback_inner_physicalHecke (U V : Lp ℂ 2 (carrierPushforward N)) :
    inner ℂ (rawPullback N p hp hpN U) (rawSecondPullbackLinear N p hN hp hpN V) =
      (Real.sqrt (p : ℝ) : ℂ) * inner ℂ U (physicalHeckeLp N p hN hp hpN V) := by
  have hleft : inner ℂ (rawPullback N p hp hpN U) (rawSecondPullbackLinear N p hN hp hpN V) =
      ∫ q, star (U (forgetPrimeLevel N p q)) * V (secondProjection N p hp hpN q)
        ∂carrierPushforward (N*p) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [rawPullback_coe N p hp hpN U, rawSecondPullback_coe N p hN hp hpN V] with q hU hV
    rw [hU,hV]
    simp only [RCLike.inner_apply', Complex.star_def]
  have hright : inner ℂ U (physicalHeckeLp N p hN hp hpN V) =
      ∫ q, star (U q) * quotientHecke N p hp hpN V q ∂carrierPushforward N := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalHeckeLp_coe N p hN hp hpN V] with q hV
    rw [hV]
    simp only [RCLike.inner_apply', Complex.star_def]
  rw [hleft, hright]
  exact physicalHecke_correspondence_pairing N p hN hp hpN U V (Lp.memLp U)
    V.stronglyMeasurable.measurable (Lp.memLp V)

end
end ImbalancedChen.Part3.ActualHeckeCorrespondencePairing20261026b

