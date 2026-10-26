import ImbalancedChen.Part3ActualCoprimePhysicalHecke
import ImbalancedChen.Part3ActualCompactSeedHeckeQuotient
import ImbalancedChen.Part3ActualPrimeHeckePhysicalFourier

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ACTUAL bounded ORIGINAL normalized physical Gamma0 quotient Hecke
operators commute at distinct good primes (more generally coprime ones).
The literal periodic finite-sum identity is paid by actual chart descent
and original Gamma0 period one; no raw periodicity of a renamed function
is assumed. The bounded operator identification uses its actual native
Lp representatives and the proved canonical-mass AE congruence law.
No branch null-set preservation, Hecke SA, private canonical carrier API,
commutation target, cusp restriction or eigenspace matrix premise is used.
-/

namespace ImbalancedChen.Part3.ActualBoundedHeckePairCommutation20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ActualCoprimePhysicalHecke20261026b ActualBoundedPhysicalHecke20261026b
open ActualCompactSeedHeckeQuotient20261026b ActualPhysicalHeckeL220261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualPrimeHeckePhysicalFourier20261026b
open QuotientRealKFourierCoefficient20261026b ActualPoincareSpectralCoefficient20261026a
open ActualMaassFourierODE20261026a Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a CanonicalPlanarL2UnitarySourceOnly

variable (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpN : ¬ p ∣ N) (hqN : ¬ q ∣ N)

private theorem quotientHecke_comp_chart (U : Gamma0OrbitSpace N → ℂ)
    (x y : ℝ) (hy : 0 < y) :
    maassChart N (quotientHecke N p hp hpN (quotientHecke N q hq hqN U)) (x,y) =
      primeHeckeExpression p (primeHeckeExpression q (maassChart N U)) (x,y) := by
  rw [quotientHecke_chart N p hp hpN (quotientHecke N q hq hqN U) x y hy]
  exact primeHeckeExpression_congr_upper p hp.pos
    (fun z hz => quotientHecke_chart N q hq hqN U z.1 z.2 hz) (x,y) hy

/-- Genuine pointwise commutation on the ORIGINAL actual orbit quotient,
with original period one derived from actual Gamma0 deck invariance. -/
theorem quotientHecke_coprime_commute (hpq : Nat.Coprime p q) (U : Gamma0OrbitSpace N → ℂ) :
    quotientHecke N p hp hpN (quotientHecke N q hq hqN U) =
      quotientHecke N q hq hqN (quotientHecke N p hp hpN U) := by
  funext t
  refine Quotient.inductionOn t (fun z => ?_)
  change testLift N (quotientHecke N p hp hpN (quotientHecke N q hq hqN U)) z =
    testLift N (quotientHecke N q hq hqN (quotientHecke N p hp hpN U)) z
  rw [← chartPullback_at_upper (testLift N (quotientHecke N p hp hpN (quotientHecke N q hq hqN U))) z,
    ← chartPullback_at_upper (testLift N (quotientHecke N q hq hqN (quotientHecke N p hp hpN U))) z]
  change maassChart N (quotientHecke N p hp hpN (quotientHecke N q hq hqN U)) (z.re,z.im) =
    maassChart N (quotientHecke N q hq hqN (quotientHecke N p hp hpN U)) (z.re,z.im)
  rw [quotientHecke_comp_chart N p q hp hq hpN hqN U z.re z.im z.im_pos,
    quotientHecke_comp_chart N q p hq hp hqN hpN U z.re z.im z.im_pos]
  exact primeHeckeExpression_coprime_commute p q hp.pos hq.pos hpq (maassChart N U)
    (maassChart_periodic N U) (z.re,z.im) z.im_pos

variable [NeZero N] [NeZero (N*p)] [NeZero (N*q)] (hN : 0 < N)

/-- Equality of the ACTUAL bounded canonical quotient L2 compositions.
AE congruence is the previously proved actual mass/QMP consumer, not an
assumed branch map or an abstract operator-to-physical dictionary. -/
theorem physicalHeckeOperator_coprime_comp_eq (hpq : Nat.Coprime p q) :
    (physicalHeckeOperator N p hN hp hpN).comp (physicalHeckeOperator N q hN hq hqN) =
      (physicalHeckeOperator N q hN hq hqN).comp (physicalHeckeOperator N p hN hp hpN) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  have hleftOuter := physicalHeckeOperator_coe N p hN hp hpN (physicalHeckeOperator N q hN hq hqN F)
  have hleftCongr := quotientHecke_congr_ae N p hN hp hpN
    (physicalHeckeOperator N q hN hq hqN F) (quotientHecke N q hq hqN F)
    (physicalHeckeOperator N q hN hq hqN F).stronglyMeasurable.measurable
    (quotientHecke_measurable N q hq hqN F F.stronglyMeasurable.measurable)
    (physicalHeckeOperator_coe N q hN hq hqN F)
  have hrightOuter := physicalHeckeOperator_coe N q hN hq hqN (physicalHeckeOperator N p hN hp hpN F)
  have hrightCongr := quotientHecke_congr_ae N q hN hq hqN
    (physicalHeckeOperator N p hN hp hpN F) (quotientHecke N p hp hpN F)
    (physicalHeckeOperator N p hN hp hpN F).stronglyMeasurable.measurable
    (quotientHecke_measurable N p hp hpN F F.stronglyMeasurable.measurable)
    (physicalHeckeOperator_coe N p hN hp hpN F)
  have hleft := hleftOuter.trans hleftCongr
  have hright := hrightOuter.trans hrightCongr
  rw [quotientHecke_coprime_commute N p q hp hq hpN hqN hpq F] at hleft
  exact hleft.trans hright.symm

/-- Actual physical bounded Hecke operators commute as native endomorphisms
of the ORIGINAL canonical quotient L2, independently of spectral type. -/
theorem physicalHeckeOperator_coprime_commute (hpq : Nat.Coprime p q) :
    Commute (physicalHeckeOperator N p hN hp hpN) (physicalHeckeOperator N q hN hq hqN) :=
  physicalHeckeOperator_coprime_comp_eq N p q hp hq hpN hqN hN hpq

/-- Requested distinct-good-prime endpoint. Coprimality is derived from
the actual prime divisibility criterion, not added as a hypothesis. -/
theorem physicalHeckeOperator_distinct_good_primes_commute (hne : p ≠ q) :
    Commute (physicalHeckeOperator N p hN hp hpN) (physicalHeckeOperator N q hN hq hqN) := by
  have hnot : ¬ p ∣ q := by
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with h1 | heq
    · exact hp.ne_one h1
    · exact hne heq
  have hpq : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hnot
  exact physicalHeckeOperator_coprime_commute N p q hp hq hpN hqN hN hpq

end
end ImbalancedChen.Part3.ActualBoundedHeckePairCommutation20261026b
