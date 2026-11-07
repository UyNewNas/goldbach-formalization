import ImbalancedChen.ActualHistoricalFifthSavingIntegral
import ImbalancedChen.ActualExtendedThirdCompactResidualProfile
import ImbalancedChen.CurrentPairedBuchstabBridge

/-!
# P2: the literal historical residual and paired gain kernels

SOURCE ONLY: no compiler, runtime, producer, replay or audit has been run.

The historical fifth saving currently supplied by P1 is a five-coordinate
integral of a difference of lower sieve profiles.  The paired certificate
is a four-coordinate integral.  These are distinct existing objects.  This
file proves the concrete normalizations available before the missing
dimension-reduction/domain identification, without assuming that identity.

The continuous own-cube gate is removable because its lower sieve profile
is already zero when its strict gate fails.  This statement includes the
wall and is purely about continuous profiles.  It does not remove any gate
from an arithmetic sum.  Both effective historical levels remain present.

On the paired side, `pairedChenQuarterWeight` is the literal weight
`(K/4)/(t*u*z^2*w)` and `pairedSemanticBuchstabGain` uses the actual pinned
Buchstab function.  The exact factor `1/20` occurs once.  No alternative
function supplied by a caller is accepted as the semantic gain.

Remaining exact obligation: construct the adopted historical data, then
prove the change of variables / residual integration that identifies its
five-coordinate signed lower-profile integral with the four-coordinate
paired Buchstab-gain integral on the same licensed arithmetic parent and
the actual adopted mask.  None of the imported files defines that map or
proves that domain identity.  In particular the positive first paired row
does not by itself identify `HistoricalPrefixCapData.fifthCorrectionIntegral`.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set Filter Topology
open MathlibNt.SieveTheory
open scoped Classical BigOperators Interval

namespace P2HistoricalFibreBinding

/-- Exact extension-factor normalization in every nonempty tuple dimension.
This is the same normalization already available for the third residual. -/
theorem minusProfile_eq_extendedLowerFactor {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    primeTupleMinusProfile lambda t =
      4 * actualExtendedThirdLowerFactor
        ((lambda - ∑ i, t i) / t (Fin.last k)) / t (Fin.last k) := by
  unfold primeTupleMinusProfile actualExtendedThirdLowerFactor thirdTailLowerFactor
  rw [Real.exp_neg]
  field_simp [ne_of_gt ht, ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]
  <;> ring

/-- The continuous strict own-cube indicator, including its equality wall,
has exactly the same zero extension as the literal lower sieve profile. -/
theorem ownCubeGatedProfile_eq_minusProfile {k : ℕ} (lambda : ℝ)
    (t : Fin (k + 1) → ℝ) (ht : 0 < t (Fin.last k)) :
    primeOwnCubeGatedProfile lambda t = primeTupleMinusProfile lambda t := by
  unfold primeOwnCubeGatedProfile
  split_ifs with hg
  · rfl
  · have hgate : lambda ≤ (∑ i, t i) + 2 * t (Fin.last k) := by
      simpa only [primeTupleOwnCubeForm] using (le_of_not_gt hg)
    have hratio : (lambda - ∑ i, t i) / t (Fin.last k) ≤ 2 :=
      (div_le_iff₀ ht).mpr (by linarith)
    rw [minusProfile_eq_extendedLowerFactor lambda t ht,
      actualExtendedThirdLowerFactor_of_le_two hratio, mul_zero, zero_div]

/-- This is the actual historical difference, with both levels retained;
it is not the Buchstab gain of the paired four-coordinate certificate. -/
theorem ownCubeGatedProfile_sub_eq_extendedLowerDifference {k : ℕ}
    (lambdaNew lambdaOld : ℝ) (t : Fin (k + 1) → ℝ)
    (ht : 0 < t (Fin.last k)) :
    (primeOwnCubeGatedProfile lambdaNew t -
        primeOwnCubeGatedProfile lambdaOld t) * (∏ i, 1 / t i) =
      (4 * (actualExtendedThirdLowerFactor
          ((lambdaNew - ∑ i, t i) / t (Fin.last k)) -
        actualExtendedThirdLowerFactor
          ((lambdaOld - ∑ i, t i) / t (Fin.last k))) / t (Fin.last k)) *
        (∏ i, 1 / t i) := by
  rw [ownCubeGatedProfile_eq_minusProfile lambdaNew t ht,
    ownCubeGatedProfile_eq_minusProfile lambdaOld t ht,
    minusProfile_eq_extendedLowerFactor lambdaNew t ht,
    minusProfile_eq_extendedLowerFactor lambdaOld t ht]
  simp only [div_eq_mul_inv]
  ring

end P2HistoricalFibreBinding

namespace HistoricalPrefixCapData

/-- An exact common-cell historical identity, preserving half-open mesh
ownership, the original first gate and the effective third ancestor gate.
Only the continuously redundant own-cube indicators have disappeared. -/
theorem fifthCellIntegral_eq_extendedLowerDifference (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
        primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
        (4 * (actualExtendedThirdLowerFactor
            (((D.cap5 j : ℝ) - ∑ i, t i) / t (Fin.last 4)) -
          actualExtendedThirdLowerFactor
            (((D.old5 j : ℝ) - ∑ i, t i) / t (Fin.last 4))) / t (Fin.last 4)) *
          (∏ i, 1 / t i) := by
  rw [D.fifthCellIntegral_eq_integral ha hab j]
  apply setIntegral_congr_fun
    ((measurableSet_logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j).inter
      (measurableSet_primeAffineGateRegion ordinaryUpperFiveGateForms
        (D.fifthParentGateBounds j)))
  intro t ht
  have hbox := mem_logPrimeBox.mp
    (logPrimeMeshCell_subset_box (by exact_mod_cast hab) D.m j ht.1)
  have hlast : 0 < t (Fin.last 4) :=
    lt_of_lt_of_le (by exact_mod_cast ha) (hbox (Fin.last 4)).1
  exact P2HistoricalFibreBinding.ownCubeGatedProfile_sub_eq_extendedLowerDifference
    (D.cap5 j : ℝ) (D.old5 j : ℝ) t hlast

/-- The entire existing historical integral is a sum of these literal
five-coordinate lower-factor differences, with no new analytic premise. -/
theorem fifthCorrectionIntegral_eq_extendedLowerDifferences
    (D : HistoricalPrefixCapData) (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∑ j ∈ D.cells5,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (4 * (actualExtendedThirdLowerFactor
              (((D.cap5 j : ℝ) - ∑ i, t i) / t (Fin.last 4)) -
            actualExtendedThirdLowerFactor
              (((D.old5 j : ℝ) - ∑ i, t i) / t (Fin.last 4))) / t (Fin.last 4)) *
            (∏ i, 1 / t i) := by
  unfold fifthCorrectionIntegral
  apply Finset.sum_congr rfl
  intro j _hj
  exact D.fifthCellIntegral_eq_extendedLowerDifference ha hab j

end HistoricalPrefixCapData

namespace Certificates
namespace P2HistoricalFibreBinding

/-- Literal Chen-quarter paired weight in the existing four coordinates. -/
def pairedChenQuarterWeight (K t u z w : ℝ) : ℝ :=
  (K / 4) / (t * u * z ^ 2 * w)

/-- Semantic extra gain: the actual pinned Buchstab function at the exact
paired residual argument, with its original half baseline subtracted. -/
def pairedSemanticBuchstabGain (t u z w : ℝ) : ℝ :=
  LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2

/-- The certificate integrand uses exactly this weight, multiplied by
`1/20` once.  No positivity or nonzero-denominator assumption is hidden. -/
theorem pairedCertificateKernel_eq_weight (K t u z w : ℝ) :
    (K / 80) * pairedFibreKernel t u z w =
      pairedChenQuarterWeight K t u z w * (1 / 20) := by
  rw [pairedFibreKernel_eq]
  unfold pairedChenQuarterWeight
  ring

/-- Exact fourfold integral adapter to the explicit Chen-quarter weight.
The real integration object and its triangular `w` fibre are unchanged. -/
theorem pairedLocalIntegral_eq_weight_integral (K a tl tr ul ur Z : ℝ) :
    pairedLocalIntegral K a tl tr ul ur Z =
      ∫ t in tl..tr, ∫ u in ul..ur, ∫ z in a..Z, ∫ w in a..z,
        pairedChenQuarterWeight K t u z w * (1 / 20) := by
  unfold pairedLocalIntegral
  simp only [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  apply intervalIntegral.integral_congr
  intro u _hu
  apply intervalIntegral.integral_congr
  intro z _hz
  apply intervalIntegral.integral_congr
  intro w _hw
  exact pairedCertificateKernel_eq_weight K t u z w

/-- On the actual first adopted fibre the semantic gain supplier applies
to the very same explicit weight as the certified local integral. -/
theorem first_fibre_weight_gain {t u z w : ℝ}
    (hs : PairedV2.firstFibreSupport t u z w) :
    pairedChenQuarterWeight (8452171 / 1250000) t u z w * (1 / 20) ≤
      pairedChenQuarterWeight (8452171 / 1250000) t u z w *
        pairedSemanticBuchstabGain t u z w := by
  obtain ⟨haw, hwz, hzu, _huh, hht, _htd, _harg⟩ :=
    PairedV2.first_fibre_argument hs
  have hw : 0 < w := by linarith
  have hz : 0 < z := hw.trans hwz
  have hu : 0 < u := hz.trans hzu
  have ht : 0 < t := by linarith
  have hweight : 0 ≤ pairedChenQuarterWeight (8452171 / 1250000) t u z w := by
    unfold pairedChenQuarterWeight
    positivity
  exact mul_le_mul_of_nonneg_left (PairedV2.first_fibre_buchstab_gain hs) hweight

/-- The frozen first certificate is the integral of this exact weight
times the proved constant gain.  This does not identify a historical
five-coordinate integral with the semantic Buchstab-gain integral. -/
theorem firstIntegral_eq_weight_integral :
    PairedV2.firstIntegral =
      ∫ t in (937361 / 4096000 : ℝ)..(1875373 / 8192000),
      ∫ u in (194217 / 1280000 : ℝ)..(388777 / 2560000),
      ∫ z in (417 / 5000 : ℝ)..(76088109 / 532480000),
      ∫ w in (417 / 5000 : ℝ)..z,
        pairedChenQuarterWeight (8452171 / 1250000) t u z w * (1 / 20) := by
  exact pairedLocalIntegral_eq_weight_integral _ _ _ _ _ _ _

end P2HistoricalFibreBinding
end Certificates

end

end ImbalancedChen
