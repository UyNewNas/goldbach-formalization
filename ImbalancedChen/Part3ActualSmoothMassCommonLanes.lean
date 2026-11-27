import ImbalancedChen.Part3ActualSmoothMassCompletion
import ImbalancedChen.Part3ActualModeCommonPoissonLanes

/-!
# Actual smooth masses in the common Poisson frequency decomposition

This finite composition consumes the original smoothMass/sixSmoothMass
completion identities and the accepted actual-medium-source primary
decomposition. The recovered supplier proofs retain their original source;
this module only connects their endpoints.

The actual g*l, signed residue, baseCarrier quotient image, shared h bound
and scaleF window are used on both sides. One common J is used in every
primary block and in all six smooth scale pairs. The original lambda and
omega do not acquire a future m or a spectral-height argument. The y=0
source retains its complete integer-m kernel, while its disjoint nonzero
part uses zero m, both signed common blocks and the complementary tail.

The first identity requires the original positive b scale M and its support
in the fixed packetBox (M <= 2*B). The six-piece identity uses b scales B and
2*B on the SAME box, c scales C, 2*C and 4*C, and no additional multiplicity
factor. No positivity or nonemptiness of the actual source is assumed.

This is finite bookkeeping for the 1106 manuscript's reciprocal completion
and common signed frequency intervals. It does not construct OriginalData
or FixedBlock, identify the coefficient functions with a missing full
energy interface, choose or bound a global truncation J, prove zero/tail
estimates, or instantiate the external spectral inputs J/A.
-/

namespace ImbalancedChen.Part3.ActualSmoothMassCommonLanes20261127

noncomputable section
open Classical Finset
open scoped BigOperators
open ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open ActualModeCommonPoissonLanes20261126

/-- The exact already-proved actual completed-piece expression. The source
depends on the original medium data, not on the smooth scales or cutoff J.
The full zero-y kernel is added once, outside the primary nonzero-y blocks. -/
def actualPieceLanes (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (J : ℕ) (M N C : ℝ) : ℂ :=
  let a := signedResidue residueNegative e.residue
  let S := actualSource e D delta g l Z residueNegative
  (∑ zy ∈ (zeroSource S).image output,
    beta (zeroSource S) lambda omega zy * completedKernel M N C a zy) +
    primaryMLanes a S lambda omega J M N C

/-- A complete actual smooth square, with the original fixed box and row,
equals the accepted zero-y/primary common-J Poisson decomposition. -/
theorem actual_smoothMass_eq_common_m_lanes
    (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M B : ℝ}
    (hM : 0 < M) (hMB : M ≤ 2 * B) (J : ℕ) (N C : ℝ) :
    (smoothMass M N (packetBox B C (scaleF e D g))
      (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega) : ℂ) =
      actualPieceLanes e D delta g l Z residueNegative lambda omega J M N C := by
  calc
    _ = completedPiece (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega M N B C (scaleF e D g) :=
      smoothMass_eq_completed_pairs (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega hM hMB N C (scaleF e D g)
    _ = _ := actual_completedPiece_eq_zero_add_primary_m_lanes
      e D delta g l Z residueNegative lambda omega hM J N B C

/-- All six original smooth pieces use the same actual row, box, source
coefficients and cutoff J. The outer c carrier still uses the original C;
only the smooth c scale changes between C, 2*C and 4*C. -/
theorem actual_sixSmoothMass_eq_common_m_lanes
    (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {B : ℝ} (hB : 0 < B)
    (J : ℕ) (C : ℝ) :
    (sixSmoothMass B C (packetBox B C (scaleF e D g))
      (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega) : ℂ) =
      actualPieceLanes e D delta g l Z residueNegative lambda omega J B C C +
      actualPieceLanes e D delta g l Z residueNegative lambda omega J B (2 * C) C +
      actualPieceLanes e D delta g l Z residueNegative lambda omega J B (4 * C) C +
      actualPieceLanes e D delta g l Z residueNegative lambda omega J (2 * B) C C +
      actualPieceLanes e D delta g l Z residueNegative lambda omega J (2 * B) (2 * C) C +
      actualPieceLanes e D delta g l Z residueNegative lambda omega J (2 * B) (4 * C) C := by
  have hp (M N : ℝ) (hM : 0 < M) :
      completedPiece (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega M N B C (scaleF e D g) =
      actualPieceLanes e D delta g l Z residueNegative lambda omega J M N C :=
    actual_completedPiece_eq_zero_add_primary_m_lanes
      e D delta g l Z residueNegative lambda omega hM J N B C
  have hB2 : 0 < 2 * B := by positivity
  rw [sixSmoothMass_eq_completed (g * l) (signedResidue residueNegative e.residue)
    (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
    lambda omega hB C (scaleF e D g)]
  rw [hp B C hB, hp B (2 * C) hB, hp B (4 * C) hB,
    hp (2 * B) C hB2, hp (2 * B) (2 * C) hB2, hp (2 * B) (4 * C) hB2]

end

end ImbalancedChen.Part3.ActualSmoothMassCommonLanes20261127
