import ImbalancedChen.P2InheritedFourthRaw31Embedding
import ImbalancedChen.P2ActualFifthCandidateBelowSixthRaw31

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.

This adapter assembles the actual rank-six pair12_fixed fifth parent domain.
Brun proves the selected third/fourth inherited seed bound, retaining W3
separately. SharpAP proves the actual fifth-row mask projection and finiteMax
bound through the two-branch raw31 tent. The results below apply those exact
source lemmas to a retained policy5 frontier state and identify its actual
rank-six test. The row-mask, support and carrier obligations stay explicit.
The lower guard H5 < fifth cap remains a separate source/data witness.
-/

namespace ImbalancedChen.P5Z.Pair12RetainedActualFifthPolicyBound

noncomputable section
open Classical
open scoped BigOperators
open P1OriginalVariableFifthContinuation
open P2OriginalFourthCapProducerInterface
open P1ThirdFallbackSupport
open Certificates.P2OriginalSixthElevenLogSemantics

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

def pair12Physical (pre : List ℕ) : Physical :=
  primeHistoryLogCoordinates N 6 pre

def pair12ActualFifthExponent (pre : List ℕ) : ℝ :=
  exponent5 e chi m omega N rows4 licensed4 J5 rows5
    (rosserAncestor 5 pre)

/-- The exact old pair12 cap is used only at its ascending winning mask.
Other fifth-row masks are bounded by SharpAP's full two-branch raw31 proof. -/
theorem pair12_oldCap_winner (pre : List ℕ)
    (hc : PhysicalCell .pair12_fixed (pair12Physical N pre)) :
    (pair12Physical N pre) 2 + (pair12Physical N pre) 3 < mu ∧
      oldCap .pair12_fixed (pair12Physical N pre) =
        (1 + (pair12Physical N pre) 2 +
          (pair12Physical N pre) 3) / 2 := by
  constructor
  · simpa only [winnerPlane, Cell.family] using hc.winner
  · rfl

/-- The previous sixth-node cap is the actual finiteMax fifth exponent
evaluated at its retained rank-five ancestor. -/
theorem pair12_actual_fifth_le_oldCap (pre : List ℕ)
    (hlen : pre.length = 6)
    (he : 0 ≤ e)
    (hc : PhysicalCell .pair12_fixed (pair12Physical N pre))
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hmask : ∀ r ∈ rows4, licensed4 r →
      (∑ i ∈ r.selected,
        (pair12Physical N pre) (i.castLE (by omega : 4 ≤ 6))) =
          subsetSum r.mask (pair12Physical N pre)) :
    pair12ActualFifthExponent e chi m omega N rows4 licensed4 J5 rows5 pre ≤
      oldCap .pair12_fixed (pair12Physical N pre) := by
  have hseed :=
    P2InheritedFourthRaw31Embedding.inherited_fourth_le_oldCap
      e chi m omega N rows4 licensed4 .pair12_fixed pre hlen hc
      he hs hgeometry hmask
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  exact P2ActualFifthCandidateBelowSixthRaw31.
    exponent5_le_sixth_oldCap_of_inherited4_le
      e chi m omega N rows4 licensed4 J5 rows5
      .pair12_fixed pre hlen heR hc hseed

theorem pair12_actual_fifth_level_le_oldLevel (pre : List ℕ)
    (hlen : pre.length = 6) (he : 0 ≤ e) (hN : 1 ≤ N)
    (hc : PhysicalCell .pair12_fixed (pair12Physical N pre))
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hmask : ∀ r ∈ rows4, licensed4 r →
      (∑ i ∈ r.selected,
        (pair12Physical N pre) (i.castLE (by omega : 4 ≤ 6))) =
          subsetSum r.mask (pair12Physical N pre)) :
    level5 e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 5 pre) ≤
      N ^ oldCap .pair12_fixed (pair12Physical N pre) := by
  exact Real.rpow_le_rpow_of_exponent_le hN
    (pair12_actual_fifth_le_oldCap e chi m omega N
      rows4 licensed4 J5 rows5 pre hlen he hc hs hgeometry hmask)

/-- `policy5` tests the rank-six prefix with its actual fifth-ancestor
level. This is the parent decision inherited by a rank-six splice. -/
theorem pair12_policy5_at_six (pre : List ℕ)
    (hlen : pre.length = 6) (positive : Bool) :
    policy5 e chi m omega N rows4 licensed4 J5 rows5 positive pre =
      ordinaryParityRosserPolicy false
        (level5 e chi m omega N rows4 licensed4 J5 rows5
          (rosserAncestor 5 pre)) positive pre := by
  have hfour : ¬ pre.length ≤ 4 := by omega
  simp only [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
    if_neg hfour, frozenParityRosserPolicy, ancestorFrozenPolicy]

/-- Membership in the actual policy5 rank-six frontier supplies the
rank-six length used by both the seed and fifth finite maxima. -/
theorem pair12_retained_state_parent_bound (Nnat cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 6
      (policy5 e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse Nnat cap w z))
    (he : 0 ≤ e)
    (hc : PhysicalCell .pair12_fixed
      (pair12Physical (Nnat : ℝ) state.selectedPrefix))
    (hs : supported (e : ℝ) chi m omega (Nnat : ℝ)
      (rosserAncestor 3 state.selectedPrefix))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hmask : ∀ r ∈ rows4, licensed4 r →
      (∑ i ∈ r.selected,
        (pair12Physical (Nnat : ℝ) state.selectedPrefix)
          (i.castLE (by omega : 4 ≤ 6))) =
        subsetSum r.mask
          (pair12Physical (Nnat : ℝ) state.selectedPrefix)) :
    pair12ActualFifthExponent e chi m omega (Nnat : ℝ)
        rows4 licensed4 J5 rows5 state.selectedPrefix ≤
      oldCap .pair12_fixed
        (pair12Physical (Nnat : ℝ) state.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 6
    (policy5 e chi m omega (Nnat : ℝ) rows4 licensed4 J5 rows5)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse Nnat cap w z) true 1 (by simp) state hstate
  exact pair12_actual_fifth_le_oldCap e chi m omega (Nnat : ℝ)
    rows4 licensed4 J5 rows5 state.selectedPrefix hlen he hc
    hs hgeometry hmask

end
end ImbalancedChen.P5Z.Pair12RetainedActualFifthPolicyBound
