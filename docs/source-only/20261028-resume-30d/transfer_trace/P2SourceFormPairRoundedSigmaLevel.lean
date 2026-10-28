import ImbalancedChen.P2ActualPairPlanRawSupport
import ImbalancedChen.P2OriginalPairSourceReceiver

/-!
# The marked SourceForm receiver supplies the rounded paired sigma level

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This consumes the NEW eps..D pair receiver, its actual parameterized seed,
and its checked SourceForm bank. It does not replace the external L6 pair by
the ordinary eps..a/h receiver or reset its root to baselineCap. The finite
fresh-cap theorem supplies the only plan ceiling needed by the raw support
proof. The returned rounded U6 data feed the unchanged native U10/U11 ledger.

Full original bank coverage, W arithmetic licensing and the seed's original
parent provenance are not inferred from the cap bound. No density convergence
or signed PP estimate is asserted by these arithmetic support conclusions.
-/

namespace ImbalancedChen.P2SourceFormPairRoundedSigmaLevel

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2ActualPairPlanRawSupport P5SelectedMaskTransport

/-- The exact new marked-pair receiver proves its finite plan cap check. -/
theorem sourceform_pair_ceiling (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (seed : ℝ) :
    PlanCeiling (pairPlan R bank buffer seed) topCap := by
  intro rank code incoming hi
  exact pairPlan_fresh_cap_bound R bank buffer seed rank code incoming hi

/-- Actual SourceForm receiver, actual external pair seed, no raw modulus
or rank hypothesis. The original U6 pair and positive rough exponent supply
all remaining arithmetic facts. -/
theorem sourceform_pair_raw_support (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (seed : ℝ) (hseed : seed ≤ topCap)
    {N : ℕ} (hN : 1 < (N : ℝ)) (enum : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ sixthSupport N) (omega : ℝ) (homega : 0 < omega) {r : ℕ}
    (hr : r ∈ P2LowerFiniteCellRounding.rawSupport
      (pairPolicy (pairPlan R bank buffer seed) (R.epsilon : ℝ) (ceiling : ℝ) seed N p)
      N enum ((N : ℝ) ^ omega) ((N : ℝ) ^ (417 / 5000 : ℝ))) :
    (((p.1 * p.2) * r : ℕ) : ℝ) ≤ (N : ℝ) ^ topCap ∧
      r.primeFactorsList.length ≤ Nat.ceil (topCap / omega) := by
  exact actual_pair_raw_full_prefix_rank (pairPlan R bank buffer seed)
    (sourceform_pair_ceiling R bank buffer seed) (R.epsilon : ℝ) (ceiling : ℝ)
    seed hseed hN enum hp omega homega hr

/-- This is the same rounded coefficient constructor as the previous
paired-ledger module. Every pair retains its own original stored seed. -/
def roundedData (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (seeds : ℕ × ℕ → ℝ) (N : ℕ) (omega ell tau : ℝ) :
    P2RoundedU6NativeJointLedger.RoundedLowerData where
  policy := fun p => pairPolicy (pairPlan R bank buffer (seeds p))
    (R.epsilon : ℝ) (ceiling : ℝ) (seeds p) N p
  w := fun _ => (N : ℝ) ^ omega
  L := fun _ => (N : ℝ) ^ ell
  mesh := fun _ => tau

/-- A single pre-N mesh supplies the actual same-sigma physical exponent
for the rounded marked-pair source and the original native negative bands.
Neither raw support/rank nor an aggregate unit coefficient bound is a premise. -/
theorem exists_sourceform_rounded_joint_sigma_level
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (omega ell nu : ℝ) (homega : 0 < omega) (hell : 0 ≤ ell)
    (hgap : topCap + ell < nu) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ (n N : ℕ), 1 < N → ∀ eta : ℚ, 0 < eta →
      ∀ (E : ℕ × ℕ → Prop) (seeds : ℕ × ℕ → ℝ),
      (∀ p ∈ P2RoundedU6NativeJointLedger.lowerRows N E, seeds p ≤ topCap) →
      ∀ q : ℕ,
      P2RoundedU6NativeJointLedger.sigma
        (roundedData R bank buffer seeds N omega ell tau) n N eta E q ≠ 0 →
      (q : ℝ) ≤ (N : ℝ) ^ nu := by
  let rank : ℕ := Nat.ceil (topCap / omega)
  let tau : ℝ := (nu - (topCap + ell)) / ((rank : ℝ) + 1)
  have htau : 0 < tau := by
    dsimp [tau]
    exact div_pos (sub_pos.mpr hgap) (by positivity)
  have hbudget : topCap + ell + (rank : ℝ) * tau ≤ nu := by
    have heq : tau * ((rank : ℝ) + 1) = nu - (topCap + ell) := by
      dsimp [tau]
      field_simp [show (rank : ℝ) + 1 ≠ 0 by positivity]
    nlinarith
  refine ⟨tau, htau, ?_⟩
  intro n N hN eta heta E seeds hseeds q hq
  have hNR : 1 < (N : ℝ) := by exact_mod_cast hN
  apply P2RoundedCausalFibreLossAndLevel.rounded_joint_sigma_physical_level
    (roundedData R bank buffer seeds N omega ell tau) hN heta E topCap ell nu rank
    (by change topCap ≤ nu; linarith) ?_ ?_ hq
  · intro p hp
    exact ⟨htau, rfl, hbudget⟩
  · intro p hp r hr
    exact sourceform_pair_raw_support R bank buffer (seeds p) (hseeds p hp) hNR
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (Finset.mem_filter.mp hp).1 omega homega hr

end
end ImbalancedChen.P2SourceFormPairRoundedSigmaLevel
