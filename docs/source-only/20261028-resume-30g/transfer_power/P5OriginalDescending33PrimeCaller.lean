import ImbalancedChen.P5OriginalDescending33ActualOmission
import ImbalancedChen.P2OriginalSixthCompactArithmeticFibre
import ImbalancedChen.P1Pair12RetainedSignedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing original descending33 source is now read on the independent
actual target-deleted six-prime carrier, not just a formal real tuple.
It is disjoint from each of the independent original eleven tuple filters.
At every member history the CURRENT common sixth continuation equals its
actual fifth continuation on every descendant. The stopped signed tests,
including the original sign-sensitive beta attachment and COMPLETE-q AP
count-minus-exact-mean terminal, therefore agree identically.

This is a concrete current-STAGE omission, not a final rho or total-density
equality. No nonempty prime-history witness, full pattern classification,
archived simplex enclosure, earlier gain absorption or native Family is
assumed or proved. A complete full22 caller must still account for the
actual original descending action with the correct owner and parent.
-/
namespace ImbalancedChen.P5Z.OriginalDescending33PrimeCaller
noncomputable section
open Classical
open scoped BigOperators
open P5OriginalCommonRefinedConstructor
open Certificates.P2OriginalSixthElevenLogSemantics
open P1Pair12RetainedSignedSource
open ImbalancedChen.P5Z.OriginalDescending33ActualOmission

/-- The same original target-deleted carrier used by the independently
loaded eleven source, now filtered by the actual DESCENDING source rows. -/
def descendingTuples (pattern : Pattern) (N : ℕ) : Finset (Fin 6 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19/96 : ℝ))).filter
    (fun p => PhysicalSource pattern (actualPrimeTupleLog N p))

def sourceHistory (p : Fin 6 → ℕ) : List ℕ := [p 5,p 4,p 3,p 2,p 1,p 0]

theorem sourceHistory_length (p : Fin 6 → ℕ) : (sourceHistory p).length = 6 := rfl

theorem sourceHistory_log (N : ℕ) (p : Fin 6 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 6 (sourceHistory p) = actualPrimeTupleLog N p := by
  ext i
  fin_cases i <;> rfl

theorem descendingTuple_prime_target_deleted (pattern : Pattern) (N : ℕ)
    {p : Fin 6 → ℕ} (hp : p ∈ descendingTuples pattern N) :
    ∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N := by
  have h := mem_actualPrimeBoxTuples_iff.mp (Finset.mem_filter.mp hp).1
  exact fun i => ⟨(h i).1,(h i).2.1⟩

/-- Actual arithmetic source disjointness, for ALL eleven masks/families.
No change of tuple coordinates or unordered product image is made. -/
theorem descendingTuples_disjoint_each_originalEleven (pattern : Pattern) (N : ℕ) (c : Cell) :
    Disjoint (descendingTuples pattern N)
      (P2OriginalSixthCompactArithmeticFibre.originalTuples c N) := by
  apply Finset.disjoint_left.mpr
  intro p hp hc
  exact (Finset.mem_filter.mp hp).2.not_any_originalEleven_cell c
    (Finset.mem_filter.mp hc).2

theorem actual_descending_tuple_current_sixth_eq_parent
    (d : OriginalData) (pattern : Pattern) (N : ℕ) {p : Fin 6 → ℕ}
    (hp : p ∈ descendingTuples pattern N) :
    lambda6 d (N : ℝ) (sourceHistory p) = actualParent5 d (N : ℝ) (sourceHistory p) := by
  apply actual_constructor_sixth_eq_parent_on_descending_source d (N : ℝ) (sourceHistory p) pattern
  rw [sourceHistory_log]
  exact (Finset.mem_filter.mp hp).2

/-- Actual fifth/sixth policies agree on every descendant of THIS source
prefix. The sixth node itself is retained; beyond it the ancestor6 reads
its unchanged actual fifth cap and ancestor5 reads that SAME fifth parent. -/
theorem actual_sixth_fifth_descendant_policy_eq
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 6)
    (pattern : Pattern) (hsource : PhysicalSource pattern (primeHistoryLogCoordinates N 6 pre))
    (later : List ℕ) (positive : Bool) :
    policy6 d N positive (later++pre) = policy5 d N positive (later++pre) := by
  by_cases h6 : (later++pre).length ≤ 6
  · simp only [policy6,firstExitDepthSplicePolicy,if_pos h6]
  · have h4 : ¬(later++pre).length ≤ 4 := by simp only [List.length_append,hlen]; omega
    have ha6 : rosserAncestor 6 (later++pre) = pre := by
      rw [rosserAncestor_append 6 later pre (by omega),rosserAncestor_self_of_length 6 pre hlen]
    have ha5 : rosserAncestor 5 (later++pre) = rosserAncestor 5 pre :=
      rosserAncestor_append 5 later pre (by omega)
    have hlevel := actual_constructor_sixth_eq_parent_on_descending_source d N pre pattern hsource
    simp [policy6,policy5,firstExitDepthSplicePolicy,h6,h4,frozenParityRosserPolicy,
      ancestorFrozenPolicy,level6,level5,ha6,ha5,hlevel,actualParent5]

/-- A real nonmultiplicative complete-product terminal is transported
through the exact stopped recursion, without an analytic distribution or
density hypothesis and without replacing the signed small beta. -/
theorem actual_sixth_fifth_signed_source_eq
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 6)
    (pattern : Pattern) (hsource : PhysicalSource pattern (primeHistoryLogCoordinates N 6 pre))
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy6 d N) h T pre positive mass remaining =
      signedTest (policy5 d N) h T pre positive mass remaining := by
  have hrec : ∀ (remaining later : List ℕ) (positive : Bool) (mass : ℝ),
      signedTest (policy6 d N) h T (later++pre) positive mass remaining =
        signedTest (policy5 d N) h T (later++pre) positive mass remaining := by
    intro remaining
    induction remaining with
    | nil => intro later positive mass; rfl
    | cons p ps ih =>
      intro later positive mass
      have hp := actual_sixth_fifth_descendant_policy_eq d N pre hlen pattern hsource
        (p::later) (!positive)
      have hp' : policy6 d N (!positive) (p::(later++pre)) =
          policy5 d N (!positive) (p::(later++pre)) := hp
      simp only [signedTest]
      rw [ih later positive mass,hp']
      by_cases hk : policy5 d N (!positive) (p::(later++pre)) = true
      · simp only [if_pos hk]
        rw [ih (p::later) (!positive) (mass*h p)]
      · simp only [if_neg hk]
  simpa only [List.nil_append] using hrec remaining [] positive mass

/-- The actual original descending prime tuple reads the unchanged
current-stage FULL-q source with its original sign-sensitive small beta. -/
theorem actual_descending_tuple_same_fullq_test
    (d : OriginalData) (pattern : Pattern) (N cap mark : ℕ) {p : Fin 6 → ℕ}
    (hp : p ∈ descendingTuples pattern N) (w L : ℝ) (G : ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy6 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap mark w L G)
      (sourceHistory p) positive mass remaining =
    signedTest (policy5 d (N : ℝ)) (fun _ => 1) (attachedLeafTest N cap mark w L G)
      (sourceHistory p) positive mass remaining := by
  apply actual_sixth_fifth_signed_source_eq d (N : ℝ) (sourceHistory p) (sourceHistory_length p) pattern
  rw [sourceHistory_log]
  exact (Finset.mem_filter.mp hp).2

/-- Count and exact full-q coprime mean are the SAME terminal source;
this zero difference is not the whole final policy8 discrepancy. -/
theorem actual_descending_tuple_count_mean_sixth_change_zero
    (d : OriginalData) (pattern : Pattern) (N cap : ℕ) {p : Fin 6 → ℕ}
    (hp : p ∈ descendingTuples pattern N) (w L : ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy6 d (N : ℝ)) (fun _ => 1)
      (attachedLeafTest N cap 1 w L (fun q => chenPrimeAPCount N N q-exactCoprimeMean N q))
      (sourceHistory p) positive mass remaining -
    signedTest (policy5 d (N : ℝ)) (fun _ => 1)
      (attachedLeafTest N cap 1 w L (fun q => chenPrimeAPCount N N q-exactCoprimeMean N q))
      (sourceHistory p) positive mass remaining = 0 := by
  rw [actual_descending_tuple_same_fullq_test d pattern N cap 1 hp w L
    (fun q => chenPrimeAPCount N N q-exactCoprimeMean N q) positive mass remaining,sub_self]

end
end ImbalancedChen.P5Z.OriginalDescending33PrimeCaller
