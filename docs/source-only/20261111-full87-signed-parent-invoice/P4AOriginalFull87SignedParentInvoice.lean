import ImbalancedChen.P4AOriginalFull87ActualParentResidualGap
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No kernel or reserve credit.

The preceding exact residual parent-gap estimate is transported through
the ORIGINAL ordered, owned rank-eight occurrence lists, with the ORIGINAL
signed sixth continuation and sign-dependent full-modulus small beta.

This bounds a signed WEIGHTED RESIDUAL-MISMATCH PROXY, not the physical
Rosser saving. In particular the ordinary-continuation-to-residual mean,
primitive errors and same-H_N reserve payments remain separate obligations.
No new state, policy, beta, mass, owner, mask, or prime-supply assumption.
-/

namespace ImbalancedChen.P4AOriginalFull87SignedParentInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87SourceDictionary (Cell comparison total product)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87OwnedEighthSource
  (states_eq_owner_filter frontier frontier_length retainedOwner_some_iff)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelIntegration
  (actualParent actual_eighth_kernel_transport)
open P4AOriginalFull87EighthKernelControl (residual cutoff)
open P4AOriginalFull87ActualParentResidualGap (realized_parent_gap_budget)
open P4AOriginalFull87AllOwnedRealizedHistory
  (exists_shared_history_for_all_owned_eighth_states)

/-- Not a free signed coefficient. This is the ORIGINAL sixth-policy
continuation at the actual occurrence, using the same ordered remaining
rough carrier and the original sign-selected beta on each full-q leaf. -/
def actualSignedContinuation (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (sixthPolicy n e q om (N : ℝ)) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G)
    s.selectedPrefix s.positive s.mass s.remaining

/-- Exactly the comparison-minus-ACTUAL sixth parent for this original
rank-eight state; the original common fourth/fifth history is retained. -/
def actualParentGap (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  comparison c (primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix) -
    actualParent n e q om (N : ℝ) s.selectedPrefix

/-- Same finite eighth endpoint in both residuals. No extra rounding
or artificial signed-saving monotonicity term is inserted. -/
def actualResidualMismatch (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  let t := primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix
  let P := actualParent n e q om (N : ℝ) s.selectedPrefix
  let R := comparison c t
  let M := (finiteCap n c t : ℝ)
  residual (total t) (product t) P M - residual (total t) (product t) R M

/-- Signed proxy on the SAME original owned occurrence list, without a
Finset conversion, deduplication or change of the full-modulus terminal. -/
def ownedSignedMismatch (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) : ℝ :=
  ((states (width r) n e q om N cap w z (fun _ => 1) c).map
    (fun s => actualSignedContinuation n e q om N cap w L G s *
      actualResidualMismatch n e q om N c s)).sum

/-- The invoice retains EACH occurrence's true gap and the absolute
value of its own signed continuation, including the small beta. -/
def ownedGapInvoice (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) : ℝ :=
  ((states (width r) n e q om N cap w z (fun _ => 1) c).map
    (fun s => |actualSignedContinuation n e q om N cap w L G s| *
      actualParentGap n e q om N c s)).sum

/-- No geometric-zero argument: this is proved for a GENUINE owned
frontier state by extracting the old owner/strict trim and invoking the
earlier actual-parent transport on the same selected eight-prime word. -/
theorem owned_state_parent_mismatch_budget
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z : ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z (fun _ => 1) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    0 ≤ actualParentGap n e q om N c s ∧
      0 ≤ actualResidualMismatch n e q om N c s ∧
      actualResidualMismatch n e q om N c s ≤
        (4 / cutoff ^ 10) * actualParentGap n e q om N c s := by
  have hfiltered := hs
  rw [states_eq_owner_filter] at hfiltered
  have hfront : s ∈ frontier n e q om N cap w z :=
    (List.mem_filter.mp hfiltered).1
  have hlen : s.selectedPrefix.length = 8 :=
    frontier_length n e q om N cap w z s hfront
  have howner : P4AOriginalFull87OwnedEighthSource.retainedOwner
      (width r) (N : ℝ) s.selectedPrefix = some c :=
    of_decide_eq_true (List.mem_filter.mp hfiltered).2
  have htrim : point8 (N : ℝ) s.selectedPrefix ∈ trim c (width r) :=
    ((retainedOwner_some_iff (width r) (N : ℝ)
      s.selectedPrefix c).mp howner).2
  have ht : primeHistoryLogCoordinates (N : ℝ) 8
      s.selectedPrefix ∈ trim c (width r) := by
    simpa only [point8,
      rosserAncestor_self_of_length 8 s.selectedPrefix hlen] using htrim
  have htransport :=
    actual_eighth_kernel_transport r n hn e q om (N : ℝ)
      s.selectedPrefix hlen c ht hr
  dsimp only at htransport
  have hPR := htransport.2.2.1
  have hres := realized_parent_gap_budget
    r n hn e q om (N : ℝ) s.selectedPrefix hlen c ht hr
  dsimp only at hres
  dsimp [actualParentGap, actualResidualMismatch]
  exact ⟨sub_nonneg.mpr hPR, hres.1, hres.2⟩

/-- Finite LIST triangle inequality with an actual per-occurrence
nonnegative gap. Repeated occurrences are counted repeatedly. -/
private theorem list_signed_gap_invoice {α : Type*} (C : ℝ)
    (xs : List α) (f g h : α → ℝ)
    (ht : ∀ x ∈ xs, 0 ≤ g x ∧ g x ≤ C * h x) :
    |(xs.map (fun x => f x * g x)).sum| ≤
      C * (xs.map (fun x => |f x| * h x)).sum := by
  revert ht
  induction xs with
  | nil =>
    intro _
    simp
  | cons x xs ih =>
    intro ht
    have hx := ht x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ g y ∧ g y ≤ C * h y :=
      fun y hy => ht y (List.mem_cons_of_mem x hy)
    have hrec := ih htail
    have habs : |f x * g x| = |f x| * g x := by
      rw [abs_mul, abs_of_nonneg hx.1]
    have hhead : |f x| * g x ≤ C * (|f x| * h x) := by
      calc
        _ ≤ |f x| * (C * h x) :=
          mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
        _ = _ := by ring
    calc
      |((x :: xs).map (fun y => f y * g y)).sum| ≤
          |f x * g x| + |(xs.map (fun y => f y * g y)).sum| := by
            simpa only [List.map_cons, List.sum_cons] using
              abs_add (f x * g x) ((xs.map (fun y => f y * g y)).sum)
      _ ≤ C * (|f x| * h x) +
          C * (xs.map (fun y => |f y| * h y)).sum := by
            rw [habs]
            exact add_le_add hhead hrec
      _ = C * ((x :: xs).map (fun y => |f y| * h y)).sum := by
            simp only [List.map_cons, List.sum_cons]
            ring

/-- One invoice on the ORIGINAL eighty-seven owned occurrence lists.
The hypothesis is ONLY the previously constructed common RealizedHistory
supplier; the theorem below discharges it from that fixed-before-N result.
This is not an equality with the actual physical signed saving. -/
theorem full87_signed_parent_invoice_of_history
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ)
    (hh : ∀ c : Cell, ∀ s : FirstExitDepthState ℕ,
      s ∈ states (width r) n e q om N cap w z (fun _ => 1) c →
        RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    |∑ c : Cell, ownedSignedMismatch r n e q om N cap w z L G c| ≤
      (4 / cutoff ^ 10) *
        ∑ c : Cell, ownedGapInvoice r n e q om N cap w z L G c := by
  have hcell (c : Cell) :
      |ownedSignedMismatch r n e q om N cap w z L G c| ≤
        (4 / cutoff ^ 10) * ownedGapInvoice r n e q om N cap w z L G c := by
    unfold ownedSignedMismatch ownedGapInvoice
    apply list_signed_gap_invoice
    intro s hs
    have h := owned_state_parent_mismatch_budget
      r n hn e q om N cap w z c s hs (hh c s hs)
    exact ⟨h.2.1, h.2.2⟩
  calc
    |∑ c : Cell, ownedSignedMismatch r n e q om N cap w z L G c| ≤
        ∑ c : Cell, |ownedSignedMismatch r n e q om N cap w z L G c| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell, (4 / cutoff ^ 10) *
          ownedGapInvoice r n e q om N cap w z L G c :=
          Finset.sum_le_sum (fun c _ => hcell c)
    _ = (4 / cutoff ^ 10) *
          ∑ c : Cell, ownedGapInvoice r n e q om N cap w z L G c := by
          rw [Finset.mul_sum]

/-- One and the SAME original fourth/fifth history schedule before N,
then the original 87 owner/trim lists and full-q signed continuation.
No new RealizedHistory premise survives in this public conclusion. -/
theorem exists_shared_full87_signed_parent_invoice
    (r n : ℕ) (hn : 4 * width n < width r) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ om : ℝ, om ≤ (1 / 100 : ℝ) →
      ∀ N : ℕ, 1 < (N : ℝ) →
      ∀ cap : ℕ, ∀ w z L : ℝ, ∀ G : ℕ → ℝ,
        |∑ c : Cell, ownedSignedMismatch r n e q om N cap w z L G c| ≤
          (4 / cutoff ^ 10) *
            ∑ c : Cell, ownedGapInvoice r n e q om N cap w z L G c := by
  obtain ⟨e0, he0, hchoose⟩ :=
    exists_shared_history_for_all_owned_eighth_states r
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0, hq0, hfor⟩ := hchoose e he hee
  refine ⟨q0, hq0, ?_⟩
  intro q hq om hom N hN cap w z L G
  apply full87_signed_parent_invoice_of_history
    r n hn e q om N cap w z L G
  intro c s hs
  exact hfor q hq om hom N hN n cap w z c s hs

end
end ImbalancedChen.P4AOriginalFull87SignedParentInvoice
