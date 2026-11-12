import ImbalancedChen.Part5OriginalH430EmittedNativeQueries
import ImbalancedChen.Part5OriginalH430RequestedNonbankSupply
import ImbalancedChen.RenewalFiniteErrorPropagationP5

/-! Pre-N row budget on the very same native chart as the query brackets.
Start from the uniform *individual generated feedback-row* results, not a
selected-family estimate filtered a second time. No hLower or closed-cell
soundness hypothesis. This pays only the arithmetic feedback discrepancy.
Source only / no formal credit. -/
namespace ImbalancedChen.Part5OriginalH430RefinedFeedbackBudget
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas Part5OriginalH430EmittedNativeQueries
open Part5OriginalH430NativeQueryPaths Part5OriginalH430SmoothPrefixRequests
open P2EnhancedLowerPrimeChildCarriers P2OriginalChildPhysicalNormalization
open P2Selected430CausalOccurrenceExporter P5OriginalActionMassBound
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430RequestedLocalBankSupply
open Part5OriginalH430RequestedNonbankSupply Part5OriginalH430BankSlotTargets
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430PhysicalRoots
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFeedbackQuotientRemainders Part5OriginalH430ActualNextTableThetaFloorBridge
open Part5OriginalUpsilon5CausalDictionary (floorValue)

inductive Paid where | bank (k : Fin 106) | buchstab
def prize : Paid → ℝ | .bank _ => 12 | .buchstab => 5
def winner : Paid → Choice | .bank k => .bank k | .buchstab => .buchstab

def gap (N : ℕ) (Q : ℝ) (r : Request) (g : Fin 430) : Paid → ℝ
  | .bank k => requestError N Q r g (actionOfSlot k)
  | .buchstab => ∑ b : RowAtom,
      |edgeRow Q r (children N Q g.val r) b - thetaAtom N Q (parentProduct r.old) *
          Part5OriginalBuchstabActualRowLimits.integralRow r.node.upper r.node.physical b| *
        |oldAtomValue (precedingH g) (precedingh g) b|

theorem gap_nonneg (N : ℕ) (Q : ℝ) (r : Request) (g : Fin 430) (a : Paid) :
    0 ≤ gap N Q r g a := by
  cases a with
  | bank k => exact requestError_nonneg _ _ _ _ _
  | buchstab => exact Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

def nativeMark {N : ℕ} (A : Plan) (p : ℕ) (o : Occurrence N)
    (j : NativeSlot (shapes o.path) → Code A) : ℝ := atom A j (tuple p o.path) * mark o

theorem nativeMark_nonneg {N : ℕ} (A : Plan) (p : ℕ) (o : Occurrence N)
    (j : NativeSlot (shapes o.path) → Code A) : 0 ≤ nativeMark A p o j :=
  mul_nonneg (atom_nonneg _ _ _) (mark_pos _).le

/-- Retention is a zero-new-slot read of its specified old cell, even when a
scalar owner moves between the two generations. Exterior reads stop exactly. -/
theorem unchanged_retained {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200}
    (h : Selected g r i .retained) (w : ℝ) :
    w*edgeValue Q (iterate g) r (children N Q g r) =
      w*(thetaAtom N Q (parentProduct r.old)*floorValue (iterate g r.node.upper) i) := by
  rw [requested_retained_children_value h]

theorem unchanged_exterior {N g : ℕ} {Q : ℝ} {r : Request}
    (h : resolve (g+1) r = none) (w : ℝ) :
    children N Q g r = [] ∧ w*requestValue (iterate (g+1)) r = 0 := by
  obtain ⟨hc,hv⟩ := exterior_children_empty (N := N) (Q := Q) h
  exact ⟨hc,by rw [hv,mul_zero]⟩

def FeedbackAt (T : ℕ) (delta : ℝ) : Prop :=
  ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ k : Root, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
  1/((n:ℝ)+1) ≤ 11/384 → ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
  physicalPrime N p ∈ rootBand k → ∀ g : Fin 430, ∀ l : Index N n k tau p g,
  ∀ i : Fin 200, ∀ a : Paid, Selected g.val (levelOccurrence l).current i (winner a) →
  ∀ A : Plan, ∀ j : NativeSlot (shapes (levelOccurrence l).path) → Code A,
    let o := levelOccurrence l
    let Q := rootQ N n k tau p
    let w := nativeMark A p o j
    let θ := thetaAtom N Q (parentProduct o.current.old)
    let row := edgeRow Q o.current (children N Q g.val o.current)
    w * gap N Q o.current g a ≤ delta * (w*θ) ∧
      (∀ b : RowAtom, 0 ≤ w * row b) ∧
      (∑ b : RowAtom, w * row b) ≤ prize a * (w*θ) ∧
      (w*θ = 0 → w * gap N Q o.current g a = 0 ∧ ∀ b : RowAtom, w * row b = 0)

/-- One threshold across ALL prechosen plans, positions (whose population
varies with N), 430 predecessors and both actual feedback winner kinds. -/
theorem uniform_feedback {delta : ℝ} (hd : 0 < delta) :
    ∃ T : ℕ, 4 ≤ T ∧ FeedbackAt T delta := by
  obtain ⟨TB,hB,hbank⟩ := uniform_requested_bank_local hd
  obtain ⟨TU,hU,hbuch⟩ := uniform_requested_buchstab_local hd
  refine ⟨max TB TU,hB.trans (le_max_left _ _),?_⟩
  intro N hN n k tau ht ht' hn p hp hb g l i a ha A j
  let o := levelOccurrence l
  let Q := rootQ N n k tau p
  let w := nativeMark A p o j
  let θ := thetaAtom N Q (parentProduct o.current.old)
  let row := edgeRow Q o.current (children N Q g.val o.current)
  have hw : 0 ≤ w := nativeMark_nonneg _ _ _ _
  have hN1 : 1 < N := by omega
  have hc := rootHistory_coherent hN1 ht ht' hn hp hb (levelOccurrence_source l).1
  have hs := rootHistory_support hN1 ht ht' hn hp hb (levelOccurrence_source l).1
  have hlocal : gap N Q o.current g a ≤ delta * θ ∧
      (∀ b : RowAtom, 0 ≤ row b) ∧ (∑ b : RowAtom, row b) ≤ prize a * θ := by
    cases a with
    | bank bank =>
      have h := hbank N ((le_max_left _ _).trans hN) Q o.current g i bank
        hc ha hs.2.2.1 hs.2.2.2.2.1
      exact ⟨h.1,h.2.1,h.2.2.1⟩
    | buchstab =>
      exact hbuch N ((le_max_right _ _).trans hN) Q o.current g i hc ha hs.2.2.1
  have hg : w * gap N Q o.current g a ≤ delta * (w*θ) := by
    calc
      _ ≤ w * (delta * θ) := mul_le_mul_of_nonneg_left hlocal.1 hw
      _ = _ := by ring
  have hr (b : RowAtom) : 0 ≤ w * row b := mul_nonneg hw (hlocal.2.1 b)
  have hm : (∑ b : RowAtom, w * row b) ≤ prize a * (w*θ) := by
    rw [← Finset.mul_sum]
    calc
      _ ≤ w * (prize a * θ) := mul_le_mul_of_nonneg_left hlocal.2.2 hw
      _ = _ := by ring
  refine ⟨hg,hr,hm,?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz,mul_zero] using hg) (mul_nonneg hw (gap_nonneg _ _ _ _ _))
  · intro b
    have h := (Finset.single_le_sum (f := fun c => w * row c)
      (fun c _ => hr c) (Finset.mem_univ b)).trans hm
    exact le_antisymm (by simpa only [hz,mul_zero] using h) (hr b)

/-- Every native mask uses the same positive mark and the exact same signed
base/floor/Theta summands. This operates in native (small,large) coordinates,
so no chronological/small-large label identification is necessary here. -/
def splitNative (A : Plan) {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {g : Fin 430}
    (S : Finset (Index N n k tau p g)) (f : Index N n k tau p g → ℝ) : ℝ :=
  ∑ l ∈ S, ∑ j : NativeSlot (shapes (levelOccurrence l).path) → Code A,
    atom A j (tuple p (levelOccurrence l).path) * f l

theorem splitNative_exact (A : Plan) {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {g : Fin 430}
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand k)
    (S : Finset (Index N n k tau p g)) (f : Index N n k tau p g → ℝ) :
    splitNative A S f = ∑ l ∈ S, f l := by
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, atom_total A (emitted_cube hN ht ht' hn hp hb (levelOccurrence_source l).1),one_mul]

theorem native_base_floor_theta (A : Plan) {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ}
    (g : Fin 430) (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N) (hb : physicalPrime N p ∈ rootBand k) :
    (∑ a : Original106Action, splitNative A (selectedLevel N n k tau p g a)
      (fun l => occurrenceScale N n k tau p g l * baseValue a)) = selectedBankBaseMass N n k tau p g ∧
    (∑ a : Original106Action, splitNative A (selectedLevel N n k tau p g a)
      (fun l => occurrenceScale N n k tau p g l * feedbackRoundingLoss (iterate g.val) a)) =
        selectedBankRoundingLoss N n k tau p g ∧
    splitNative A (Finset.univ : Finset (Index N n k tau p g))
      (fun l => levelMark l * ((occurrenceTheta N n k tau p g l - 1) *
        requestValue (iterate (g.val+1)) (levelOccurrence l).current)) =
        actualThetaReadCorrection N n k tau p g := by
  have hs := splitNative_exact (g := g) A hN ht ht' hn hp hb
  exact ⟨Finset.sum_congr rfl (fun a _ => hs _ _),Finset.sum_congr rfl (fun a _ => hs _ _),hs _ _⟩

/-- Reserve first, then local accuracy, a genuine chart of small diameter,
then an arithmetic threshold. This threshold is for FeedbackAt only. -/
theorem reserve_mesh_feedback {reserve deltaMax : ℝ} (hr : 0 < reserve) (hd : 0 < deltaMax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < deltaMax ∧
      (7/2:ℝ) * (delta * (((12:ℝ)^441-1)/11)) < reserve ∧
      ∃ m : ℕ, (∀ (j : Code (.mesh m)) (x y : ℝ),
          mask (.mesh m) j x ≠ 0 → mask (.mesh m) j y ≠ 0 → |x-y| < delta) ∧
        ∃ T : ℕ, 4 ≤ T ∧ FeedbackAt T delta := by
  obtain ⟨d,hpos,hmax,hbudget⟩ := P5RenewalFiniteError.exists_local_reserve reserve deltaMax hr hd
  obtain ⟨m,hm⟩ := choose_fine_mesh hpos
  exact ⟨d,hpos,hmax,hbudget,m,hm,uniform_feedback hpos⟩

end
end ImbalancedChen.Part5OriginalH430RefinedFeedbackBudget
