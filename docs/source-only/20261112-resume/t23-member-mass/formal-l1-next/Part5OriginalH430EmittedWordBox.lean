import ImbalancedChen.Part5OriginalH430EmittedPathMultiplicity
import ImbalancedChen.Part5OriginalH430AbsoluteWordBox

/-! The shape and ordered arithmetic word determine the emitted code.
The positions summed below are the original rootHistory list positions. -/
namespace ImbalancedChen.Part5OriginalH430EmittedWordBox
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430IntegerItineraries Part5OriginalH430OwnedRootCounts
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OwnedMemberMass Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430EmittedPathMultiplicity Part5OriginalH430AbsoluteWordBox
open P2OriginalChildPhysicalNormalization

def letters {N : ℕ} (es : List (Edge N)) : List ℕ :=
  es.flatMap (fun e => appendedWord (edgeShape e) (edgePrimes e))

private def parse (s : StepShape) (w : List ℕ) : Letter × List ℕ :=
  match s with
  | .buchstabUpper | .buchstabLower | .w1Singleton _ _ | .w2Singleton _ _ =>
    ((s,w.headD 1,1),w.tail)
  | .w2Pair _ _ => ((s,w.tail.headD 1,w.headD 1),w.tail.tail)
  | _ => ((s,1,1),w)

def decode : List StepShape → List ℕ → List Letter
  | [], _ => []
  | s::ss, w => (parse s w).1 :: decode ss (parse s w).2

private theorem parse_edge {N : ℕ} (e : Edge N) (w : List ℕ) :
    parse (edgeShape e) (appendedWord (edgeShape e) (edgePrimes e) ++ w) = (letter e,w) := by
  cases e with
  | buchstab up p => cases up <;> rfl
  | _ => rfl

theorem decode_letters {N : ℕ} (es : List (Edge N)) :
    decode (es.map edgeShape) (letters es) = es.map letter := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change (parse _ (appendedWord _ _ ++ letters es)).1 ::
      decode (es.map edgeShape) (parse _ (appendedWord _ _ ++ letters es)).2 = _
    rw [parse_edge]
    exact congrArg (List.cons (letter e)) ih

private theorem replay_old {N : ℕ} (r : Request) (es : List (Edge N)) :
    (replay r es).old = r.old ++ letters es := by
  induction es generalizing r with
  | nil => simp [replay,letters]
  | cons e es ih => simpa only [replay,letters,List.flatMap_cons,nextRequest,List.append_assoc] using
      ih (nextRequest r e)

theorem occurrence_old {N n : ℕ} {k : Root} {tau : ℝ} {p : ℕ} {o : Occurrence N}
    (ho : o ∈ rootHistory N n k tau p) : o.current.old = p :: letters o.path := by
  rw [(history_facts ho).2.2,replay_old]
  rfl

def selectedWordMark {N : ℕ} (shapes : List StepShape) (w : List ℕ) :
    List (Occurrence N) → ℝ
  | [] => 0
  | o::os => (if o.path.map edgeShape = shapes ∧ o.current.old = w then mark o else 0) +
      selectedWordMark shapes w os

private theorem subsum {N : ℕ} (p : ℕ) (shapes : List StepShape) (w : List ℕ)
    (os : List (Occurrence N)) (h : ∀ o ∈ os, o.current.old = p :: letters o.path) :
    0 ≤ selectedWordMark shapes w os ∧
    selectedWordMark shapes w os ≤ fibreMark (decode shapes w.tail) os := by
  induction os with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | cons o os ih =>
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have ho := h o (List.mem_cons_self ..)
    rw [selectedWordMark,fibreMark]
    split_ifs with hs hk
    · exact ⟨add_nonneg (mark_pos o).le ht.1,add_le_add_left ht.2 _⟩
    · exfalso
      apply hk
      rw [← hs.1,← hs.2,ho]
      exact (decode_letters o.path).symm
    all_goals simp only [zero_add] <;> exact ⟨ht.1,by linarith only [ht.2, (mark_pos o).le]⟩

theorem actual_shape_word_mark {N n : ℕ} (k : Root) (tau : ℝ) (p : ℕ)
    (shapes : List StepShape) (w : List ℕ) :
    |selectedWordMark shapes w (rootHistory N n k tau p)| ≤ 1 := by
  have h := subsum p shapes w (rootHistory N n k tau p) (fun _ ho => occurrence_old ho)
  rw [abs_of_nonneg h.1]
  exact h.2.trans (rootHistory_itinerary_mass_le_one N n k tau p _)

private theorem bounded_path {N : ℕ} (hN : 1 ≤ N) (es : List (Edge N)) :
    ∀ i j, pathPrimes es i j ≤ N := by
  have hfin (p : Fin (N+1)) : p.val ≤ N := Nat.le_of_lt_succ p.isLt
  have hedge (e : Edge N) (j : Fin 2) : edgePrimes e j ≤ N := by
    cases e <;> fin_cases j <;> first | exact hN | exact hfin _
  induction es with
  | nil => intro i; exact Fin.elim0 i
  | cons e es ih => exact Fin.cases (hedge e) ih

/-- The existing rootHistory_catalog forgets the root tag and prime in its
existential conclusion. Use the same original pathCode and its bounded
prime coordinates to retain both fields of the actual owned fibre. -/
theorem emitted_owned_word {N n m : ℕ} (mesh : ℕ) {k : Root} {tau : ℝ} {p : ℕ}
    (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hf : p ∈ originalBand N k) {o : Occurrence N} (ho : o ∈ rootHistory N n k tau p) :
    ∃ h ∈ ownedMembers N n m mesh k tau (keyAt N n m k tau p), labelWord h = o.current.old := by
  have hp := original_band_prime hf
  have hb := original_band_geometry hN hf
  have hpN := prime_le_target (by omega : 1 < N) hp.1.pos ((rootBand_subset k hb).2.trans (by norm_num))
  have hlen := (history_facts ho).2.1
  let h : Label N mesh := ⟨⟨o.path.length,by omega⟩,k,⟨p,Nat.lt_succ_of_le hpN⟩,
    pathCode mesh o.path, fun i j => ⟨pathPrimes o.path i j,
      Nat.lt_succ_of_le (bounded_path (by omega : 1 ≤ N) o.path i j)⟩⟩
  refine ⟨h,mem_ownedMembers.mpr ⟨?_,rfl,Finset.mem_filter.mpr ⟨hf,rfl⟩⟩,
    (rootHistory_realization mesh ho).2⟩
  exact ⟨hp,hb,chosen_primeLetters mesh (root_coherent (by omega) ht ht' hn hp hb) (history_facts ho).1,
    path_canonical mesh o.path,rootHistory_member mesh (by omega) ht ht' hn hp hb ho⟩

def emittedTerm {r : ℕ} (N n m : ℕ) (k : Root) (tau : ℝ) (shapes : List StepShape)
    (v : Fin (r+1) → ℕ) : ℝ :=
  let p := v 0
  let c := keyAt N n m k tau p
  let ps := List.ofFn v
  let Q := cellQ N n c.1
  if p ∈ originalBand N k then
    selectedWordMark shapes ps (rootHistory N n k tau p) *
      |thetaAtom N Q ps.prod / singularNormalization N -
        (4/physicalLevel N Q ps)*primeBoxWord ps|
  else 0

private theorem selectedWordMark_zero {N : ℕ} (shapes : List StepShape) (w : List ℕ)
    (os : List (Occurrence N)) (h : ∀ o ∈ os, o.current.old ≠ w) :
    selectedWordMark shapes w os = 0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rw [selectedWordMark,if_neg (fun hs => h o (List.mem_cons_self ..) hs.2),zero_add]
    exact ih (fun q hq => h _ (List.mem_cons_of_mem _ hq))

/-- Actual root-band tests, deterministic history multiplicities, original
owner Q, and the W2 [larger,smaller] append order enter one absolute
arithmetic estimate. All word tests may vary with N, within the one
coefficient budget. -/
theorem uniform_emitted_box {r : ℕ} (a b : Fin (r+1) → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) {eps : ℝ} (heps : 0 < eps) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N → ∀ n m : ℕ, ∀ k : Root, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 → ∀ shapes : List StepShape,
      ∀ w : (Fin (r+1) → ℕ) → ℝ, (∀ v ∈ actualPrimeBoxTuples N a b, |w v| ≤ 1) →
      ∑ v ∈ actualPrimeBoxTuples N a b, |w v|*emittedTerm N n m k tau shapes v ≤ eps := by
  obtain ⟨T,hT⟩ := uniform_wordBox_normalization a b ha hab heps
  refine ⟨max 2 T,?_⟩
  intro N hN he n m k tau ht ht' hn shapes w hw
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have h := hT N ((le_max_right _ _).trans hN) he n m 0 k tau ht ht' hn w hw
  refine le_trans (Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) h
  let p := v 0
  let c := keyAt N n m k tau p
  let ps := List.ofFn v
  by_cases hf : p ∈ originalBand N k
  · by_cases hs : ∃ h ∈ ownedMembers N n m 0 k tau c, labelWord h = ps
    · rw [emittedTerm,if_pos hf,wordError,if_pos hs]
      exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
        (actual_shape_word_mark k tau p shapes ps)) (abs_nonneg _)).trans_eq (one_mul _)
    · have hz := selectedWordMark_zero shapes ps (rootHistory N n k tau p) (fun o ho hEq => by
        obtain ⟨label,hl,hw'⟩ := emitted_owned_word (m := m) 0 hN2 ht ht' hn hf ho
        exact hs ⟨label,hl,hw'.trans hEq⟩)
      rw [emittedTerm,if_pos hf,hz,zero_mul,wordError,if_neg hs]
  · rw [emittedTerm,if_neg hf]
    unfold wordError
    split_ifs <;> first | apply abs_nonneg | exact le_rfl

end
end ImbalancedChen.Part5OriginalH430EmittedWordBox

