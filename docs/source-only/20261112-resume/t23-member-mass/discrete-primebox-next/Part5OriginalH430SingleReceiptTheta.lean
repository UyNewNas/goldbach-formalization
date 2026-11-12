import ImbalancedChen.Part5OriginalH430FullPrimeTheta
import ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback

namespace ImbalancedChen.Part5OriginalH430SingleReceiptTheta
noncomputable section
open Set Filter Topology
open scoped Classical
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph P2FrozenReceiverCountActions
open P2EnhancedLowerPrimeChildCarriers Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430NativeQueryPaths
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootMass
open Part5OriginalH430FixedProgramL1 Part5OriginalH430EmittedWordBox
open Part5OriginalH430PrimeProgramWord Part5OriginalH430DiscreteThetaTransport Part5OriginalH430FullPrimeTheta
open Part5OriginalUpsilon5CausalDictionary (FloorAtom)

/-- Filter the actual original history by one specified additive prime's
congruence and rough quotient receipt. Every position keeps its real
integer word, its own original member cutoff, and this root fibre's Q. -/
def probe {N : ℕ} (rootP ell : ℕ) (Q : ℝ) (ss : List StepShape) (word : List ℕ) :
    List (Occurrence N) → ℝ
  | [] => 0
  | o :: os =>
      (if (o.path.map edgeShape = ss ∧ o.current.old = word) ∧
          ell ∈ frozenCarrier N (parentProduct o.current.old) (rootMask N rootP) (memberCutoff Q o)
        then mark o else 0) + probe rootP ell Q ss word os

theorem probe_le {N : ℕ} (rootP ell : ℕ) (Q : ℝ) (ss : List StepShape) (word : List ℕ)
    (os : List (Occurrence N)) :
    0 ≤ probe rootP ell Q ss word os ∧ probe rootP ell Q ss word os ≤ selectedWordMark ss word os := by
  induction os with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | cons o os ih =>
    let P := o.path.map edgeShape = ss ∧ o.current.old = word
    let R := ell ∈ frozenCarrier N (parentProduct o.current.old) (rootMask N rootP) (memberCutoff Q o)
    have hterm : 0 ≤ (if P ∧ R then mark o else 0) ∧
        (if P ∧ R then mark o else 0) ≤ (if P then mark o else 0) := by
      by_cases hp : P <;> by_cases hr : R <;> simp [hp,hr,(mark_pos o).le]
    exact ⟨add_nonneg hterm.1 ih.1,add_le_add hterm.2 ih.2⟩

def receiptMark {d mesh r : ℕ} (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (ell : ℕ) (p : Fin r → ℕ) : ℝ :=
  let rootP := p (e.symm (.inl ()))
  let Q := cellQ N n (keyAt N n m k (finiteTau n) rootP).1
  probe rootP ell Q (List.ofFn (shapes code)) (originalWord code e p) (rootHistory N n k (finiteTau n) rootP)

theorem receiptMark_le_one {d mesh r : ℕ} (N n m : ℕ) (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (ell : ℕ) (p : Fin r → ℕ) :
    |receiptMark N n m k code e ell p| ≤ 1 := by
  unfold receiptMark
  dsimp only
  have h := probe_le (p (e.symm (.inl ()))) ell
    (cellQ N n (keyAt N n m k (finiteTau n) (p (e.symm (.inl ())))).1)
    (List.ofFn (shapes code)) (originalWord code e p) (rootHistory N n k (finiteTau n) (p (e.symm (.inl ()))))
  exact (abs_of_nonneg h.1).le.trans (h.2.trans
    ((le_abs_self _).trans (actual_shape_word_mark k (finiteTau n) _ _ _)))

/-- Every individual receipt and all root tuple partitions share the
threshold. Both geometries use the same actual frozen occurrence mark. -/
theorem all_single_receipt_threshold (mesh : ℕ) {eps : ℝ} (he : 0 < eps) :
    ∃ T : ℕ, ∀ n ≥ T, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ v : Programs mesh, ∀ k : Root,
      ∀ lower : Bool, ∀ atom : FloorAtom, ∀ m ell : ℕ,
      markedError N n 0 k v.2 (order v.2) lower atom (receiptMark N n m k v.2 (order v.2) ell) < eps := by
  obtain ⟨T,hT⟩ := all_program_arithmetic_threshold mesh he
  refine ⟨T,fun n hn => ?_⟩
  obtain ⟨N₀,hN⟩ := hT n hn
  exact ⟨N₀,fun N hn v k lower atom m ell =>
    hN N hn v k lower atom _ (fun p _ => receiptMark_le_one N n m k v.2 (order v.2) ell p)⟩

end
end ImbalancedChen.Part5OriginalH430SingleReceiptTheta
