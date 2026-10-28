import ImbalancedChen.P2CanonicalPairTentWarmHistory
import ImbalancedChen.P2OriginalPostFifthRoughSquares

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Actual accepted canonical warm words, including every short/inherited lane,
pay all full squares at their actual final cap. This does not adopt W:
it supplies the ORIGINAL full-vector input needed by a separate W rescue.
The initial pair and rough-head reserves are discharged from the original
L5/L6 selectors by the companion source, not assumed for an entire word. -/
namespace ImbalancedChen.P2CanonicalWarmAllRankSquareEnvelope
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2CanonicalPairTentWarmHistory P2OriginalPostFifthRoughSquares
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (prefixCode)
open P2OriginalLowerNestedBufferedStages (prefixCode_nested)

private theorem square_cap_mono {c d T : ℝ} (xs : List ℝ)
    (hcd : c ≤ d) (h : SquareGates c T xs) : SquareGates d T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨h.1.trans hcd,ih h.2⟩

private theorem append_square {c : ℝ} (xs : List ℝ) (x : ℝ)
    (h : SquareGates c 0 xs) (hx : xs.sum+2*x ≤ c) :
    SquareGates c 0 (xs++[x]) := by
  rw [squareGates_append_iff]
  exact ⟨h,by simpa [SquareGates] using hx⟩

private theorem code_three_four (R : PairRange) (mesh : ℕ) (x0 x1 x2 x3 : ℝ) :
    prefixCode 3 (codeAt R mesh 4 [x0,x1,x2,x3]) = codeAt R mesh 3 [x0,x1,x2] := by
  funext i
  fin_cases i <;> simp [codeAt,incomingCode,physicalCode,marked,prefixCode,exponentCode,ceiling]

private theorem code_four_five (R : PairRange) (mesh : ℕ) (x0 x1 x2 x3 x4 : ℝ) :
    prefixCode 4 (codeAt R mesh 5 [x0,x1,x2,x3,x4]) = codeAt R mesh 4 [x0,x1,x2,x3] := by
  funext i
  fin_cases i <;> simp [codeAt,incomingCode,physicalCode,marked,prefixCode,exponentCode,ceiling]

private theorem cap3_prefix (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed : ℝ) (code : P2OriginalLowerSelectedCapConstructor.Code mesh)
    (r : ℕ) (hr : 3 ≤ r) :
    cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
      (prefixCode r code) =
    cap3 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed code := by
  simp only [cap3,checkedCap,checkedChoice,prefixCode_nested 3 r hr]

private theorem cap4_prefix (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed : ℝ) (code : P2OriginalLowerSelectedCapConstructor.Code mesh) :
    cap4 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed
      (prefixCode 4 code) =
    cap4 R (P2OriginalCanonicalPairTentBank.bank R mesh buffer floor) buffer seed code := by
  unfold cap4
  rw [cap3_prefix R mesh buffer floor seed code 4 (by omega)]
  simp only [checkedCap,checkedChoice,prefixCode_nested 4 4 (le_refl _)]

/-- The actual first five states have monotone caps, with the rational
    bank floor distinct from the real incoming root. No ideal parent is read. -/
theorem warm_first_caps_mono (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 x2 x3 x4 : ℝ) :
    let P := warmPlan R mesh buffer floor seed
    let H2 : Trace := ⟨[x0,x1],seed,[],true⟩
    let H3 := run P R.epsilon ceiling H2 [x2]
    let H4 := run P R.epsilon ceiling H2 [x2,x3]
    let H5 := run P R.epsilon ceiling H2 [x2,x3,x4]
    seed ≤ H3.cap ∧ H3.cap ≤ H4.cap ∧ H4.cap ≤ H5.cap := by
  dsimp only
  let B := P2OriginalCanonicalPairTentBank.bank R mesh buffer floor
  let c3 := codeAt R mesh 3 [x0,x1,x2]
  let c4 := codeAt R mesh 4 [x0,x1,x2,x3]
  let c5 := codeAt R mesh 5 [x0,x1,x2,x3,x4]
  rw [warm_third_cap,warm_fourth_cap,pair_run_three_cap]
  have h34 : cap3 R B buffer seed c3 = cap3 R B buffer seed c4 := by
    rw [← code_three_four R mesh x0 x1 x2 x3]
    exact cap3_prefix R mesh buffer floor seed c4 3 (le_refl _)
  have h45 : cap4 R B buffer seed c4 = cap4 R B buffer seed c5 := by
    rw [← code_four_five R mesh x0 x1 x2 x3 x4]
    exact cap4_prefix R mesh buffer floor seed c5
  exact ⟨P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh buffer floor 3 c3 seed,
    h34.trans_le (P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh buffer floor 4 c4 _),
    h45.trans_le (P2OriginalCanonicalPairTentBank.checked_cap_mono R mesh buffer floor 5 c5 _)⟩

/-- All actual full squares, WITHOUT assuming a rough-support conclusion.
    At full rank3 the root head reserve pays the bypass; full rank4 has its
    actual cube; rank5 uses that cube and decreasing order. Later ranks
    use the already proved even-cube/odd-carry theorem. This includes every
    inherited cap and short word and never forces a fresh fifth source. -/
theorem accepted_warm_full_squares (R : PairRange) (mesh : ℕ) (buffer floor : ℚ)
    (seed x0 x1 ceilingR : ℝ)
    (hroot : SquareGates seed 0 [x0,x1]) (hhead : x0+x1+2*ceilingR ≤ seed)
    (xs : List ℝ) (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) (hceil : ∀ x ∈ xs, x ≤ ceilingR)
    (haccept : (run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ xs).accepted=true) :
    let H := run (warmPlan R mesh buffer floor seed) R.epsilon ceiling
      ⟨[x0,x1],seed,[],true⟩ xs
    SquareGates H.cap 0 H.word := by
  let P := warmPlan R mesh buffer floor seed
  let H2 : Trace := ⟨[x0,x1],seed,[],true⟩
  cases xs with
  | nil => exact hroot
  | cons x2 rest =>
      let H3 := run P R.epsilon ceiling H2 [x2]
      have hc := warm_first_caps_mono R mesh buffer floor seed x0 x1 x2 0 0
      have hseed3 : seed ≤ H3.cap := hc.1
      have h3 : SquareGates H3.cap 0 H3.word := by
        have hsquare : [x0,x1].sum+2*x2 ≤ seed := by
          have hu := hceil x2 (by simp)
          simp only [List.sum_cons,List.sum_nil,add_zero]
          linarith
        exact square_cap_mono _ hseed3 (append_square [x0,x1] x2 hroot hsquare)
      cases rest with
      | nil => exact h3
      | cons x3 rest =>
          let H4 := run P R.epsilon ceiling H2 [x2,x3]
          have h34 : H3.cap ≤ H4.cap :=
            (warm_first_caps_mono R mesh buffer floor seed x0 x1 x2 x3 0).2.1
          have h4acc : H4.accepted=true := by
            exact run_accepted_incoming P R.epsilon ceiling H4 rest haccept
          have hcube : H3.word.sum+3*x3 < H3.cap := by
            have hadm := ((step_accepted_iff P R.epsilon ceiling H3 x3).mp h4acc).2
            have hlen3 : H3.word.length=3 := rfl
            simpa only [admission,hlen3,show (3:ℕ)≠0 by omega,
              if_false,show ((3:ℕ)+1)%2=0 by rfl,if_true] using hadm
          have hx3 := hnonneg x3 (by simp)
          have h4 : SquareGates H4.cap 0 H4.word := by
            have hsquare : H3.word.sum+2*x3 ≤ H3.cap := by linarith
            exact square_cap_mono _ h34 (append_square H3.word x3 h3 hsquare)
          cases rest with
          | nil => exact h4
          | cons x4 tail =>
              let H5 := run P R.epsilon ceiling H2 [x2,x3,x4]
              have h45 : H4.cap ≤ H5.cap :=
                (warm_first_caps_mono R mesh buffer floor seed x0 x1 x2 x3 x4).2.2
              have hx43 : x4 ≤ x3 :=
                (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).1 x4 (by simp)
              have h5 : SquareGates H5.cap 0 H5.word := by
                have hsquare : H4.word.sum+2*x4 ≤ H4.cap := by
                  have hsum : H4.word.sum=H3.word.sum+x3 := by
                    simp [H4,H3,H2,run,step]
                  rw [hsum]
                  linarith
                exact square_cap_mono _ h45 (append_square H4.word x4 h4 hsquare)
              have hlen : H5.word.length=5 := rfl
              have htailacc : (run P R.epsilon ceiling H5 tail).accepted=true := haccept
              have htail0 : ∀ x ∈ tail, 0 ≤ x := by
                intro x hx
                exact hnonneg x (by simp [hx])
              have htailSort :=
                (List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2).2
              have htail := actual_postfive_suffix_squares P R.epsilon ceiling H5 hlen
                tail htailSort htail0 htailacc
              have hword := run_word P R.epsilon ceiling H5 tail
              have hcap := run_cap_after_five P R.epsilon ceiling H5 (by omega) tail
              change SquareGates (run P R.epsilon ceiling H5 tail).cap 0
                (run P R.epsilon ceiling H5 tail).word
              rw [hcap,hword,squareGates_append_iff]
              exact ⟨h5,by simpa using htail⟩

end
end ImbalancedChen.P2CanonicalWarmAllRankSquareEnvelope
