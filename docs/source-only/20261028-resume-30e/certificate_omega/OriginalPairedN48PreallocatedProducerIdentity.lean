import ImbalancedChen.OriginalPairedN48CanonicalArrays

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent fixed-length/preallocated translation of the original Python
Omega(8192) U loop.  This is not defined as the canonical prefix builder.
The update formula, initial allocation, and mutation order are explicit.
The proof connects their fields; it is not a recovered historical dump or
a proof of the Python interpreter/serializer or a successful finite run.
-/

namespace ImbalancedChen.OriginalPairedN48PreallocatedProducerIdentity

noncomputable section
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48CanonicalArrays

/-- Translation of the two original assignment branches.  The first
branch merely writes the original preallocated J(1) back to itself. -/
def originalLoopValue (u : List Token) (i : ℕ) : Token :=
  if i ≤ 2 * mesh then rational 1
  else if i ≤ 3 * mesh then
    sourceAdd (rational 1) (sourceSmallLog (((i - mesh : ℕ) : ℚ) / (mesh : ℚ)))
  else
    let j := i - mesh
    let left := sourceDiv ((u[j - 1]?).getD ⟨0, 0⟩)
      (rational (((j - 1 : ℕ) : ℚ) / (mesh : ℚ)))
    let right := sourceDiv ((u[j]?).getD ⟨0, 0⟩)
      (rational ((j : ℚ) / (mesh : ℚ)))
    sourceAdd
      (sourceAdd ((u[i - 1]?).getD ⟨0, 0⟩)
        (sourceDiv (sourceAdd left right) (rational (2 * (mesh : ℚ)))))
      ⟨-(rational (1 / (6 * (mesh : ℚ) ^ 3))).hi,
        (rational (1 / (6 * (mesh : ℚ) ^ 3))).hi⟩

/-- The original allocation has its FULL final length from the outset.
This construction uses replacement, unlike buildU's append recursion. -/
def preallocatedU : ℕ → List Token
  | 0 => List.replicate uCount (rational 1)
  | n + 1 =>
      let previous := preallocatedU n
      previous.set n (originalLoopValue previous n)

theorem preallocatedU_length (n : ℕ) : (preallocatedU n).length = uCount := by
  induction n with
  | zero => simp only [preallocatedU, List.length_replicate]
  | succ n ih => simpa only [preallocatedU, List.length_set] using ih

private theorem assignment_eq_nextU (n : ℕ)
    (hprefix : ∀ j : ℕ, j < n →
      (preallocatedU n)[j]? = (buildU n)[j]?) :
    originalLoopValue (preallocatedU n) n = nextU (buildU n) n := by
  unfold originalLoopValue nextU
  split_ifs with hfirst hsecond
  · rfl
  · rfl
  · have hm : 0 < mesh := by norm_num [mesh]
    have hprev : n - 1 < n := by omega
    have hleft : n - mesh - 1 < n := by omega
    have hright : n - mesh < n := by omega
    dsimp only [sourceStep, nodePayload, Uat, sourceErrorBand, sourceError]
    rw [hprefix (n - 1) hprev, hprefix (n - mesh - 1) hleft,
      hprefix (n - mesh) hright]

/-- Before the moving cursor, the preallocated program has exactly the
canonical prefix.  At/after it the untouched original J(1) values remain.
This invariant also proves that the original delayed reads see prior rows. -/
theorem preallocatedU_cursor (n j : ℕ) (hn : n ≤ uCount) (hj : j < uCount) :
    (preallocatedU n)[j]? =
      if j < n then (buildU n)[j]? else some (rational 1) := by
  induction n generalizing j with
  | zero => simp [preallocatedU, hj]
  | succ n ih =>
    have hnc : n < uCount := by omega
    have hprefix : ∀ k : ℕ, k < n →
        (preallocatedU n)[k]? = (buildU n)[k]? := by
      intro k hk
      have h := ih k (by omega) (by omega)
      simpa only [if_pos hk] using h
    have hv := assignment_eq_nextU n hprefix
    have hlen : n < (preallocatedU n).length := by rw [preallocatedU_length]; exact hnc
    change ((preallocatedU n).set n (originalLoopValue (preallocatedU n) n))[j]? = _
    by_cases he : j = n
    · subst j
      rw [List.getElem?_set_self hlen, if_pos (Nat.lt_succ_self n), buildU_last, hv]
    · rw [List.getElem?_set_ne (Ne.symm he)]
      by_cases hjn : j < n
      · rw [if_pos (show j < n + 1 by omega),
          buildU_lookup_stable n (n + 1) j hjn (by omega)]
        exact hprefix j hjn
      · rw [if_neg (by omega : ¬j < n + 1)]
        have h := ih j (by omega) hj
        simpa only [if_neg hjn] using h

/-- The extra initial sweep assignments are actual no-ops, matching the
original Python loop that starts only at index2*mesh+1. -/
theorem preallocated_initial_assignment_noop (n : ℕ)
    (hn : n ≤ 2 * mesh) (hnc : n < uCount) :
    preallocatedU (n + 1) = preallocatedU n := by
  have hcursor := preallocatedU_cursor n n hnc.le hnc
  rw [if_neg (Nat.lt_irrefl n)] at hcursor
  have hbound : n < (preallocatedU n).length := by rw [preallocatedU_length]; exact hnc
  have hget : (preallocatedU n)[n] = rational 1 := by
    rw [List.getElem?_eq_getElem hbound] at hcursor
    exact Option.some.inj hcursor
  change (preallocatedU n).set n (originalLoopValue (preallocatedU n) n) = preallocatedU n
  rw [show originalLoopValue (preallocatedU n) n = rational 1 by
    simp only [originalLoopValue, if_pos hn]]
  rw [← hget]
  exact List.set_getElem_self (by rw [preallocatedU_length]; exact hnc)

theorem preallocated_final_U_eq_canonical : preallocatedU uCount = canonicalU := by
  apply List.ext_getElem
  · rw [preallocatedU_length]
    exact (buildU_length uCount).symm
  · intro j hp hc
    have hj : j < uCount := by rw [← preallocatedU_length uCount]; exact hp
    have h := preallocatedU_cursor uCount j le_rfl hj
    rw [if_pos hj] at h
    simpa only [canonicalU, List.getElem?_eq_getElem hp,
      List.getElem?_eq_getElem hc, Option.some.injEq] using h

def originalFixedU : List Token := preallocatedU uCount

def originalFixedNodePayload : SourceArrays := nodePayload originalFixedU

def originalFixedCells : List ℤ :=
  (List.range cellCount).map (fun k => sourceCell originalFixedNodePayload k)

def originalFixedScanPayload : SourceArrays := ⟨originalFixedU, originalFixedCells, [], 0⟩

/-- Literal original max-scan fields after the preallocated producer.
They remain definitions, not asserted serialized/transient runtime output. -/
def originalFixedFields : SourceArrays :=
  ⟨originalFixedU, originalFixedCells, [], sourceQueryMax originalFixedScanPayload⟩

theorem original_fixed_U_identity : originalFixedFields.U = canonicalSourceArrays.U :=
  preallocated_final_U_eq_canonical

theorem original_fixed_cell_identity : originalFixedFields.cell = canonicalSourceArrays.cell := by
  simp only [originalFixedFields, originalFixedCells, originalFixedNodePayload,
    originalFixedU, preallocated_final_U_eq_canonical, canonicalSourceArrays,
    canonicalCells, canonicalNodePayload]

/-- An identity between independently defined preallocated/replacement and
prefix/append producer fields, proved without any finite checker premise. -/
theorem original_fixed_fields_identity : originalFixedFields = canonicalSourceArrays := by
  have hu := original_fixed_U_identity
  have hc := original_fixed_cell_identity
  have hq : originalFixedFields.queryMax = canonicalSourceArrays.queryMax := by
    change sourceQueryMax originalFixedScanPayload = sourceQueryMax canonicalScanPayload
    simpa only [sourceQueryMax, originalFixedScanPayload, canonicalScanPayload] using
      congrArg (fun cs : List ℤ =>
        ((cs.drop firstCell).take (lastCell - firstCell + 1)).foldl max 0) hc
  have hu0 : originalFixedU = canonicalU := hu
  have hc0 : originalFixedCells = canonicalCells := hc
  have hq0 : sourceQueryMax originalFixedScanPayload = sourceQueryMax canonicalScanPayload := hq
  change SourceArrays.mk originalFixedU originalFixedCells [] (sourceQueryMax originalFixedScanPayload) =
    SourceArrays.mk canonicalU canonicalCells [] (sourceQueryMax canonicalScanPayload)
  rw [hu0, hc0, hq0]

theorem original_fixed_query_numerator_identity :
    originalFixedFields.queryMax = canonicalQueryNumerator :=
  congrArg SourceArrays.queryMax original_fixed_fields_identity

end
end ImbalancedChen.OriginalPairedN48PreallocatedProducerIdentity
