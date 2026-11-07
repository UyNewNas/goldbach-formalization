import ImbalancedChen.SelectedPrefixRationalMesh

/-!
# Whole-box permits for the rational cap actually stored in a cell

The stored cap may be any rational strictly between the existing whole-box
lower and upper bounds.  The midpoint construction is a compatible special
case.  The soundness conclusions concern that stored cap itself, including
the complete and selected-subproduct square gates and the envelope gate.

A common rational mesh admits different masks, old caps, ceilings and new
caps on different selected cells.  Its Boolean checker explicitly traverses
the selected finset.  All these data precede the target.  The caller must
supply the actual inherited old value for each cell; this module does not
identify those fields with a historical policy or assert its coverage.
No own-cube admission, integral estimate or final numerical bound is a
condition of this finite permit interface.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open VariableEnvelope

/-- Check the supplied rational cap, independently of the automatic
midpoint.  Both endpoints are strict whole-box bounds. -/
def storedBoxCapCheck {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) : Bool :=
  decide (selectedCapLower I old hi < cap ∧ cap < selectedCapUpper I nu lo hi)

theorem storedBoxCapCheck_iff {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) :
    storedBoxCapCheck I old nu lo hi cap = true ↔
      selectedCapLower I old hi < cap ∧ cap < selectedCapUpper I nu lo hi := by
  simp only [storedBoxCapCheck, decide_eq_true_eq]

/-- The finite permit implies the strict comparison with the explicitly
supplied inherited cap, without assuming a midpoint identity. -/
theorem storedBoxCapCheck_old_lt {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true) : old < cap :=
  (selectedCapLower_old_le I old hi).trans_lt
    ((storedBoxCapCheck_iff I old nu lo hi cap).mp hc).1

/-- The already proved midpoint construction is accepted by the stored-cap
checker.  General users of the checker need no midpoint equality. -/
theorem storedBoxCapCheck_midpoint {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu lo hi = true) :
    storedBoxCapCheck I old nu lo hi (selectedBoxCap I old nu lo hi) = true :=
  (storedBoxCapCheck_iff I old nu lo hi _).mpr
    (selectedBoxCap_between I old nu lo hi hc)

/-- Every point of the closed box has all six licensing conclusions at
the actual stored cap.  The endpoint bounds use the existing finite
maximum, monotone square expressions and interval bound for the envelope. -/
theorem storedBoxCapCheck_sound {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (old : ℝ) < cap ∧ (cap : ℝ) < nu ∧ (1 / 2 : ℝ) < cap ∧
      (∀ j, prefixSquareExpr t j < cap) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < cap) ∧
      (cap : ℝ) < v (∑ i ∈ I, t i) := by
  have hb := (storedBoxCapCheck_iff I old nu lo hi cap).mp hc
  have hlow : (selectedCapLower I old hi : ℝ) < cap := by
    exact_mod_cast hb.1
  have hhigh : (cap : ℝ) < selectedCapUpper I nu lo hi := by
    exact_mod_cast hb.2
  have hold : (old : ℝ) ≤ selectedCapLower I old hi := by
    exact_mod_cast selectedCapLower_old_le I old hi
  have hhalf : (1 / 2 : ℝ) ≤ selectedCapLower I old hi := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr (selectedCapLower_half_le I old hi)
    push_cast at hh
    exact hh
  have htop : (selectedCapUpper I nu lo hi : ℝ) =
      min (nu : ℝ) (qVLo (∑ i ∈ I, lo i) (∑ i ∈ I, hi i) : ℝ) := by
    simp [selectedCapUpper]
  rw [htop] at hhigh
  refine ⟨hold.trans_lt hlow, hhigh.trans_le (min_le_left _ _), hhalf.trans_lt hlow,
    ?_, ?_, ?_⟩
  · intro j
    have hj : ((prefixSquareExpr hi j : ℚ) : ℝ) ≤ selectedCapLower I old hi := by
      exact_mod_cast selectedCapLower_prefix_le I old hi j
    rw [cast_prefixSquareExpr] at hj
    exact (prefixSquareExpr_mono hu j).trans_lt (hj.trans_lt hlow)
  · intro j hj
    have hg : ((selectedSquareExpr I hi j : ℚ) : ℝ) ≤ selectedCapLower I old hi := by
      exact_mod_cast selectedCapLower_selected_le I old hi j hj
    rw [cast_selectedSquareExpr] at hg
    exact (selectedSquareExpr_mono I hu j).trans_lt (hg.trans_lt hlow)
  · have hls : ((∑ i ∈ I, lo i : ℚ) : ℝ) ≤ ∑ i ∈ I, t i := by
      push_cast
      exact Finset.sum_le_sum (fun i _ => hl i)
    have hus : (∑ i ∈ I, t i) ≤ ((∑ i ∈ I, hi i : ℚ) : ℝ) := by
      push_cast
      exact Finset.sum_le_sum (fun i _ => hu i)
    exact (hhigh.trans_le (min_le_right _ _)).trans_le (qVLo_le_v hls hus)

/-- The stored cap licenses the exact natural prefix and selected square
products.  No replacement of the selected subproducts is made. -/
theorem storedBoxCapCheck_actual_square_gates {n : ℕ} (I : Finset (Fin n))
    (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ))
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ (cap : ℝ)) ∧
    (∀ j ∉ I, ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ (cap : ℝ)) := by
  have hg := storedBoxCapCheck_sound I old nu lo hi cap hc t hl hu
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hg.2.2.2.1 j),
    fun j hj => selectedSquareExpr_actual_gate I N hN p t hp j (hg.2.2.2.2.1 j hj)⟩

/-- Check only the selected mesh cells, with independently supplied
mask, inherited old cap, ceiling and stored new cap at every cell.
The outer decider does not enumerate the full cell-label function space. -/
def storedMeshCapCheck {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := J)
    (p := fun j _ => storedBoxCapCheck (I j) (old j) (nu j)
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) (cap j) = true))

theorem storedMeshCapCheck_iff {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) :
    storedMeshCapCheck a b m J I old nu cap = true ↔
      ∀ j ∈ J, storedBoxCapCheck (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) (cap j) = true := by
  simp only [storedMeshCapCheck, decide_eq_true_eq]

/-- Projection of the whole-box permits to the finite strict inherited
level comparisons.  Identifying `old j` with an actual ancestor remains
the responsibility of the caller. -/
theorem storedMeshCapCheck_old_lt {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true) :
    ∀ j ∈ J, old j < cap j := by
  intro j hj
  exact storedBoxCapCheck_old_lt (I j) (old j) (nu j) _ _ (cap j)
    ((storedMeshCapCheck_iff a b m J I old nu cap).mp hc j hj)

/-- The permit is valid at every point of the original half-open cell.
Only the upper membership inequality is weakened to apply the closed-box
soundness theorem; ownership itself retains its strict upper endpoint. -/
theorem storedMeshCapCheck_sound {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    (old j : ℝ) < cap j ∧ (cap j : ℝ) < nu j ∧ (1 / 2 : ℝ) < cap j ∧
      (∀ i, prefixSquareExpr t i < cap j) ∧
      (∀ i ∉ I j, selectedSquareExpr (I j) t i < cap j) ∧
      (cap j : ℝ) < v (∑ i ∈ I j, t i) := by
  have hcj := (storedMeshCapCheck_iff a b m J I old nu cap).mp hc j hj
  apply storedBoxCapCheck_sound (I j) (old j) (nu j) _ _ (cap j) hcj t
  · intro i
    rw [congrFun (cast_qLogPrimeMeshLo a b m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  · intro i
    rw [congrFun (cast_qLogPrimeMeshHi a b m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le

/-- Every selected cell supplies its own precise integer square-product
licenses at its stored cap.  The target and labels are introduced after
the fixed table and its finite check. -/
theorem storedMeshCapCheck_actual_square_gates {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j)
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ k, ((∏ i ∈ Finset.univ.filter (fun i => i < k), p i : ℕ) : ℝ) *
      (p k : ℝ) ^ 2 < N ^ (cap j : ℝ)) ∧
    (∀ k ∉ I j, ((∏ i ∈ I j, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < k ∧ i ∉ I j), p i : ℕ) : ℝ) *
        (p k : ℝ) ^ 2 < N ^ (cap j : ℝ)) := by
  have hg := storedMeshCapCheck_sound a b m J I old nu cap hc j hj t ht
  exact ⟨fun k => prefixSquareExpr_actual_gate N hN p t hp k (hg.2.2.2.1 k),
    fun k hk => selectedSquareExpr_actual_gate (I j) N hN p t hp k (hg.2.2.2.2.1 k hk)⟩

/-- Per-cell midpoint data produced by the existing checker can be
received without changing either checker or its licensing theorem. -/
theorem storedMeshCapCheck_of_selectedBoxCapChecks {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu : (Fin n → Fin (m + 1)) → ℚ)
    (hc : ∀ j ∈ J, selectedBoxCapCheck (I j) (old j) (nu j)
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    storedMeshCapCheck a b m J I old nu
      (fun j => selectedBoxCap (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j)) = true := by
  apply (storedMeshCapCheck_iff a b m J I old nu _).mpr
  intro j hj
  exact storedBoxCapCheck_midpoint (I j) (old j) (nu j) _ _ (hc j hj)

end

end ImbalancedChen
