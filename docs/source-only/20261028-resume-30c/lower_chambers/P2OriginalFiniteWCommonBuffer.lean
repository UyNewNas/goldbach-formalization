import ImbalancedChen.P2OriginalLocalWBoxMeshLicence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite strict-W box covers possess one positive rational buffer before N.
Shrinking both buffers preserves every original endpoint and winner gate;
the top-cap gate is proved again from the genuine positive third endpoint,
not from a monotonicity assertion in the wrong direction. No box endpoint,
actual parent, selected mark or chamber is moved by rebuffering.
-/

namespace ImbalancedChen.P2OriginalFiniteWCommonBuffer

noncomputable section
open scoped Classical
open Set
open P2PhysicalIncomingPrefixCells
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalStrictWLocalRationalCover
open P2OriginalLocalWBoxMeshLicence

-- All non-top endpoint slack inequalities improve when beta/delta shrink.
-- At the top endpoint the positive third coordinate gives the strict gap.
def rebuffer {S : CompactStart} {rho : ℝ} (Q : LocalWBox S rho)
    (beta delta : ℚ) (hb0 : 0 < beta) (hd0 : 0 < delta)
    (hb : beta ≤ Q.beta) (hd : delta ≤ Q.delta) : LocalWBox S rho :=
  { lo := Q.lo
    hi := Q.hi
    beta := beta
    delta := delta
    beta_pos := hb0
    delta_pos := hd0
    lo_lt_hi := Q.lo_lt_hi
    feasible := by
      have hbR : (beta : ℝ) ≤ Q.beta := by exact_mod_cast hb
      have hdR : (delta : ℝ) ≤ Q.delta := by exact_mod_cast hd
      have hb0R : (0 : ℝ) < beta := by exact_mod_cast hb0
      have hthird := Q.feasible.1 13
      have hlohi : (Q.lo 2 : ℝ) < Q.hi 2 := by exact_mod_cast Q.lo_lt_hi 2
      constructor
      · intro j
        have hold := Q.feasible.1 j
        fin_cases j <;>
          simp [geometricSlack, endpointCap, pack, B, Lambda, topCap] at * <;>
          linarith
      · intro I
        have hold := Q.feasible.2 I
        simp [winnerSlack, endpointCap, pack] at hold ⊢
        linarith }

@[simp] theorem rebuffer_interior {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) (beta delta : ℚ) (hb0 : 0 < beta) (hd0 : 0 < delta)
    (hb : beta ≤ Q.beta) (hd : delta ≤ Q.delta) :
    (rebuffer Q beta delta hb0 hd0 hb hd).interiorSet = Q.interiorSet := rfl

@[simp] theorem rebuffer_closed {S : CompactStart} {rho : ℝ}
    (Q : LocalWBox S rho) (beta delta : ℚ) (hb0 : 0 < beta) (hd0 : 0 < delta)
    (hb : beta ≤ Q.beta) (hd : delta ≤ Q.delta) :
    (rebuffer Q beta delta hb0 hd0 hb hd).closedSet = Q.closedSet := rfl

-- The family may be empty. In that case tau itself is a legitimate
-- positive choice; no min of an empty set or nonempty-cover premise occurs.
theorem finite_common_buffer {S : CompactStart} {rho : ℝ}
    (F : Finset (LocalWBox S rho)) (tau : ℚ) (htau : 0 < tau) :
    ∃ r : ℚ, 0 < r ∧ r ≤ tau ∧
      ∀ Q ∈ F, r ≤ Q.beta ∧ r ≤ Q.delta := by
  induction F using Finset.induction_on with
  | empty => exact ⟨tau, htau, le_rfl, by simp⟩
  | @insert Q F hnot ih =>
      obtain ⟨r, hr, hrtau, hF⟩ := ih
      refine ⟨min r (min Q.beta Q.delta),
        lt_min hr (lt_min Q.beta_pos Q.delta_pos), ?_, ?_⟩
      · exact (min_le_left _ _).trans hrtau
      · intro R hR
        rcases Finset.mem_insert.mp hR with hRQ | hRF
        · subst R
          exact ⟨(min_le_right _ _).trans (min_le_left _ _),
            (min_le_right _ _).trans (min_le_right _ _)⟩
        · exact ⟨(min_le_left _ _).trans (hF R hRF).1,
            (min_le_left _ _).trans (hF R hRF).2⟩

-- The actual common-buffer cover retains each original rational endpoint
-- exactly. Its finite index is the subtype of the previously constructed
-- finite cover, and all boxes now use beta=delta=r before any target N.
theorem compact_strict_chamber_common_buffer_cover
    (S : CompactStart) (rho : ℝ) (K : Set Point) (hK : IsCompact K)
    (hstrict : ∀ x ∈ K, StrictWPoint S rho x)
    (tau : ℚ) (htau : 0 < tau) :
    ∃ (F : Finset (LocalWBox S rho)) (r : ℚ)
      (R : {Q : LocalWBox S rho // Q ∈ F} → LocalWBox S rho),
      0 < r ∧ r ≤ tau ∧
      (∀ q, (R q).lo = q.val.lo ∧ (R q).hi = q.val.hi ∧
        (R q).beta = r ∧ (R q).delta = r) ∧
      K ⊆ ⋃ q, (R q).interiorSet := by
  obtain ⟨F, hcover⟩ := compact_strict_chamber_finite_cover S rho K hK hstrict
  obtain ⟨r, hr, hrtau, hF⟩ := finite_common_buffer F tau htau
  let R : {Q : LocalWBox S rho // Q ∈ F} → LocalWBox S rho := fun q =>
    rebuffer q.val r r hr hr (hF q.val q.property).1 (hF q.val q.property).2
  refine ⟨F, r, R, hr, hrtau, ?_, ?_⟩
  · intro q
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp (hcover hx)
    refine Set.mem_iUnion.mpr ⟨⟨Q, hQ⟩, ?_⟩
    simpa only [R, rebuffer_interior] using hxQ

-- The same common scalar supplies the existing original mesh licence;
-- this is not a new scalar checker or an assumed final lower estimate.
theorem rebuffered_actual_mesh_WBoxCheck (S : CompactStart) {rho : ℝ}
    (Q : LocalWBox S rho) (r : ℚ) (hr : 0 < r)
    (hb : r ≤ Q.beta) (hd : r ≤ Q.delta)
    {mesh : ℕ} (code : Code mesh) (href : CellRefines Q code)
    (hmarks : ∀ i : Fin 5, i.val < 3 → (code i).2 = false) :
    WBoxCheck S code rho r r := by
  let R := rebuffer Q r r hr hr hb hd
  have hRef : CellRefines R code := href
  exact refined_cell_WBoxCheck S R code hRef hmarks

end
end ImbalancedChen.P2OriginalFiniteWCommonBuffer
