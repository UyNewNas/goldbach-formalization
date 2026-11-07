import ImbalancedChen.P4AOriginalRankThreeRestorationSource
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Coverage for the ACTUAL HistoricalThirdCoarse grid, whose selected CLOSED
rectangles must be wholly ordered.  The different ordered-portions dyadic
policy is not substituted for it.  Half-open ownership is unchanged.

An unselected point in the ambient cube is confined to two explicit order
strips or the actual first-stop strip.  On an actual historical parent the
first-stop strip disappears: its already-frozen first label has passed the
same upper-endpoint test.  Disabled small thirds remain a separate branch.
The statements below are pointwise arithmetic-source geometry, not an
assertion that these strips or the small-third source have small density.
-/

namespace ImbalancedChen.P4ACatalogFiveHistoricalCoverage
noncomputable section
open scoped Classical
open Set Filter Topology VariableEnvelope HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P4AOriginalCausalHistory P4AOriginalRankThreeRestorationSource

def meshStep (m : ℕ) : ℝ := logPrimeMeshStep 0 (19 / 96) m

theorem meshStep_pos (m : ℕ) : 0 < meshStep m :=
  logPrimeMeshStep_pos (by norm_num) m

private theorem box_coordinate_width (m : ℕ) (j : Cell m) (i : Fin 3) :
    (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) -
      (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) = meshStep m := by
  rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i,
    congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i,
    logPrimeMeshHi_eq_lo_add_step]
  simp only [meshStep, add_sub_cancel_left]

/-- The actual rational rectangle has exactly the common mesh width. -/
theorem box_width (m : ℕ) (j : Cell m) :
    ((box m j).width : ℝ) = meshStep m := by
  have h0 := box_coordinate_width m j 0
  have h1 := box_coordinate_width m j 1
  have h2 := box_coordinate_width m j 2
  simp only [RationalBox.width, Rat.cast_max, Rat.cast_sub, Rat.cast_zero]
  change max 0 (max
    ((qLogPrimeMeshHi 0 (19 / 96) m j 0 : ℝ) - qLogPrimeMeshLo 0 (19 / 96) m j 0)
    (max
      ((qLogPrimeMeshHi 0 (19 / 96) m j 1 : ℝ) - qLogPrimeMeshLo 0 (19 / 96) m j 1)
      ((qLogPrimeMeshHi 0 (19 / 96) m j 2 : ℝ) - qLogPrimeMeshLo 0 (19 / 96) m j 2))) = _
  rw [h0, h1, h2, max_self, max_self, max_eq_right (meshStep_pos m).le]

private theorem box_geometry (m : ℕ) (j : Cell m) :
    (box m j).WellFormed ∧ 0 ≤ (box m j).lz := by
  have h0 := logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) m j 0
  have h1 := logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) m j 1
  have h2 := logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) m j 2
  have hlo := cast_qLogPrimeMeshLo 0 (19 / 96) m j
  have hhi := cast_qLogPrimeMeshHi 0 (19 / 96) m j
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact_mod_cast (show (qLogPrimeMeshLo 0 (19 / 96) m j 0 : ℝ) ≤
      qLogPrimeMeshHi 0 (19 / 96) m j 0 by
        rw [congrFun hlo 0, congrFun hhi 0]; exact h0.2.1.le)
  · exact_mod_cast (show (qLogPrimeMeshLo 0 (19 / 96) m j 1 : ℝ) ≤
      qLogPrimeMeshHi 0 (19 / 96) m j 1 by
        rw [congrFun hlo 1, congrFun hhi 1]; exact h1.2.1.le)
  · exact_mod_cast (show (qLogPrimeMeshLo 0 (19 / 96) m j 2 : ℝ) ≤
      qLogPrimeMeshHi 0 (19 / 96) m j 2 by
        rw [congrFun hlo 2, congrFun hhi 2]; exact h2.2.1.le)
  · exact_mod_cast (show (0 : ℝ) ≤ qLogPrimeMeshLo 0 (19 / 96) m j 2 by
        rw [congrFun hlo 2]; exact h2.1)

/-- Two mesh widths suffice for whole-rectangle order, including equality
at the resulting CLOSED rectangle boundaries. -/
theorem owner_selected_of_clearance (e chi : ℝ) (m : ℕ) (j : Cell m)
    (t : Fin 3 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hmesh : meshStep m ≤ chi)
    (hxy : 2 * meshStep m ≤ t 0 - t 1)
    (hyz : 2 * meshStep m ≤ t 1 - t 2)
    (hstop : ((box m j).ux : ℝ) ≤ extendedFirstStop - 4 * e) :
    j ∈ cells e chi m := by
  have hb := inBox_of_cell ht
  have hg := box_geometry m j
  have h0 := box_coordinate_width m j 0
  have h1 := box_coordinate_width m j 1
  have h2 := box_coordinate_width m j 2
  change ((box m j).ux : ℝ) - (box m j).lx = meshStep m at h0
  change ((box m j).uy : ℝ) - (box m j).ly = meshStep m at h1
  change ((box m j).uz : ℝ) - (box m j).lz = meshStep m at h2
  apply (mem_cells e chi m j).mpr
  refine ⟨hg.1, hg.2, ?_, ?_, hstop, ?_⟩
  · exact_mod_cast (show ((box m j).uz : ℝ) ≤ (box m j).ly by
      linarith [hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2])
  · exact_mod_cast (show ((box m j).uy : ℝ) ≤ (box m j).lx by
      linarith [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1])
  · simpa only [box_width] using hmesh

/-- This is the actual omitted-cell cover, rather than a cover for an
alternative dyadic policy. No false label or ordering-wall atom is erased. -/
theorem unselected_owner_in_strips (e chi : ℝ) (m : ℕ) (j : Cell m)
    (t : Fin 3 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hmesh : meshStep m ≤ chi) (hmiss : j ∉ cells e chi m) :
    t 0 - t 1 < 2 * meshStep m ∨ t 1 - t 2 < 2 * meshStep m ∨
      extendedFirstStop - 4 * e - meshStep m < t 0 := by
  by_contra hh
  push_neg at hh
  have hb := inBox_of_cell ht
  have hw := box_coordinate_width m j 0
  change ((box m j).ux : ℝ) - (box m j).lx = meshStep m at hw
  exact hmiss (owner_selected_of_clearance e chi m j t ht hmesh hh.1 hh.2.1
    (by linarith [hb.1, hh.2.2]))

/-- A passed historical first label removes the stop alternative altogether.
This statement does not choose that label from any child wall. -/
theorem unsupported_owner_in_order_strips (e chi : ℝ) (m : ℕ)
    (j : Cell m) (t : Fin 3 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hmesh : meshStep m ≤ chi)
    (hstop : ((box m j).ux : ℝ) ≤ extendedFirstStop - 4 * e)
    (hmiss : t ∉ P1ThirdFallbackSupport.jointCells e chi m) :
    t 0 - t 1 < 2 * meshStep m ∨ t 1 - t 2 < 2 * meshStep m := by
  by_contra hh
  push_neg at hh
  have hj := owner_selected_of_clearance e chi m j t ht hmesh hh.1 hh.2 hstop
  exact hmiss ((P1ThirdFallbackSupport.mem_jointCells e chi m t).mpr ⟨j, hj, ht⟩)

/-- The literal historical firstStop and the first coordinate of a third
owner are the SAME half-open owner, not just nearby real coordinates. -/
theorem owner_stop_of_historical_firstStop (e : ℝ) (m : ℕ) (N : ℝ)
    (p1 p2 p3 : ℕ) (j : Cell m)
    (ht : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∈
      logPrimeMeshCell 0 (19 / 96) m j)
    (hs : firstStop e m N [p1]) :
    ((box m j).ux : ℝ) ≤ extendedFirstStop - 4 * e := by
  obtain ⟨i, hil, hiu, his⟩ := hs
  have hcoord : primeHistoryLogCoordinates N 1 [p1] 0 =
      primeHistoryLogCoordinates N 3 [p3,p2,p1] 0 := by
    simp [primeHistoryLogCoordinates, primeHistoryTuple]
  have ht0 := mem_logPrimeMeshCell.mp ht 0
  have hij : i = j 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep := logPrimeMeshPoint_mono (by norm_num : (0 : ℝ) ≤ 19 / 96) m
        (show i.val + 1 ≤ (j 0).val from h)
      change logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤
        logPrimeMeshLo 0 (19 / 96) m j 0 at hsep
      exact (not_lt_of_ge (hsep.trans ht0.1)) (hcoord ▸ hiu)
    · have hsep := logPrimeMeshPoint_mono (by norm_num : (0 : ℝ) ≤ 19 / 96) m
        (show (j 0).val + 1 ≤ i.val from h)
      change logPrimeMeshHi 0 (19 / 96) m j 0 ≤
        logPrimeMeshPoint 0 (19 / 96) m i.val at hsep
      exact (not_lt_of_ge (hsep.trans (hcoord ▸ hil))) ht0.2
  subst i
  simpa [box, qLogPrimeMeshHi, logPrimeMeshHi] using his

/-- The complete disabled/unselected split on a genuine historical parent.
In particular it includes all active-but-unselected coarse cells. -/
theorem actual_unsupported_third_in_tail_or_order_strips
    (d : OriginalData) (N : ℝ) (p1 p2 p3 : ℕ)
    (j : Cell d.m)
    (ht : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∈
      logPrimeMeshCell 0 (19 / 96) d.m j)
    (hmesh : meshStep d.m ≤ d.chi)
    (hstop : firstStop (d.e : ℝ) d.m N [p1])
    (hs : ¬selectedThird d N [p3,p2,p1]) :
    (p3 : ℝ) < N ^ d.omega ∨
      primeHistoryLogCoordinates N 3 [p3,p2,p1] 0 -
        primeHistoryLogCoordinates N 3 [p3,p2,p1] 1 < 2 * meshStep d.m ∨
      primeHistoryLogCoordinates N 3 [p3,p2,p1] 1 -
        primeHistoryLogCoordinates N 3 [p3,p2,p1] 2 < 2 * meshStep d.m := by
  by_cases hp : N ^ d.omega ≤ (p3 : ℝ)
  · right
    have hout : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∉
        P1ThirdFallbackSupport.jointCells (d.e : ℝ) d.chi d.m := by
      intro hu
      apply hs
      change P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
        (rosserAncestor 3 [p3,p2,p1])
      rw [rosserAncestor_self_of_length 3 _ (by simp)]
      exact (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mpr ⟨hp, hu⟩
    exact unsupported_owner_in_order_strips (d.e : ℝ) d.chi d.m j _ ht hmesh
      (owner_stop_of_historical_firstStop _ _ _ _ _ _ j ht hstop) hout
  · exact Or.inl (lt_of_not_ge hp)

/-- The firstStop premise of the preceding geometry is supplied by P's
actual candidate list, even if this third node failed the old cube. -/
theorem candidate_original_firstStop (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (carrier : List ℕ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d N h carrier) (p1 p2 p3 : ℕ)
    (hp : s.selectedPrefix = [p3,p2,p1]) :
    firstStop (d.e : ℝ) d.m N [p1] := by
  have hperm := firstExitRootFrontier_admitted_history_perm 3
    (beforeThirdPolicy (old3 d N)) h carrier
  have hm : s.selectedPrefix.reverse ∈
      firstExitAdmittedChoices 3 (beforeThirdPolicy (old3 d N)) [] true carrier :=
    hperm.mem_iff.mp (List.mem_map.mpr ⟨s, hs, rfl⟩)
  have hv : FirstExitValidSelection (beforeThirdPolicy (old3 d N)) [] true
      s.selectedPrefix.reverse := of_decide_eq_true (List.mem_filter.mp hm).2
  have hv' : FirstExitValidSelection (beforeThirdPolicy (old3 d N)) [] true
      [p1,p2,p3] := by simpa only [hp, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.cons_append] using hv
  have hfirst : old3 d N false [p1] = true := by
    simpa [beforeThirdPolicy, firstExitDepthSplicePolicy] using hv'.1
  exact (P1OriginalFirstStopInheritance.singleton_original_tests
    (d.e : ℝ) d.chi d.m d.omega N p1 hfirst).2.1

/-- Direct actual-source form: neither retained-old admission nor a
caller-supplied firstStop is required on this before-test occurrence. -/
theorem candidate_unsupported_in_tail_or_order_strips
    (d : OriginalData) (N : ℝ) (h : ℕ → ℝ) (carrier : List ℕ)
    (s : FirstExitDepthState ℕ) (hs : s ∈ candidates d N h carrier)
    (p1 p2 p3 : ℕ) (hp : s.selectedPrefix = [p3,p2,p1]) (j : Cell d.m)
    (ht : primeHistoryLogCoordinates N 3 [p3,p2,p1] ∈
      logPrimeMeshCell 0 (19 / 96) d.m j)
    (hmesh : meshStep d.m ≤ d.chi) (hu : ¬selectedThird d N [p3,p2,p1]) :
    (p3 : ℝ) < N ^ d.omega ∨
      primeHistoryLogCoordinates N 3 [p3,p2,p1] 0 -
        primeHistoryLogCoordinates N 3 [p3,p2,p1] 1 < 2 * meshStep d.m ∨
      primeHistoryLogCoordinates N 3 [p3,p2,p1] 1 -
        primeHistoryLogCoordinates N 3 [p3,p2,p1] 2 < 2 * meshStep d.m :=
  actual_unsupported_third_in_tail_or_order_strips d N p1 p2 p3 j ht hmesh
    (candidate_original_firstStop d N h carrier s hs p1 p2 p3 hp) hu

/-- A single pre-N choice covers every strictly separated compact source.
Only the OLD table is being refined here; no second/third cap is boxed. -/
theorem exists_uniform_historical_owner_threshold (delta chi : ℝ)
    (hd : 0 < delta) (hchi : 0 < chi) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ e : ℝ, 0 ≤ e → 4 * e ≤ delta / 2 →
      ∀ t : Fin 3 → ℝ,
        t ∈ logPrimeBox (fun _ => 0) (fun _ => (19 / 96 : ℝ)) →
        delta ≤ t 0 - t 1 → delta ≤ t 1 - t 2 →
        t 0 ≤ extendedFirstStop - delta →
        ∃! j : Cell m, j ∈ cells e chi m ∧ t ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually
      (gt_mem_nhds (lt_min hchi (half_pos hd))))
  refine ⟨m0, ?_⟩
  intro m hm e he hedelta t ht hxy hyz hstop
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) m ht
  have hsmall : meshStep m < min chi (delta / 2) := hm0 m hm
  have hb := inBox_of_cell hj
  have hw := box_coordinate_width m j 0
  change ((box m j).ux : ℝ) - (box m j).lx = meshStep m at hw
  have hjs : j ∈ cells e chi m := owner_selected_of_clearance e chi m j t hj
    ((lt_min_iff.mp hsmall).1.le) (by linarith [(lt_min_iff.mp hsmall).2])
    (by linarith [(lt_min_iff.mp hsmall).2])
    (by linarith [hb.1, (lt_min_iff.mp hsmall).2])
  refine ⟨j, ⟨hjs, hj⟩, ?_⟩
  intro k hk
  exact logPrimeMeshCell_unique (by norm_num) hk.2 hj

end
end ImbalancedChen.P4ACatalogFiveHistoricalCoverage
