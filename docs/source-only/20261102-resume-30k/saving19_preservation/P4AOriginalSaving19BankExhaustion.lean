import ImbalancedChen.P4AOriginalSaving19CommonHistory
import ImbalancedChen.SelectedPrefixRationalMesh

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual G ascending19 bank exhausts each of the original thirteen
strict cells. This is the existing rational row-lower bank, with its
projected HistoricalThirdCoarse.cells, first-stop and rough tests intact.
The two zero identities are still absent from the strict rows. No full87
source identity, frontier admission, gain estimate or reserve is assumed.
-/

namespace ImbalancedChen.P4AOriginalSaving19BankExhaustion

noncomputable section
open Filter Set VariableEnvelope HistoricalThirdCoarse
open scoped Classical BigOperators Topology
open P4AOriginalLive171819Atlas P4AOriginalLive171819PrimeBank
open P4AOriginalCell0HalfOpenPrimeCarrier
open OriginalAscendingThirteenCellOwnership
open OriginalAscendingThirteenLiteralAffineRows
open OriginalAscendingThirteenExportOwnershipJoin
open OriginalDescendingFifteenLiteralAffineRows
  (evaluate subsetExpr ascendingExpr descendingExpr K X)

/-- The G source row has the original semantic evaluation, at the SAME
cell and row index. Only symbolic affine arithmetic is used; no literal
row bank, hash or desired source equality is a premise. -/
theorem liveRow_eq_semanticSlack (i : Fin 13) (r : Fin 97) (t : Point) :
    eval (rows19 i r) t = semanticSlack i r t := by
  fin_cases r
  all_goals
    simp [rows19, common19, gap19, mask19, eval,
      P4AOriginalSeed7Unequal15Literal.evalAffine, semanticSlack,
      semanticExpr, oldExpr, thirdExpr, newExpr, evaluate, subsetExpr,
      ascendingExpr, descendingExpr, K, X, Fin.sum_univ_succ]
    <;> split_ifs <;> simp [evaluate] <;> ring

/-- Both independently defined thirteen-cell sources agree; the reverse
direction was absent from G's source19_guard. -/
theorem liveSource_iff_original (i : Fin 13) (t : Point) :
    sourceRows (.ascending19 i) t ↔ StrictRows i t := by
  constructor
  · exact source19_guard i t
  · intro ht r
    have hex : StrictExportedRows i t :=
      (strictExportedRows_iff_StrictRows i t).mpr ht
    have hsem := (strictExportedRows_iff_strictSemanticRows i t).mp hex r
    change 0 < eval (rows19 i r) t
    rwa [liveRow_eq_semanticSlack]

theorem qLo_real (m : ℕ) (j : BoxIndex m) (k : Fin 8) :
    (qLo m j k : ℝ) = logPrimeMeshLo 0 (19 / 96) m j k := by
  norm_num [qLo, qPoint, logPrimeMeshLo, logPrimeMeshPoint, logPrimeMeshStep]
  push_cast
  ring

theorem qHi_real (m : ℕ) (j : BoxIndex m) (k : Fin 8) :
    (qHi m j k : ℝ) = logPrimeMeshHi 0 (19 / 96) m j k := by
  norm_num [qHi, qPoint, logPrimeMeshHi, logPrimeMeshPoint, logPrimeMeshStep]
  push_cast
  ring

private theorem rowLower_real (i : Fin 13) (m : ℕ) (j : BoxIndex m)
    (r : Fin 97) :
    (rowLower (.ascending19 i) m j r : ℝ) =
      ((rows19 i r) 0 : ℝ) + ∑ k : Fin 8,
        ((rows19 i r) k.succ : ℝ) *
          (if 0 ≤ (rows19 i r) k.succ then
            logPrimeMeshLo 0 (19 / 96) m j k
           else logPrimeMeshHi 0 (19 / 96) m j k) := by
  simp only [rowLower, rows, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp only [qLo_real, qHi_real]

/-- The actual whole-box infimum approaches its original strict row.
The selected endpoint is determined by the original rational slope. -/
theorem rowLower_tendsto (i : Fin 13) (r : Fin 97)
    (j : ∀ m, BoxIndex m) (t : Point)
    (ht : ∀ m, t ∈ logPrimeMeshCell 0 (19 / 96) m (j m)) :
    Tendsto (fun m => (rowLower (.ascending19 i) m (j m) r : ℝ)) atTop
      (𝓝 (eval (rows19 i r) t)) := by
  let endpoint : ℕ → Point := fun m k =>
    if 0 ≤ (rows19 i r) k.succ then logPrimeMeshLo 0 (19 / 96) m (j m) k
      else logPrimeMeshHi 0 (19 / 96) m (j m) k
  have hend : Tendsto endpoint atTop (𝓝 t) := by
    apply tendsto_pi_nhds.mpr
    intro k
    by_cases hs : 0 ≤ (rows19 i r) k.succ
    · simpa [endpoint, hs] using tendsto_logPrimeMeshLo_apply 0 (19 / 96) j ht k
    · simpa [endpoint, hs] using tendsto_logPrimeMeshHi_apply 0 (19 / 96) j ht k
  have hc : Continuous (eval (rows19 i r)) := by
    unfold eval P4AOriginalSeed7Unequal15Literal.evalAffine
    fun_prop
  simpa only [rowLower_real, eval, P4AOriginalSeed7Unequal15Literal.evalAffine,
    endpoint] using hc.continuousAt.tendsto.comp hend

/-- Every third-coordinate projected box has precisely the common
mesh width. Its rational lookup and cell definition are not replaced. -/
theorem third_box_width (m : ℕ) (j : Cell m) :
    ((box m j).width : ℝ) = logPrimeMeshStep 0 (19 / 96) m := by
  have hd (k : Fin 3) :
      (qLogPrimeMeshHi 0 (19 / 96) m j k : ℝ) -
        (qLogPrimeMeshLo 0 (19 / 96) m j k : ℝ) =
          logPrimeMeshStep 0 (19 / 96) m := by
    rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) k,
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) k]
    norm_num only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat]
    rw [logPrimeMeshHi_eq_lo_add_step]
    ring
  have hs := (logPrimeMeshStep_pos (by norm_num : (0 : ℝ) < 19 / 96) m).le
  simp only [RationalBox.width, box, Rat.cast_max, Rat.cast_zero, Rat.cast_sub,
    hd, max_self, max_eq_right hs]

/-- Strict first-three order makes the original wholly ordered cell test
eventually succeed. Width, firstStop and positivity are proved together. -/
theorem projected_third_eventually_selected
    (e : ℚ) (chi : ℝ) (hchi : 0 < chi) (j : ∀ m, BoxIndex m)
    (t : Point) (ht : ∀ m, t ∈ logPrimeMeshCell 0 (19 / 96) m (j m))
    (h21 : t 2 < t 1) (h10 : t 1 < t 0)
    (hstop : t 0 < 19 / 96 - 4 * (e : ℝ)) :
    ∀ᶠ m in atTop,
      historicalPrefixProject (by omega : 3 ≤ 8) (j m) ∈ cells (e : ℝ) chi m := by
  let jp : ∀ m, Cell m := fun m => historicalPrefixProject (by omega : 3 ≤ 8) (j m)
  let tp : Fin 3 → ℝ := historicalPrefixProject (by omega : 3 ≤ 8) t
  have htp (m : ℕ) : tp ∈ logPrimeMeshCell 0 (19 / 96) m (jp m) :=
    mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 8) (ht m)
  have h21' : tp 2 < tp 1 := h21
  have h10' : tp 1 < tp 0 := h10
  have hstop' : tp 0 < 19 / 96 - 4 * (e : ℝ) := hstop
  have hlo (k : Fin 3) := tendsto_logPrimeMeshLo_apply 0 (19 / 96) jp htp k
  have hhi (k : Fin 3) := tendsto_logPrimeMeshHi_apply 0 (19 / 96) jp htp k
  have horder21 := ((hlo 1).sub (hhi 2)).eventually
    (lt_mem_nhds (sub_pos.mpr h21'))
  have horder10 := ((hlo 0).sub (hhi 1)).eventually
    (lt_mem_nhds (sub_pos.mpr h10'))
  have hstopEv := (hhi 0).eventually (gt_mem_nhds hstop')
  have hwidth := (tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hchi)
  filter_upwards [horder21, horder10, hstopEv, hwidth] with m h21m h10m hsm hwm
  apply (mem_cells (e : ℝ) chi m (jp m)).mpr
  have hl (k : Fin 3) : (qLogPrimeMeshLo 0 (19 / 96) m (jp m) k : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m (jp m) k := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m (jp m)) k
  have hu (k : Fin 3) : (qLogPrimeMeshHi 0 (19 / 96) m (jp m) k : ℝ) =
      logPrimeMeshHi 0 (19 / 96) m (jp m) k := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m (jp m)) k
  refine ⟨RationalBox.wellFormed_of_inBox (inBox_of_cell (htp m)), ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ qLogPrimeMeshLo 0 (19 / 96) m (jp m) 2
    apply Rat.cast_le.mp
    rw [Rat.cast_zero, hl]
    exact (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) m (jp m) 2).1
  · change qLogPrimeMeshHi 0 (19 / 96) m (jp m) 2 ≤ qLogPrimeMeshLo 0 (19 / 96) m (jp m) 1
    apply Rat.cast_le.mp
    rw [hu, hl]
    linarith
  · change qLogPrimeMeshHi 0 (19 / 96) m (jp m) 1 ≤ qLogPrimeMeshLo 0 (19 / 96) m (jp m) 0
    apply Rat.cast_le.mp
    rw [hu, hl]
    linarith
  · change (qLogPrimeMeshHi 0 (19 / 96) m (jp m) 0 : ℝ) ≤ _
    rw [hu]
    exact hsm.le
  · rw [third_box_width]
    exact hwm.le

theorem original_source_box {i : Fin 13} {t : Point} (ht : StrictRows i t) :
    t ∈ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => 19 / 96) := by
  apply mem_logPrimeBox.mpr
  intro k
  have ha := rows_antitone ht
  have hl := ht.lastFloor
  have hu := ht.largest
  have hklo := ha (Fin.le_last k)
  have hkhi := ha (Fin.zero_le k)
  dsimp [mu] at hu
  constructor <;> linarith

/-- Fixed e,chi,omega are chosen before the mesh and before N. Every
original point eventually passes ALL tests of the original G bank.
No bank, support, firstStop or source equality hypothesis is retained. -/
theorem original_eventually_bank (i : Fin 13) (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100)
    (t : Point) (ht : StrictRows i t) :
    ∃ j : ∀ m, BoxIndex m,
      (∀ m, t ∈ logPrimeMeshCell 0 (19 / 96) m (j m)) ∧
        ∀ᶠ m in atTop, j m ∈ bank (.ascending19 i) e chi m omega := by
  choose j hj using fun m => exists_logPrimeMeshCell 0 (19 / 96) m (original_source_box ht)
  have hr := (liveSource_iff_original i t).mpr ht
  have hrows : ∀ᶠ m in atTop, ∀ r : Fin 97,
      0 < (rowLower (.ascending19 i) m (j m) r : ℝ) := by
    apply eventually_all.mpr
    intro r
    exact (rowLower_tendsto i r j t hj).eventually (lt_mem_nhds (hr r))
  have heR : (e : ℝ) ≤ 1 / 1536 := by exact_mod_cast he
  have hstop : t 0 < 19 / 96 - 4 * (e : ℝ) := by
    have hl := ht.largest
    dsimp [mu] at hl
    linarith
  have hstopEv := (tendsto_logPrimeMeshHi_apply 0 (19 / 96) j hj (0 : Fin 8)).eventually
    (gt_mem_nhds hstop)
  have hthird := projected_third_eventually_selected e chi hchi j t hj
    (ht.order 1) (ht.order 0) hstop
  have hrough := (tendsto_logPrimeMeshLo_apply 0 (19 / 96) j hj (2 : Fin 8)).eventually
    (lt_mem_nhds (homega.trans_lt ht.thirdFloor))
  refine ⟨j, hj, ?_⟩
  filter_upwards [hrows, hstopEv, hthird, hrough] with m hm hs h3 hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_, h3, hw.le⟩
  · have hs' : (qHi m (j m) 0 : ℝ) ≤ 19 / 96 - 4 * (e : ℝ) := by
      rw [qHi_real]
      exact hs.le
    exact_mod_cast hs'
  · intro r
    exact_mod_cast hm r

/-- Geometric footprint of the existing bank; no new selection rule. -/
def bankRegion (i : Fin 13) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) : Set Point :=
  {t | ∃ j ∈ bank (.ascending19 i) e chi m omega,
    t ∈ logPrimeMeshCell 0 (19 / 96) m j}

theorem bankRegion_subset_original (i : Fin 13) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) :
    bankRegion i e chi m omega ⊆ cell i := by
  rintro t ⟨j, hj, ht⟩
  apply (liveSource_iff_original i t).mp
  intro r
  have hrows := (Finset.mem_filter.mp hj).2.2.1 r
  have hpos : (0 : ℝ) < (rowLower (.ascending19 i) m j r : ℝ) := by exact_mod_cast hrows
  exact hpos.trans_le (rowLower_le (.ascending19 i) m j r t ht)

theorem original_eventually_bankRegion (i : Fin 13) (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100)
    (t : Point) (ht : t ∈ cell i) :
    ∀ᶠ m in atTop, t ∈ bankRegion i e chi m omega := by
  obtain ⟨j, hj, hevent⟩ := original_eventually_bank i e he chi hchi omega homega t ht
  filter_upwards [hevent] with m hm
  exact ⟨j m, hm, hj m⟩

/-- Exact original-cell exhaustion, not an assumption about the
triangulation or the unrelated full87 physical selection. -/
theorem original_eq_iUnion_bankRegion (i : Fin 13) (e : ℚ) (he : e ≤ 1 / 1536)
    (chi : ℝ) (hchi : 0 < chi) (omega : ℝ) (homega : omega ≤ 1 / 100) :
    cell i = ⋃ m : ℕ, bankRegion i e chi m omega := by
  ext t
  constructor
  · intro ht
    obtain ⟨m, hm⟩ := (original_eventually_bankRegion i e he chi hchi omega homega t ht).exists
    exact mem_iUnion.mpr ⟨m, hm⟩
  · intro ht
    obtain ⟨m, hm⟩ := mem_iUnion.mp ht
    exact bankRegion_subset_original i e chi m omega hm

/-- For a given original point, both the original thirteen-cell index
and its half-open box index are unique. No index deduplication occurs. -/
theorem bank_owner_unique {i i' : Fin 13} {e : ℚ} {chi omega : ℝ} {m : ℕ}
    {j j' : BoxIndex m} {t : Point}
    (hj : j ∈ bank (.ascending19 i) e chi m omega)
    (hj' : j' ∈ bank (.ascending19 i') e chi m omega)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (ht' : t ∈ logPrimeMeshCell 0 (19 / 96) m j') : i = i' ∧ j = j' := by
  exact ⟨owner_unique
    (bankRegion_subset_original i e chi m omega ⟨j, hj, ht⟩)
    (bankRegion_subset_original i' e chi m omega ⟨j', hj', ht'⟩),
    logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) ht ht'⟩

end
end ImbalancedChen.P4AOriginalSaving19BankExhaustion
