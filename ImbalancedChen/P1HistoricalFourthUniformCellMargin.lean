import ImbalancedChen.P1HistoricalUpperFourthPhysicalGates

/-!
# P1: checkable rational cell margins for the fourth PLUS source

An open-domain proof s>1 need not stay inside that domain on a closed box.
The finite check below requires a rational positive whole-box gap.  Its
soundness proves a uniform quantitative separation on the complete closed
box, and therefore on every actual admitted tuple in its half-open cell.
No existing cell is asserted to pass this additional check.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Set

/-- Closed rational box used only as a compact parameter enclosure. -/
def p1_fourthClosedRationalBox (lo hi : Fin 4 → ℚ) : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun i => Set.Icc (lo i : ℝ) (hi i : ℝ)

/-- The PLUS gate has positive coefficients, so its whole-box upper bound is
at hi.  The test retains explicit rational gap and terminal upper bound. -/
def p1_fourthWholeBoxMarginCheck (old delta rho : ℚ) (lo hi : Fin 4 → ℚ) : Bool :=
  decide (0 < delta ∧ 0 < lo 3 ∧ hi 3 ≤ rho ∧ 0 < rho ∧
    (∑ i, hi i) + hi 3 ≤ old - delta)

theorem p1_fourthWholeBoxMarginCheck_iff (old delta rho : ℚ) (lo hi : Fin 4 → ℚ) :
    p1_fourthWholeBoxMarginCheck old delta rho lo hi = true ↔
      0 < delta ∧ 0 < lo 3 ∧ hi 3 ≤ rho ∧ 0 < rho ∧
        (∑ i, hi i) + hi 3 ≤ old - delta := by
  simp only [p1_fourthWholeBoxMarginCheck, decide_eq_true_eq]

/-- A checked whole-box margin gives a quantitative lower bound for both
residual levels lambda >= old.  The smaller half-gap is strictly positive. -/
theorem p1_fourthWholeBoxMargin_sound (old delta rho : ℚ) (lo hi : Fin 4 → ℚ)
    (hc : p1_fourthWholeBoxMarginCheck old delta rho lo hi = true)
    (lambda : ℝ) (hold : (old : ℝ) ≤ lambda)
    (t : Fin 4 → ℝ) (ht : t ∈ p1_fourthClosedRationalBox lo hi) :
    0 < t 3 ∧ (∑ i, t i) + t 3 ≤ lambda - (delta : ℝ) ∧
      1 + (delta : ℝ) / (rho : ℝ) ≤ (lambda - ∑ i, t i) / t 3 ∧
      0 < (delta : ℝ) / (2 * (rho : ℝ)) ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) < (lambda - ∑ i, t i) / t 3 := by
  have hcheck := (p1_fourthWholeBoxMarginCheck_iff old delta rho lo hi).mp hc
  have hdelta : (0 : ℝ) < delta := by exact_mod_cast hcheck.1
  have hrho : (0 : ℝ) < rho := by exact_mod_cast hcheck.2.2.2.1
  have hlo : (0 : ℝ) < lo 3 := by exact_mod_cast hcheck.2.1
  have hirho : (hi 3 : ℝ) ≤ rho := by exact_mod_cast hcheck.2.2.1
  have hwhole : (∑ i, (hi i : ℝ)) + (hi 3 : ℝ) ≤ (old : ℝ) - delta := by
    exact_mod_cast hcheck.2.2.2.2
  have ht3 : 0 < t 3 := hlo.trans_le (ht 3 (Set.mem_univ 3)).1
  have ht3rho : t 3 ≤ (rho : ℝ) := (ht 3 (Set.mem_univ 3)).2.trans hirho
  have hsum : (∑ i, t i) ≤ ∑ i, (hi i : ℝ) := by
    apply Finset.sum_le_sum
    intro i _hi
    exact (ht i (Set.mem_univ i)).2
  have hmargin : (∑ i, t i) + t 3 ≤ lambda - (delta : ℝ) := by
    have h := (add_le_add hsum (ht 3 (Set.mem_univ 3)).2).trans hwhole
    linarith
  have hmul : ((delta : ℝ) / (rho : ℝ)) * t 3 ≤ (delta : ℝ) := by
    have h := mul_le_mul_of_nonneg_left ht3rho (div_nonneg hdelta.le hrho.le)
    simpa only [div_mul_cancel₀ _ hrho.ne'] using h
  have hratio : 1 + (delta : ℝ) / (rho : ℝ) ≤ (lambda - ∑ i, t i) / t 3 := by
    apply (le_div_iff₀ ht3).mpr
    nlinarith only [hmargin, hmul]
  have hhalf : 0 < (delta : ℝ) / (2 * (rho : ℝ)) := div_pos hdelta (by positivity)
  have heq : (delta : ℝ) / (rho : ℝ) = 2 * ((delta : ℝ) / (2 * (rho : ℝ))) := by
    field_simp [hrho.ne'] <;> ring
  exact ⟨ht3, hmargin, hratio, hhalf, by rw [heq] at hratio; linarith⟩

/-- This parameter set encloses the actual quotient parameters on the
complete closed cell, including every face. -/
def p1_fourthMarginParameterSet (lo hi : Fin 4 → ℚ) (lambda : ℝ) : Set (ℝ × ℝ) :=
  (fun t : Fin 4 → ℝ => (lambda - ∑ i, t i, t 3)) '' p1_fourthClosedRationalBox lo hi

theorem p1_fourthMarginParameterSet_isCompact (lo hi : Fin 4 → ℚ) (lambda : ℝ) :
    IsCompact (p1_fourthMarginParameterSet lo hi lambda) := by
  have hbox : IsCompact (p1_fourthClosedRationalBox lo hi) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hF : Continuous (fun t : Fin 4 → ℝ => (lambda - ∑ i, t i, t 3)) := by
    fun_prop
  exact hbox.image hF

/-- The checked closed image satisfies the exact domain of
exists_actualSmallRosserPlusDensity_quotient_compact_normalized_threshold. -/
theorem p1_fourthMarginParameterSet_legal (old delta rho : ℚ) (lo hi : Fin 4 → ℚ)
    (hc : p1_fourthWholeBoxMarginCheck old delta rho lo hi = true)
    (lambda : ℝ) (hold : (old : ℝ) ≤ lambda) :
    ∀ q ∈ p1_fourthMarginParameterSet lo hi lambda,
      0 < q.2 ∧ q.2 < q.1 ∧
        1 + (delta : ℝ) / (rho : ℝ) ≤ q.1 / q.2 ∧
        1 + (delta : ℝ) / (2 * (rho : ℝ)) < q.1 / q.2 := by
  rintro q ⟨t, ht, rfl⟩
  have hs := p1_fourthWholeBoxMargin_sound old delta rho lo hi hc lambda hold t ht
  have hdelta : (0 : ℝ) < delta := by
    exact_mod_cast ((p1_fourthWholeBoxMarginCheck_iff old delta rho lo hi).mp hc).1
  refine ⟨hs.1, ?_, hs.2.2.1, hs.2.2.2.2⟩
  dsimp
  linarith [hs.2.1]

namespace HistoricalPrefixCapData

/-- A concrete rational test for one actual historical cell. -/
def p1_fourthCellMarginCheck (D : HistoricalPrefixCapData)
    (delta rho : ℚ) (j : Fin 4 → Fin (D.m + 1)) : Bool :=
  p1_fourthWholeBoxMarginCheck (D.old4 j) delta rho
    (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j)

/-- Explicit finite selected-cell traversal; no check over all label types. -/
def p1_fourthSelectedMarginCheck (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (delta rho : ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := J)
    (p := fun j _ => D.p1_fourthCellMarginCheck delta rho j = true))

theorem p1_fourthSelectedMarginCheck_sound (D : HistoricalPrefixCapData)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (delta rho : ℚ)
    (hc : D.p1_fourthSelectedMarginCheck J delta rho = true) :
    ∀ j ∈ J, D.p1_fourthCellMarginCheck delta rho j = true := by
  simpa only [p1_fourthSelectedMarginCheck, decide_eq_true_eq] using hc

/-- A half-open mesh cell lies in its rational closed-box enclosure. -/
theorem p1_fourthCell_subset_closedRationalBox (D : HistoricalPrefixCapData)
    (j : Fin 4 → Fin (D.m + 1)) :
    logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ⊆
      p1_fourthClosedRationalBox (qLogPrimeMeshLo D.a D.b D.m j)
        (qLogPrimeMeshHi D.a D.b D.m j) := by
  intro t ht i _hi
  rw [congrFun (cast_qLogPrimeMeshLo D.a D.b D.m j) i,
    congrFun (cast_qLogPrimeMeshHi D.a D.b D.m j) i]
  exact ⟨(mem_logPrimeMeshCell.mp ht i).1, (mem_logPrimeMeshCell.mp ht i).2.le⟩

/-- A passed selected-cell check gives a target-independent strict gap
for both actual historical fourth residual coordinates. -/
theorem p1_fourthCell_uniform_gap (D : HistoricalPrefixCapData)
    (hlevels : D.levelCheck = true) (delta rho : ℚ)
    (j : Fin 4 → Fin (D.m + 1)) (hc : D.p1_fourthCellMarginCheck delta rho j = true)
    (t : Fin 4 → ℝ)
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    0 < (delta : ℝ) / (2 * (rho : ℝ)) ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.old4 j : ℝ) - ∑ i, t i) / t 3 ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.cell4 j : ℝ) - ∑ i, t i) / t 3 := by
  have htbox := D.p1_fourthCell_subset_closedRationalBox j ht
  have hold := p1_fourthWholeBoxMargin_sound _ delta rho _ _ hc
    (D.old4 j : ℝ) le_rfl t htbox
  have hle : (D.old4 j : ℝ) ≤ D.cell4 j := by
    exact_mod_cast D.p1_old4_le_cell4 hlevels j
  have hnew := p1_fourthWholeBoxMargin_sound _ delta rho _ _ hc
    (D.cell4 j : ℝ) hle t htbox
  exact ⟨hold.2.2.2.1, hold.2.2.2.2, hnew.2.2.2.2⟩

/-- Both closed-cell parameter sets are compact and meet the true PLUS
supplier's strict parameter domain.  This is conditional on this cell's
rational margin check, rather than inferred from open parent admission. -/
theorem p1_fourthCell_compact_supplier_domains (D : HistoricalPrefixCapData)
    (hlevels : D.levelCheck = true) (delta rho : ℚ)
    (j : Fin 4 → Fin (D.m + 1)) (hc : D.p1_fourthCellMarginCheck delta rho j = true) :
    let lo := qLogPrimeMeshLo D.a D.b D.m j
    let hi := qLogPrimeMeshHi D.a D.b D.m j
    IsCompact (p1_fourthMarginParameterSet lo hi (D.old4 j : ℝ)) ∧
      IsCompact (p1_fourthMarginParameterSet lo hi (D.cell4 j : ℝ)) ∧
      (∀ q ∈ p1_fourthMarginParameterSet lo hi (D.old4 j : ℝ), 0 < q.2 ∧ q.2 < q.1) ∧
      (∀ q ∈ p1_fourthMarginParameterSet lo hi (D.cell4 j : ℝ), 0 < q.2 ∧ q.2 < q.1) := by
  dsimp only
  have hle : (D.old4 j : ℝ) ≤ D.cell4 j := by
    exact_mod_cast D.p1_old4_le_cell4 hlevels j
  refine ⟨p1_fourthMarginParameterSet_isCompact _ _ _,
    p1_fourthMarginParameterSet_isCompact _ _ _, ?_, ?_⟩
  · intro q hq
    have h := p1_fourthMarginParameterSet_legal _ delta rho _ _ hc _ le_rfl q hq
    exact ⟨h.1, h.2.1⟩
  · intro q hq
    have h := p1_fourthMarginParameterSet_legal _ delta rho _ _ hc _ hle q hq
    exact ⟨h.1, h.2.1⟩

end HistoricalPrefixCapData

/-- The actual quotient parameter is in the compact enclosure, with the
complete four-prime prefix product as denominator. -/
theorem p1_fourthCell_actualParameters_mem (D : HistoricalPrefixCapData)
    (N : ℕ) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (lambda : ℝ)
    (j : Fin 4 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) lambda ∈
      p1_fourthMarginParameterSet (qLogPrimeMeshLo D.a D.b D.m j)
        (qLogPrimeMeshHi D.a D.b D.m j) lambda := by
  rw [p1_fourth_quotientParameters_eq N p hp lambda]
  exact Set.mem_image_of_mem _ (D.p1_fourthCell_subset_closedRationalBox j ht)

/-- Every actual admitted tuple in a passed cell has the same explicit
positive margin, before any prime-density limit or integral approximation. -/
theorem p1_admittedFourth_uniform_cell_margin
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (delta rho : ℚ) (j : Fin 4 → Fin (D.m + 1))
    (hc : D.p1_fourthCellMarginCheck delta rho j = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ)
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    0 < (delta : ℝ) / (2 * (rho : ℝ)) ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.old4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3 ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.cell4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3 ∧
      actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) (D.old4 j : ℝ) ∈
        p1_fourthMarginParameterSet (qLogPrimeMeshLo D.a D.b D.m j)
          (qLogPrimeMeshHi D.a D.b D.m j) (D.old4 j : ℝ) ∧
      actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) (D.cell4 j : ℝ) ∈
        p1_fourthMarginParameterSet (qLogPrimeMeshLo D.a D.b D.m j)
          (qLogPrimeMeshHi D.a D.b D.m j) (D.cell4 j : ℝ) := by
  have hdict := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab hlevels N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hdict.2.1 i).1.pos
  have hgap := D.p1_fourthCell_uniform_gap hlevels delta rho j hc _ ht
  exact ⟨hgap.1, hgap.2.1, hgap.2.2,
    p1_fourthCell_actualParameters_mem D N p hpos _ j ht,
    p1_fourthCell_actualParameters_mem D N p hpos _ j ht⟩

namespace HistoricalPrefixCapData

/-- The bounded finite family check supplies one identical half-gap on
every checked cell; this also covers boundary faces of its enclosure. -/
theorem p1_fourthSelected_uniform_gap (D : HistoricalPrefixCapData)
    (hlevels : D.levelCheck = true)
    (J : Finset (Fin 4 → Fin (D.m + 1))) (delta rho : ℚ)
    (hc : D.p1_fourthSelectedMarginCheck J delta rho = true) :
    ∀ j ∈ J, ∀ t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j,
      0 < (delta : ℝ) / (2 * (rho : ℝ)) ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.old4 j : ℝ) - ∑ i, t i) / t 3 ∧
      1 + (delta : ℝ) / (2 * (rho : ℝ)) <
        ((D.cell4 j : ℝ) - ∑ i, t i) / t 3 := by
  intro j hj t ht
  exact D.p1_fourthCell_uniform_gap hlevels delta rho j
    (D.p1_fourthSelectedMarginCheck_sound J delta rho hc j hj) t ht

end HistoricalPrefixCapData

end
end ImbalancedChen
