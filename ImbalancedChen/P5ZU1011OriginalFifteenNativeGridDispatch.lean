import ImbalancedChen.P5ZU1011OriginalFifteenNativeGridCells
import ImbalancedChen.P5ZU11AdaptiveMinimum

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

One actual original15-policy action per original U11 prime tuple on the
finite certified native grid. The existing least-tag selector is reused;
its eligibility is now the CONCRETE WholeBoxEligibleTest of the unique
half-open grid owner. Endpoint H248/switched scores choose the action only:
no scalar score is identified with the native Rosser density or with a
pointwise count bound. The tag0 switched fallback retains its ACTUAL count.

Selected ordinary tuples partition into disjoint policy x cell fibres.
The literal tuple-selected support/rho is exactly each fibre's common
fixed native support/rho. All finite main/AP/centre terms use that same
action. W16, coverage away from proper-wall strips, endpoint density
approximation, switched count payment and signed AP estimates remain OPEN.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenNativeGridDispatch

noncomputable section
open scoped BigOperators
open Classical
open Set U11Integral U11H248 U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenArithmeticEligibility
open U1011OriginalFifteenNativeGridCells P5U1011JointOverlap

def bank : Finset ℕ := Finset.range 15
def eligible (n N j : ℕ) (t : Four) : Prop :=
  if hj : j < 15 then wholeBoxEligibleTest ⟨j,by omega⟩ (gridBox n (owner n (coordinates N t))) = true
  else False
def switchedScore (N : ℕ) (t : Four) : ℝ :=
  U11Integral.switchedKernel currentK LiLiuPrereqBuchstab.buchstab (coordinates N t)
def ordinaryScore (N j : ℕ) (t : Four) : ℝ :=
  U11Integral.ordinaryKernel Part5UpperTables.H248 U1011OriginalSixteenPolicyBank.residual j (coordinates N t)
def tag (n N : ℕ) (t : Four) : ℕ :=
  U11Adaptive.chosen bank (eligible n N) (switchedScore N) (ordinaryScore N) t

theorem ordinary_tag_spec (n N : ℕ) (t : Four) (h : tag n N t ≠ 0) :
    ∃ j : ℕ, j < 15 ∧ tag n N t = j + 1 ∧ eligible n N j t := by
  have hc := (U11Adaptive.chosen_spec bank (eligible n N) (switchedScore N) (ordinaryScore N) t).1
  rcases Finset.mem_insert.mp hc with hz | hc
  · exact (h hz).elim
  · obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hc
    obtain ⟨hjbank,hje⟩ := Finset.mem_filter.mp hj
    exact ⟨j,Finset.mem_range.mp hjbank,heq.symm,hje⟩

private theorem source_joint {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U11Adaptive.source N E) : t ∈ jointSelector N E :=
  originalU11_mem_joint (by exact_mod_cast (Nat.le_of_lt hN)) ht

/-- Original carrier, ordering and literal end bands prove membership in
the ambient cube; this is not a mask-geometric or prime-test premise. -/
theorem source_coordinates_cube {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ U11Adaptive.source N E) : coordinates N t ∈ cube := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hjoint := source_joint hN ht
  have hband := joint_band_and_mask hjoint
  have hanti := (slots_strictAnti hjoint).antitone
  apply mem_logPrimeBox.mpr
  intro i
  have hsmall : (t.1.1 : ℝ) ≤ (slots t i : ℝ) := by
    have h := hanti (show i ≤ (3 : Fin 4) by omega)
    have h' : (slots t 3 : ℝ) ≤ (slots t i : ℝ) := by exact_mod_cast h
    simpa only [slots,Matrix.cons_val_three] using h'
  have hlarge : (slots t i : ℝ) ≤ (t.2.2 : ℝ) := by
    have h := hanti (show (0 : Fin 4) ≤ i by omega)
    have h' : (slots t i : ℝ) ≤ (slots t 0 : ℝ) := by exact_mod_cast h
    simpa only [slots,Matrix.cons_val_zero] using h'
  have hlo : (N : ℝ) ^ (lower : ℝ) ≤ (slots t i : ℝ) := by
    simpa [lower] using hband.1.trans hsmall
  have hhi : (slots t i : ℝ) < (N : ℝ) ^ (upper : ℝ) := by
    simpa [upper] using hlarge.trans_lt hband.2.2.1
  rw [← slot_rpow hN hjoint i] at hlo hhi
  exact ⟨(Real.rpow_le_rpow_left_iff hNr).mp hlo,(Real.rpow_lt_rpow_left_iff hNr).mp hhi⟩

def ordinaryTuples (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => tag n N t ≠ 0)
def fallbackTuples (n N : ℕ) (E : ℕ × ℕ → Prop) : Finset Four :=
  (U11Adaptive.source N E).filter (fun t => tag n N t = 0)
def selectedTuples (n N : ℕ) (E : ℕ × ℕ → Prop) (i : Index n) : Finset Four :=
  (cellTuples n N E i).filter (fun t => tag n N t = i.1.val + 1)

theorem selectedTuples_unique {n N : ℕ} {E : ℕ × ℕ → Prop} {i k : Index n} {t : Four}
    (hi : t ∈ selectedTuples n N E i) (hk : t ∈ selectedTuples n N E k) : i = k := by
  obtain ⟨hiCell,hiTag⟩ := Finset.mem_filter.mp hi
  obtain ⟨hkCell,hkTag⟩ := Finset.mem_filter.mp hk
  have hval : i.1.val = k.1.val := by omega
  have hcell : i.2 = k.2 :=
    (cellTuples_geometric_owner hiCell).symm.trans (cellTuples_geometric_owner hkCell)
  exact Prod.ext (Fin.ext hval) hcell

theorem selectedTuples_subset_ordinary (n N : ℕ) (E : ℕ × ℕ → Prop) (i : Index n) :
    selectedTuples n N E i ⊆ ordinaryTuples n N E := by
  intro t ht
  obtain ⟨hcell,htag⟩ := Finset.mem_filter.mp ht
  have hs := (Finset.mem_filter.mp hcell).1
  exact Finset.mem_filter.mpr ⟨hs,by rw [htag]; omega⟩

/-- Every nonfallback actual tuple is owned by exactly one ACTIVE marked
cell. True scalar endpoint eligibility is not used as a physical license. -/
theorem ordinary_has_unique_active_cell {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ ordinaryTuples n N E) :
    ∃! i : Index n, i ∈ activeCells n ∧ t ∈ selectedTuples n N E i := by
  obtain ⟨hsource,hne⟩ := Finset.mem_filter.mp ht
  obtain ⟨j,hj,htag,hel⟩ := ordinary_tag_spec n N t hne
  have hcert : wholeBoxEligibleTest ⟨j,by omega⟩ (gridBox n (owner n (coordinates N t))) = true := by
    simpa only [eligible,dif_pos hj] using hel
  let i : Index n := (⟨j,hj⟩,owner n (coordinates N t))
  have hactive : i ∈ activeCells n := (mem_activeCells i).mpr hcert
  have hselected : t ∈ selectedTuples n N E i := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hsource,owner_mem n (source_coordinates_cube hN hsource)⟩,htag⟩
  refine ⟨i,⟨hactive,hselected⟩,?_⟩
  intro k hk
  exact selectedTuples_unique hk.2 hselected

/-- Signed finite reindexing AFTER selecting one action. No policy
multiplicity remains and no positivity is needed for the summand. -/
theorem sum_ordinary_eq_selected_cells {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (F : Four → ℝ) :
    (∑ t ∈ ordinaryTuples n N E, F t) =
      ∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i, F t := by
  have hrestrict (i : Index n) :
      (∑ t ∈ selectedTuples n N E i, F t) =
        ∑ t ∈ ordinaryTuples n N E, if t ∈ selectedTuples n N E i then F t else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun ht => ⟨selectedTuples_subset_ordinary n N E i ht,ht⟩,fun h => h.2⟩
  simp_rw [hrestrict]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨i,hi,hunique⟩ := ordinary_has_unique_active_cell hN ht
  symm
  rw [Finset.sum_eq_single i]
  · exact if_pos hi.2
  · intro k hk hki
    apply if_neg
    intro htK
    exact hki (hunique k ⟨hk,htK⟩)
  · intro hn
    exact (hn hi.1).elim

theorem sum_source_eq_fallback_add_selected {n N : ℕ} (hN : 1 < N)
    (E : ℕ × ℕ → Prop) (F : Four → ℝ) :
    (∑ t ∈ U11Adaptive.source N E, F t) =
      (∑ t ∈ fallbackTuples n N E, F t) +
        ∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i, F t := by
  rw [← sum_ordinary_eq_selected_cells hN E F]
  exact (Finset.sum_filter_add_sum_filter_not (U11Adaptive.source N E)
    (fun t => tag n N t = 0) F).symm

/-- The literal tuple-selected physical support and coefficient. Tag0
keeps no ordinary residual row; its actual switched count is retained in
fallbackTuples, pending the separate switched arithmetic estimate. -/
def selectedPolicy (n N : ℕ) (t : Four) : Policy :=
  if hj : (tag n N t).pred < 15 then ⟨(tag n N t).pred,by omega⟩ else first
def selectedSupport (n N : ℕ) (t : Four) : Finset ℕ :=
  if tag n N t = 0 then ∅ else
    U1011OriginalFifteenFixedCellNative.support (selectedPolicy n N t)
      (gridBox n (owner n (coordinates N t))) N
def selectedCoefficient (n N : ℕ) (t : Four) (d : ℕ) : ℝ :=
  if tag n N t = 0 then 0 else
    U1011OriginalFifteenFixedCellNative.coefficient (selectedPolicy n N t)
      (gridBox n (owner n (coordinates N t))) N d

theorem selected_row_eq_fixed_cell {n N : ℕ} {E : ℕ × ℕ → Prop} {i : Index n} {t : Four}
    (ht : t ∈ selectedTuples n N E i) :
    selectedPolicy n N t = policy i ∧
      selectedSupport n N t = U1011OriginalFifteenFixedCellNative.support (policy i) (gridBox n i.2) N ∧
      ∀ d, selectedCoefficient n N t d =
        U1011OriginalFifteenFixedCellNative.coefficient (policy i) (gridBox n i.2) N d := by
  obtain ⟨hcell,htag⟩ := Finset.mem_filter.mp ht
  have howner := cellTuples_geometric_owner hcell
  have hp : selectedPolicy n N t = policy i := by
    simp [selectedPolicy,htag,policy,i.1.isLt]
  have hz : tag n N t ≠ 0 := by rw [htag]; omega
  refine ⟨hp,?_,?_⟩
  · simp only [selectedSupport,if_neg hz,hp,howner]
  · intro d
    simp only [selectedCoefficient,if_neg hz,hp,howner]

def selectedMain (n N : ℕ) (t : Four) : ℝ :=
  if tag n N t = 0 then 0 else U1011OriginalFifteenFixedCellNative.main (selectedPolicy n N t)
    (gridBox n (owner n (coordinates N t))) N t
def selectedAP (n N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ selectedSupport n N t, selectedCoefficient n N t d *
    chenQuotientPrimeAPError N
      (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N) (fullPrefix t * d)
def selectedCentre (n N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ selectedSupport n N t, selectedCoefficient n N t d * chenCentrePrimeAPCount N N (fullPrefix t * d)
def selectedEstimator (n N : ℕ) (t : Four) : ℝ :=
  ∑ d ∈ selectedSupport n N t, selectedCoefficient n N t d *
    (chenPrimeAPCount N N (fullPrefix t * d) - chenCentrePrimeAPCount N N (fullPrefix t * d))

theorem selected_terms_eq_fixed_cell {n N : ℕ} {E : ℕ × ℕ → Prop} {i : Index n} {t : Four}
    (ht : t ∈ selectedTuples n N E i) :
    selectedMain n N t = U1011OriginalFifteenFixedCellNative.main (policy i) (gridBox n i.2) N t ∧
    selectedAP n N t = U1011OriginalFifteenFixedCellNative.signedAP (policy i) (gridBox n i.2) N t ∧
    selectedCentre n N t = U1011OriginalFifteenFixedCellNative.signedCentre (policy i) (gridBox n i.2) N t ∧
    selectedEstimator n N t = U1011OriginalFifteenFixedCellNative.estimator (policy i) (gridBox n i.2) N t := by
  have hrow := selected_row_eq_fixed_cell ht
  have howner := cellTuples_geometric_owner (Finset.mem_filter.mp ht).1
  have htag := (Finset.mem_filter.mp ht).2
  have hz : tag n N t ≠ 0 := by rw [htag]; omega
  refine ⟨?_,?_,?_,?_⟩
  · simp only [selectedMain,if_neg hz,hrow.1,howner]
  · unfold selectedAP U1011OriginalFifteenFixedCellNative.signedAP
    rw [hrow.2.1]
    simp_rw [hrow.2.2]
  · unfold selectedCentre U1011OriginalFifteenFixedCellNative.signedCentre
    rw [hrow.2.1]
    simp_rw [hrow.2.2]
  · unfold selectedEstimator U1011OriginalFifteenFixedCellNative.estimator
    rw [hrow.2.1]
    simp_rw [hrow.2.2]

/-- Exact reindexing of the literal tuple-selected SAME-rho main and both
signed corrections. No norm or independent replacement policy is inserted. -/
theorem selected_components_reindex {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ ordinaryTuples n N E, selectedMain n N t) =
      (∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i,
        U1011OriginalFifteenFixedCellNative.main (policy i) (gridBox n i.2) N t) ∧
    (∑ t ∈ ordinaryTuples n N E, selectedAP n N t) =
      (∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i,
        U1011OriginalFifteenFixedCellNative.signedAP (policy i) (gridBox n i.2) N t) ∧
    (∑ t ∈ ordinaryTuples n N E, selectedCentre n N t) =
      ∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i,
        U1011OriginalFifteenFixedCellNative.signedCentre (policy i) (gridBox n i.2) N t := by
  refine ⟨?_,?_,?_⟩
  · rw [sum_ordinary_eq_selected_cells hN E]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    exact (selected_terms_eq_fixed_cell ht).1
  · rw [sum_ordinary_eq_selected_cells hN E]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    exact (selected_terms_eq_fixed_cell ht).2.1
  · rw [sum_ordinary_eq_selected_cells hN E]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    exact (selected_terms_eq_fixed_cell ht).2.2.1

/-- An actual source upper bound with fallback retained and ONE physical
row per selected ordinary tuple. No bound for the switched fallback is
assumed or inferred from its scalar score. -/
theorem source_upper_selected_native {n N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E ≤
      (∑ t ∈ fallbackTuples n N E, U11Adaptive.weight N t) +
      ∑ i ∈ activeCells n, ∑ t ∈ selectedTuples n N E i,
        U1011OriginalFifteenFixedCellNative.main (policy i) (gridBox n i.2) N t +
        U1011OriginalFifteenFixedCellNative.signedAP (policy i) (gridBox n i.2) N t -
        U1011OriginalFifteenFixedCellNative.signedCentre (policy i) (gridBox n i.2) N t := by
  rw [U11Adaptive.current_eq_sum_weight,sum_source_eq_fallback_add_selected hN E]
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨hcell,_⟩ := Finset.mem_filter.mp ht
  obtain ⟨hsource,hgeom⟩ := Finset.mem_filter.mp hcell
  exact U1011OriginalFifteenFixedCellNative.native_row_upper hN hsource (policy i)
    (policy_lt_fifteen i) (gridBox n i.2) (gridBox_valid n i.2)
    (gridBox_lower_positive n i.2 3) ((mem_activeCells i).mp hi) (cell_subset_closed_box n i.2 hgeom)

end
end ImbalancedChen.P5Z.U1011OriginalFifteenNativeGridDispatch
