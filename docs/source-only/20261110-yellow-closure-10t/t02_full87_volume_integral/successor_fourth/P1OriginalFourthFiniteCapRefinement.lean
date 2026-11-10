import ImbalancedChen.P1OriginalFourthActualSourceCoverage

/-! SOURCE_ONLY / UNCOMPILED.
One finite fine-mesh threshold for ALL original rows and ALL actual old
coarse labels. Each compact patch is the original row's interior trim
intersected with the CLOSED old mesh box. The old cap is that label's
actual Gamma-2e, not a constant asserted for the original rectangle.
The existing selected-prefix selector supplies checked constant caps,
unique half-open ownership, and its actual lookup on every patch.
-/
namespace ImbalancedChen.P1OriginalFourthFiniteCapRefinement
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalFourthCapProducerInterface P1OriginalCoarseContinuation
open P5OriginalFourthFifthSourceInputs P1OriginalFourthAllRowsAdmission
open P1OriginalFourthCommonHistoricalMesh

def patchLower (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m) : Point :=
  fun i => max ((r.lower i : ℝ) + delta) (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ)

def patchUpper (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m) : Point :=
  fun i => min ((r.upper i : ℝ) - delta) (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ)

def patch (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m) : Set Point :=
  Icc (patchLower r delta m j) (patchUpper r delta m j)

theorem patch_compact (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m) :
    IsCompact (patch r delta m j) := isCompact_Icc

theorem patch_subset_trim (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m) :
    patch r delta m j ⊆ trimmedBox r delta := by
  intro t ht i
  exact ⟨(le_max_left _ _).trans (ht.1 i),(ht.2 i).trans (min_le_left _ _)⟩

theorem trim_mem_patch_of_mesh (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m)
    (t : Point) (ht : t ∈ trimmedBox r delta)
    (hj : t ∈ logPrimeMeshCell 0 (19 / 96) m j) : t ∈ patch r delta m j := by
  have hlo (i : Fin 4) : (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) ≤ t i := by
    simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using
      (congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i).trans_le
        (mem_logPrimeMeshCell.mp hj i).1
  have hhi (i : Fin 4) : t i ≤ (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) := by
    simpa only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] using
      (mem_logPrimeMeshCell.mp hj i).2.le.trans_eq
        (congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i).symm
  exact ⟨fun i => max_le (ht i).1 (hlo i),fun i => le_min (ht i).2 (hhi i)⟩

theorem patch_coarse (r : ProducerRow) (delta : ℝ) (m : ℕ) (j : FourthCell m)
    (t : Point) (ht : t ∈ patch r delta m j) :
    (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 4) j)).InBox
      (t 0) (t 1) (t 2) := by
  have hL (i : Fin 4) : (qLogPrimeMeshLo 0 (19 / 96) m j i : ℝ) ≤ t i :=
    (le_max_right _ _).trans (ht.1 i)
  have hU (i : Fin 4) : t i ≤ (qLogPrimeMeshHi 0 (19 / 96) m j i : ℝ) :=
    (ht.2 i).trans (min_le_right _ _)
  change (qLogPrimeMeshLo 0 (19 / 96) m j 0 : ℝ) ≤ t 0 ∧
    t 0 ≤ (qLogPrimeMeshHi 0 (19 / 96) m j 0 : ℝ) ∧
    (qLogPrimeMeshLo 0 (19 / 96) m j 1 : ℝ) ≤ t 1 ∧
    t 1 ≤ (qLogPrimeMeshHi 0 (19 / 96) m j 1 : ℝ) ∧
    (qLogPrimeMeshLo 0 (19 / 96) m j 2 : ℝ) ≤ t 2 ∧
    t 2 ≤ (qLogPrimeMeshHi 0 (19 / 96) m j 2 : ℝ)
  exact ⟨hL 0,hU 0,hL 1,hU 1,hL 2,hU 2⟩

theorem patch_subset_prime_box (r : ProducerRow) (hr : r ∈ originalRows4)
    {delta : ℝ} (hd : 0 ≤ delta) (m : ℕ) (j : FourthCell m) :
    patch r delta m j ⊆ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  intro t ht
  have hb := trimmedBox_subset r hd (patch_subset_trim r delta m j ht)
  have hg := originalRows4_geometry r hr
  have ho := r.ordered hg t hb
  have hu : t 0 ≤ (39 / 200 : ℝ) := by
    have hh : (r.upper 0 : ℝ) ≤ (39 / 200 : ℝ) := by exact_mod_cast hg.2.2.2.2.2.1
    exact (hb.2 0).trans hh
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i <;> constructor <;> linarith [ho.1.1,ho.1.2.1,ho.1.2.2.1,ho.2.1,ho.2.2]

theorem patch_strict_license (r : ProducerRow) (hr : r ∈ originalRows4)
    {delta : ℝ} (hd : 0 ≤ delta) (e : ℚ) (he : 0 ≤ e) (m : ℕ) (j : FourthCell m)
    (t : Point) (ht : t ∈ patch r delta m j) :
    SelectedPrefixLicense r.selected (thirdCellExponent e m j) (299 / 500) t :=
  producer_selectedPrefixLicense r (originalRows4_geometry r hr) e he m j t
    (trimmedBox_subset r hd (patch_subset_trim r delta m j ht))
    (patch_coarse r delta m j t ht)

/-- One threshold for the complete finite original bank times every old
label; the arbitrary fine resolution remains free above that threshold.
This is a finite maximum of existing compact-refinement thresholds.
-/
theorem exists_all_original_checked_refinements (delta : ℝ) (hd : 0 ≤ delta)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r ∈ originalRows4, ∀ j : FourthCell m,
      ∀ k ∈ selectedPrefixMeetingCells 0 (19 / 96) n (patch r delta m j),
      selectedBoxCapCheck r.selected (thirdCellExponent e m j) (299 / 500)
        (qLogPrimeMeshLo 0 (19 / 96) n k) (qLogPrimeMeshHi 0 (19 / 96) n k) = true := by
  let pairs := originalRows4.product (Finset.univ : Finset (FourthCell m))
  have H (a : ProducerRow × FourthCell m) (ha : a ∈ pairs) :
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ k ∈ selectedPrefixMeetingCells 0 (19 / 96) n (patch a.1 delta m a.2),
        selectedBoxCapCheck a.1.selected (thirdCellExponent e m a.2) (299 / 500)
          (qLogPrimeMeshLo 0 (19 / 96) n k) (qLogPrimeMeshHi 0 (19 / 96) n k) = true := by
    exact exists_selectedPrefixMeetingCells_check_threshold a.1.selected
      (thirdCellExponent e m a.2) (299 / 500) 0 (19 / 96) (by norm_num)
      (patch a.1 delta m a.2) (patch_compact a.1 delta m a.2)
      (patch_strict_license a.1 (Finset.mem_product.mp ha).1 hd e he m a.2)
  let threshold (a : ProducerRow × FourthCell m) : ℕ :=
    if ha : a ∈ pairs then Classical.choose (H a ha) else 0
  refine ⟨pairs.sup threshold,?_⟩
  intro n hn r hr j k hk
  have ha : (r,j) ∈ pairs := Finset.mem_product.mpr ⟨hr,Finset.mem_univ _⟩
  have hbound : threshold (r,j) ≤ n := (Finset.le_sup (f := threshold) ha).trans hn
  have hvalue : threshold (r,j) = Classical.choose (H (r,j) ha) := dif_pos ha
  rw [hvalue] at hbound
  exact Classical.choose_spec (H (r,j) ha) n hbound k hk

/-- Same checked fine mesh, actual half-open ownership, and actual finite
lookup. Empty patches need no invented positive-volume witness.
-/
theorem exists_all_original_constant_cap_tables (delta : ℝ) (hd : 0 ≤ delta)
    (e : ℚ) (he : 0 ≤ e) (m : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r ∈ originalRows4, ∀ j : FourthCell m,
      let J := selectedPrefixMeetingCells 0 (19 / 96) n (patch r delta m j)
      (∀ k ∈ J, selectedBoxCapCheck r.selected (thirdCellExponent e m j) (299 / 500)
        (qLogPrimeMeshLo 0 (19 / 96) n k) (qLogPrimeMeshHi 0 (19 / 96) n k) = true) ∧
      (∀ t ∈ patch r delta m j, ∃! k, k ∈ J ∧ t ∈ logPrimeMeshCell 0 (19 / 96) n k) ∧
      (∀ t ∈ patch r delta m j, (thirdCellExponent e m j : ℝ) <
        selectedPrefixMeshCap r.selected (thirdCellExponent e m j) (299 / 500) 0 (19 / 96) n J t) := by
  obtain ⟨n0,hn0⟩ := exists_all_original_checked_refinements delta hd e he m
  refine ⟨n0,?_⟩
  intro n hn r hr j
  let J := selectedPrefixMeetingCells 0 (19 / 96) n (patch r delta m j)
  have hc := hn0 n hn r hr j
  refine ⟨hc,?_,?_⟩
  · intro t ht
    exact selectedPrefixMeetingCells_unique_cover 0 (19 / 96) (by norm_num) n
      (patch r delta m j) (patch_subset_prime_box r hr hd m j) ht
  · intro t ht
    obtain ⟨k,hk,_⟩ := selectedPrefixMeetingCells_unique_cover 0 (19 / 96) (by norm_num) n
      (patch r delta m j) (patch_subset_prime_box r hr hd m j) ht
    exact (selectedPrefixMeshCap_on_cell_sound r.selected (thirdCellExponent e m j) (299 / 500)
      0 (19 / 96) (by norm_num) n J hc t k hk.1 hk.2).1

end
end ImbalancedChen.P1OriginalFourthFiniteCapRefinement
