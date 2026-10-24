import ImbalancedChen.ActualSelectedPrefixCapSelector

/-!
# Actual selected-history lookup on a common intersection refinement

Each input is literal finite rational mesh data. Refined labels are the
nonempty intersections of adopted half-open cells. Their lookup is a sum
of fixed rational minimum-cap increments, with the same old fallback.
Its equality with the minimum of the two existing actual selectors is
proved at every point, including points outside either adopted union.

The common-mask whole-cell licenses and actual ancestor freezing are
inherited from the existing checked selectors. Distinct masks would need
additional cross-licenses for their different selected-square expressions;
no such implication is asserted. Original 22-policy data, coverage, and
its binding to these finite selectors remain unproved and are not inputs
disguised as gain or density assumptions.
-/

namespace ImbalancedChen.P2MinSelectedLookupRefinement

noncomputable section

open Set VariableEnvelope
open scoped Classical BigOperators

/-- Raw finite selector data, without a target-policy or saving field. -/
structure MeshFamily (d : ℕ) where
  a : ℚ
  b : ℚ
  mesh : ℕ
  labels : Finset (Fin d → Fin (mesh + 1))

namespace MeshFamily

def Label {d : ℕ} (F : MeshFamily d) := Fin d → Fin (F.mesh + 1)

def cell {d : ℕ} (F : MeshFamily d) (j : F.Label) : Set (Fin d → ℝ) :=
  logPrimeMeshCell (F.a : ℝ) (F.b : ℝ) F.mesh j

def cap {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (j : F.Label) : ℚ :=
  selectedBoxCap I old nu (qLogPrimeMeshLo F.a F.b F.mesh j)
    (qLogPrimeMeshHi F.a F.b F.mesh j)

def lookup {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (t : Fin d → ℝ) : ℚ :=
  selectedPrefixMeshCap I old nu F.a F.b F.mesh F.labels t

def Checked {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ) : Prop :=
  ∀ j ∈ F.labels, selectedBoxCapCheck I old nu
    (qLogPrimeMeshLo F.a F.b F.mesh j) (qLogPrimeMeshHi F.a F.b F.mesh j) = true

theorem lookup_on_cell {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hab : F.a ≤ F.b) (j : F.Label) (hj : j ∈ F.labels)
    (t : Fin d → ℝ) (ht : t ∈ F.cell j) :
    F.lookup I old nu t = F.cap I old nu j :=
  selectedPrefixMeshCap_on_cell I old nu F.a F.b hab F.mesh F.labels t j hj ht

theorem lookup_outside {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (t : Fin d → ℝ) (ht : ∀ j ∈ F.labels, t ∉ F.cell j) :
    F.lookup I old nu t = old :=
  selectedPrefixMeshCap_outside I old nu F.a F.b F.mesh F.labels t ht

theorem lookup_ge_old {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hc : F.Checked I old nu) (t : Fin d → ℝ) :
    old ≤ F.lookup I old nu t :=
  selectedPrefixMeshCap_ge_old I old nu F.a F.b F.mesh F.labels hc t

theorem cap_sound {d : ℕ} (F : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hab : F.a ≤ F.b) (hc : F.Checked I old nu)
    (j : F.Label) (hj : j ∈ F.labels) (t : Fin d → ℝ) (ht : t ∈ F.cell j) :
    (old : ℝ) < F.cap I old nu j ∧ (F.cap I old nu j : ℝ) < nu ∧
      (1 / 2 : ℝ) < F.cap I old nu j ∧
      (∀ i, prefixSquareExpr t i < F.cap I old nu j) ∧
      (∀ i ∉ I, selectedSquareExpr I t i < F.cap I old nu j) ∧
      (F.cap I old nu j : ℝ) < v (∑ i ∈ I, t i) := by
  have h := selectedPrefixMeshCap_on_cell_sound I old nu F.a F.b hab F.mesh
    F.labels hc t j hj ht
  rw [selectedPrefixMeshCap_on_cell I old nu F.a F.b hab F.mesh F.labels t j hj ht] at h
  exact h

end MeshFamily

def intersectionCell {d : ℕ} (F G : MeshFamily d) (p : F.Label × G.Label) :
    Set (Fin d → ℝ) := F.cell p.1 ∩ G.cell p.2

def intersectionLo {d : ℕ} (F G : MeshFamily d) (p : F.Label × G.Label) : Fin d → ℚ :=
  fun i => max (qLogPrimeMeshLo F.a F.b F.mesh p.1 i)
    (qLogPrimeMeshLo G.a G.b G.mesh p.2 i)

def intersectionHi {d : ℕ} (F G : MeshFamily d) (p : F.Label × G.Label) : Fin d → ℚ :=
  fun i => min (qLogPrimeMeshHi F.a F.b F.mesh p.1 i)
    (qLogPrimeMeshHi G.a G.b G.mesh p.2 i)

/-- The actual intersection is a rational half-open box, with no endpoint
perturbation and no assertion that an empty intersection is nonempty. -/
theorem intersectionCell_eq_box {d : ℕ} (F G : MeshFamily d) (p : F.Label × G.Label) :
    intersectionCell F G p =
      logPrimeBox (fun i => (intersectionLo F G p i : ℝ))
        (fun i => (intersectionHi F G p i : ℝ)) := by
  have hcastLo (i : Fin d) : ((intersectionLo F G p i : ℚ) : ℝ) =
      max (logPrimeMeshLo (F.a : ℝ) (F.b : ℝ) F.mesh p.1 i)
        (logPrimeMeshLo (G.a : ℝ) (G.b : ℝ) G.mesh p.2 i) := by
    simp [intersectionLo, qLogPrimeMeshLo, logPrimeMeshLo]
  have hcastHi (i : Fin d) : ((intersectionHi F G p i : ℚ) : ℝ) =
      min (logPrimeMeshHi (F.a : ℝ) (F.b : ℝ) F.mesh p.1 i)
        (logPrimeMeshHi (G.a : ℝ) (G.b : ℝ) G.mesh p.2 i) := by
    simp [intersectionHi, qLogPrimeMeshHi, logPrimeMeshHi]
  ext t
  constructor
  · intro ht
    apply mem_logPrimeBox.mpr
    intro i
    rw [hcastLo i, hcastHi i]
    have hf := mem_logPrimeMeshCell.mp ht.1 i
    have hg := mem_logPrimeMeshCell.mp ht.2 i
    exact ⟨max_le hf.1 hg.1, lt_min hf.2 hg.2⟩
  · intro ht
    have h := mem_logPrimeBox.mp ht
    constructor <;> apply mem_logPrimeMeshCell.mpr <;> intro i
    · have hi := h i
      rw [hcastLo i, hcastHi i] at hi
      exact ⟨(le_max_left _ _).trans hi.1, hi.2.trans_le (min_le_left _ _)⟩
    · have hi := h i
      rw [hcastLo i, hcastHi i] at hi
      exact ⟨(le_max_right _ _).trans hi.1, hi.2.trans_le (min_le_right _ _)⟩

def refinementLabels {d : ℕ} (F G : MeshFamily d) : Finset (F.Label × G.Label) :=
  (F.labels.product G.labels).filter (fun p => (intersectionCell F G p).Nonempty)

theorem mem_refinementLabels {d : ℕ} (F G : MeshFamily d) (p : F.Label × G.Label) :
    p ∈ refinementLabels F G ↔
      (p.1 ∈ F.labels ∧ p.2 ∈ G.labels) ∧ (intersectionCell F G p).Nonempty := by
  simp only [refinementLabels, Finset.mem_filter, Finset.mem_product]

theorem intersectionCell_unique {d : ℕ} (F G : MeshFamily d)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b) (p q : F.Label × G.Label)
    (t : Fin d → ℝ) (hp : t ∈ intersectionCell F G p) (hq : t ∈ intersectionCell F G q) :
    p = q := by
  have hf : (F.a : ℝ) ≤ F.b := by exact_mod_cast hF
  have hg : (G.a : ℝ) ≤ G.b := by exact_mod_cast hG
  exact Prod.ext (logPrimeMeshCell_unique hf hp.1 hq.1)
    (logPrimeMeshCell_unique hg hp.2 hq.2)

theorem refinementLabels_unique_cover {d : ℕ} (F G : MeshFamily d)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b) (t : Fin d → ℝ)
    (hf : ∃ j ∈ F.labels, t ∈ F.cell j) (hg : ∃ k ∈ G.labels, t ∈ G.cell k) :
    ∃! p : F.Label × G.Label, p ∈ refinementLabels F G ∧ t ∈ intersectionCell F G p := by
  obtain ⟨j, hj, htj⟩ := hf
  obtain ⟨k, hk, htk⟩ := hg
  have hp : (j, k) ∈ refinementLabels F G :=
    (mem_refinementLabels F G _).mpr ⟨⟨hj, hk⟩, ⟨t, htj, htk⟩⟩
  refine ⟨(j, k), ⟨hp, htj, htk⟩, ?_⟩
  intro q hq
  exact intersectionCell_unique F G hF hG q (j, k) t hq.2 ⟨htj, htk⟩

/-- The two successful original whole-box checks license their minimum
throughout the closed intersection, including every common endpoint. This
does not replace that fixed minimum by a newly recomputed midpoint cap. -/
theorem intersectionCap_closed_sound {d : ℕ} (F G : MeshFamily d)
    (I : Finset (Fin d)) (old nu : ℚ) (hcF : F.Checked I old nu)
    (hcG : G.Checked I old nu) (p : F.Label × G.Label)
    (hp : p ∈ refinementLabels F G) (t : Fin d → ℝ)
    (hl : ∀ i, (intersectionLo F G p i : ℝ) ≤ t i)
    (hu : ∀ i, t i ≤ (intersectionHi F G p i : ℝ)) :
    (old : ℝ) < (min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ) ∧
      ((min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ) : ℝ) < nu ∧
      (1 / 2 : ℝ) < (min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ) ∧
      (∀ i, prefixSquareExpr t i < (min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ)) ∧
      (∀ i ∉ I, selectedSquareExpr I t i <
        (min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ)) ∧
      ((min (F.cap I old nu p.1) (G.cap I old nu p.2) : ℚ) : ℝ) < v (∑ i ∈ I, t i) := by
  have hm := (mem_refinementLabels F G p).mp hp
  have hflo (i : Fin d) : (qLogPrimeMeshLo F.a F.b F.mesh p.1 i : ℝ) ≤ t i := by
    have h : (qLogPrimeMeshLo F.a F.b F.mesh p.1 i : ℝ) ≤ intersectionLo F G p i := by
      exact_mod_cast (le_max_left (qLogPrimeMeshLo F.a F.b F.mesh p.1 i)
        (qLogPrimeMeshLo G.a G.b G.mesh p.2 i))
    exact h.trans (hl i)
  have hglo (i : Fin d) : (qLogPrimeMeshLo G.a G.b G.mesh p.2 i : ℝ) ≤ t i := by
    have h : (qLogPrimeMeshLo G.a G.b G.mesh p.2 i : ℝ) ≤ intersectionLo F G p i := by
      exact_mod_cast (le_max_right (qLogPrimeMeshLo F.a F.b F.mesh p.1 i)
        (qLogPrimeMeshLo G.a G.b G.mesh p.2 i))
    exact h.trans (hl i)
  have hfhi (i : Fin d) : t i ≤ (qLogPrimeMeshHi F.a F.b F.mesh p.1 i : ℝ) := by
    have h : (intersectionHi F G p i : ℝ) ≤ qLogPrimeMeshHi F.a F.b F.mesh p.1 i := by
      exact_mod_cast (min_le_left (qLogPrimeMeshHi F.a F.b F.mesh p.1 i)
        (qLogPrimeMeshHi G.a G.b G.mesh p.2 i))
    exact (hu i).trans h
  have hghi (i : Fin d) : t i ≤ (qLogPrimeMeshHi G.a G.b G.mesh p.2 i : ℝ) := by
    have h : (intersectionHi F G p i : ℝ) ≤ qLogPrimeMeshHi G.a G.b G.mesh p.2 i := by
      exact_mod_cast (min_le_right (qLogPrimeMeshHi F.a F.b F.mesh p.1 i)
        (qLogPrimeMeshHi G.a G.b G.mesh p.2 i))
    exact (hu i).trans h
  have hf := selectedBoxCapCheck_sound I old nu _ _ (hcF p.1 hm.1.1) t hflo hfhi
  have hg := selectedBoxCapCheck_sound I old nu _ _ (hcG p.2 hm.1.2) t hglo hghi
  rcases le_total (F.cap I old nu p.1) (G.cap I old nu p.2) with h | h
  · simpa only [min_eq_left h] using hf
  · simpa only [min_eq_right h] using hg

def refinedLookup {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (t : Fin d → ℝ) : ℚ :=
  old + ∑ p ∈ refinementLabels F G,
    if t ∈ intersectionCell F G p then min (F.cap I old nu p.1) (G.cap I old nu p.2) - old
    else 0

theorem refinedLookup_on_cell {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (p : F.Label × G.Label) (hp : p ∈ refinementLabels F G)
    (t : Fin d → ℝ) (ht : t ∈ intersectionCell F G p) :
    refinedLookup F G I old nu t = min (F.cap I old nu p.1) (G.cap I old nu p.2) := by
  unfold refinedLookup
  rw [Finset.sum_eq_single_of_mem p hp]
  · rw [if_pos ht]
    ring
  · intro q _hqm hqp
    apply if_neg
    intro hq
    exact hqp (intersectionCell_unique F G hF hG q p t hq ht)

theorem refinedLookup_outside {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (t : Fin d → ℝ)
    (ht : ∀ p ∈ refinementLabels F G, t ∉ intersectionCell F G p) :
    refinedLookup F G I old nu t = old := by
  unfold refinedLookup
  rw [Finset.sum_eq_zero (fun p hp => if_neg (ht p hp)), add_zero]

/-- Global equality, paying both outside-region cases with the checked
old-cap lower bounds rather than assuming active coverage. -/
theorem refinedLookup_eq_min {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu) (t : Fin d → ℝ) :
    refinedLookup F G I old nu t = min (F.lookup I old nu t) (G.lookup I old nu t) := by
  by_cases hf : ∃ j ∈ F.labels, t ∈ F.cell j
  · obtain ⟨j, hj, htj⟩ := hf
    by_cases hg : ∃ k ∈ G.labels, t ∈ G.cell k
    · obtain ⟨k, hk, htk⟩ := hg
      have hp : (j, k) ∈ refinementLabels F G :=
        (mem_refinementLabels F G _).mpr ⟨⟨hj, hk⟩, ⟨t, htj, htk⟩⟩
      rw [refinedLookup_on_cell F G I old nu hF hG (j, k) hp t ⟨htj, htk⟩,
        F.lookup_on_cell I old nu hF j hj t htj, G.lookup_on_cell I old nu hG k hk t htk]
    · have hgo : ∀ k ∈ G.labels, t ∉ G.cell k := fun k hk ht => hg ⟨k, hk, ht⟩
      have hout : ∀ p ∈ refinementLabels F G, t ∉ intersectionCell F G p := by
        intro p hp ht
        exact hgo p.2 ((mem_refinementLabels F G p).mp hp).1.2 ht.2
      rw [refinedLookup_outside F G I old nu t hout, G.lookup_outside I old nu t hgo]
      exact (min_eq_right (F.lookup_ge_old I old nu hcF t)).symm
  · have hfo : ∀ j ∈ F.labels, t ∉ F.cell j := fun j hj ht => hf ⟨j, hj, ht⟩
    have hout : ∀ p ∈ refinementLabels F G, t ∉ intersectionCell F G p := by
      intro p hp ht
      exact hfo p.1 ((mem_refinementLabels F G p).mp hp).1.1 ht.1
    rw [refinedLookup_outside F G I old nu t hout, F.lookup_outside I old nu t hfo]
    exact (min_eq_left (G.lookup_ge_old I old nu hcG t)).symm

theorem refinedLookup_ge_old {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu) (t : Fin d → ℝ) :
    old ≤ refinedLookup F G I old nu t := by
  rw [refinedLookup_eq_min F G I old nu hF hG hcF hcG t]
  exact le_min (F.lookup_ge_old I old nu hcF t) (G.lookup_ge_old I old nu hcG t)

/-- Every existing whole-box semantic license survives on every refined
intersection. The chosen rational value is fixed throughout that cell. -/
theorem refinedLookup_on_cell_sound {d : ℕ} (F G : MeshFamily d) (I : Finset (Fin d))
    (old nu : ℚ) (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu)
    (p : F.Label × G.Label) (hp : p ∈ refinementLabels F G)
    (t : Fin d → ℝ) (ht : t ∈ intersectionCell F G p) :
    (old : ℝ) < refinedLookup F G I old nu t ∧
      (refinedLookup F G I old nu t : ℝ) < nu ∧
      (1 / 2 : ℝ) < refinedLookup F G I old nu t ∧
      (∀ i, prefixSquareExpr t i < refinedLookup F G I old nu t) ∧
      (∀ i ∉ I, selectedSquareExpr I t i < refinedLookup F G I old nu t) ∧
      (refinedLookup F G I old nu t : ℝ) < v (∑ i ∈ I, t i) := by
  have hm := (mem_refinementLabels F G p).mp hp
  have hf := F.cap_sound I old nu hF hcF p.1 hm.1.1 t ht.1
  have hg := G.cap_sound I old nu hG hcG p.2 hm.1.2 t ht.2
  rw [refinedLookup_on_cell F G I old nu hF hG p hp t ht]
  rcases le_total (F.cap I old nu p.1) (G.cap I old nu p.2) with h | h
  · simpa only [min_eq_left h] using hf
  · simpa only [min_eq_right h] using hg

def actualMinSelectedLevel {d : ℕ} (N : ℝ) (F G : MeshFamily d)
    (I : Finset (Fin d)) (old nu : ℚ) (history : List ℕ) : ℝ :=
  N ^ (refinedLookup F G I old nu (primeHistoryLogCoordinates N d history) : ℝ)

/-- Equality of literal levels on actual histories, not just exponent
functions or a target record. Outside either selected union the old level
is recovered by the preceding global lookup theorem. -/
theorem actualMinSelectedLevel_eq_min {d : ℕ} (N : ℝ) (hN : 1 ≤ N)
    (F G : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu) (history : List ℕ) :
    actualMinSelectedLevel N F G I old nu history =
      min (actualSelectedPrefixLevel N I old nu F.a F.b F.mesh F.labels history)
        (actualSelectedPrefixLevel N I old nu G.a G.b G.mesh G.labels history) := by
  let t := primeHistoryLogCoordinates N d history
  change N ^ (refinedLookup F G I old nu t : ℝ) =
    min (N ^ (F.lookup I old nu t : ℝ)) (N ^ (G.lookup I old nu t : ℝ))
  rw [refinedLookup_eq_min F G I old nu hF hG hcF hcG t]
  rcases le_total (F.lookup I old nu t) (G.lookup I old nu t) with h | h
  · rw [min_eq_left h]
    have hpow : N ^ (F.lookup I old nu t : ℝ) ≤ N ^ (G.lookup I old nu t : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hN
      exact_mod_cast h
    exact (min_eq_left hpow).symm
  · rw [min_eq_right h]
    have hpow : N ^ (G.lookup I old nu t : ℝ) ≤ N ^ (F.lookup I old nu t : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hN
      exact_mod_cast h
    exact (min_eq_right hpow).symm

theorem actualMinSelectedLevel_outside_either {d : ℕ} (N : ℝ)
    (F G : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ) (history : List ℕ)
    (hout : (∀ j ∈ F.labels, primeHistoryLogCoordinates N d history ∉ F.cell j) ∨
      (∀ k ∈ G.labels, primeHistoryLogCoordinates N d history ∉ G.cell k)) :
    actualMinSelectedLevel N F G I old nu history = N ^ (old : ℝ) := by
  have hNo : ∀ p ∈ refinementLabels F G,
      primeHistoryLogCoordinates N d history ∉ intersectionCell F G p := by
    intro p hp ht
    have hm := (mem_refinementLabels F G p).mp hp
    rcases hout with hf | hg
    · exact hf p.1 hm.1.1 ht.1
    · exact hg p.2 hm.1.2 ht.2
  unfold actualMinSelectedLevel
  rw [refinedLookup_outside F G I old nu _ hNo]

theorem actualMinSelectedLevel_inherited_admissible {d : ℕ} (N : ℝ) (hN : 1 ≤ N)
    (F G : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu)
    (lower : Bool) (parent history : List ℕ)
    (hparent : ordinaryRosserPrefixAdmissible lower (N ^ (old : ℝ)) parent) :
    ordinaryRosserPrefixAdmissible lower (actualMinSelectedLevel N F G I old nu history) parent := by
  apply ordinaryRosserPrefixAdmissible_mono lower parent _ hparent
  apply Real.rpow_le_rpow_of_exponent_le hN
  exact_mod_cast refinedLookup_ge_old F G I old nu hF hG hcF hcG
    (primeHistoryLogCoordinates N d history)

/-- Both families' literal integer square gates hold at their minimum
history level on an adopted common cell. -/
theorem actualMinSelectedLevel_square_gates {d : ℕ} (N : ℝ) (hN : 1 < N)
    (F G : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu)
    (history : List ℕ) (hlen : history.length = d) (hpos : ∀ q ∈ history, 0 < q)
    (p : F.Label × G.Label) (hp : p ∈ refinementLabels F G)
    (ht : primeHistoryLogCoordinates N d history ∈ intersectionCell F G p) :
    (∀ i, ((∏ k ∈ Finset.univ.filter (fun k => k < i),
        primeHistoryTuple d history k : ℕ) : ℝ) *
      (primeHistoryTuple d history i : ℝ) ^ 2 < actualMinSelectedLevel N F G I old nu history) ∧
    (∀ i ∉ I, ((∏ k ∈ I, primeHistoryTuple d history k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k => k < i ∧ k ∉ I),
        primeHistoryTuple d history k : ℕ) : ℝ) *
      (primeHistoryTuple d history i : ℝ) ^ 2 < actualMinSelectedLevel N F G I old nu history) := by
  have hm := (mem_refinementLabels F G p).mp hp
  have hf := actualSelectedPrefixLevel_square_gates N hN I old nu F.a F.b hF F.mesh F.labels
    hcF history hlen hpos p.1 hm.1.1 ht.1
  have hg := actualSelectedPrefixLevel_square_gates N hN I old nu G.a G.b hG G.mesh G.labels
    hcG history hlen hpos p.2 hm.1.2 ht.2
  rw [actualMinSelectedLevel_eq_min N hN.le F G I old nu hF hG hcF hcG history]
  exact ⟨fun i => lt_min (hf.1 i) (hg.1 i), fun i hi => lt_min (hf.2 i hi) (hg.2 i hi)⟩

def actualMinSelectedFrozenLevel {d : ℕ} (N : ℝ) (F G : MeshFamily d)
    (I : Finset (Fin d)) (old nu : ℚ) (history : List ℕ) : ℝ :=
  actualMinSelectedLevel N F G I old nu (rosserAncestor d history)

theorem actualMinSelectedFrozenLevel_eq_min {d : ℕ} (N : ℝ) (hN : 1 ≤ N)
    (F G : MeshFamily d) (I : Finset (Fin d)) (old nu : ℚ)
    (hF : F.a ≤ F.b) (hG : G.a ≤ G.b)
    (hcF : F.Checked I old nu) (hcG : G.Checked I old nu) (history : List ℕ) :
    actualMinSelectedFrozenLevel N F G I old nu history =
      min (actualSelectedPrefixFrozenLevel N I old nu F.a F.b F.mesh F.labels history)
        (actualSelectedPrefixFrozenLevel N I old nu G.a G.b G.mesh G.labels history) := by
  exact actualMinSelectedLevel_eq_min N hN F G I old nu hF hG hcF hcG (rosserAncestor d history)

theorem actualMinSelectedFrozenLevel_append {d : ℕ} (N : ℝ) (F G : MeshFamily d)
    (I : Finset (Fin d)) (old nu : ℚ) (later history : List ℕ) (hlen : d ≤ history.length) :
    actualMinSelectedFrozenLevel N F G I old nu (later ++ history) =
      actualMinSelectedFrozenLevel N F G I old nu history := by
  unfold actualMinSelectedFrozenLevel
  rw [rosserAncestor_append d later history hlen]

theorem actualMinSelectedFrozenLevel_at_rank {d : ℕ} (N : ℝ) (F G : MeshFamily d)
    (I : Finset (Fin d)) (old nu : ℚ) (history : List ℕ) (hlen : history.length = d) :
    actualMinSelectedFrozenLevel N F G I old nu history =
      actualMinSelectedLevel N F G I old nu history := by
  unfold actualMinSelectedFrozenLevel
  rw [rosserAncestor_self_of_length d history hlen]

end

end ImbalancedChen.P2MinSelectedLookupRefinement
