import ImbalancedChen.P1AffineCertifiedMesh
import ImbalancedChen.P1FiniteAffineQuantizerTable

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A finite rational grid accelerates the SAME exact affine-sign table. The
unapproved/equality branch retains the exact original sign-table evaluation;
it is not discarded or assigned a convenient constant. Every approved closed
box has one rational scalar output. Ancestor labels are literal projections
of a common grid, independent of later-coordinate acceptance.
-/
namespace ImbalancedChen.P1AffineCertifiedLookup
noncomputable section
open scoped Classical BigOperators
open Set P1FiniteAffineDecisionProgram P1AffineCertifiedMesh P1FiniteAffineQuantizerTable

/-- Half-open ownership; the total default is used only outside the cube. -/
def gridLabel {k : ℕ} (m : ℕ) (t : Fin k → ℝ) : Label k m :=
  if h : t ∈ cube k then Classical.choose (exists_logPrimeMeshCell 0 1 m h)
  else fun _ => 0

theorem gridLabel_mem {k : ℕ} (m : ℕ) (t : Fin k → ℝ) (ht : t ∈ cube k) :
    t ∈ cell m (gridLabel m t) := by
  unfold gridLabel
  rw [dif_pos ht]
  exact Classical.choose_spec (exists_logPrimeMeshCell 0 1 m ht)

theorem gridLabel_eq_of_mem {k : ℕ} (m : ℕ) (t : Fin k → ℝ)
    (j : Label k m) (ht : t ∈ cell m j) : gridLabel m t = j := by
  have hc := logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 1) m j ht
  exact logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 1) (gridLabel_mem m t hc) ht

theorem mem_covered_iff {k : ℕ} (p : Program k) (m : ℕ) (t : Fin k → ℝ) :
    t ∈ covered p m ↔ t ∈ cube k ∧ gridLabel m t ∈ approved p m := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    obtain ⟨hja, ht⟩ := mem_iUnion.mp hj
    exact ⟨logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 1) m j ht,
      (gridLabel_eq_of_mem m t j ht).symm ▸ hja⟩
  · rintro ⟨hc, hj⟩
    exact mem_iUnion.mpr ⟨gridLabel m t, mem_iUnion.mpr ⟨hj, gridLabel_mem m t hc⟩⟩

/-- The label of an ancestor is the restriction of the common ambient
label, even if a later-rank box is rejected. -/
theorem gridLabel_project {k d : ℕ} (f : Fin k → Fin d) (m : ℕ)
    (t : Fin d → ℝ) (ht : t ∈ cube d) :
    gridLabel m (fun i => t (f i)) = fun i => gridLabel m t (f i) := by
  apply gridLabel_eq_of_mem
  have hm := mem_logPrimeMeshCell.mp (gridLabel_mem m t ht)
  exact mem_logPrimeMeshCell.mpr (fun i => hm (f i))

/-- All closed endpoints are rational numbers fixed by m and the label. -/
def rationalLo {k : ℕ} (m : ℕ) (j : Label k m) : Fin k → ℚ :=
  fun i => ((j i).val : ℚ) / ((m : ℚ) + 1)
def rationalHi {k : ℕ} (m : ℕ) (j : Label k m) : Fin k → ℚ :=
  fun i => (((j i).val : ℚ) + 1) / ((m : ℚ) + 1)

theorem rational_endpoints {k : ℕ} (m : ℕ) (j : Label k m) :
    (fun i => (rationalLo m j i : ℝ)) = lo m j ∧
    (fun i => (rationalHi m j i : ℝ)) = hi m j := by
  constructor <;> funext i
  · simp [rationalLo, lo, logPrimeMeshLo, logPrimeMeshPoint, logPrimeMeshStep, div_eq_mul_inv]
  · simp [rationalHi, hi, logPrimeMeshHi, logPrimeMeshPoint, logPrimeMeshStep, div_eq_mul_inv]

def scalarLookup {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (m : ℕ) (t : Fin k → ℝ) : ℝ :=
  let q := protectedProgram n b p
  if t ∈ cube k ∧ gridLabel m t ∈ approved q m then
    scalarTable n b p (q.signature (center m (gridLabel m t)))
  else scalarTable n b p (q.signature t)

theorem scalarLookup_exact {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (m : ℕ) (t : Fin k → ℝ) :
    scalarLookup n b p m t = P1GuardFrozenFiniteCapAlgebra.protect n (b : ℝ) (p.eval t) := by
  unfold scalarLookup
  split_ifs with ht
  · apply scalarTable_on_region
    have hb := mem_logPrimeMeshCell.mp (gridLabel_mem m t ht.1)
    exact (certificate_on_approved (protectedProgram n b p) m (gridLabel m t)
      ht.2 t (fun i => (hb i).1) (fun i => (hb i).2.le)).1
  · exact scalarTable_exact n b p t

/-- On rejected or equality-crossing boxes the exact finite-sign table is
retained, including its nonstrict tie conventions. No wall value is lost. -/
theorem scalarLookup_fallback {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (m : ℕ) (t : Fin k → ℝ) (ht : t ∉ covered (protectedProgram n b p) m) :
    scalarLookup n b p m t = scalarTable n b p ((protectedProgram n b p).signature t) := by
  unfold scalarLookup
  rw [if_neg (fun h => ht ((mem_covered_iff _ _ _).mpr h))]

/-- Every point of the CLOSED certified box has the same rational output,
not merely points belonging to the source slice or sampled tuples. -/
theorem scalarTable_closed_box {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (m : ℕ) (j : Label k m) (hj : j ∈ approved (protectedProgram n b p) m) :
    ∃ a ∈ outputAlphabet n b, ∀ t : Fin k → ℝ,
      (∀ i, lo m j i ≤ t i) → (∀ i, t i ≤ hi m j i) →
      scalarLookup n b p m t = (a : ℝ) := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp
    (scalarTable_mem n b p ((protectedProgram n b p).signature (center m j)))
  refine ⟨a, ha, ?_⟩
  intro t hl hu
  rw [scalarLookup_exact]
  have hr := (certificate_on_approved (protectedProgram n b p) m j hj t hl hu).1
  rw [← scalarTable_on_region n b p _ t hr]
  exact heq.symm


/-- Intersect the fine own-rank box with the ORIGINAL third half-open
label. The extra label is finite and frozen at rank3; it is not a child
choice. max/min endpoints show the common refinement is still rectangular. -/
def taggedLo {k : ℕ} (hk : 3 ≤ k) (coarse m : ℕ)
    (j3 : Fin 3 → Fin (coarse + 1)) (j : Label k m) : Fin k → ℝ :=
  fun i => if h : i.val < 3 then
    max (lo m j i) (logPrimeMeshLo 0 (19 / 96) coarse j3 ⟨i.val, h⟩)
  else lo m j i

def taggedHi {k : ℕ} (hk : 3 ≤ k) (coarse m : ℕ)
    (j3 : Fin 3 → Fin (coarse + 1)) (j : Label k m) : Fin k → ℝ :=
  fun i => if h : i.val < 3 then
    min (hi m j i) (logPrimeMeshHi 0 (19 / 96) coarse j3 ⟨i.val, h⟩)
  else hi m j i

def taggedCell {k : ℕ} (hk : 3 ≤ k) (coarse m : ℕ)
    (j3 : Fin 3 → Fin (coarse + 1)) (j : Label k m) : Set (Fin k → ℝ) :=
  logPrimeBox (taggedLo hk coarse m j3 j) (taggedHi hk coarse m j3 j)

theorem taggedCell_exact {k : ℕ} (hk : 3 ≤ k) (coarse m : ℕ)
    (j3 : Fin 3 → Fin (coarse + 1)) (j : Label k m) (t : Fin k → ℝ) :
    t ∈ taggedCell hk coarse m j3 j ↔
      t ∈ cell m j ∧
      (fun i : Fin 3 => t (i.castLE hk)) ∈ logPrimeMeshCell 0 (19 / 96) coarse j3 := by
  constructor
  · intro ht
    have h := mem_logPrimeBox.mp ht
    constructor
    · apply mem_logPrimeMeshCell.mpr
      intro i
      have hh := h i
      by_cases hi3 : i.val < 3
      · simp only [taggedLo, taggedHi, dif_pos hi3] at hh
        exact ⟨(le_max_left _ _).trans hh.1, hh.2.trans_le (min_le_left _ _)⟩
      · simpa only [taggedLo, taggedHi, dif_neg hi3] using hh
    · apply mem_logPrimeMeshCell.mpr
      intro i
      have hh := h (i.castLE hk)
      simp only [taggedLo, taggedHi, dif_pos i.isLt] at hh
      exact ⟨(le_max_right _ _).trans hh.1, hh.2.trans_le (min_le_right _ _)⟩
  · rintro ⟨hf, hc⟩
    apply mem_logPrimeBox.mpr
    intro i
    have hh := mem_logPrimeMeshCell.mp hf i
    by_cases hi3 : i.val < 3
    · have ht3 := mem_logPrimeMeshCell.mp hc (⟨i.val, hi3⟩ : Fin 3)
      have he : (⟨i.val, hi3⟩ : Fin 3).castLE hk = i := Fin.ext rfl
      rw [he] at ht3
      simp only [taggedLo, taggedHi, dif_pos hi3]
      exact ⟨max_le hh.1 ht3.1, lt_min hh.2 ht3.2⟩
    · simpa only [taggedLo, taggedHi, dif_neg hi3] using hh

end
end ImbalancedChen.P1AffineCertifiedLookup
