import ImbalancedChen.P2Winner9LiftingGeometry
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact edge determinants from the original affine pulling flags. -/

namespace ImbalancedChen.P2Winner9PullingDeterminant

open P2Winner9LiftingGeometry (LiftingPlane PullingFace rowTail)
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix)

/-- The columns are edges from `b` to the other vertices in their original order. -/
def edgesFrom {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) (b : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => v (b.succAbove j) i - v b i

private def homogeneous {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i => Fin.cons 1 (v i)

private def translated {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) (b : Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j => homogeneous v i j + (if i = b then 0 else -1) * homogeneous v b j

private theorem translated_det {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) (b : Fin (n + 1)) :
    (translated v b).det = (homogeneous v).det :=
  Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = b then 0 else -1) b
    (by simp) (fun _ _ => rfl)

private theorem det_homogeneous {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) (b : Fin (n + 1)) :
    (homogeneous v).det = (-1 : ℚ)^b.val * (edgesFrom v b).det := by
  have hminor : (translated v b).submatrix b.succAbove Fin.succ = (edgesFrom v b).transpose := by
    ext i j
    change translated v b (b.succAbove i) j.succ = edgesFrom v b j i
    simp [translated, homogeneous, edgesFrom, sub_eq_add_neg]
  rw [← translated_det v b, Matrix.det_succ_column_zero, Finset.sum_eq_single b, hminor,
    Matrix.det_transpose]
  · simp [translated, homogeneous]
  · intro i _ hi
    simp [translated, homogeneous, hi]
  · simp

/-- The absolute determinant of an ordered simplex is independent of the chosen base vertex. -/
theorem abs_det_edgesFrom {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ)
    (a b : Fin (n + 1)) : |(edgesFrom v a).det| = |(edgesFrom v b).det| := by
  have habs (k : Fin (n + 1)) : |(homogeneous v).det| = |(edgesFrom v k).det| := by
    rw [det_homogeneous v k, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact (habs a).symm.trans (habs b)

/-- Edges based at the last vertex of the pulling flag. -/
def lastEdges {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  edgesFrom v (Fin.last n)

@[simp] theorem lastEdges_apply {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) (i j : Fin n) :
    lastEdges v i j = v j.castSucc i - v (Fin.last n) i := by
  simp [lastEdges, edgesFrom]

/-- The last-base determinant gives the same absolute Jacobian as the original first-base definition. -/
theorem abs_det_lastEdges (v : Fin 9 → Fin 8 → ℚ) :
    |(lastEdges v).det| = |(edgeMatrix v).det| := by
  have he : edgesFrom v 0 = edgeMatrix v := by
    ext i j
    simp [edgesFrom, edgeMatrix]
  rw [← he]
  exact abs_det_edgesFrom v (Fin.last 8) 0

/-- Each row of this matrix is the normal of the corresponding pulling plane. -/
def normalMatrix (g : Fin 8 → LiftingPlane) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (g i).coeff j

/-- A previously checked integer normal determinant can be cast to the rational formula. -/
theorem det_normalMatrix_integer (offset : Fin 8 → ℤ) (coeff : Matrix (Fin 8) (Fin 8) ℤ) :
    (normalMatrix (fun i => ⟨offset i, fun j => coeff i j⟩)).det = (coeff.det : ℚ) :=
  (Int.cast_det coeff).symm

/-- The absolute determinant can be reused for any ordering of the same normals. -/
theorem abs_det_normalMatrix_perm (g : Fin 8 → LiftingPlane) (perm : Equiv.Perm (Fin 8)) :
    |(normalMatrix (g ∘ perm)).det| = |(normalMatrix g).det| :=
  Matrix.abs_det_submatrix_equiv_equiv perm (Equiv.refl _) (normalMatrix g)

/-- Taking the dot product along an edge cancels the affine offset. -/
theorem normal_mul_last_apply (v : Fin 9 → Fin 8 → ℚ) (g : Fin 8 → LiftingPlane)
    (i j : Fin 8) :
    (normalMatrix g * lastEdges v) i j = (g i).evalQ (v j.castSucc) - (g i).evalQ (v (Fin.last 8)) := by
  simp only [Matrix.mul_apply, normalMatrix, lastEdges_apply, LiftingPlane.evalQ, mul_sub,
    Finset.sum_sub_distrib]
  ring

/-- The triangular product identifies the determinant before taking absolute values. -/
theorem det_product (v : Fin 9 → Fin 8 → ℚ) (g : Fin 8 → LiftingPlane)
    (hzero : ∀ i k, i.castSucc < k → (g i).evalQ (v k) = 0) :
    (normalMatrix g).det * (lastEdges v).det = ∏ i, (g i).evalQ (v i.castSucc) := by
  have hb (i : Fin 8) : (g i).evalQ (v (Fin.last 8)) = 0 :=
    hzero i (Fin.last 8) (Fin.castSucc_lt_last i)
  have htri : (normalMatrix g * lastEdges v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    rw [normal_mul_last_apply, hzero i j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij), hb i,
      sub_self]
  rw [← Matrix.det_mul, Matrix.det_of_lowerTriangular _ htri]
  exact Finset.prod_congr rfl (fun i _ => by rw [normal_mul_last_apply, hb i, sub_zero])

/-- The original absolute edge determinant is the product of the eight apex scores
 divided by the absolute determinant of the normal matrix. -/
theorem abs_det_of_flags (v : Fin 9 → Fin 8 → ℚ) (g : Fin 8 → LiftingPlane)
    (hzero : ∀ i k, i.castSucc < k → (g i).evalQ (v k) = 0)
    (hpos : ∀ i, 0 < (g i).evalQ (v i.castSucc)) :
    (normalMatrix g).det ≠ 0 ∧ (edgeMatrix v).det ≠ 0 ∧
      |(edgeMatrix v).det| = (∏ i, (g i).evalQ (v i.castSucc)) / |(normalMatrix g).det| := by
  have he := det_product v g hzero
  have hp : 0 < ∏ i, (g i).evalQ (v i.castSucc) := Finset.prod_pos fun i _ => hpos i
  obtain ⟨hn, hl⟩ := mul_ne_zero_iff.mp (he ▸ hp.ne' :
    (normalMatrix g).det * (lastEdges v).det ≠ 0)
  have hlast := abs_det_lastEdges v
  have hnl : |(normalMatrix g).det| ≠ 0 := (abs_pos.mpr hn).ne'
  refine ⟨hn, abs_pos.mp (hlast ▸ abs_pos.mpr hl), ?_⟩
  apply (eq_div_iff hnl).2
  rw [← hlast, mul_comm, ← abs_mul, he, abs_of_pos hp]

/-- Integer vertex scores and a checked normal determinant give the original
 absolute determinant by one division of integer products. -/
theorem abs_det_of_integer_scores (v : Fin 9 → Fin 8 → ℚ) (g : Fin 8 → LiftingPlane)
    (score : Fin 8 → ℤ) (den : Fin 8 → ℕ) (normalDet : ℤ)
    (hzero : ∀ i k, i.castSucc < k → (g i).evalQ (v k) = 0)
    (hpos : ∀ i, 0 < (g i).evalQ (v i.castSucc))
    (hscore : ∀ i, (g i).evalQ (v i.castSucc) = (score i : ℚ) / (den i : ℚ))
    (hd : (normalMatrix g).det = (normalDet : ℚ)) :
    (edgeMatrix v).det ≠ 0 ∧
      |(edgeMatrix v).det| = ((∏ i, score i : ℤ) : ℚ) /
        (((∏ i, den i : ℕ) : ℚ) * ((|normalDet| : ℤ) : ℚ)) := by
  obtain ⟨_, hv, he⟩ := abs_det_of_flags v g hzero hpos
  refine ⟨hv, ?_⟩
  simp only [he, hd, hscore, ← Int.cast_abs, Finset.prod_div_distrib, ← Nat.cast_prod,
    ← Int.cast_prod, div_div]

private theorem gate_checks {κ : Type*} {n : ℕ} {zeroes : κ → Finset (Fin n)}
    {face : Finset (Fin n)} {apex : Fin n} {tail : List (Fin n)} {gs : List κ}
    (h : PullingFace zeroes face apex tail gs) :
    ∀ (i : ℕ) (g : κ), gs[i]? = some g →
      (∀ v, (apex :: tail)[i]? = some v → v ∉ zeroes g) ∧
      (∀ j v, i < j → (apex :: tail)[j]? = some v → v ∈ zeroes g) := by
  induction h with
  | singleton _ _ =>
    intro i g hg
    simp at hg
  | @cone face apex next tail first rest _ _ hpos hrest ih =>
    intro i g hg
    cases i with
    | zero =>
      have he : first = g := by simpa using hg
      subst g
      constructor
      · intro v hv
        have he : apex = v := by simpa using hv
        exact he ▸ hpos
      · intro j v hj hv
        cases j with
        | zero => omega
        | succ j =>
          have htail : (next :: tail)[j]? = some v := by simpa using hv
          exact (Finset.mem_inter.mp (hrest.vertices_mem v (List.mem_of_getElem? htail))).2
    | succ i =>
      obtain ⟨hpos', hzero'⟩ := ih i g (by simpa using hg)
      constructor
      · intro v hv
        exact hpos' v (by simpa using hv)
      · intro j v hj hv
        cases j with
        | zero => omega
        | succ j => exact hzero' j v (Nat.lt_of_succ_lt_succ hj) (by simpa using hv)

/-- A checked pulling path supplies every triangular zero and every positive apex score. -/
theorem abs_det_from_pulling {κ : Type*} {n : ℕ} (points : Fin n → Fin 8 → ℚ)
    (gates : κ → LiftingPlane) (zeroes : κ → Finset (Fin n))
    (ids : Fin 9 → Fin n) (flags : Fin 8 → κ) {face : Finset (Fin n)}
    (h : PullingFace zeroes face (ids 0) (rowTail ids) (List.ofFn flags))
    (hzero : ∀ g v, v ∈ zeroes g ↔ (gates g).evalQ (points v) = 0)
    (hnonneg : ∀ g v, 0 ≤ (gates g).evalQ (points v)) :
    let p := fun i => gates (flags i)
    let v := fun i => points (ids i)
    (normalMatrix p).det ≠ 0 ∧ (edgeMatrix v).det ≠ 0 ∧
      |(edgeMatrix v).det| = (∏ i, (p i).evalQ (v i.castSucc)) / |(normalMatrix p).det| := by
  have hv (j : Fin 9) : (ids 0 :: rowTail ids)[j.val]? = some (ids j) := by
    unfold rowTail
    rw [← List.ofFn_succ]
    simp only [List.getElem?_ofFn, dif_pos j.isLt]
  have hg (i : Fin 8) : (List.ofFn flags)[i.val]? = some (flags i) := by
    simp only [List.getElem?_ofFn, dif_pos i.isLt]
  apply abs_det_of_flags
  · intro i j hj
    exact (hzero _ _).mp ((gate_checks h i.val (flags i) (hg i)).2 j.val (ids j) hj (hv j))
  · intro i
    refine lt_of_le_of_ne (hnonneg (flags i) (ids i.castSucc)) ?_
    intro he
    exact (gate_checks h i.val (flags i) (hg i)).1 _ (hv i.castSucc) ((hzero _ _).mpr he.symm)

/-- Read an eight-step path directly from the archived list of planes. -/
theorem abs_det_from_pullingList {κ : Type*} {n : ℕ} (points : Fin n → Fin 8 → ℚ)
    (gates : κ → LiftingPlane) (zeroes : κ → Finset (Fin n))
    (ids : Fin 9 → Fin n) (flags : List κ) (hlen : flags.length = 8) {face : Finset (Fin n)}
    (h : PullingFace zeroes face (ids 0) (rowTail ids) flags)
    (hzero : ∀ g v, v ∈ zeroes g ↔ (gates g).evalQ (points v) = 0)
    (hnonneg : ∀ g v, 0 ≤ (gates g).evalQ (points v)) :
    let p : Fin 8 → LiftingPlane := fun i => gates (flags[i.val]'(hlen.symm ▸ i.isLt))
    let v := fun i => points (ids i)
    (normalMatrix p).det ≠ 0 ∧ (edgeMatrix v).det ≠ 0 ∧
      |(edgeMatrix v).det| = (∏ i, (p i).evalQ (v i.castSucc)) / |(normalMatrix p).det| := by
  let f : Fin 8 → κ := fun i => flags[i.val]'(hlen.symm ▸ i.isLt)
  have he : List.ofFn f = flags := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hj
    simp only [List.getElem_ofFn, f]
  exact abs_det_from_pulling points gates zeroes ids f (he.symm ▸ h) hzero hnonneg

end ImbalancedChen.P2Winner9PullingDeterminant
