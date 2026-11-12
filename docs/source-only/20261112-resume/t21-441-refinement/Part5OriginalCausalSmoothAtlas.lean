import ImbalancedChen.P5RoughLogGridSmoothTensorPartition

/-! A finite common smooth partition on the *original* log-prime coordinates.
The margin [-1,2] makes both ends of [0,1] part of the exact plateau.
`join` retains the two old tests as factors, even with unrelated meshes.
Refining the native word by future slots leaves every earlier marginal unchanged.
Source only. No arithmetic small-error or uniform-in-N density theorem is assumed. -/
namespace ImbalancedChen.Part5OriginalCausalSmoothAtlas
noncomputable section
open Set Filter
open scoped Classical BigOperators Topology
open P5Z.RoughLogGridSmoothPartition

def width (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)
theorem width_pos (m : ℕ) : 0 < width m := by unfold width; positivity
theorem width_le_one (m : ℕ) : width m ≤ 1 := by
  unfold width
  apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
  simp

/-- All cuts, including widths and the order of joins, are fixed without N. -/
inductive Plan where
  | mesh (m : ℕ)
  | join (old fresh : Plan)

def Code : Plan → Type
  | .mesh m => Fin (m+1)
  | .join P Q => Code P × Code Q

private def codeType : (P : Plan) → Fintype (Code P)
  | .mesh m => inferInstanceAs (Fintype (Fin (m+1)))
  | .join P Q => by
    letI : Fintype (Code P) := codeType P
    letI : Fintype (Code Q) := codeType Q
    exact inferInstanceAs (Fintype (Code P × Code Q))

instance (P : Plan) : Fintype (Code P) := codeType P

def mask : (P : Plan) → Code P → ℝ → ℝ
  | .mesh m, j, x => label (-1) 2 m (width m) j x
  | .join P Q, j, x => mask P j.1 x * mask Q j.2 x

theorem mask_nonneg (P : Plan) (j : Code P) (x : ℝ) : 0 ≤ mask P j x := by
  induction P with
  | mesh m => exact (label_bounds (by norm_num : (-1:ℝ) ≤ 2) (width_pos m) m j x).1
  | join P Q hP hQ => exact mul_nonneg (hP j.1) (hQ j.2)

theorem mask_le_one (P : Plan) (j : Code P) (x : ℝ) : mask P j x ≤ 1 := by
  induction P with
  | mesh m => exact (label_bounds (by norm_num : (-1:ℝ) ≤ 2) (width_pos m) m j x).2
  | join P Q hP hQ =>
    exact (mul_le_mul_of_nonneg_right (hP j.1) (mask_nonneg Q j.2 x)).trans
      (by simpa only [one_mul] using hQ j.2)

theorem mask_smooth (P : Plan) (j : Code P) : ContDiff ℝ ∞ (mask P j) := by
  induction P with
  | mesh m => exact contDiff_label (-1) 2 m (width m) j
  | join P Q hP hQ => exact (hP j.1).mul (hQ j.2)

theorem mask_compact (P : Plan) (j : Code P) : HasCompactSupport (mask P j) := by
  induction P with
  | mesh m => exact hasCompactSupport_label (by norm_num : (-1:ℝ) ≤ 2) (width_pos m) m j
  | join P Q hP _ =>
    apply HasCompactSupport.of_support_subset_isCompact
      (hP j.1 : IsCompact (tsupport (mask P j.1)))
    intro x hx
    exact subset_closure (show mask P j.1 x ≠ 0 from (mul_ne_zero_iff.mp hx).1)

theorem mask_total (P : Plan) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    (∑ j : Code P, mask P j x) = 1 := by
  induction P with
  | mesh m =>
    exact sum_labels_eq_one (width_pos m) (by linarith [hx.1] : (-1:ℝ) ≤ x)
      (by linarith [hx.2,width_le_one m] : x ≤ 2 - width m) m
  | join P Q hP hQ =>
    change (∑ j : Code P × Code Q, mask P j.1 x * mask Q j.2 x) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hQ, mul_one, hP]

/-- Any finite list of requested precisions fits into ONE common positive plan. -/
def overlay (P : Plan) : List Plan → Plan
  | [] => P
  | Q :: qs => .join (overlay P qs) Q

def restrictOld (P : Plan) : (qs : List Plan) → Code (overlay P qs) → Code P
  | [], j => j
  | _ :: qs, j => restrictOld P qs j.1

/-- A particular occurrence of any chart inside the binary overlay tree,
including repeated equal meshes. Left/right are part of the address. -/
inductive Factor (A : Plan) : Plan → Type
  | here : Factor A A
  | left {P Q : Plan} (p : Factor A P) : Factor A (.join P Q)
  | right {P Q : Plan} (p : Factor A Q) : Factor A (.join P Q)

def Factor.read {A : Plan} : {P : Plan} → Factor A P → Code P → Code A
  | _, .here, j => j
  | _, .left p, j => p.read j.1
  | _, .right p, j => p.read j.2

theorem factor_of_mem {A : Plan} (P : Plan) {qs : List Plan} (h : A ∈ qs) :
    Nonempty (Factor A (overlay P qs)) := by
  induction qs with
  | nil => simp at h
  | cons Q qs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst Q; exact ⟨.right .here⟩
    · obtain ⟨p⟩ := ih h; exact ⟨.left p⟩

theorem factor_marginal {A P : Plan} (p : Factor A P) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (F : Code A → ℝ) :
    (∑ j : Code P, mask P j x * F (p.read j)) = ∑ j : Code A, mask A j x * F j := by
  induction p with
  | here => rfl
  | @left P Q p ih =>
    change (∑ j : Code P × Code Q, (mask P j.1 x * mask Q j.2 x) * F (p.read j.1)) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j : Code P, (mask P j x * F (p.read j)) * ∑ k : Code Q, mask Q k x := by
        apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by simpa only [mask_total Q hx,mul_one] using ih
  | @right P Q p ih =>
    change (∑ j : Code P × Code Q, (mask P j.1 x * mask Q j.2 x) * F (p.read j.2)) = _
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, mask_total P hx, one_mul]
    exact ih

/-- Exact marginal of *all* other precisions on the same slot. No monotonicity
of a local analytic estimate under mesh or cap changes is used. -/
theorem overlay_marginal (P : Plan) (qs : List Plan) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) (F : Code P → ℝ) :
    (∑ j : Code (overlay P qs), mask (overlay P qs) j x * F (restrictOld P qs j)) =
      ∑ j : Code P, mask P j x * F j := by
  induction qs with
  | nil => rfl
  | cons Q qs ih =>
    change (∑ j : Code (overlay P qs) × Code Q,
      (mask (overlay P qs) j.1 x * mask Q j.2 x) * F (restrictOld P qs j.1)) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j : Code (overlay P qs),
          (mask (overlay P qs) j x * F (restrictOld P qs j)) * ∑ k : Code Q, mask Q k x := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by simpa only [mask_total Q hx,mul_one] using ih

abbrev Box (P : Plan) (r : ℕ) := Fin r → Code P
def atom {ι : Type*} [Fintype ι] (P : Plan) (j : ι → Code P) (x : ι → ℝ) : ℝ :=
  ∏ i, mask P (j i) (x i)

theorem atom_nonneg {ι : Type*} [Fintype ι] (P : Plan) (j : ι → Code P) (x : ι → ℝ) : 0 ≤ atom P j x :=
  Finset.prod_nonneg (fun i _ => mask_nonneg P (j i) (x i))

theorem atom_le_one {ι : Type*} [Fintype ι] (P : Plan) (j : ι → Code P) (x : ι → ℝ) : atom P j x ≤ 1 :=
  (Finset.prod_le_prod (fun i _ => mask_nonneg P (j i) (x i))
    (fun i _ => mask_le_one P (j i) (x i))).trans_eq (by simp)

theorem atom_smooth {ι : Type*} [Fintype ι] (P : Plan) (j : ι → Code P) : ContDiff ℝ ∞ (atom P j) := by
  unfold atom
  apply contDiff_prod
  intro i _
  exact (mask_smooth P (j i)).comp (contDiff_apply ℝ ℝ i)

theorem atom_total {ι : Type*} [Fintype ι] (P : Plan) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) : (∑ j : ι → Code P, atom P j x) = 1 := by
  unfold atom
  rw [← Fintype.prod_sum]
  simp only [fun i => mask_total P (hx i), Finset.prod_const_one]

theorem atom_append {r s : ℕ} (P : Plan) (j : Box P r) (k : Box P s)
    (x : Fin r → ℝ) (y : Fin s → ℝ) :
    atom P (Fin.append j k) (Fin.append x y) = atom P j x * atom P k y := by
  unfold atom
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]

/-- For each fixed earlier label, summing *only future* labels gives back
its earlier weight, before integration, positivity, primes or division by Θ.
Rank zero is included, so fixed-point/retained reads append no dummy prime. -/
theorem prefix_marginal {r s : ℕ} (P : Plan) (j : Box P r)
    (x : Fin r → ℝ) {y : Fin s → ℝ} (hy : ∀ i, y i ∈ Icc (0:ℝ) 1) :
    (∑ k : Box P s, atom P (Fin.append j k) (Fin.append x y)) = atom P j x := by
  simp only [atom_append, ← Finset.mul_sum, atom_total P hy, mul_one]

/-- Multiplying a signed term by the positive split does not alter its sign
or its total. Applicable to bases, fixed reads, floor losses and zero mass. -/
theorem integrate_constant {r : ℕ} (P : Plan) {x : Fin r → ℝ}
    (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) (v : ℝ) :
    (∑ j : Box P r, atom P j x * v) = v := by
  rw [← Finset.sum_mul, atom_total P hx, one_mul]

/-- The new independent chart can be as fine as requested BEFORE N.
Points sharing a nonzero one-dimensional label are <4/(m+1) apart. -/
theorem mesh_diameter (m : ℕ) (j : Code (.mesh m)) {x y : ℝ}
    (hx : mask (.mesh m) j x ≠ 0) (hy : mask (.mesh m) j y ≠ 0) :
    |x-y| < 4 * width m := by
  have h₁ := label_nonzero_support (by norm_num : (-1:ℝ) ≤ 2) (width_pos m) m j hx
  have h₂ := label_nonzero_support (by norm_num : (-1:ℝ) ≤ 2) (width_pos m) m j hy
  have hstep : right (-1) 2 m j = left (-1) 2 m j + 3 * width m := by
    rw [right,left,logPrimeMeshPoint_succ]
    unfold logPrimeMeshStep width
    ring
  rw [hstep] at h₁ h₂
  exact abs_lt.mpr ⟨by linarith [h₁.1,h₂.2],by linarith [h₁.2,h₂.1]⟩

theorem choose_fine_mesh {eta : ℝ} (he : 0 < eta) :
    ∃ m : ℕ, ∀ (j : Code (.mesh m)) (x y : ℝ),
      mask (.mesh m) j x ≠ 0 → mask (.mesh m) j y ≠ 0 → |x-y| < eta := by
  obtain ⟨m, hm⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (eventually_lt_nhds (by positivity : (0:ℝ) < eta / 4))).exists
  change width m < eta / 4 at hm
  exact ⟨m, fun j x y hx hy => (mesh_diameter m j hx hy).trans (by linarith)⟩

end
end ImbalancedChen.Part5OriginalCausalSmoothAtlas
