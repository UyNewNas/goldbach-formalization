import ImbalancedChen.P2GammaOriginalCartesianMask
import ImbalancedChen.P2GammaSmoothLogGrid

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal Gamma geometry omitted by O.  The prime is the original head;
the complete complement is d * tail.prod * quotient, including quotient 1.
Numerical endpoints supply O's zero-extension premise.  The rejected
weight is explicit, and its support is proved; its ordering-wall mass is
NOT assumed small.  This file does not assert a BV estimate.
-/

namespace ImbalancedChen.P2GammaRetainedInteriorGeometry
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid
open P5OriginalU5CausalFinite (pairSupport)

/-- All three tests are fixed before q, the primitive conductor, and the
moving residue.  The lower test uses the COMPLETE two-factor product. -/
def Retain (N : ℕ) (H δ : ℝ) (j l : ℕ) (y : Label) : Prop :=
  H ≤ lower δ j * lower δ l ∧
  upper δ j * upper δ l ≤ N ∧
  ∀ r ∈ y.1, upper δ j ≤ (r : ℝ)

def betaLabel (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (j l : ℕ)
    (y : Label) : ℂ :=
  if Retain N H δ j l y then
    complexWeight δ l (product (t.1*t.2) y) else 0

def rejectedLabel (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (j l : ℕ)
    (y : Label) : ℂ :=
  if Retain N H δ j l y then 0 else
    complexWeight δ l (product (t.1*t.2) y)

theorem beta_add_rejected (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ)
    (j l : ℕ) (y : Label) :
    betaLabel N t H δ j l y + rejectedLabel N t H δ j l y =
      complexWeight δ l (product (t.1*t.2) y) := by
  by_cases h : Retain N H δ j l y <;> simp [betaLabel,rejectedLabel,h]

theorem betaLabel_norm_le_one (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ)
    (j l : ℕ) (y : Label) : ‖betaLabel N t H δ j l y‖ ≤ 1 := by
  by_cases h : Retain N H δ j l y
  · simpa only [betaLabel,if_pos h] using complexWeight_norm_le_one δ l _
  · simp [betaLabel,h]

private theorem real_weight_ne_zero {δ p : ℝ} {j : ℕ}
    (h : complexWeight δ j p ≠ 0) : weight δ j p ≠ 0 := by
  intro hz
  exact h (by simp [complexWeight,hz])

/-- A nonzero explicit retained row is an original legal pair.  No
source identity, ordering mask, or boundary estimate is a premise. -/
theorem retained_row_legal {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ) {j l p : ℕ}
    (hp : p ∈ headCarrier N t c) {y : Label}
    (hy : y ∈ rootComplementLabels N t (c::cs))
    (hw : complexWeight δ j p * betaLabel N t H δ j l y ≠ 0) :
    rebuild p y ∈ rootLabels N t (c::cs) := by
  have ha : complexWeight δ j p ≠ 0 := fun h => hw (by rw [h,zero_mul])
  have hb : betaLabel N t H δ j l y ≠ 0 := fun h => hw (by rw [h,mul_zero])
  have hr : Retain N H δ j l y := by
    by_contra hn
    exact hb (by simp [betaLabel,hn])
  have hb' : complexWeight δ l (product (t.1*t.2) y) ≠ 0 := by
    simpa only [betaLabel,if_pos hr] using hb
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
  have hm0 : (0 : ℝ) < product (t.1*t.2) y := by
    exact_mod_cast complement_product_pos ht hy
  obtain ⟨_,hpu⟩ := weight_nonzero_support hδ hp0 j (real_weight_ne_zero ha)
  obtain ⟨_,hmu⟩ := weight_nonzero_support hδ hm0 l (real_weight_ne_zero hb')
  apply (rebuild_mem_root_iff hp hy).mpr
  constructor
  · intro r hmem
    exact_mod_cast hpu.trans_le (hr.2.2 r hmem)
  · have hprod : (p : ℝ) * (product (t.1*t.2) y : ℝ) < N :=
      ((mul_lt_mul_of_pos_right hpu hm0).trans
        (mul_lt_mul_of_pos_left hmu (upper_pos δ j))).trans_le hr.2.1
    have hprod' : ((product (t.1*t.2) y*p : ℕ) : ℝ) < N := by
      simpa only [Nat.cast_mul,mul_comm] using hprod
    exact_mod_cast hprod'

/-- The exact endpoint supplier for O's hzero. -/
theorem retained_row_zero_on_illegal {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ) (j l : ℕ)
    {p : ℕ} (hp : p ∈ headCarrier N t c) {y : Label}
    (hy : y ∈ rootComplementLabels N t (c::cs))
    (hn : rebuild p y ∉ rootLabels N t (c::cs)) :
    complexWeight δ j p * betaLabel N t H δ j l y = 0 := by
  by_contra hw
  exact hn (retained_row_legal ht hδ hp hy hw)

/-- A literal source row becomes a Cartesian prime/complement row.
Changing F to a count, exact coprime mean, or character does not change
the row or its construction order. -/
theorem original_retained_row_eq_cartesian {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (c : ℕ) (cs : List ℕ) {H δ : ℝ}
    (hδ : 0 < δ) (j l : ℕ) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (complexWeight δ j (labelHead x) *
        betaLabel N t H δ j l (labelComplement x)) *
          F (product (t.1*t.2) x)) =
      ∑ p ∈ headCarrier N t c,
        ∑ y ∈ rootComplementLabels N t (c::cs),
          (complexWeight δ j p * betaLabel N t H δ j l y) *
            F (product (t.1*t.2) y*p) := by
  apply original_word_test_eq_cartesian
  intro p hp y hy hn
  exact retained_row_zero_on_illegal ht hδ j l hp hy hn

theorem retained_row_complete_scale {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ) {j l p : ℕ}
    (hp : p ∈ headCarrier N t c) {y : Label}
    (hy : y ∈ rootComplementLabels N t (c::cs))
    (hw : complexWeight δ j p * betaLabel N t H δ j l y ≠ 0) :
    H < (product (t.1*t.2) y : ℝ)*(p : ℝ) ∧
      (product (t.1*t.2) y : ℝ)*(p : ℝ) < N := by
  have hlegal := retained_row_legal ht hδ hp hy hw
  have hr : Retain N H δ j l y := by
    by_contra hn
    exact hw (by simp [betaLabel,hn])
  have ha : complexWeight δ j p ≠ 0 := fun h => hw (by rw [h,zero_mul])
  have hb : complexWeight δ l (product (t.1*t.2) y) ≠ 0 := by
    intro h
    exact hw (by simp [betaLabel,hr,h])
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
  have hm0 : (0 : ℝ) < product (t.1*t.2) y := by
    exact_mod_cast complement_product_pos ht hy
  have hpl := (weight_nonzero_support hδ hp0 j (real_weight_ne_zero ha)).1
  have hml := (weight_nonzero_support hδ hm0 l (real_weight_ne_zero hb)).1
  constructor
  · have h := hr.1.trans_lt
      ((mul_lt_mul_of_pos_right hpl (lower_pos δ l)).trans
        (mul_lt_mul_of_pos_left hml hp0))
    simpa only [mul_comm] using h
  · have h := (rootLabels_data hlegal).2.2.2
    rw [rebuild_product] at h
    exact_mod_cast h

/-- Endpoint inflation is explicit.  It costs exp(2 delta) per factor,
not an unspecified geometric constant. -/
theorem upper_lt_point_mul_exp {δ p : ℝ} (hδ : 0 < δ) (hp : 0 < p)
    {j : ℕ} (hw : complexWeight δ j p ≠ 0) :
    upper δ j < p * Real.exp (2*δ) := by
  rw [upper_eq_lower_mul]
  exact mul_lt_mul_of_pos_right
    (weight_nonzero_support hδ hp j (real_weight_ne_zero hw)).1 (Real.exp_pos _)

/-- A rejected nonzero grid term is supported on the literal lower
complete-product tail, upper complete-product wall, or head-order wall.
This is a support theorem, not a claim that any of these masses is paid. -/
theorem rejected_row_support {N : ℕ} {t : ℕ × ℕ} {H δ : ℝ}
    (hδ : 0 < δ) {j l p : ℕ} {y : Label}
    (hp : (0 : ℝ) < p) (hm : (0 : ℝ) < product (t.1*t.2) y)
    (hw : complexWeight δ j p * rejectedLabel N t H δ j l y ≠ 0) :
    (p : ℝ)*(product (t.1*t.2) y : ℝ) < H*Real.exp (4*δ) ∨
      (N : ℝ) < (p : ℝ)*(product (t.1*t.2) y : ℝ)*Real.exp (4*δ) ∨
      ∃ r ∈ y.1, (r : ℝ) < (p : ℝ)*Real.exp (2*δ) := by
  have ha : complexWeight δ j p ≠ 0 := fun h => hw (by rw [h,zero_mul])
  have hn : ¬ Retain N H δ j l y := by
    intro h
    exact hw (by simp [rejectedLabel,h])
  have hb : complexWeight δ l (product (t.1*t.2) y) ≠ 0 := by
    intro h
    exact hw (by simp [rejectedLabel,hn,h])
  have hpu := (weight_nonzero_support hδ hp j (real_weight_ne_zero ha)).2
  have hmu := (weight_nonzero_support hδ hm l (real_weight_ne_zero hb)).2
  have hj := upper_lt_point_mul_exp hδ hp ha
  have hl := upper_lt_point_mul_exp hδ hm hb
  have he : Real.exp (2*δ)*Real.exp (2*δ) = Real.exp (4*δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  by_contra h
  push_neg at h
  apply hn
  refine ⟨?_,?_,?_⟩
  · have hprod := (mul_lt_mul_of_pos_right hpu hm).trans
      (mul_lt_mul_of_pos_left hmu (upper_pos δ j))
    rw [upper_eq_lower_mul,upper_eq_lower_mul] at hprod
    have heq : (lower δ j*Real.exp (2*δ))*(lower δ l*Real.exp (2*δ)) =
        (lower δ j*lower δ l)*Real.exp (4*δ) := by
      rw [← he]
      ring
    rw [heq] at hprod
    exact ((mul_lt_mul_right (Real.exp_pos (4*δ))).mp
      (h.1.trans_lt hprod)).le
  · have hprod := (mul_lt_mul_of_pos_right hj (upper_pos δ l)).trans
      (mul_lt_mul_of_pos_left hl (mul_pos hp (Real.exp_pos _)))
    have heq : ((p : ℝ)*Real.exp (2*δ))*
        ((product (t.1*t.2) y : ℝ)*Real.exp (2*δ)) =
        (p : ℝ)*(product (t.1*t.2) y : ℝ)*Real.exp (4*δ) := by
      rw [← he]
      ring
    rw [heq] at hprod
    exact hprod.le.trans h.2.1
  · intro r hr
    exact hj.le.trans (h.2.2 r hr)

def retainedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℂ :=
  ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
    complexWeight δ j (labelHead x) *
      betaLabel N t H δ j l (labelComplement x)

def rejectedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℂ :=
  ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
    complexWeight δ j (labelHead x) *
      rejectedLabel N t H δ j l (labelComplement x)

/-- One finite grid covers every actual label at once.  The only cover
input is the numerical log N endpoint, fixed before an arithmetic test. -/
theorem retained_add_rejected_eq_one {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ) {K : ℕ}
    (hK : Real.log (N : ℝ)/δ+1 ≤ K) {x : Label}
    (hx : x ∈ rootLabels N t (c::cs)) :
    retainedWeight N t H δ K x + rejectedWeight N t H δ K x = 1 := by
  have hy : labelComplement x ∈ rootComplementLabels N t (c::cs) :=
    Finset.mem_image_of_mem (fun z : Label => (z.1.tail,z.2)) hx
  have hp0 : 0 < labelHead x :=
    (original_label_head_prime (by simp) hx).pos
  have hm0 : 0 < product (t.1*t.2) (labelComplement x) :=
    complement_product_pos ht hy
  have hp1 : 1 ≤ labelHead x := hp0
  have hm1 : 1 ≤ product (t.1*t.2) (labelComplement x) := hm0
  have hprod := (rootLabels_data hx).2.2.2
  rw [original_label_head_product (by simp) hx] at hprod
  have hpn : labelHead x ≤ N := by nlinarith
  have hmn : product (t.1*t.2) (labelComplement x) ≤ N := by nlinarith
  have hcover (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
      (∑ j ∈ Finset.range K, complexWeight δ j (n : ℝ)) = 1 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN)
    have hc : Real.log (n : ℝ)/δ+1 ≤ K := by
      have hh := div_le_div_of_nonneg_right hlog hδ.le
      linarith
    have hs := weight_sum_eq_one hδ (by exact_mod_cast hn : (1 : ℝ) ≤ n) hc
    simpa only [complexWeight,Complex.ofReal_sum,Complex.ofReal_one] using
      congrArg (fun a : ℝ => (a : ℂ)) hs
  have hsp := hcover (labelHead x) hp0 hpn
  have hsm := hcover (product (t.1*t.2) (labelComplement x)) hm0 hmn
  calc
    _ = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        complexWeight δ j (labelHead x) *
          (betaLabel N t H δ j l (labelComplement x)+
            rejectedLabel N t H δ j l (labelComplement x)) := by
      simp only [retainedWeight,rejectedWeight,mul_add,Finset.sum_add_distrib]
    _ = ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        complexWeight δ j (labelHead x) *
          complexWeight δ l (product (t.1*t.2) (labelComplement x)) := by
      simp_rw [beta_add_rejected]
    _ = 1 := by
      simp only [← Finset.mul_sum,hsm,mul_one,hsp]

/-- Exact literal original source reconstruction, with every rejected
grid term displayed.  F is quantified after all rows; it may be the
count-minus-exact-coprime-mean kernel at any q or moving residue.  There
is no assumption that the rejected sum is small. -/
theorem original_word_eq_retained_rows_add_rejected
    {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (c : ℕ) (cs : List ℕ) {H δ : ℝ} (hδ : 0 < δ) {K : ℕ}
    (hK : Real.log (N : ℝ)/δ+1 ≤ K) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs), F (product (t.1*t.2) x)) =
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ∑ p ∈ headCarrier N t c,
          ∑ y ∈ rootComplementLabels N t (c::cs),
            (complexWeight δ j p * betaLabel N t H δ j l y) *
              F (product (t.1*t.2) y*p)) +
      ∑ x ∈ rootLabels N t (c::cs),
        rejectedWeight N t H δ K x * F (product (t.1*t.2) x) := by
  have hsplit : (∑ x ∈ rootLabels N t (c::cs), F (product (t.1*t.2) x)) =
      (∑ x ∈ rootLabels N t (c::cs),
        retainedWeight N t H δ K x * F (product (t.1*t.2) x)) +
      ∑ x ∈ rootLabels N t (c::cs),
        rejectedWeight N t H δ K x * F (product (t.1*t.2) x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← add_mul,retained_add_rejected_eq_one ht hδ hK hx,one_mul]
  rw [hsplit]
  apply congrArg (fun z : ℂ => z+
    ∑ x ∈ rootLabels N t (c::cs),
      rejectedWeight N t H δ K x * F (product (t.1*t.2) x))
  have hswap :
      (∑ x ∈ rootLabels N t (c::cs),
        retainedWeight N t H δ K x * F (product (t.1*t.2) x)) =
      ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ∑ x ∈ rootLabels N t (c::cs),
          (complexWeight δ j (labelHead x) *
            betaLabel N t H δ j l (labelComplement x)) *
              F (product (t.1*t.2) x) := by
    simp only [retainedWeight,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  exact original_retained_row_eq_cartesian ht c cs hδ j l F

/-- The actual retained beta inherits the earlier proven complement
norm; no number of possible heads is inserted. -/
theorem retained_complement_norm {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l m : ℕ) :
    ‖rootComplementCoefficient N t (c::cs) (betaLabel N t H δ j l) m‖ ≤
      (MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.fouvryTau
        ((c::cs).length+1) m : ℝ) := by
  apply rootComplementCoefficient_norm_le ht _ (by simp)
  intro y _
  exact betaLabel_norm_le_one N t H δ j l y

def gridAbelCost (δ : ℝ) (K : ℕ) (u v : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
    (‖complexWeight δ j (v j l)‖+
      ∫ p in Ioc (u j l) (v j l), ‖deriv (complexWeight δ j) p‖)

/-- Counting-measure integration of the actual grid rows has a fixed
scalar/Abel budget.  The clipped prime intervals may be shorter than a
dyadic interval, as required by the source SW theorem. -/
theorem exists_fixed_grid_Abel_budget :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ δ : ℝ, 0 < δ → 2*δ ≤ Real.log 2 →
      ∀ (K : ℕ) (u v : ℕ → ℕ → ℝ),
      (∀ j ∈ Finset.range K, ∀ l ∈ Finset.range K,
        lower δ j ≤ u j l ∧ u j l ≤ v j l ∧ v j l ≤ upper δ j) →
      gridAbelCost δ K u v ≤ (K : ℝ)^2*(1+2*D/δ) := by
  obtain ⟨D,hD,hbudget⟩ := exists_complexWeight_Abel_budget
  refine ⟨D,hD,?_⟩
  intro δ hδ hwidth K u v hwindow
  calc
    _ ≤ ∑ j ∈ Finset.range K, ∑ _l ∈ Finset.range K, (1+2*D/δ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨hlo,huv,hhi⟩ := hwindow j hj l hl
      exact hbudget δ hδ j (lower δ j) (u j l) (v j l)
        (lower_pos δ j) hlo huv (hhi.trans (upper_le_two_lower hwidth j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

def gridSize (B N : ℕ) : ℕ := Nat.ceil (Real.log (N : ℝ)^(B+1)+1)

theorem gridSize_covers (B N : ℕ) :
    Real.log (N : ℝ)/(1/Real.log (N : ℝ)^B)+1 ≤ gridSize B N := by
  calc
    _ = Real.log (N : ℝ)^(B+1)+1 := by
      rw [div_div,div_one,pow_succ]
      ring
    _ ≤ _ := Nat.le_ceil _

/-- For delta=log(N)^(-B), the precise two-index retained-grid budget
is at most 9(1+2D)log(N)^(3B+2).  D precedes B,N and every clipped
interval.  B is fixed before N and the arithmetic tests. -/
theorem exists_fixed_logarithmic_grid_budget :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (B N : ℕ), 1 ≤ Real.log (N : ℝ) →
      2*(1/Real.log (N : ℝ)^B) ≤ Real.log 2 →
      ∀ u v : ℕ → ℕ → ℝ,
      (∀ j ∈ Finset.range (gridSize B N),
        ∀ l ∈ Finset.range (gridSize B N),
          lower (1/Real.log (N : ℝ)^B) j ≤ u j l ∧
          u j l ≤ v j l ∧
          v j l ≤ upper (1/Real.log (N : ℝ)^B) j) →
      gridAbelCost (1/Real.log (N : ℝ)^B) (gridSize B N) u v ≤
        9*(1+2*D)*Real.log (N : ℝ)^(3*B+2) := by
  obtain ⟨D,hD,hbudget⟩ := exists_fixed_grid_Abel_budget
  refine ⟨D,hD,?_⟩
  intro B N hlog hwidth u v hwindow
  have hD0 : 0 ≤ D := by linarith
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hδ : 0 < 1/Real.log (N : ℝ)^B := by positivity
  have hK : (gridSize B N : ℝ) ≤ 3*Real.log (N : ℝ)^(B+1) := by
    have hceil := Nat.ceil_lt_add_one
      (by positivity : 0 ≤ Real.log (N : ℝ)^(B+1)+1)
    have hp : (1 : ℝ) ≤ Real.log (N : ℝ)^(B+1) := one_le_pow₀ hlog
    change (gridSize B N : ℝ) < Real.log (N : ℝ)^(B+1)+1+1 at hceil
    linarith
  have hbracket : 1+2*D/(1/Real.log (N : ℝ)^B) ≤
      (1+2*D)*Real.log (N : ℝ)^B := by
    rw [div_div,div_one]
    have hp : (1 : ℝ) ≤ Real.log (N : ℝ)^B := one_le_pow₀ hlog
    nlinarith
  have hpow : (Real.log (N : ℝ)^(B+1))^2*Real.log (N : ℝ)^B =
      Real.log (N : ℝ)^(3*B+2) := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  calc
    _ ≤ (gridSize B N : ℝ)^2*(1+2*D/(1/Real.log (N : ℝ)^B)) :=
      hbudget _ hδ hwidth _ u v hwindow
    _ ≤ (3*Real.log (N : ℝ)^(B+1))^2*((1+2*D)*Real.log (N : ℝ)^B) := by
      apply mul_le_mul
        (pow_le_pow_left₀ (Nat.cast_nonneg (gridSize B N)) hK 2) hbracket
        <;> positivity
    _ = 9*(1+2*D)*((Real.log (N : ℝ)^(B+1))^2*Real.log (N : ℝ)^B) := by ring
    _ = _ := by rw [hpow]

end
end ImbalancedChen.P2GammaRetainedInteriorGeometry
