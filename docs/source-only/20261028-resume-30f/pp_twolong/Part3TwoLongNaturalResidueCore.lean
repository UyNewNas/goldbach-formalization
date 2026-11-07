import Mathlib
import ImbalancedChen.Part3TwoLongContinuousModeReconstruction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original natural finite AP count and its exact complete-product
coprime mean are grouped by their ACTUAL residue masses, then reduced
to the primitive unit graph. No P1, P2, or count identity is assumed.
-/
namespace ImbalancedChen.Part3.TwoLongNaturalResidueCore
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongFixedMRectangularCore
open ImbalancedChen.Part3.TwoLongContinuousModeReconstruction

variable {q : ℕ} [NeZero q]

def rowMass (I : Finset ℕ) (f : ℕ → ℂ) (x : ZMod q) : ℂ :=
  ∑ n ∈ I, if (n : ZMod q)=x then f n else 0

/-- An independently defined residue mass has the exact weighted
pushforward identity, not merely a name shared with a candidate. -/
theorem rowMass_pushforward (I : Finset ℕ) (f : ℕ → ℂ) (T : ZMod q → ℂ) :
    (∑ x : ZMod q, T x * rowMass I f x) = ∑ n ∈ I, T (n : ZMod q) * f n := by
  unfold rowMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_ite,eq_comm]

theorem double_rowMass_pushforward (I J : Finset ℕ) (f g : ℕ → ℂ)
    (T : ZMod q → ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q, T x y * rowMass I f x * rowMass J g y) =
      ∑ n ∈ I, ∑ l ∈ J, T (n : ZMod q) (l : ZMod q) * f n * g l := by
  calc
    _ = ∑ x : ZMod q, (∑ y : ZMod q, T x y * rowMass J g y) * rowMass I f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ n ∈ I, (∑ y : ZMod q, T (n : ZMod q) y * rowMass J g y) * f n :=
      rowMass_pushforward I f _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [rowMass_pushforward,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring

def residueKernel (m a x y : ZMod q) : ℂ :=
  (if m*x*y=a then 1 else 0) -
    (Nat.totient q : ℂ)⁻¹ * (if IsUnit (m*x*y) then 1 else 0)

def residueCore (m a : ZMod q) (F G : ZMod q → ℂ) : ℂ :=
  ∑ x : ZMod q, ∑ y : ZMod q, residueKernel m a x y * F x * G y

/-- The literal natural congruence and coprime tests are preserved. -/
theorem natural_residueWeight (m a n l : ℕ) :
    residueWeight m a q (n,l) =
      residueKernel (m : ZMod q) (a : ZMod q) (n : ZMod q) (l : ZMod q) := by
  simp only [residueWeight,residueKernel,← Nat.cast_mul,
    ZMod.natCast_eq_natCast_iff,ZMod.isUnit_iff_coprime,Complex.ofReal_inv]
  rfl

/-- Exact original compact-carrier count-minus-exact-coprime-mean
identity, with the SAME alpha in both terms. -/
theorem fixedMCore_eq_residueCore (I J : Finset ℕ) (m a : ℕ) (alpha : ℂ)
    (f g : ℝ → ℂ) (U V : ℝ) :
    fixedMCore I J m a q alpha f g U V =
      alpha * residueCore (m : ZMod q) (a : ZMod q)
        (rowMass I (fun n => f ((n : ℝ)/U))) (rowMass J (fun n => g ((n : ℝ)/V))) := by
  rw [residueCore,double_rowMass_pushforward]
  rw [fixedMCore,physicalDiscrepancy_eq_kernel,Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [natural_residueWeight]
  simp only [fixedMProfile]
  ring

/-- Both coordinates in a product are units when the complete product is. -/
theorem unit_complete_product_iff (m x y : ZMod q) (hm : IsUnit m) :
    IsUnit (m*x*y) ↔ IsUnit x ∧ IsUnit y := by
  constructor
  · intro h
    exact ⟨isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h),
      isUnit_of_mul_isUnit_right h⟩
  · rintro ⟨hx,hy⟩
    exact (hm.mul hx).mul hy

/-- Solve the actual primitive product congruence at a unit y. -/
theorem product_eq_iff (m a x y : ZMod q) (hm : IsUnit m) (hy : IsUnit y) :
    m*x*y=a ↔ x=(a*m⁻¹)*y⁻¹ := by
  have hmI := ZMod.mul_inv_of_unit m hm
  have hyI := ZMod.mul_inv_of_unit y hy
  constructor
  · intro h
    calc
      x = m⁻¹*(m*x*y)*y⁻¹ := by
        have he : m⁻¹*(m*x*y)*y⁻¹=(m*m⁻¹)*(y*y⁻¹)*x := by ring
        rw [he,hmI,hyI]; ring
      _ = m⁻¹*a*y⁻¹ := congrArg (fun z => m⁻¹*z*y⁻¹) h
      _ = _ := by ring
  · intro h
    rw [h]
    calc
      _ = (m*m⁻¹)*(y*y⁻¹)*a := by ring
      _ = _ := by rw [hmI,hyI]; ring

/-- The actual finite unit-graph count, kept separate from its independent
unit-product mean. -/
def unitGraphCount (b : ZMod q) (F G : ZMod q → ℂ) : ℂ :=
  ∑ y : ZMod q, if IsUnit y then F (b*y⁻¹) * G y else 0

def unitMass (F : ZMod q → ℂ) : ℂ :=
  ∑ x : ZMod q, if IsUnit x then F x else 0

/-- The complete finite residue count collapses to the ACTUAL primitive
unit graph; nonunit y contribute zero because a is primitive. -/
theorem residue_count_eq_unitGraph (m a : ZMod q) (ha : IsUnit a) (hm : IsUnit m)
    (F G : ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q, if m*x*y=a then F x*G y else 0) =
      unitGraphCount (a*m⁻¹) F G := by
  rw [Finset.sum_comm]
  unfold unitGraphCount
  apply Finset.sum_congr rfl
  intro y hyMem
  by_cases hy : IsUnit y
  · simp only [if_pos hy,product_eq_iff m a _ y hm hy]
    simp
  · have hn (x : ZMod q) : m*x*y ≠ a := by
      intro he
      have hu : IsUnit (m*x*y) := he.symm ▸ ha
      exact hy (isUnit_of_mul_isUnit_right hu)
    simp [hy,hn]

theorem residue_mean_eq_unitMass (m : ZMod q) (hm : IsUnit m) (F G : ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q, if IsUnit (m*x*y) then F x*G y else 0) =
      unitMass F * unitMass G := by
  unfold unitMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [unit_complete_product_iff m x y hm]
  by_cases hxU : IsUnit x <;> by_cases hyU : IsUnit y <;> simp [hxU,hyU]

/-- The exact 1/phi(q) mean is an independent product of unit masses,
not a product of unrestricted residue sums. -/
theorem residueCore_eq_unitGraph (m a : ZMod q) (ha : IsUnit a) (hm : IsUnit m)
    (F G : ZMod q → ℂ) :
    residueCore m a F G = unitGraphCount (a*m⁻¹) F G -
      (Nat.totient q : ℂ)⁻¹ * unitMass F * unitMass G := by
  have he : residueCore m a F G =
      (∑ x : ZMod q, ∑ y : ZMod q, if m*x*y=a then F x*G y else 0) -
      (Nat.totient q : ℂ)⁻¹ *
        (∑ x : ZMod q, ∑ y : ZMod q, if IsUnit (m*x*y) then F x*G y else 0) := by
    unfold residueCore residueKernel
    simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      split_ifs <;> ring
    · apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      split_ifs <;> ring
  rw [he,residue_count_eq_unitGraph m a ha hm,residue_mean_eq_unitMass m hm]
  ring

/-- The nonprimitive short m branch vanishes in BOTH count and exact
coprime mean; this is an arithmetic proof, not a P2 assumption. -/
theorem residueCore_zero_of_nonunit (m a : ZMod q) (ha : IsUnit a) (hm : ¬ IsUnit m)
    (F G : ZMod q → ℂ) : residueCore m a F G = 0 := by
  have hn (x y : ZMod q) : m*x*y ≠ a := by
    intro h
    have hu : IsUnit (m*x*y) := h.symm ▸ ha
    exact hm (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  have hnu (x y : ZMod q) : ¬ IsUnit (m*x*y) := by
    intro h
    exact hm (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h))
  simp [residueCore,residueKernel,hn,hnu]

end
end ImbalancedChen.Part3.TwoLongNaturalResidueCore
