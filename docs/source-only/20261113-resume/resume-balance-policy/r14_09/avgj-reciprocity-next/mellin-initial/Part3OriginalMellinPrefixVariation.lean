import ImbalancedChen.Part3OriginalSwitchedMellinRows
import ImbalancedChen.Part3PrimeMellinProfileVariation

/-! Finite partial summation for the same Mellin wave used in the switched
row. The weight of both boundary terms is included. -/
namespace ImbalancedChen.Part3.OriginalMellinPrefixVariation20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalSwitchedMellinRows20261113

private theorem wave_phase (t x : ℝ) :
    wave x t=PrimeMellinProfileVariation20261026b.phase t x := by
  unfold wave PrimeMellinProfileVariation20261026b.phase
  congr 1
  push_cast
  ring

private theorem wave_step (t : ℝ) {a i : ℕ} (ha : 0<a) (hai : a≤i) :
    ‖wave (i:ℝ) t-wave ((i+1:ℕ):ℝ) t‖ ≤ |t|/(a:ℝ) := by
  have ap : (0:ℝ)<a := by exact_mod_cast ha
  have ar : (a:ℝ)≤i := by exact_mod_cast hai
  let S := Set.Icc (i:ℝ) (i+1:ℝ)
  let F := PrimeMellinProfileVariation20261026b.phase t
  let D := fun x : ℝ => F x*(Complex.I*(t:ℂ)/(x:ℂ))
  have dd (x : ℝ) (hx : x∈S) : HasDerivWithinAt F (D x) S x :=
    (PrimeMellinProfileVariation20261026b.phase_hasDerivAt t (ap.trans_le (ar.trans hx.1))).hasDerivWithinAt
  have bd (x : ℝ) (hx : x∈S) : ‖D x‖ ≤ |t|/(a:ℝ) := by
    dsimp only [D,F]
    rw [norm_mul,PrimeMellinProfileVariation20261026b.phase_norm,one_mul,norm_div,norm_mul,
      Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_pos (ap.trans_le (ar.trans hx.1))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) ap (ar.trans hx.1)
  have L := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le dd bd
    (convex_Icc (i:ℝ) (i+1:ℝ))
    (show (i+1:ℝ)∈S from ⟨by linarith,le_rfl⟩)
    (show (i:ℝ)∈S from ⟨le_rfl,by linarith⟩)
  simpa [F,wave_phase,Nat.cast_add,Nat.cast_one,Real.norm_eq_abs] using L

/-- Endpoint at b and the forward differences in [a,b); the k-th
coefficient multiplies the prefix whose upper endpoint is k+1. -/
def coeff (t : ℝ) (b i : ℕ) : ℂ :=
  if i=b then wave (b:ℝ) t else wave (i:ℝ) t-wave ((i+1:ℕ):ℝ) t

private theorem suffix (t : ℝ) {b m : ℕ} (hm : m≤b) :
    (∑ i ∈ Icc m b, coeff t b i) = wave (m:ℝ) t := by
  classical
  have set : Icc m b=insert b (Ico m b) := by
    ext i
    simp only [mem_Icc,mem_insert,mem_Ico]
    omega
  have nn : b∉Ico m b := by simp
  have rest (i) (hi : i∈Ico m b) : coeff t b i=wave (i:ℝ) t-wave ((i+1:ℕ):ℝ) t :=
    if_neg (mem_Ico.mp hi).2.ne
  rw [set,sum_insert nn,show coeff t b b=wave (b:ℝ) t from if_pos rfl,sum_congr rfl rest]
  have H := sum_Ico_sub (fun i : ℕ => -wave (i:ℝ) t) hm
  simp only [neg_sub_neg] at H
  rw [H]
  ring

theorem abel (f : ℕ → ℂ) (t : ℝ) (a b : ℕ) :
    (∑ m ∈ Ico a b, wave (m:ℝ) t*f m) =
      ∑ i ∈ Icc a b, coeff t b i*∑ m ∈ Ico a (min b (i+1)), f m := by
  classical
  have prefix (i : ℕ) : Ico a (min b (i+1))=(Ico a b).filter (fun m => m≤i) := by
    ext m
    simp only [mem_Ico,mem_filter,lt_min_iff]
    omega
  have tail (m : ℕ) (hm : m∈Ico a b) :
      (Icc a b).filter (fun i => m≤i)=Icc m b := by
    ext i
    simp only [mem_filter,mem_Icc]
    have h := mem_Ico.mp hm
    omega
  simp_rw [prefix,sum_filter,mul_sum,mul_ite,mul_zero]
  rw [sum_comm (s := Icc a b) (t := Ico a b)]
  apply sum_congr rfl
  intro m hm
  rw [←sum_filter,tail m hm,←sum_mul,suffix t (mem_Ico.mp hm).2.le]

/-- Explicit Abel cost on the full range of the native positive dyadic
interval. The upper endpoint is exclusive and can be at 2a. -/
theorem variation (t : ℝ) {a b : ℕ} (ha : 0<a) (hab : a≤b) (cap : b≤2*a) :
    (∑ i ∈ Icc a b, ‖coeff t b i‖) ≤ 1+|t| := by
  classical
  have set : Icc a b=insert b (Ico a b) := by
    ext i
    simp only [mem_Icc,mem_insert,mem_Ico]
    omega
  rw [set,sum_insert (by simp),show coeff t b b=wave (b:ℝ) t from if_pos rfl,wave_norm]
  apply add_le_add le_rfl
  have ap : (0:ℝ)<a := by exact_mod_cast ha
  calc
    _ ≤ ∑ _i ∈ Ico a b, |t|/(a:ℝ) := sum_le_sum (fun i hi => by
      rw [coeff,if_neg (mem_Ico.mp hi).2.ne]
      exact wave_step t ha (mem_Ico.mp hi).1)
    _ = ((b-a:ℕ):ℝ)*(|t|/(a:ℝ)) := by simp [Nat.card_Ico]
    _ ≤ (a:ℝ)*(|t|/(a:ℝ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : b-a≤a))
      (div_nonneg (abs_nonneg _) ap.le)
    _ = _ := by field_simp [ap.ne']

end
end ImbalancedChen.Part3.OriginalMellinPrefixVariation20261113
