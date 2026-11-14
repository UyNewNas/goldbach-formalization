import ImbalancedChen.Part3ActualMarkedCubicPrice
import Mathlib.Algebra.Order.Archimedean.Basic

/-! The half-open bands for the prescribed cubic weight. The band containing
zero also contains the spectral threshold. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCubicBands20261113
noncomputable section
open Real Set MeasureTheory
open ActualMarkedCubicPrice20261112 (cubic)

def radius (n : ℕ) : ℝ := (2:ℝ)^n
def discount (n : ℕ) : ℝ := (radius n)⁻¹^3
def shell (n : ℕ) : Set ℝ := {t | 1+|t|∈Ico (radius n) (radius (n+1))}

theorem radius_pos (n : ℕ) : 0<radius n := by unfold radius; positivity
theorem radius_one (n : ℕ) : 1≤radius n := one_le_pow₀ (by norm_num)
theorem discount_nn (n : ℕ) : 0≤discount n := by unfold discount; positivity [radius_pos n]

theorem shell_meas (n : ℕ) : MeasurableSet (shell n) :=
  measurableSet_Ico.preimage (continuous_const.add continuous_abs).measurable

theorem cover (t : ℝ) : ∃ n,t∈shell n :=
  exists_nat_pow_near (by linarith only [abs_nonneg t] : 1≤1+|t|) (by norm_num : 1<(2:ℝ))

theorem all_shells : (⋃ n,shell n)=univ := by
  apply eq_univ_of_forall
  exact fun t => mem_iUnion.mpr (cover t)

theorem shells_disjoint : Pairwise (fun a b => Disjoint (shell a) (shell b)) := by
  have sep (a b : ℕ) (h : a<b) : Disjoint (shell a) (shell b) := by
    apply disjoint_left.mpr
    intro t ha hb
    have up : radius (a+1)≤radius b := pow_le_pow_right₀ (by norm_num) h
    exact (ha.2.trans_le up).not_ge hb.1
  intro a b h
  rcases lt_or_gt_of_ne h with h|h
  · exact sep a b h
  · exact (sep b a h).symm

theorem within {n : ℕ} {t : ℝ} (h : t∈shell n) :
    t∈Icc (-(radius (n+1))) (radius (n+1)) :=
  abs_le.mp (by linarith only [h.2])

theorem cubic_le {n : ℕ} {t : ℝ} (h : t∈shell n) : cubic t≤discount n := by
  rw [cubic,discount,inv_pow,one_div]
  exact inv_anti₀ (pow_pos (radius_pos n) _) (pow_le_pow_left₀ (radius_pos n).le h.1 _)

def bill (K : ℝ) (n : ℕ) := K*(1/2:ℝ)^n
theorem bill_sum (K : ℝ) : HasSum (bill K) (2*K) := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).hasSum.mul_left K
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  convert h using 1 <;> norm_num <;> ring

theorem dyadic_charge {A D E : ℝ} (a0 : 0≤A) (d0 : 0≤D) (e0 : 0≤E) (n : ℕ) :
    discount n*(D*((radius (n+1))^2+A)*E)≤bill (4*D*(1+A)*E) n := by
  let r := radius n
  have rp : 0<r := radius_pos n
  have r1 : 1≤r := radius_one n
  have h2 : 1≤r^2 := one_le_pow₀ r1
  have a := mul_le_mul_of_nonneg_right h2 a0
  have p : (2*r)^2+A≤4*r^2*(1+A) := by nlinarith only [a,mul_nonneg (sq_nonneg r) a0]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p d0) e0) (discount_nn n)
  have norm : (1/2:ℝ)^n=r⁻¹ := by simp [r,radius,one_div]
  have next : radius (n+1)=2*r := by dsimp [r,radius];rw [pow_succ,mul_comm]
  rw [next]
  apply h.trans_eq
  dsimp only [bill]
  rw [norm]
  change r⁻¹^3*(D*(4*r^2*(1+A))*E)=4*D*(1+A)*E*r⁻¹
  field_simp [rp.ne'] <;> ring

end
end ImbalancedChen.Part3.OriginalSwitchedCubicBands20261113
