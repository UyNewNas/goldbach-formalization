import ImbalancedChen.Part3ActualPrescribedPositiveJ
import ImbalancedChen.Part3OriginalSwitchedCutoffModes
import Batteries.Tactic.OpenPrivate

/-! Propagate actual polynomial frequency prices through continuous
Schwartz operators and the positive-branch substitution u ↦ cosh u. -/
namespace ImbalancedChen.Part3.OriginalSwitchedSchwartzPrices20261113
noncomputable section
open Set Complex
open scoped Topology
open ActualPositiveCosineProfile20261112 (hyperbolicProfile)
open private X d jet jet_deriv from ImbalancedChen.Part3ActualPositiveCosineProfile

abbrev Space := SchwartzMap ℝ ℂ
def weight (k : ℤ) := 1+|(k:ℝ)|
def Priced (f : ℤ→ℝ) := ∃ (r : ℕ) (C : ℝ),0≤C ∧ ∀ k,f k≤C*(weight k)^r
def Controlled (U : ℤ→Space) := ∀ a b : ℕ,Priced (fun k => SchwartzMap.seminorm ℂ a b (U k))

theorem w_one (k : ℤ) : 1≤weight k := by dsimp [weight]; linarith [abs_nonneg (k:ℝ)]

theorem smaller {f g : ℤ→ℝ} (h : Priced g) (le : ∀ k,f k≤g k) : Priced f := by
  obtain ⟨r,C,c,B⟩ := h
  exact ⟨r,C,c,fun k => (le k).trans (B k)⟩

theorem price_zero : Priced (fun _ => 0) := ⟨0,0,le_rfl,fun _ => by simp⟩

theorem price_add {f g : ℤ→ℝ} (A : Priced f) (B : Priced g) : Priced (fun k => f k+g k) := by
  obtain ⟨a,C,c,h⟩ := A
  obtain ⟨b,D,d,l⟩ := B
  refine ⟨max a b,C+D,add_nonneg c d,fun k => ?_⟩
  rw [add_mul]
  exact add_le_add ((h k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (w_one k) (le_max_left _ _)) c))
    ((l k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (w_one k) (le_max_right _ _)) d))

theorem price_scale {f : ℤ→ℝ} (h : Priced f) {A : ℝ} (a : 0≤A) : Priced (fun k => A*f k) := by
  obtain ⟨r,C,c,B⟩ := h
  exact ⟨r,A*C,mul_nonneg a c,fun k => by rw [mul_assoc];exact mul_le_mul_of_nonneg_left (B k) a⟩

private theorem finite_price {ι : Type*} (S : Finset ι) (f : ι→ℤ→ℝ) (h : ∀ i∈S,Priced (f i)) :
    Priced (fun k => ∑ i ∈ S,f i k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using price_zero
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi] using price_add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem map_control {U : ℤ→Space} (h : Controlled U) (L : Space→L[ℂ]Space) :
    Controlled (fun k => L (U k)) := by
  intro a b
  let p := schwartzSeminormFamily ℂ ℝ ℂ
  let s := (p (a,b)).comp L.toLinearMap
  have ct : Continuous s := ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (a,b)).comp L.continuous
  obtain ⟨S,C,_,bound⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) s ct
  apply smaller (price_scale (finite_price S (fun j k => p j (U k)) (fun j _ => h j.1 j.2)) C.coe_nonneg)
  intro k
  have first := bound (U k)
  change p (a,b) (L (U k)) ≤ (C:ℝ)*S.sup p (U k) at first
  apply first.trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  apply Seminorm.finset_sup_apply_le (Finset.sum_nonneg (fun _ _ => apply_nonneg _ _))
  intro j hj
  exact Finset.single_le_sum (fun i _ => apply_nonneg _ _) hj

private theorem sub_control {U V : ℤ→Space} (hu : Controlled U) (hv : Controlled V) :
    Controlled (fun k => U k-V k) := fun a b => smaller (price_add (hu a b) (hv a b))
      (fun k => map_sub_le_add _ _ _)

theorem add_control {U V : ℤ→Space} (hu : Controlled U) (hv : Controlled V) :
    Controlled (fun k => U k+V k) := fun a b => smaller (price_add (hu a b) (hv a b))
      (fun k => map_add_le_add _ _ _)

private theorem controlled_jet {U : ℤ→Space} (h : Controlled U) (r : ℕ) :
    ∃ A B : ℤ→Space,Controlled A ∧ Controlled B ∧
      ∀ k,iteratedDeriv r (fun u => U k (Real.cosh u))=jet (A k) (B k) := by
  induction r with
  | zero =>
    refine ⟨U,fun _ => 0,h,fun _ _ => by simpa using price_zero,fun k => ?_⟩
    funext u
    simp [jet]
  | succ r ih =>
    obtain ⟨A,B,hA,hB,E⟩ := ih
    let M := SchwartzMap.smulLeftCLM ℂ Complex.ofReal
    let D := SchwartzMap.derivCLM ℂ ℂ
    refine ⟨fun k => X (B k)+X (X (d (B k)))-d (B k),fun k => d (A k),
      sub_control (add_control (map_control hB M) (map_control (map_control (map_control hB D) M) M))
        (map_control hB D),map_control hA D,?_⟩
    intro k
    rw [iteratedDeriv_succ,E,jet_deriv]

theorem hyperbolic_control {U : ℤ→Space} (h : Controlled U) :
    Controlled (fun k => hyperbolicProfile (U k)) := by
  intro a b
  obtain ⟨A,B,hA,hB,E⟩ := controlled_jet h b
  apply smaller (price_add (hA a 0) (hB (a+1) 0))
  intro k
  apply SchwartzMap.seminorm_le_bound' ℂ a b _ (by positivity)
  intro u
  have hs : |Real.sinh u|≤Real.cosh u := by rw [Real.abs_sinh,←Real.cosh_abs];exact (Real.sinh_lt_cosh _).le
  have hu : |u|≤Real.cosh u :=
    (Real.self_le_sinh_iff.mpr (abs_nonneg _)).trans ((Real.abs_sinh u).symm.le.trans hs)
  have ta := SchwartzMap.le_seminorm' ℂ a 0 (A k) (Real.cosh u)
  have tb := SchwartzMap.le_seminorm' ℂ (a+1) 0 (B k) (Real.cosh u)
  simp only [abs_of_pos (Real.cosh_pos _),iteratedDeriv_zero] at ta tb
  change |u|^a*‖iteratedDeriv b (fun x => U k (Real.cosh x)) u‖≤_
  rw [E,jet]
  apply (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hu a) ((norm_add_le _ _).trans
    (add_le_add le_rfl (show ‖(Real.sinh u:ℂ)*B k (Real.cosh u)‖≤Real.cosh u*‖B k (Real.cosh u)‖ by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)))) (norm_nonneg _) (pow_nonneg (Real.cosh_pos _).le _)).trans
  rw [pow_succ] at tb
  linarith only [ta,tb]

end
end ImbalancedChen.Part3.OriginalSwitchedSchwartzPrices20261113
