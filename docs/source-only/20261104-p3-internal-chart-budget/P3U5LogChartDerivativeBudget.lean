import ImbalancedChen.P3AffineTransitionJets
import ImbalancedChen.P3U5SmoothRootPartition

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The existing four-lane weights are pulled back by ORIGINAL GROUP logarithms.
The two groups may have any fixed finite number of HB slots; other slots
can be tagged `none`. No sharp group-product boundary is introduced.
A concrete fixed smooth cutoff is one on [0,log 2]^d, with support in
[-2,2]^d. All derivative constants precede N, group scales, slot tags and m.
This supplies the ATLAS multiplier, not all other factors of a PP chart.
-/
namespace ImbalancedChen.P3U5LogChartDerivativeBudget
noncomputable section
open scoped Classical BigOperators Topology
open P3AffineTransitionJets
open P3U5RootAtlas
open P3U5SmoothRootPartition (margin wallOffset wallForm smoothWeight smoothWeight_sum circuit gate)

/-- Coefficients of the four ORIGINAL affine margins, including signs. -/
def marginCoeff : Fin 4 → Fin 2 → ℝ :=
  ![![-1,-1],![0,-(1/2 : ℝ)],![(3/2 : ℝ),3/2],![-(3/2 : ℝ),-2]]

theorem marginCoeff_abs_le (j : Fin 4) (i : Fin 2) : |marginCoeff j i| ≤ 2 := by
  fin_cases j <;> fin_cases i <;> norm_num [marginCoeff]

theorem margin_affine (j : Fin 4) (x : Fin 2 → ℝ) :
    margin j x = wallOffset j + ∑ i : Fin 2,marginCoeff j i*x i := by
  fin_cases j <;> simp [margin,wallForm,wallOffset,marginCoeff,Fin.sum_univ_two] <;> ring

def groupLog {d : ℕ} (slot : Fin d → Option (Fin 2)) (x : Point d) (i : Fin 2) : ℝ :=
  ∑ k,if slot k = some i then x k else 0

/-- ell is log N. The original product scale R is not a residual quotient. -/
def chartPoint {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (x : Point d) : Fin 2 → ℝ :=
  fun i => Real.log (R i)/ell + groupLog slot x i/ell

theorem chartPoint_original_group {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (hR : ∀ i,0 < R i) (slot : Fin d → Option (Fin 2)) (x : Point d) (i : Fin 2) :
    chartPoint ell R slot x i = Real.log (R i * Real.exp (groupLog slot x i))/ell := by
  rw [Real.log_mul (hR i).ne' (Real.exp_pos _).ne',Real.log_exp]
  simp only [chartPoint,add_div]

def coefficient {d : ℕ} (ell : ℝ) (slot : Fin d → Option (Fin 2))
    (j : Fin 4) (k : Fin d) : ℝ :=
  (match slot k with | none => 0 | some i => marginCoeff j i)/ell

private theorem grouped_linear_sum {d : ℕ} (ell : ℝ)
    (slot : Fin d → Option (Fin 2)) (j : Fin 4) (x : Point d) :
    (∑ i : Fin 2,marginCoeff j i*(groupLog slot x i/ell)) =
      ∑ k,coefficient ell slot j k*x k := by
  simp only [groupLog,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  cases h : slot k with
  | none => simp [coefficient,h]
  | some i =>
      fin_cases i <;> simp [coefficient,h,Fin.sum_univ_two] <;> ring

theorem margin_chartPoint {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (j : Fin 4) (x : Point d) :
    margin j (chartPoint ell R slot x) =
      (wallOffset j + ∑ i : Fin 2,marginCoeff j i*(Real.log (R i)/ell)) +
        ∑ k,coefficient ell slot j k*x k := by
  rw [margin_affine]
  simp only [chartPoint,mul_add,Finset.sum_add_distrib]
  rw [grouped_linear_sum]
  ring

abbrev Atom (d : ℕ) := Sum (Fin 4) (Fin d × Bool)

def compl {ι : Type*} {d : ℕ} (e : Expr ι d) : Expr ι d :=
  .add (.const 1) (.mul (.const (-1)) e)

def atlasExpr (d : ℕ) (l : Lane) : Expr (Atom d) d :=
  let g := fun j : Fin 4 => Expr.step (Sum.inl j) 0
  match l with
  | .rise => g 0
  | .plateau => .mul (compl (g 0)) (.mul (g 1) (g 2))
  | .fall => .mul (.mul (compl (g 0)) (compl (.mul (g 1) (g 2)))) (g 3)
  | .head => .mul (.mul (compl (g 0)) (compl (.mul (g 1) (g 2)))) (compl (g 3))

def exprProduct {ι : Type*} {d : ℕ} : List (Expr ι d) → Expr ι d
  | [] => .const 1
  | e::es => .mul e (exprProduct es)

def cutoffExpr (d : ℕ) : Expr (Atom d) d :=
  exprProduct (List.ofFn (fun i : Fin d =>
    Expr.mul (.step (.inr (i,false)) 0) (compl (.step (.inr (i,true)) 0))))

def profileExpr (d : ℕ) (l : Lane) : Expr (Atom d) d :=
  .mul (cutoffExpr d) (atlasExpr d l)

def window {d : ℕ} (x : Point d) : ℝ :=
  ∏ i,Real.smoothTransition (x i+2)*(1-Real.smoothTransition (x i-1))

def profile {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) (x : Point d) : ℝ :=
  window x * smoothWeight m l (chartPoint ell R slot x)

/-- Constant-width cutoff atoms are encoded with slope 1/(m+1).
They remain the SAME cutoff for every m; no sharpening is hidden here. -/
def offsets {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ) (m : ℕ) : Atom d → ℝ
  | .inl j => (m+1 : ℝ)*(wallOffset j + ∑ i : Fin 2,marginCoeff j i*(Real.log (R i)/ell))
  | .inr (_,false) => 2
  | .inr (_,true) => -1

def slopes {d : ℕ} (ell : ℝ) (slot : Fin d → Option (Fin 2)) (m : ℕ) :
    Atom d → Fin d → ℝ
  | .inl j, k => coefficient ell slot j k
  | .inr (i,_), k => if k=i then (m+1 : ℝ)⁻¹ else 0

theorem atlas_argument {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (j : Fin 4) (x : Point d) :
    affine (offsets ell R m) (slopes ell slot m) (m+1 : ℝ) (.inl j) x =
      (m+1 : ℝ)*margin j (chartPoint ell R slot x) := by
  rw [margin_chartPoint]
  simp only [affine,offsets,slopes]
  ring

theorem cutoff_argument {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (i : Fin d) (b : Bool) (x : Point d) :
    affine (offsets ell R m) (slopes ell slot m) (m+1 : ℝ) (.inr (i,b)) x =
      if b then x i-1 else x i+2 := by
  have hm : (m+1 : ℝ) ≠ 0 := by positivity
  cases b <;> simp [affine,offsets,slopes,ite_mul,hm,mul_assoc] <;> ring

private theorem eval_exprProduct {ι : Type*} {d : ℕ} (es : List (Expr ι d))
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) :
    eval b a s (exprProduct es) x = (es.map (fun e => eval b a s e x)).prod := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [exprProduct,eval,List.map_cons,List.prod_cons,ih]

private theorem eval_compl {ι : Type*} {d : ℕ} (e : Expr ι d)
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) :
    eval b a s (compl e) x = 1-eval b a s e x := by simp [compl,eval]; ring

theorem eval_atlasExpr {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) (x : Point d) :
    eval (offsets ell R m) (slopes ell slot m) (m+1 : ℝ) (atlasExpr d l) x =
      smoothWeight m l (chartPoint ell R slot x) := by
  cases l <;> simp only [atlasExpr,eval_compl,eval,iteratedDeriv_zero,atlas_argument,
    smoothWeight,circuit,gate]

theorem eval_cutoffExpr {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (x : Point d) :
    eval (offsets ell R m) (slopes ell slot m) (m+1 : ℝ) (cutoffExpr d) x = window x := by
  rw [cutoffExpr,eval_exprProduct,List.map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [eval,eval_compl,iteratedDeriv_zero,cutoff_argument,Bool.false_eq_true,
    if_false,if_true]

theorem eval_profileExpr {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) :
    eval (offsets ell R m) (slopes ell slot m) (m+1 : ℝ) (profileExpr d l) =
      profile ell R slot m l := by
  funext x
  rw [profileExpr,eval,eval_cutoffExpr,eval_atlasExpr]
  rfl

theorem slopes_bound {d : ℕ} {ell : ℝ} (hell : 1 ≤ ell)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (j : Atom d) (i : Fin d) :
    |slopes ell slot m j i| ≤ 2 := by
  have he : 0 < ell := by linarith
  have hm : (1 : ℝ) ≤ m+1 := by linarith [Nat.cast_nonneg m]
  cases j with
  | inl j =>
      cases h : slot i with
      | none => simp [slopes,coefficient,h]
      | some k =>
          rw [slopes,coefficient,h,abs_div,abs_of_pos he]
          apply (div_le_iff₀ he).mpr
          have hc := marginCoeff_abs_le j k
          nlinarith
  | inr ib =>
      rcases ib with ⟨k,b⟩
      by_cases h : i=k
      · simp only [slopes,if_pos h,abs_inv,abs_of_pos (show (0 : ℝ)<m+1 by positivity)]
        rw [inv_eq_one_div]
        apply (div_le_iff₀ (by positivity : (0 : ℝ)<m+1)).mpr
        nlinarith
      · simp only [slopes,if_neg h,abs_zero]; norm_num

theorem window_eq_one {d : ℕ} {x : Point d}
    (hx : ∀ i,-1 ≤ x i ∧ x i ≤ 1) : window x = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  rw [Real.smoothTransition.one_of_one_le (by linarith [(hx i).1]),
    Real.smoothTransition.zero_of_nonpos (by linarith [(hx i).2])]
  norm_num

theorem profile_eq_original_on_chart {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) {x : Point d}
    (hx : ∀ i,0 ≤ x i ∧ x i ≤ Real.log 2) :
    profile ell R slot m l x = smoothWeight m l (chartPoint ell R slot x) := by
  have hlog : Real.log 2 ≤ (1 : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
  rw [profile,window_eq_one (fun i => ⟨by linarith [(hx i).1],(hx i).2.trans hlog⟩),one_mul]

theorem profile_sum {d : ℕ} (ell : ℝ) (R : Fin 2 → ℝ)
    (slot : Fin d → Option (Fin 2)) (m : ℕ) (x : Point d) :
    (∑ l : Lane,profile ell R slot m l x) = window x := by
  simp only [profile,← Finset.mul_sum,smoothWeight_sum,mul_one]

/-- Fixed derivative order and dimension precede every later chart datum.
No derivative/variation/Fourier budget is a premise of this theorem. -/
theorem exists_profile_mixed_bound (d q : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ ell : ℝ,1 ≤ ell → ∀ R : Fin 2 → ℝ,
      ∀ slot : Fin d → Option (Fin 2),∀ m : ℕ,∀ l : Lane,
      ∀ v : Fin q → Fin d,∀ x : Point d,
        |mixed (List.ofFn v) (profile ell R slot m l) x| ≤ C*(m+1 : ℝ)^q := by
  obtain ⟨C,hC,hbound⟩ := exists_family_mixed_bound (profileExpr d) q 2 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ell hell R slot m l v x
  rw [← eval_profileExpr]
  exact hbound (offsets ell R m) (slopes ell slot m) (slopes_bound hell slot m)
    (m+1) (by positivity) l v x

theorem continuous_mixed_profile {d : ℕ} (is : List (Fin d)) (ell : ℝ)
    (R : Fin 2 → ℝ) (slot : Fin d → Option (Fin 2)) (m : ℕ) (l : Lane) :
    Continuous (mixed is (profile ell R slot m l)) := by
  rw [← eval_profileExpr]
  exact continuous_mixed_eval _ _ _ _ _

end
end ImbalancedChen.P3U5LogChartDerivativeBudget
