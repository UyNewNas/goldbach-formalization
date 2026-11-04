import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Finite chain/product-rule calculation for the ACTUAL smoothTransition.
`mixed` is defined with ordinary derivatives, not with the formal expression.
The equality between these derivatives and the finite jet calculation is proved.
Constants are chosen before affine offsets, scale and bounded coefficients.
No BV, SW, PNT, Fourier, spectral or PP assertion is introduced here.
-/
namespace ImbalancedChen.P3AffineTransitionJets
noncomputable section
open scoped Classical BigOperators Topology

abbrev Point (d : ℕ) := Fin d → ℝ

/-- Constant slope leaves allow differentiation without putting later
arithmetic data into the syntax or into its chosen derivative constant. -/
inductive Expr (ι : Type*) (d : ℕ) where
  | const : ℝ → Expr ι d
  | step : ι → ℕ → Expr ι d
  | slope : ι → Fin d → Expr ι d
  | add : Expr ι d → Expr ι d → Expr ι d
  | mul : Expr ι d → Expr ι d → Expr ι d

def affine {ι : Type*} {d : ℕ} (b : ι → ℝ)
    (a : ι → Fin d → ℝ) (s : ℝ) (j : ι) (x : Point d) : ℝ :=
  b j + s * ∑ i, a j i * x i

def eval {ι : Type*} {d : ℕ} (b : ι → ℝ)
    (a : ι → Fin d → ℝ) (s : ℝ) : Expr ι d → Point d → ℝ
  | .const c, _ => c
  | .step j n, x => iteratedDeriv n Real.smoothTransition (affine b a s j x)
  | .slope j i, _ => a j i
  | .add e f, x => eval b a s e x + eval b a s f x
  | .mul e f, x => eval b a s e x * eval b a s f x

/-- The common scale s is kept OUTSIDE the normalized jet. -/
def jet {ι : Type*} {d : ℕ} (i : Fin d) : Expr ι d → Expr ι d
  | .const _ => .const 0
  | .step j n => .mul (.slope j i) (.step j (n+1))
  | .slope _ _ => .const 0
  | .add e f => .add (jet i e) (jet i f)
  | .mul e f => .add (.mul (jet i e) f) (.mul e (jet i f))

def shift {d : ℕ} (x : Point d) (i : Fin d) (t : ℝ) : Point d :=
  fun k => x k + if k=i then t else 0

@[simp] theorem shift_zero {d : ℕ} (x : Point d) (i : Fin d) : shift x i 0 = x := by
  funext k
  simp [shift]

theorem affine_shift {ι : Type*} {d : ℕ} (b : ι → ℝ)
    (a : ι → Fin d → ℝ) (s : ℝ) (j : ι) (x : Point d) (i : Fin d) (t : ℝ) :
    affine b a s j (shift x i t) = affine b a s j x + (s*a j i)*t := by
  simp only [affine,shift,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

/-- Genuine one-dimensional differentiation along a coordinate line. -/
theorem eval_hasDerivAt {ι : Type*} {d : ℕ} (e : Expr ι d)
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) (x : Point d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => eval b a s e (shift x i t))
      (s*eval b a s (jet i e) x) 0 := by
  induction e with
  | const c => simpa [eval,jet] using hasDerivAt_const (0 : ℝ) c
  | slope j k => simpa [eval,jet] using hasDerivAt_const (0 : ℝ) (a j k)
  | step j n =>
      have hd : Differentiable ℝ (iteratedDeriv n Real.smoothTransition) :=
        ContDiff.differentiable_iteratedDeriv' n
          (Real.smoothTransition.contDiff (n := (n+1 : ℕ)))
      have hinner : HasDerivAt
          (fun t : ℝ => affine b a s j x + (s*a j i)*t) (s*a j i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (s*a j i)).const_add
          (affine b a s j x)
      have h := (hd (affine b a s j x)).hasDerivAt.comp 0 hinner
      simp only [mul_zero,add_zero] at h
      rw [← iteratedDeriv_succ] at h
      convert h using 1
      · funext t
        simp only [eval,affine_shift]
      · simp only [eval,jet]
        ring
  | add e f he hf =>
      convert he.add hf using 1 <;> simp only [eval,jet] <;> ring
  | mul e f he hf =>
      convert he.mul hf using 1 <;> simp only [eval,jet,shift_zero] <;> ring

/-- Ordered mixed derivatives. Repeated coordinate directions are allowed. -/
def coordinateDeriv {d : ℕ} (i : Fin d) (f : Point d → ℝ) (x : Point d) : ℝ :=
  deriv (fun t : ℝ => f (shift x i t)) 0

def mixed {d : ℕ} : List (Fin d) → (Point d → ℝ) → Point d → ℝ
  | [], f => f
  | i::is, f => coordinateDeriv i (mixed is f)

def jets {ι : Type*} {d : ℕ} : List (Fin d) → Expr ι d → Expr ι d
  | [], e => e
  | i::is, e => jet i (jets is e)

theorem mixed_eq_jets {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    mixed is (eval b a s e) = fun x => s^is.length * eval b a s (jets is e) x := by
  induction is with
  | nil => funext x; simp [mixed,jets]
  | cons i is ih =>
      funext x
      simp only [mixed,ih,coordinateDeriv]
      rw [((eval_hasDerivAt (jets is e) b a s x i).const_mul (s^is.length)).deriv]
      simp only [jets,List.length_cons,pow_succ]
      ring

theorem continuous_eval {ι : Type*} {d : ℕ} (e : Expr ι d)
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) : Continuous (eval b a s e) := by
  induction e with
  | const c => exact continuous_const
  | slope j i => exact continuous_const
  | step j n =>
      apply (P4B.continuous_iteratedDeriv_smoothTransition n).comp
      unfold affine
      fun_prop
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem continuous_mixed_eval {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    Continuous (mixed is (eval b a s e)) := by
  rw [mixed_eq_jets]
  exact continuous_const.mul (continuous_eval _ _ _ _)

/-- Finite expression majorant. No assumption about a derivative of the
composite chart is used: scalar smoothTransition bounds are invoked here. -/
theorem exists_eval_bound {ι : Type*} {d : ℕ} (e : Expr ι d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ (s : ℝ) (x : Point d),|eval b a s e x| ≤ C := by
  induction e with
  | const c => exact ⟨|c|+1,by linarith [abs_nonneg c],by intros; dsimp [eval]; linarith⟩
  | slope j i =>
      refine ⟨L+1,by linarith,?_⟩
      intro b a ha s x
      exact (ha j i).trans (by linarith)
  | step j n =>
      obtain ⟨C,hC,hbound⟩ := P4B.exists_smoothTransition_global_derivative_bound n
      exact ⟨C,hC,fun b a ha s x => hbound _⟩
  | add e f he hf =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hf
      refine ⟨C+D,by linarith,?_⟩
      intro b a ha s x
      exact (abs_add _ _).trans (add_le_add (hc b a ha s x) (hd b a ha s x))
  | mul e f he hf =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hf
      refine ⟨C*D,by nlinarith,?_⟩
      intro b a ha s x
      rw [eval,abs_mul]
      exact mul_le_mul (hc b a ha s x) (hd b a ha s x) (abs_nonneg _) (by linarith)

/-- A common constant for a finite family and ALL ordered q-fold partials.
The affine coefficients and offsets are later data. No evaluation of the
finite jet expressions is requested by this theorem. -/
theorem exists_family_mixed_bound {ι κ : Type*} [Fintype κ] {d : ℕ}
    (E : κ → Expr ι d) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ s : ℝ,0 ≤ s → ∀ k : κ,
      ∀ v : Fin q → Fin d,∀ x : Point d,
        |mixed (List.ofFn v) (eval b a s (E k)) x| ≤ C*s^q := by
  have h : ∀ u : κ × (Fin q → Fin d),∃ C : ℝ,1 ≤ C ∧
      ∀ (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ (s : ℝ) (x : Point d),
        |eval b a s (jets (List.ofFn u.2) (E u.1)) x| ≤ C :=
    fun u => exists_eval_bound _ L hL
  choose c hc hb using h
  let C := 1 + ∑ u : κ × (Fin q → Fin d),c u
  have hc0 (u : κ × (Fin q → Fin d)) : 0 ≤ c u := zero_le_one.trans (hc u)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hsum : 0 ≤ ∑ u : κ × (Fin q → Fin d),c u := Finset.sum_nonneg (fun u _ => hc0 u)
    linarith
  intro b a ha s hs k v x
  have hle : c (k,v) ≤ C :=
    (Finset.single_le_sum (fun u _ => hc0 u) (Finset.mem_univ (k,v))).trans (by dsimp [C]; linarith)
  rw [mixed_eq_jets,abs_mul,abs_of_nonneg (pow_nonneg hs _),List.length_ofFn]
  calc
    _ ≤ s^q * c (k,v) := mul_le_mul_of_nonneg_left (hb (k,v) b a ha s x) (pow_nonneg hs q)
    _ ≤ s^q*C := mul_le_mul_of_nonneg_left hle (pow_nonneg hs q)
    _ = _ := mul_comm _ _

end
end ImbalancedChen.P3AffineTransitionJets
