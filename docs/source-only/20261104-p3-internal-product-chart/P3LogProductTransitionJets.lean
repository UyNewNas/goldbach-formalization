import ImbalancedChen.P3AffineTransitionJets
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The manuscript's eta and psi are realized by the SAME smoothTransition.
The complete-product and original-group factors become affine compositions
of logStep. Existing Expr/jet/jets/mixed are reused, not redefined.
No distribution, Fourier, sieve or spectral theorem is implemented here.
-/
namespace ImbalancedChen.P3LogProductTransitionJets
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open P3AffineTransitionJets

/-- eta(r)=0 for r<=1 and eta(r)=1 for r>=2. -/
def eta (r : ℝ) : ℝ := Real.smoothTransition (r-1)

/-- The original smooth dyadic difference chi(r)-chi(2r), chi=1-eta. -/
def psi (r : ℝ) : ℝ := eta (2*r)-eta r

def logStep (y : ℝ) : ℝ := eta (Real.exp y)

def logHat (y : ℝ) : ℝ := logStep (y+Real.log 2)-logStep y

theorem logStep_contDiff : ContDiff ℝ ∞ logStep := by
  exact Real.smoothTransition.contDiff.comp (Real.contDiff_exp.sub contDiff_const)

theorem logStep_range (y : ℝ) : 0 ≤ logStep y ∧ logStep y ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem logStep_mono : Monotone logStep := by
  intro x y hxy
  exact Real.smoothTransition.monotone
    (sub_le_sub_right (Real.exp_le_exp.mpr hxy) 1)

theorem logStep_zero {y : ℝ} (hy : y ≤ 0) : logStep y=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := Real.exp_le_exp.mpr hy
  rw [Real.exp_zero] at h
  linarith

theorem logStep_one {y : ℝ} (hy : Real.log 2 ≤ y) : logStep y=1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := Real.exp_le_exp.mpr hy
  rw [Real.exp_log (by norm_num : (0 : ℝ)<2)] at h
  linarith

theorem logStep_log {r : ℝ} (hr : 0 < r) : logStep (Real.log r)=eta r := by
  simp only [logStep,Real.exp_log hr]

theorem logHat_log {r : ℝ} (hr : 0 < r) : logHat (Real.log r)=psi r := by
  simp only [logHat,logStep,Real.exp_add,Real.exp_log hr,
    Real.exp_log (by norm_num : (0 : ℝ)<2),psi]
  rw [mul_comm r 2]

theorem logHat_range (y : ℝ) : 0 ≤ logHat y ∧ logHat y ≤ 1 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hmono := logStep_mono (show y ≤ y+Real.log 2 by linarith)
  have h0 := logStep_range y
  have h1 := logStep_range (y+Real.log 2)
  dsimp [logHat]
  constructor <;> linarith

theorem logHat_zero_left {y : ℝ} (hy : y ≤ -Real.log 2) : logHat y=0 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [logHat,logStep_zero (by linarith),logStep_zero (by linarith),sub_self]

theorem logHat_zero_right {y : ℝ} (hy : Real.log 2 ≤ y) : logHat y=0 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [logHat,logStep_one (by linarith),logStep_one hy,sub_self]

/-- Exact finite dyadic telescoping. Endpoints are not discarded. -/
theorem sum_logHat (K : ℕ) (y : ℝ) :
    (∑ j ∈ Finset.range K,logHat (y-(j : ℝ)*Real.log 2)) =
      logStep (y+Real.log 2)-logStep (y+Real.log 2-(K : ℝ)*Real.log 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ,ih,logHat]
      have h1 : y-(K : ℝ)*Real.log 2+Real.log 2 =
          y+Real.log 2-(K : ℝ)*Real.log 2 := by ring
      have h2 : y+Real.log 2-((K+1 : ℕ) : ℝ)*Real.log 2 =
          y-(K : ℝ)*Real.log 2 := by push_cast; ring
      rw [h1,h2]
      ring

theorem sum_logHat_eq_one {K : ℕ} {y : ℝ} (hy : 0 ≤ y)
    (hK : y+Real.log 2 ≤ (K : ℝ)*Real.log 2) :
    (∑ j ∈ Finset.range K,logHat (y-(j : ℝ)*Real.log 2)) = 1 := by
  rw [sum_logHat,logStep_one (by linarith),logStep_zero (by linarith)]
  norm_num

/-- Exp-chain factors do not introduce a growing scale: each positive
order is zero on the two open constant plateaus and bounded on [0,log 2]. -/
theorem exists_logStep_derivative_bound (n : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ y : ℝ,|iteratedDeriv n logStep y| ≤ C := by
  cases n with
  | zero =>
      refine ⟨1,le_rfl,?_⟩
      intro y
      simpa only [iteratedDeriv_zero,abs_of_nonneg (logStep_range y).1] using
        (logStep_range y).2
  | succ n =>
      have hc : Continuous (iteratedDeriv (n+1) logStep) :=
        ContDiff.continuous_iteratedDeriv' (n+1)
          (logStep_contDiff.of_le (by simp))
      obtain ⟨B,hB⟩ :=
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) (Real.log 2))).exists_bound_of_continuousOn
          hc.continuousOn
      refine ⟨max B 1,le_max_right _ _,?_⟩
      intro y
      by_cases hlo : y < 0
      · have he : logStep =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
          filter_upwards [Iio_mem_nhds hlo] with z hz
          exact logStep_zero hz.le
        have hz : iteratedDeriv (n+1) logStep y=0 := by
          simpa only [iteratedDeriv_fun_const_zero] using he.iteratedDeriv_eq (n+1)
        rw [hz,abs_zero]
        exact zero_le_one.trans (le_max_right _ _)
      by_cases hhi : Real.log 2 < y
      · have he : logStep =ᶠ[𝓝 y] (fun _ : ℝ => 1) := by
          filter_upwards [Ioi_mem_nhds hhi] with z hz
          exact logStep_one hz.le
        have hz : iteratedDeriv (n+1) logStep y=0 := by
          simpa only [iteratedDeriv_const,if_neg (Nat.succ_ne_zero n)] using
            he.iteratedDeriv_eq (n+1)
        rw [hz,abs_zero]
        exact zero_le_one.trans (le_max_right _ _)
      have h := hB y ⟨le_of_not_gt hlo,le_of_not_gt hhi⟩
      exact (by simpa only [Real.norm_eq_abs] using h).trans (le_max_left _ _)

inductive Kind where
  | transition
  | product
  deriving DecidableEq

def scalar : Kind → ℝ → ℝ
  | .transition => Real.smoothTransition
  | .product => logStep

theorem scalar_contDiff (k : Kind) : ContDiff ℝ ∞ (scalar k) := by
  cases k
  · exact Real.smoothTransition.contDiff
  · exact logStep_contDiff

theorem exists_scalar_derivative_bound (n : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ k : Kind,∀ y : ℝ,|iteratedDeriv n (scalar k) y| ≤ C := by
  obtain ⟨C,hC,hc⟩ := P4B.exists_smoothTransition_global_derivative_bound n
  obtain ⟨D,hD,hd⟩ := exists_logStep_derivative_bound n
  refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
  intro k y
  cases k
  · exact (hc y).trans (le_max_left _ _)
  · exact (hd y).trans (le_max_right _ _)

/-- Only the scalar interpretation changes. The original normalized jet,
coordinate derivative and ordered mixed derivative are reused verbatim. -/
def evalK {ι : Type*} {d : ℕ} (kind : ι → Kind) (b : ι → ℝ)
    (a : ι → Fin d → ℝ) (s : ℝ) : Expr ι d → Point d → ℝ
  | .const c, _ => c
  | .step j n, x => iteratedDeriv n (scalar (kind j)) (affine b a s j x)
  | .slope j i, _ => a j i
  | .add e f, x => evalK kind b a s e x + evalK kind b a s f x
  | .mul e f, x => evalK kind b a s e x * evalK kind b a s f x

theorem evalK_hasDerivAt {ι : Type*} {d : ℕ} (e : Expr ι d)
    (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ)
    (x : Point d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => evalK kind b a s e (shift x i t))
      (s*evalK kind b a s (jet i e) x) 0 := by
  induction e with
  | const c => simpa [evalK,jet] using hasDerivAt_const (0 : ℝ) c
  | slope j k => simpa [evalK,jet] using hasDerivAt_const (0 : ℝ) (a j k)
  | step j n =>
      have hd : Differentiable ℝ (iteratedDeriv n (scalar (kind j))) :=
        ContDiff.differentiable_iteratedDeriv' n
          ((scalar_contDiff (kind j)).of_le (by simp))
      have hi : HasDerivAt
          (fun t : ℝ => affine b a s j x+(s*a j i)*t) (s*a j i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (s*a j i)).const_add
          (affine b a s j x)
      have h := (hd (affine b a s j x)).hasDerivAt.comp 0 hi
      simp only [mul_zero,add_zero] at h
      rw [← iteratedDeriv_succ] at h
      convert h using 1
      · funext t; simp only [evalK,affine_shift]
      · simp only [evalK,jet]; ring
  | add e f he hf => convert he.add hf using 1 <;> simp only [evalK,jet] <;> ring
  | mul e f he hf => convert he.mul hf using 1 <;> simp only [evalK,jet,shift_zero] <;> ring

theorem mixed_evalK {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    mixed is (evalK kind b a s e) =
      fun x => s^is.length * evalK kind b a s (jets is e) x := by
  induction is with
  | nil => funext x; simp [mixed,jets]
  | cons i is ih =>
      funext x
      simp only [mixed,ih,coordinateDeriv]
      rw [((evalK_hasDerivAt (jets is e) kind b a s x i).const_mul (s^is.length)).deriv]
      simp only [jets,List.length_cons,pow_succ]
      ring

theorem continuous_evalK {ι : Type*} {d : ℕ} (e : Expr ι d)
    (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    Continuous (evalK kind b a s e) := by
  induction e with
  | const c => exact continuous_const
  | slope j i => exact continuous_const
  | step j n =>
      apply (ContDiff.continuous_iteratedDeriv' n
        ((scalar_contDiff (kind j)).of_le (by simp))).comp
      unfold affine
      fun_prop
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf

theorem continuous_mixed_evalK {ι : Type*} {d : ℕ} (is : List (Fin d)) (e : Expr ι d)
    (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ) (s : ℝ) :
    Continuous (mixed is (evalK kind b a s e)) := by
  rw [mixed_evalK]
  exact continuous_const.mul (continuous_evalK _ _ _ _ _)

theorem exists_evalK_bound {ι : Type*} {d : ℕ} (e : Expr ι d)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ (s : ℝ) (x : Point d),|evalK kind b a s e x| ≤ C := by
  induction e with
  | const c => exact ⟨|c|+1,by linarith [abs_nonneg c],by intros; dsimp [evalK]; linarith⟩
  | slope j i =>
      refine ⟨L+1,by linarith,?_⟩
      intro kind b a ha s x
      exact (ha j i).trans (by linarith)
  | step j n =>
      obtain ⟨C,hC,hc⟩ := exists_scalar_derivative_bound n
      exact ⟨C,hC,fun kind b a ha s x => hc (kind j) _⟩
  | add e f he hf =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hf
      refine ⟨C+D,by linarith,?_⟩
      intro kind b a ha s x
      exact (abs_add _ _).trans (add_le_add (hc kind b a ha s x) (hd kind b a ha s x))
  | mul e f he hf =>
      obtain ⟨C,hC,hc⟩ := he
      obtain ⟨D,hD,hd⟩ := hf
      refine ⟨C*D,by nlinarith,?_⟩
      intro kind b a ha s x
      rw [evalK,abs_mul]
      exact mul_le_mul (hc kind b a ha s x) (hd kind b a ha s x) (abs_nonneg _) (by linarith)

theorem exists_family_mixed_boundK {ι κ : Type*} [Fintype κ] {d : ℕ}
    (E : κ → Expr ι d) (q : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (kind : ι → Kind) (b : ι → ℝ) (a : ι → Fin d → ℝ),
      (∀ j i,|a j i| ≤ L) → ∀ s : ℝ,0 ≤ s → ∀ k : κ,
      ∀ v : Fin q → Fin d,∀ x : Point d,
        |mixed (List.ofFn v) (evalK kind b a s (E k)) x| ≤ C*s^q := by
  have h := fun u : κ × (Fin q → Fin d) => exists_evalK_bound (jets (List.ofFn u.2) (E u.1)) L hL
  choose c hc hb using h
  let C := 1+∑ u : κ × (Fin q → Fin d),c u
  have hc0 (u : κ × (Fin q → Fin d)) : 0 ≤ c u := zero_le_one.trans (hc u)
  refine ⟨C,?_,?_⟩
  · dsimp [C]
    have hsum : 0 ≤ ∑ u : κ × (Fin q → Fin d),c u := Finset.sum_nonneg (fun u _ => hc0 u)
    linarith
  intro kind b a ha s hs k v x
  have hle : c (k,v) ≤ C :=
    (Finset.single_le_sum (fun u _ => hc0 u) (Finset.mem_univ (k,v))).trans (by dsimp [C]; linarith)
  rw [mixed_evalK,abs_mul,abs_of_nonneg (pow_nonneg hs _),List.length_ofFn]
  calc
    _ ≤ s^q*c (k,v) := mul_le_mul_of_nonneg_left (hb (k,v) kind b a ha s x) (pow_nonneg hs q)
    _ ≤ s^q*C := mul_le_mul_of_nonneg_left hle (pow_nonneg hs q)
    _ = _ := mul_comm _ _

def rename {ι κ : Type*} {d : ℕ} (f : ι → κ) : Expr ι d → Expr κ d
  | .const c => .const c
  | .step j n => .step (f j) n
  | .slope j i => .slope (f j) i
  | .add e g => .add (rename f e) (rename f g)
  | .mul e g => .mul (rename f e) (rename f g)

/-- Reuse the previous atlas expression exactly, not an independently
constructed replacement for its gates or compact cutoff. -/
theorem evalK_rename_transition {ι κ : Type*} {d : ℕ} (e : Expr ι d) (f : ι → κ)
    (kind : κ → Kind) (b : κ → ℝ) (a : κ → Fin d → ℝ) (s : ℝ)
    (hk : ∀ j,kind (f j)=.transition) (x : Point d) :
    evalK kind b a s (rename f e) x = eval (b ∘ f) (a ∘ f) s e x := by
  induction e with
  | const c => rfl
  | slope j i => rfl
  | step j n => simp only [rename,evalK,hk,scalar,eval,affine,Function.comp_apply]
  | add e g he hg => simp only [rename,evalK,eval,he,hg]
  | mul e g he hg => simp only [rename,evalK,eval,he,hg]

end
end ImbalancedChen.P3LogProductTransitionJets
