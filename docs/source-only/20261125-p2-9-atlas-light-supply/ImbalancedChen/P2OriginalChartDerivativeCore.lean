import ImbalancedChen.P2OriginalEulerWordConjugacyCore
import ImbalancedChen.P2SmoothLogFloorDerivativeCore
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW MATHEMATICAL CREDIT.
Exact original BoundedDerivatives definition and affine, constant, sum,
difference, product and finite-product proof texts from the original
ClassicalSmoothEulerBounds owner. Every original fully qualified name
and source body is retained. This removes its unrelated full classical
history dependency from the new actual Gamma5 atlas consumer.
-/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
noncomputable section
open Finset Set Filter Real
open P4B
open scoped Classical Topology BigOperators ContDiff

/-- Bounds at every mixed order, uniform in the chart parameters. -/
def BoundedDerivatives {ι : Type*} {d : ℕ} (F : ι → E d → ℝ) : Prop :=
  (∀ i,ContDiff ℝ ∞ (F i)) ∧
    ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ i x,‖iteratedFDeriv ℝ n (F i) x‖≤C

theorem affine {ι : Type*} {d : ℕ} {f : ℝ → ℝ} (hf : ScalarBound f) (a λ : ι → ℝ)
    (L : E d →L[ℝ] ℝ) {R : ℝ} (hR : 0≤R) (hλ : ∀i,|λ i|≤R) :
    BoundedDerivatives (fun i x => f (a i+λ i*L x)) := by
  refine ⟨fun i => hf.1.comp (contDiff_const.add (contDiff_const.mul L.contDiff)),?_⟩
  intro n
  obtain ⟨A,hA,hfA⟩ := hf.2 n
  refine ⟨A*(R*‖L‖)^n,mul_nonneg hA (pow_nonneg (mul_nonneg hR (norm_nonneg _)) _),?_⟩
  intro i x
  let g := fun t : ℝ => f (a i+t)
  let M := (λ i) • L
  have hg : ContDiff ℝ ∞ g := hf.1.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ n (g ∘ M) x‖≤_
  rw [M.iteratedFDeriv_comp_right hg x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n g (M x)).norm_compContinuousLinearMap_le (fun _ : Fin n => M)
  have heq := congrFun (iteratedDeriv_comp_const_add n f (a i)) (M x)
  have he : ‖iteratedFDeriv ℝ n g (M x)‖≤A := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,show iteratedDeriv n g (M x)=_ from heq]
    exact hfA _
  have hM : ‖M‖≤R*‖L‖ := by
    rw [show ‖M‖=|λ i|*‖L‖ by simp [M,Real.norm_eq_abs]]
    exact mul_le_mul_of_nonneg_right (hλ i) (norm_nonneg _)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (M x)‖*‖M‖^n := by
      simpa only [prod_const,card_univ,Fintype.card_fin] using hnorm
    _ ≤ _ := mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hM n) (pow_nonneg (norm_nonneg _) n) hA

theorem one {ι : Type*} {d : ℕ} : BoundedDerivatives (fun _ : ι => fun _ : E d => (1:ℝ)) := by
  refine ⟨fun _ => contDiff_const,fun n => ⟨1,zero_le_one,?_⟩⟩
  intro _ x
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

theorem add {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x+G i x) := by
  refine ⟨fun i => (hF.1 i).add (hG.1 i),?_⟩
  intro n
  obtain ⟨B,hB,hf⟩ := hF.2 n
  obtain ⟨C,hC,hg⟩ := hG.2 n
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro i x
  change ‖iteratedFDeriv ℝ n (F i+G i) x‖≤_
  rw [iteratedFDeriv_add_apply ((hF.1 i).of_le (by simp)).contDiffAt ((hG.1 i).of_le (by simp)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf i x) (hg i x))

theorem sub {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x-G i x) := by
  refine ⟨fun i => (hF.1 i).sub (hG.1 i),?_⟩
  intro n
  obtain ⟨B,hB,hf⟩ := hF.2 n
  obtain ⟨C,hC,hg⟩ := hG.2 n
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro i x
  change ‖iteratedFDeriv ℝ n (F i-G i) x‖≤_
  rw [iteratedFDeriv_sub_apply ((hF.1 i).of_le (by simp)).contDiffAt ((hG.1 i).of_le (by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hf i x) (hg i x))

theorem mul {ι : Type*} {d : ℕ} {F G : ι → E d → ℝ}
    (hF : BoundedDerivatives F) (hG : BoundedDerivatives G) :
    BoundedDerivatives (fun i x => F i x*G i x) := by
  refine ⟨fun i => (hF.1 i).mul (hG.1 i),?_⟩
  choose B hB hf using hF.2
  choose C hC hg using hG.2
  intro n
  refine ⟨∑ j∈range (n+1),(n.choose j:ℝ)*B j*C (n-j),
    sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hC _)),?_⟩
  intro i x
  have hle : ‖iteratedFDeriv ℝ n (fun y => F i y*G i y) x‖≤
      ∑ j∈range (n+1),(n.choose j:ℝ)*‖iteratedFDeriv ℝ j (F i) x‖*‖iteratedFDeriv ℝ (n-j) (G i) x‖ :=
    norm_iteratedFDeriv_mul_le (hF.1 i) (hG.1 i) x (by simp)
  apply hle.trans
  exact sum_le_sum (fun j _ => mul_le_mul (mul_le_mul_of_nonneg_left (hf j i x) (Nat.cast_nonneg _))
    (hg (n-j) i x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j)))

theorem prod {ι σ : Type*} [DecidableEq σ] {d : ℕ} (S : Finset σ) (F : σ → ι → E d → ℝ)
    (hF : ∀ j,BoundedDerivatives (F j)) :
    BoundedDerivatives (fun i x => ∏ j∈S,F j i x) := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using (one (ι:=ι) (d:=d))
  | @insert j S hj ih => simpa only [prod_insert hj] using mul (hF j) ih

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
