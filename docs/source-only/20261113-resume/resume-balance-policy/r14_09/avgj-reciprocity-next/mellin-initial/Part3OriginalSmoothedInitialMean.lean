import ImbalancedChen.Part3OriginalTwistedInitialMean
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Insert the original smooth geometric cutoff in the inverse-sum mean.
The dilation Y and modulus k only contribute a unit-modulus Mellin wave. -/
namespace ImbalancedChen.Part3.OriginalSmoothedInitialMean20261113
noncomputable section
open Finset MeasureTheory
open scoped BigOperators
open OriginalSwitchedMellinRows20261113 OriginalTwistedInitialMean20261113 CommonSmoothCutoff

def smoothSum (k : ℕ+) (a b c d : ℕ) (ω Y : ℝ) : ℂ :=
  ∑ m ∈ Ico a b, ∑ n ∈ Ico c d, kernel k ω m n*
    (dyadicCutoff (Y*(4*Real.pi*Real.sqrt ((m:ℝ)*n)/(k.val:ℝ))):ℂ)

private def oscillation (k : ℕ+) (a b c d : ℕ) (ω Y t : ℝ) : ℂ :=
  wave (4*Real.pi*Y/(k.val:ℝ)) t*density t*twistedSum k a b c d ω (t/2) (t/2)

private theorem transform (k : ℕ+) (a b c d : ℕ) (ω : ℝ) {Y : ℝ} (hY : 0<Y)
    (ha : 0<a) (hc : 0<c) :
    Integrable (oscillation k a b c d ω Y) ∧
      smoothSum k a b c d ω Y=((2*Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, oscillation k a b c d ω Y t := by
  classical
  let S := Ico a b
  let T := Ico c d
  let z (m n : ℕ) := Y*(4*Real.pi*Real.sqrt ((m:ℝ)*n)/(k.val:ℝ))
  let F (m n : ℕ) (t : ℝ) := kernel k ω m n*(wave (z m n) t*density t)
  have kp : (0:ℝ)<k.val := by exact_mod_cast k.property
  have hF (m n) : Integrable (F m n) := by
    apply Integrable.const_mul
    apply density_integrable.bdd_mul
    · change AEStronglyMeasurable (wave (z m n)) _
      unfold wave
      fun_prop
    · exact Filter.Eventually.of_forall (fun t => (wave_norm _ t).le)
  have sep (m) (hm : m∈S) (n) (hn : n∈T) (t : ℝ) :
      wave (z m n) t=wave (4*Real.pi*Y/(k.val:ℝ)) t*wave (m:ℝ) (t/2)*wave (n:ℝ) (t/2) := by
    have mp : (0:ℝ)<m := by exact_mod_cast ha.trans_le (mem_Ico.mp hm).1
    have np : (0:ℝ)<n := by exact_mod_cast hc.trans_le (mem_Ico.mp hn).1
    have h := half_split (div_pos kp hY) mp np (show (0:ℝ)<1 by norm_num) t
    have ze : z m n=4*Real.pi*Real.sqrt ((m:ℝ)*n)/(((k.val:ℝ)/Y)*1) := by
      dsimp [z]
      field_simp [kp.ne',hY.ne'] <;> ring
    rw [ze,h]
    have e : 4*Real.pi/((k.val:ℝ)/Y)=4*Real.pi*Y/(k.val:ℝ) := by field_simp [kp.ne',hY.ne'] <;> ring
    simp [e,wave]
  have expand (t : ℝ) : oscillation k a b c d ω Y t=∑ m ∈ S, ∑ n ∈ T, F m n t := by
    unfold oscillation twistedSum
    simp only [mul_sum]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp only [F]
    rw [sep m hm n hn]
    ring
  have hi : Integrable (oscillation k a b c d ω Y) := by
    simp_rw [show oscillation k a b c d ω Y=fun t => ∑ m ∈ S, ∑ n ∈ T, F m n t from funext expand]
    exact integrable_finsetSum S (fun m _ => integrable_finsetSum T (fun n _ => hF m n))
  refine ⟨hi,?_⟩
  have single (m) (hm : m∈S) (n) (hn : n∈T) :
      kernel k ω m n*(dyadicCutoff (z m n):ℂ)=((2*Real.pi)⁻¹:ℝ) • ∫ t : ℝ, F m n t := by
    have mp : (0:ℝ)<m := by exact_mod_cast ha.trans_le (mem_Ico.mp hm).1
    have np : (0:ℝ)<n := by exact_mod_cast hc.trans_le (mem_Ico.mp hn).1
    rw [cutoff_inversion (show 0<z m n by dsimp [z]; positivity)]
    simp only [F,integral_const_mul,Complex.real_smul]
    ring
  change (∑ m ∈ S, ∑ n ∈ T, kernel k ω m n*(dyadicCutoff (z m n):ℂ))=_
  simp_rw [expand]
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum T (fun n _ => hF m n))]
  have integral_row (m : ℕ) : (∫ t : ℝ, ∑ n ∈ T, F m n t)=∑ n ∈ T, ∫ t : ℝ, F m n t :=
    integral_finsetSum T (fun n _ => hF m n)
  simp_rw [integral_row,Finset.smul_sum]
  exact sum_congr rfl (fun m hm => sum_congr rfl (single m hm))

private theorem decay_cost (t : ℝ) :
    (1+|t/2|)^2/(1+t^4) ≤ 4*(1+t^2)⁻¹ := by
  rw [←div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0<1+t^4) (by positivity : 0<1+t^2)).mpr
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have sq := sq_abs t
  have one : (1+|t|/2)^2≤2*(1+t^2) := by nlinarith [sq_nonneg (|t|-1)]
  have prod := mul_le_mul_of_nonneg_right one (by positivity : 0≤1+t^2)
  nlinarith only [prod,sq_nonneg (t^2-1)]

/-- The arithmetic term of (4.30) before applying the original 1/k and
divisor costs. The smooth cutoff is exactly Φ(Y·4π√(mn)/k).
The constant is independent of Y, ω, the modulus subset and endpoints. -/
theorem smooth_initial_mean {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (L : Finset ℕ+) (X M N : ℕ), 1≤X → 1≤M → 1≤N →
      (∀ k ∈ L, k.val≤X) → ∀ a b c d : ℕ,
      0<a → a≤b → b≤2*a → b-a≤M → 0<c → c≤d → d≤2*c → d-c≤N →
      ∀ ω : ℝ, ∀ Y : ℝ, 0<Y →
        (∑ k ∈ L, ‖smoothSum k a b c d ω Y‖) ≤ C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N) := by
  classical
  obtain ⟨C,cpos,bound⟩ := twisted_initial_mean he
  obtain ⟨D,dpos,decay⟩ := density_decay
  refine ⟨2*D*C,by positivity,?_⟩
  intro L X M N x m n cap a b c d ha hab bc hm hc hcd dc hn ω Y hY
  let B := C*((X:ℝ)*M*N)^ε*(X:ℝ)*((X:ℝ)+(M:ℝ)*N)
  have bp : 0≤B := by dsimp [B]; positivity
  let F (k : ℕ+) := oscillation k a b c d ω Y
  have bound' (t : ℝ) := bound L X M N x m n cap a b c d ha hab bc hm hc hcd dc hn ω (t/2) (t/2)
  have each (t : ℝ) : (∑ k ∈ L, ‖F k t‖) ≤ (4*D*B)*(1+t^2)⁻¹ := by
    simp only [F,oscillation,norm_mul,wave_norm,one_mul,←mul_sum]
    have q := mul_le_mul (decay t) (bound' t) (sum_nonneg (fun _ _ => norm_nonneg _))
      (div_nonneg dpos.le (by positivity))
    apply q.trans
    change D/(1+t^4)*(B*(1+|t/2|)*(1+|t/2|))≤_
    calc
      _ = (D*B)*((1+|t/2|)^2/(1+t^4)) := by ring
      _ ≤ (D*B)*(4*(1+t^2)⁻¹) := mul_le_mul_of_nonneg_left (decay_cost t) (mul_nonneg dpos.le bp)
      _ = _ := by ring
  have intk (k : ℕ+) : Integrable (F k) := (transform k a b c d ω hY ha hc).1
  have E (k : ℕ+) : ‖smoothSum k a b c d ω Y‖ ≤ ((2*Real.pi)⁻¹ : ℝ)*(∫ t : ℝ, ‖F k t‖) := by
    rw [(transform k a b c d ω hY ha hc).2,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have E' := integral_mono (integrable_finsetSum L (fun k _ => (intk k).norm))
    (integrable_inv_one_add_sq.const_mul (4*D*B)) each
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at E'
  calc
    _ ≤ ∑ k ∈ L, ((2*Real.pi)⁻¹:ℝ)*(∫ t : ℝ, ‖F k t‖) := sum_le_sum (fun k _ => E k)
    _ = ((2*Real.pi)⁻¹:ℝ)*(∫ t : ℝ, ∑ k ∈ L, ‖F k t‖) := by
      rw [←mul_sum,integral_finsetSum L (fun k _ => (intk k).norm)]
    _ ≤ ((2*Real.pi)⁻¹:ℝ)*((4*D*B)*Real.pi) := mul_le_mul_of_nonneg_left E' (by positivity)
    _ = _ := by dsimp [B]; field_simp [Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.OriginalSmoothedInitialMean20261113
