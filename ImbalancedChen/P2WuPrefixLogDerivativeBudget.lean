import ImbalancedChen.P2WuPrefixLogProfile
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
The common quantitative budget of the actual prefix profile in the preceding
module. The constants precede every endpoint, target and positive prime point.
The full mixed logarithmic-chart tensor is bounded; no derivative budget or
prime-product distribution conclusion is an input.

This is the polylogarithmic smooth-weight step in release-20261106/en/
coefficient-appendix.tex, lines 323--331 and 551--561.  The scalar estimates
are reused from P4BSmoothStepDerivativeBudget.  The finite product step below
is the genuine Mathlib iterated Frechet Leibniz estimate.  It avoids imports
of the unavailable historical P5AllWordAmbientOccurrenceBound source.

SOURCE ONLY: not compiled and no kernel credit until separately replayed.
The same-rho signed PP bound and the remaining non-prefix carrier walls are
still separate obligations.  No syntactic EulerWord dictionary is asserted.
-/
namespace ImbalancedChen.P2WuPrefixLogDerivativeBudget

noncomputable section
open Finset Real P4B P2WuPrefixLogProfile
open scoped BigOperators Classical ContDiff

private theorem projection_norm_le {r : ℕ} (j : Fin r) :
    ‖(ContinuousLinearMap.proj j : (Fin r → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x j

private theorem affine_step_budget {r : ℕ} (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (L : (Fin r → ℝ) →L[ℝ] ℝ), ‖L‖ ≤ 1 →
      ∀ x : Fin r → ℝ,
        ‖iteratedFDeriv ℝ q (fun y => smoothGateUpperStep 1 (a+L y)) x‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := exists_smoothGateUpperStep_derivative_budget q
  refine ⟨C, zero_le_one.trans hC, ?_⟩
  intro a L hL x
  let g := fun t : ℝ => smoothGateUpperStep 1 (a+t)
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_smoothGateUpperStep _).comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ q (g ∘ L) x‖ ≤ C
  rw [L.iteratedFDeriv_comp_right hg x
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hnorm := (iteratedFDeriv ℝ q g (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin q => L)
  have hscalar : ‖iteratedFDeriv ℝ q g (L x)‖ ≤ C := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have he := congrFun (iteratedDeriv_comp_const_add q (smoothGateUpperStep 1) a) (L x)
    rw [show iteratedDeriv q g (L x) = _ from he]
    simpa only [one_pow, div_one] using H 1 zero_lt_one (a+L x)
  have hpow : ‖L‖^q ≤ 1 := pow_le_one₀ (norm_nonneg _) hL
  calc
    _ ≤ ‖iteratedFDeriv ℝ q g (L x)‖*‖L‖^q := by
      simpa only [prod_const, card_univ, Fintype.card_fin] using hnorm
    _ ≤ C*1 := mul_le_mul hscalar hpow (pow_nonneg (norm_nonneg _) _) (zero_le_one.trans hC)
    _ = C := mul_one _

private theorem mul_budget {ι : Type*} {r : ℕ}
    (F G : ι → (Fin r → ℝ) → ℝ)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) (hG : ∀ a, ContDiff ℝ ∞ (G a))
    (HF : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ q (F a) x‖ ≤ C)
    (HG : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ q (G a) x‖ ≤ C) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      ‖iteratedFDeriv ℝ q (fun y => F a y*G a y) x‖ ≤ C := by
  choose B hB HB using HF
  choose C hC HC using HG
  intro q
  refine ⟨∑ j∈range (q+1), (q.choose j:ℝ)*B j*C (q-j),
    sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hC _)), ?_⟩
  intro a x
  apply (norm_iteratedFDeriv_mul_le (hF a) (hG a) x
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).trans
  apply sum_le_sum
  intro j _
  exact mul_le_mul (mul_le_mul_of_nonneg_left (HB j a x) (Nat.cast_nonneg _))
    (HC (q-j) a x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB j))

private theorem prod_budget {ι σ : Type*} [DecidableEq σ] {r : ℕ}
    (S : Finset σ) (F : σ → ι → (Fin r → ℝ) → ℝ)
    (hF : ∀ j a, ContDiff ℝ ∞ (F j a))
    (HF : ∀ j q, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ q (F j a) x‖ ≤ C) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x,
      ‖iteratedFDeriv ℝ q (fun y => ∏ j∈S, F j a y) x‖ ≤ C := by
  induction S using Finset.induction_on with
  | empty =>
    intro q
    refine ⟨1, zero_le_one, ?_⟩
    intro a x
    cases q with
    | zero => simp
    | succ q => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero q)]
  | @insert j S hj ih =>
    have hS (a : ι) : ContDiff ℝ ∞ (fun x => ∏ l∈S, F l a x) :=
      contDiff_prod (fun l _ => hF l a)
    simpa only [prod_insert hj] using
      mul_budget (F j) (fun a x => ∏ l∈S, F l a x) (hF j) hS (HF j) ih

private def unitWindow {r : ℕ} (a b : ℝ) (j : Fin r) (x : Fin r → ℝ) : ℝ :=
  smoothGateUpperStep 1 (x j-a)*smoothGateUpperStep 1 (b-x j)

private theorem unitWindow_smooth {r : ℕ} (a b : ℝ) (j : Fin r) :
    ContDiff ℝ ∞ (unitWindow a b j) := by
  unfold unitWindow
  exact ((contDiff_smoothGateUpperStep _).comp
    ((contDiff_apply ℝ ℝ j).sub contDiff_const)).mul
      ((contDiff_smoothGateUpperStep _).comp
        (contDiff_const.sub (contDiff_apply ℝ ℝ j)))

private theorem unitWindow_budget {r : ℕ} (j : Fin r) :
    ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a b x, ‖iteratedFDeriv ℝ q (unitWindow a b j) x‖ ≤ C := by
  let L : (Fin r → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hL : ‖L‖ ≤ 1 := projection_norm_le j
  have hneg : ‖-L‖ ≤ 1 := by simpa only [norm_neg] using hL
  let F := fun a : ℝ×ℝ => fun x : Fin r → ℝ => smoothGateUpperStep 1 (x j-a.1)
  let G := fun a : ℝ×ℝ => fun x : Fin r → ℝ => smoothGateUpperStep 1 (a.2-x j)
  have hF (a : ℝ×ℝ) : ContDiff ℝ ∞ (F a) :=
    (contDiff_smoothGateUpperStep _).comp ((contDiff_apply ℝ ℝ j).sub contDiff_const)
  have hG (a : ℝ×ℝ) : ContDiff ℝ ∞ (G a) :=
    (contDiff_smoothGateUpperStep _).comp (contDiff_const.sub (contDiff_apply ℝ ℝ j))
  have HF : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ q (F a) x‖ ≤ C := by
    intro q
    obtain ⟨C, hC, H⟩ := affine_step_budget (r:=r) q
    refine ⟨C, hC, ?_⟩
    intro a x
    simpa only [F, L, ContinuousLinearMap.proj_apply, sub_eq_add_neg, add_comm] using H (-a.1) L hL x
  have HG : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ q (G a) x‖ ≤ C := by
    intro q
    obtain ⟨C, hC, H⟩ := affine_step_budget (r:=r) q
    refine ⟨C, hC, ?_⟩
    intro a x
    simpa only [G, L, neg_apply, ContinuousLinearMap.proj_apply, sub_eq_add_neg]
      using H a.2 (-L) hneg x
  intro q
  obtain ⟨C, hC, H⟩ := mul_budget F G hF hG HF HG q
  refine ⟨C, hC, ?_⟩
  intro a b x
  unfold unitWindow
  simpa only [F, G] using H (a, b) x

private def unitProfile {i r : ℕ} (a b : Fin i → ℝ) (slot : Fin i → Fin r)
    (x : Fin r → ℝ) : ℝ := ∏ j, unitWindow (a j) (b j) (slot j) x

private theorem unitProfile_smooth {i r : ℕ} (a b : Fin i → ℝ) (slot : Fin i → Fin r) :
    ContDiff ℝ ∞ (unitProfile a b slot) := by
  unfold unitProfile
  exact contDiff_prod (fun j _ => unitWindow_smooth _ _ _)

private theorem unitProfile_budget {i r : ℕ} (slot : Fin i → Fin r) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b x, ‖iteratedFDeriv ℝ q (unitProfile a b slot) x‖ ≤ C := by
  let F := fun j : Fin i => fun a : (Fin i → ℝ)×(Fin i → ℝ) =>
    unitWindow (a.1 j) (a.2 j) (slot j)
  have H j n : ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, ‖iteratedFDeriv ℝ n (F j a) x‖ ≤ C := by
    obtain ⟨C, hC, H⟩ := unitWindow_budget (slot j) n
    exact ⟨C, hC, fun a x => H (a.1 j) (a.2 j) x⟩
  obtain ⟨C, hC, HC⟩ := prod_budget univ F (fun _ _ => unitWindow_smooth _ _ _) H q
  refine ⟨C, hC, ?_⟩
  intro a b x
  unfold unitProfile
  simpa only [F] using HC (a, b) x

private theorem profile_scaled_unit {i r : ℕ} (a b : Fin i → ℝ) (w : ℝ)
    (slot : Fin i → Fin r) :
    profileFromLogs a b w slot = fun x =>
      unitProfile (fun j => a j/innerLogWidth w) (fun j => b j/innerLogWidth w)
        slot ((innerLogWidth w)⁻¹ • x) := by
  funext x
  unfold profileFromLogs unitProfile
  apply prod_congr rfl
  intro j _
  simp only [windowFromLogs, unitWindow, smoothGateUpperStep, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv]
  congr 1 <;> congr 1 <;> ring

/-- The constant is independent of every moving endpoint and every width.
All mixed derivatives, including repeated coordinate derivatives, are in
the full tensor norm. The original rank and prefix-slot map remain fixed. -/
theorem profileFromLogs_tensor_budget {i r : ℕ} (slot : Fin i → Fin r) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 → ∀ a b x,
      ‖iteratedFDeriv ℝ q (profileFromLogs a b w slot) x‖ ≤ C/w^q := by
  obtain ⟨C, hC, H⟩ := unitProfile_budget slot q
  refine ⟨C*2^q, mul_nonneg hC (by positivity), ?_⟩
  intro w hw hw1 a b x
  have hs := innerLogWidth_pos hw
  let u := unitProfile (fun j => a j/innerLogWidth w) (fun j => b j/innerLogWidth w) slot
  let M : (Fin r → ℝ) →L[ℝ] (Fin r → ℝ) :=
    (innerLogWidth w)⁻¹ • ContinuousLinearMap.id ℝ (Fin r → ℝ)
  have hu : ContDiff ℝ ∞ u := unitProfile_smooth _ _ _
  have hM : ‖M‖ ≤ (innerLogWidth w)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hs.le)
    intro y
    simp only [M, smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    exact le_rfl
  rw [profile_scaled_unit a b w slot]
  change ‖iteratedFDeriv ℝ q (u ∘ M) x‖ ≤ _
  rw [M.iteratedFDeriv_comp_right hu x
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)]
  have hnorm := (iteratedFDeriv ℝ q u (M x)).norm_compContinuousLinearMap_le (fun _ : Fin q => M)
  have hder : ‖iteratedFDeriv ℝ q u (M x)‖ ≤ C := H _ _ _
  have hi : (innerLogWidth w)⁻¹ ≤ 2/w := by
    rw [innerLogWidth, inv_div]
    exact div_le_div_of_nonneg_right (by linarith) hw.le
  calc
    _ ≤ ‖iteratedFDeriv ℝ q u (M x)‖*‖M‖^q := by
      simpa only [prod_const, card_univ, Fintype.card_fin] using hnorm
    _ ≤ C*((innerLogWidth w)⁻¹)^q :=
      mul_le_mul hder (pow_le_pow_left₀ (norm_nonneg _) hM q)
        (pow_nonneg (norm_nonneg _) q) hC
    _ ≤ C*(2/w)^q := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hi q) hC
    _ = (C*2^q)/w^q := by rw [div_pow]; ring

/-- This is exactly the existing logarithmic width (log 2/log(N+2))^B,
written out to avoid importing the unavailable historical P5 Euler chain.
The constant precedes N, all endpoints and the logarithmic base point. -/
theorem moving_log_width_tensor_budget {i r : ℕ} (slot : Fin i → Fin r) (B q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a b : Fin i → ℝ) (x : Fin r → ℝ),
      ‖iteratedFDeriv ℝ q
        (profileFromLogs a b ((log 2/log ((N:ℝ)+2))^B) slot) x‖ ≤ 
          C*(log ((N:ℝ)+2))^(B*q) := by
  obtain ⟨C, hC, H⟩ := profileFromLogs_tensor_budget slot q
  have htwo : 0 < log (2:ℝ) := log_pos (by norm_num)
  refine ⟨C/(log (2:ℝ))^(B*q), div_nonneg hC (pow_nonneg htwo.le _), ?_⟩
  intro N a b x
  have hL : log (2:ℝ) ≤ log ((N:ℝ)+2) :=
    log_le_log (by norm_num)
      (by linarith only [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N])
  have hLpos : 0 < log ((N:ℝ)+2) := htwo.trans_le hL
  have hw : 0 < (log 2/log ((N:ℝ)+2))^B := pow_pos (div_pos htwo hLpos) _
  have hw1 : (log 2/log ((N:ℝ)+2))^B ≤ 1 :=
    pow_le_one₀ (div_nonneg htwo.le hLpos.le) ((div_le_one hLpos).mpr hL)
  apply (H _ hw hw1 a b x).trans_eq
  rw [←pow_mul, div_pow]
  field_simp [htwo.ne', hLpos.ne']

/-- Genuine mixed derivatives on the original positive multiplicative
chart, uniformly in the moving endpoints, prime point and logarithmic width.
This is the analytic Euler-chart quantity, before any syntactic operator-word
conversion or prime-product distribution theorem. -/
theorem moving_physical_log_chart_budget {i r : ℕ} (slot : Fin i → Fin r) (B q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (L V : Fin i → ℝ) (p : Fin r → ℝ),
      (∀ l, 0 < p l) → ∀ z : Fin r → ℝ,
      ‖iteratedFDeriv ℝ q
        (fun y => physicalProfile L V ((log 2/log ((N:ℝ)+2))^B) slot
          (fun l => p l*exp (y l))) z‖ ≤ C*(log ((N:ℝ)+2))^(B*q) := by
  obtain ⟨C, hC, H⟩ := moving_log_width_tensor_budget slot B q
  refine ⟨C, hC, ?_⟩
  intro N L V p hp z
  rw [physicalProfile_log_chart L V _ slot p hp]
  exact H _ _ _ _

end
end ImbalancedChen.P2WuPrefixLogDerivativeBudget
