import ImbalancedChen.Part3TwoLongActualHBShortMass
import ImbalancedChen.Part3TwoLongActualLowerBrunMoment
import ImbalancedChen.Part3TwoLongMellinLogBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Uniform logarithmic payment of the actual signed lower-rho EXPANDED
two-long core with the literal remaining HB coefficient. This is the last
E4 power-error term. The rough restoration and retained-row identification
are not hypotheses and are not claimed to follow from this local result.
-/
namespace ImbalancedChen.Part3.TwoLongActualLowerCorePayment
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles (Block)
open ImbalancedChen.P5Z.ActualHBDyadicProductWindow (lower)
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords (Role)
open ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail (lowerQ lowerRho)
open TwoLongActualHBShortMass TwoLongActualLowerBrunMoment
open TwoLongHBMellinBrunProfiles TwoLongMellinLogBudget
open TwoLongInternalP2Modes (CompositeWeilInput)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowCore (policy : List ℕ → Bool) (N cap : ℕ) (w z L Z : ℝ)
    (j : ℕ) (b₁ b₂ : Bool) (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role) : ℂ :=
  ∑ m ∈ shortSupport bs,
    lowerBrunCoreSum policy N cap w z L Z j b₁ b₂ delta U V t₁ t₂ label log₁ log₂
      (shortSequence bs Z y xi rs m) m

/-- Both finite inventories are paid from their actual coefficients.
The target N and physical rho stay the same for every short product. -/
theorem rowCore_bound (hWeil : CompositeWeilInput)
    (policy : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ) {Z X : ℝ}
    (hZ : 1 ≤ Z) (hX : 1 ≤ X)
    (hlevel : ∀ q ∈ lowerQ policy N cap w z,
      lowerRho policy N cap w z L q ≠ 0 → q ≤ D)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ a, 2 * (lower (bs a) : ℝ) ≤ X) :
    ‖rowCore policy N cap w z L Z j b₁ b₂ delta U V t₁ t₂ label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16) *
          (1 + Real.log X)^Fintype.card ι := by
  let T : ℝ := ((D : ℝ) * Real.sqrt D + 1) *
    (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmass := shortSequence_mass bs Z y xi rs hX hcap
  calc
    _ ≤ ∑ m ∈ shortSupport bs,
        ‖lowerBrunCoreSum policy N cap w z L Z j b₁ b₂ delta U V t₁ t₂ label log₁ log₂
          (shortSequence bs Z y xi rs m) m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ shortSupport bs,
        pairCost delta U V H * ((Z^(2*j+1))^2 * ‖shortSequence bs Z y xi rs m‖) * T :=
      Finset.sum_le_sum (fun m hm => actual_lower_Brun_P2 hWeil policy N cap D w z L hZ
        hlevel hd hs hU hV hH ht₁ ht₂ j b₁ b₂ label log₁ log₂ _ m)
    _ = (pairCost delta U V H * (Z^(2*j+1))^2 * T) *
        ∑ m ∈ shortSupport bs, ‖shortSequence bs Z y xi rs m‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (pairCost delta U V H * (Z^(2*j+1))^2 * T) *
        ((shortScale bs : ℝ) * (1+Real.log X)^Fintype.card ι) :=
      mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (mul_nonneg (pairCost_nonneg _ _ _ _) (sq_nonneg _)) hT)
    _ = _ := by dsimp [T]; ring

theorem sqrt_power_budget {D : ℝ} (hD : 1 ≤ D) :
    D * Real.sqrt D + 1 ≤ 2 * D^(3/2 : ℝ) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hid : D * Real.sqrt D = D^(3/2 : ℝ) := by
    calc
      _ = D^(1 : ℝ) * D^(1/2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = D^((1 : ℝ)+1/2) := (Real.rpow_add hD0 _ _).symm
      _ = _ := by norm_num
  have hp : 1 ≤ D^(3/2 : ℝ) := Real.one_le_rpow hD (by norm_num)
  rw [hid]
  linarith

/-- An explicit fixed 16th logarithmic loss, inherited from the proved
fourth-divisor moment. There is no growing-order divisor estimate. -/
theorem moment_log_budget {D : ℕ} {x : ℝ} (hD : 1 ≤ D)
    (hlog : 1 ≤ Real.log x) (hDx : (D : ℝ) ≤ x) :
    (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16) ≤
      (2 * 8^16 : ℝ) * (D : ℝ)^(3/2 : ℝ) * (Real.log x)^16 := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := zero_lt_one.trans_le hD1
  have hld := Real.log_le_log hD0 hDx
  have hln := Real.log_nonneg hD1
  rw [max_eq_right hD1]
  calc
    _ ≤ (2 * (D : ℝ)^(3/2 : ℝ)) * (8 * Real.log x)^16 := by
      apply mul_le_mul (sqrt_power_budget hD1) _ (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 16
    _ = _ := by rw [mul_pow]; ring

theorem short_log_budget {s : ℕ} (hs : s ≤ 6) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (1+Real.log x)^s ≤ 64 * (Real.log x)^6 := by
  calc
    _ ≤ (1+Real.log x)^6 := pow_le_pow_right₀ (by linarith) hs
    _ ≤ (2*Real.log x)^6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    _ = _ := by ring

/-- Original quantifier order: B,K,A,c,zeta,theta,epsilon precede the
threshold; target, policy, rank, HB row, real cutoffs, frequencies, and
every Brun order follow it. The last E4 power error is now an actual
expanded arithmetic sum, rather than an assumed modulus-moment monomial.
The active support and original complete-scale geometry remain explicit.
-/
theorem eventually_actual_lower_core_paid (hWeil : CompositeWeilInput)
    (B K A : ℕ) (hB : 1 ≤ B) (c : ℝ) (hc : 0 < c)
    (zeta theta epsilon : ℝ) (hepsilon : 0 < epsilon) (htheta : theta ≤ 1)
    (hmargin : 40*zeta+2*epsilon+3*theta/2 < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (policy : List ℕ → Bool) (N cap D : ℕ)
      (w z L Z U V t₁ t₂ : ℝ) (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3)
      (log₁ log₂ : Bool) (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role),
      Fintype.card ι ≤ 6 → 1 ≤ D → 1 ≤ Z →
      (∀ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q ≠ 0 → q ≤ D) →
      (D : ℝ) ≤ x^theta → (shortScale bs : ℝ) ≤ x^(40*zeta) → Z^(2*j+1) ≤ x^epsilon →
      (∀ a, 2 * (lower (bs a) : ℝ) ≤ x) →
      1 ≤ U → 1 ≤ V → U ≤ c*x → V ≤ c*x →
      |t₁| ≤ (Real.log x)^K → |t₂| ≤ (Real.log x)^K →
      ‖rowCore policy N cap w z L Z j b₁ b₂ ((Real.log x)^B)⁻¹ U V t₁ t₂
        label log₁ log₂ bs y xi rs‖ ≤ x/(Real.log x)^A := by
  filter_upwards [eventually_schedule B hB,
    eventually_twoLong_E4_monomial B K 23 A c hc zeta theta epsilon hepsilon hmargin,
    Real.tendsto_log_atTop.eventually_ge_atTop (128 * 8^16 : ℝ)]
    with x hsched hpay hlarge
  intro ι instF instD policy N cap D w z L Z U V t₁ t₂ j b₁ b₂ label log₁ log₂ bs y xi rs
    hrank hD hZ hlevel hDx hMx hyx hcap hU hV hUx hVx ht₁ ht₂
  have hx := hpay.1
  have hlog := hpay.2.1
  have hl0 : 0 ≤ Real.log x := le_trans zero_le_one hlog
  have hDX : (D : ℝ) ≤ x := hDx.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx htheta)
  have hp := rowCore_bound hWeil policy N cap D w z L hZ hx hlevel
    hsched.2.1 hsched.2.2 (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)
    (pow_nonneg hl0 K) ht₁ ht₂ j b₁ b₂ label log₁ log₂ bs y xi rs hcap
  have hM : 0 ≤ (shortScale bs : ℝ) := Nat.cast_nonneg _
  have hy : 0 ≤ Z^(2*j+1) := pow_nonneg (le_trans zero_le_one hZ) _
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
  have hpc := pairCost_nonneg ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)
  calc
    _ ≤ pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        ((2*8^16 : ℝ)*(D : ℝ)^(3/2 : ℝ)*(Real.log x)^16) *
        (64*(Real.log x)^6) := by
      apply hp.trans
      gcongr
      · exact moment_log_budget hD hlog hDX
      · exact short_log_budget hrank hlog
    _ = pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2 * (D : ℝ)^(3/2 : ℝ)) *
        ((128*8^16 : ℝ)*(Real.log x)^22) := by ring
    _ ≤ pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) *
        ((shortScale bs : ℝ) * (Z^(2*j+1))^2 * (D : ℝ)^(3/2 : ℝ)) *
        (Real.log x)^23 := by
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg (pairCost_nonneg _ _ _ _)
          (mul_nonneg (mul_nonneg hM (sq_nonneg _)) (Real.rpow_nonneg hD0 _)))
      calc
        _ ≤ Real.log x * (Real.log x)^22 :=
          mul_le_mul_of_nonneg_right hlarge (pow_nonneg hl0 _)
        _ = _ := by ring
    _ ≤ _ := hpay.2.2 (shortScale bs) (Z^(2*j+1)) D U V hM hy hD0
      hMx hyx hDx hU hV hUx hVx

end
end ImbalancedChen.Part3.TwoLongActualLowerCorePayment
