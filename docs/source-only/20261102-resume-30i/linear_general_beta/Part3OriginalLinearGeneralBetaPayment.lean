import ImbalancedChen.Part3OriginalLinearHigherShiu
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine physical LINEAR smooth-factor deletion is paid for the
original arbitrary fixed divisor order B. Beta is never truncated or
replaced. The count uses primitive Shiu at order B+1; its q=1 instance
pays the original mean. Gamma multiplicity tau^3 and the reciprocal
totient loss tau give collapsed order 4 for every B. Only the fixed
logarithmic exponent grows with B.
-/

namespace ImbalancedChen.Part3.OriginalLinearGeneralBetaPayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumActualPostSquareDeletion20261028
open MediumReceiverCutoffArithmetic20261028 ActualRoughContourParameters20261026b
open OriginalLinearDiscardModulusBinding20261028 OriginalLinearDiscardSmoothSupport20261102
open OriginalLinearDivisorMoment20261102 OriginalLinearHigherShiu20261102
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open MediumPrimitiveShiuWindow20261028

def generalLinearLogFactor {B : ℕ}
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (atom : MediumAtom) : ℝ :=
  2 * momentConstant hShiu * Real.log (8 * atom.scale) ^ (2 ^ (B + 1) : ℕ)

theorem generalLinearLogFactor_nonneg {B : ℕ}
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (atom : MediumAtom) (hx : 1 ≤ atom.scale) : 0 ≤ generalLinearLogFactor hShiu atom := by
  have := (momentConstant_pos hShiu).le
  have : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
  unfold generalLinearLogFactor
  positivity

/-- Native Shiu gates are discharged from the actual original physical
modulus range. The same boundary at q=1 controls the mean mass. -/
theorem original_general_beta_deletedModulus_primitive_return
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ atom.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < atom.scale)
    (hthreshold : 3 * hShiu.X0 ≤ atom.scale)
    (ell : ℕ) (hell : 0 < ell) (hcop : ell.Coprime atom.residue.natAbs)
    (hmod : ell ≤ Nat.floor (atom.scale ^ ((4 : ℝ) / 5))) :
    ‖deletedModulusDiscrepancy atom ell‖ ≤
      (generalLinearLogFactor hShiu atom * atom.scale) *
        ((ell.divisors.card : ℝ) / ell) := by
  have hX0 : hShiu.X0 ≤ (firstWindowScale atom : ℝ) := by
    have hK := (firstWindowScale_bounds atom hx).1
    linarith
  have hmodR : (ell : ℝ) ≤ atom.scale ^ ((4 : ℝ) / 5) :=
    (show (ell : ℝ) ≤ (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)) : ℝ) by exact_mod_cast hmod).trans
      (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ atom.scale) _))
  have hmargin := physical_modulus_shiu_margin atom hx hlarge ell hmodR
  have hmargin1 : (1 : ℝ) < (firstWindowScale atom : ℝ) ^ (1 - (1 / 10 : ℝ)) :=
    (show (1 : ℝ) ≤ ell by exact_mod_cast hell).trans_lt hmargin
  have hp := divisorProgressionMoment_le_logBudget hA hx hShiu ell hell hcop hX0 hmargin
  have hp1 := divisorProgressionMoment_le_logBudget hA hx hShiu 1 (by norm_num)
    (by simp) hX0 hmargin1
  let T : ℝ := momentConstant hShiu * atom.scale *
    Real.log (8 * atom.scale) ^ (2 ^ (B + 1) : ℕ)
  have hT : 0 ≤ T := by
    have := (momentConstant_pos hShiu).le
    have : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
    dsimp [T]
    positivity
  have hp1' : divisorProgressionMoment (B + 1) atom 1 ≤ T := by
    simpa only [momentLogBudget, Nat.divisors_one, card_singleton, Nat.cast_one,
      div_one, mul_one] using hp1
  have hm : divisorProgressionMoment (B + 1) atom 1 / (ell.totient : ℝ) ≤
      T * ((ell.divisors.card : ℝ) / ell) := by
    calc
      _ ≤ T / (ell.totient : ℝ) := div_le_div_of_nonneg_right hp1' (Nat.cast_nonneg _)
      _ = T * (1 / (ell.totient : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_totient_le_tau_over_self ell hell) hT
  calc
    _ ≤ divisorProgressionMoment (B + 1) atom ell +
        divisorProgressionMoment (B + 1) atom 1 / (ell.totient : ℝ) :=
      original_deletedModulusDiscrepancy_le_divisor_moments atom hA ell
    _ ≤ momentLogBudget hShiu atom ell + T * ((ell.divisors.card : ℝ) / ell) :=
      add_le_add hp hm
    _ = _ := by unfold momentLogBudget generalLinearLogFactor T; ring

/-- The true collapsed order is 3+1=4. Higher beta moments change the
Euler/log exponent, not the modulus multiplicity in primitive Shiu. -/
theorem original_general_beta_linear_discard_le_collapsed_arithmetic
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ atom.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < atom.scale)
    (hthreshold : 3 * hShiu.X0 ≤ atom.scale)
    (hphysical : (10 : ℝ) ^ (10 : ℕ) ≤ atom.scale) (z : ℝ) (hz : 0 ≤ z) :
    ‖discardedSource atom (strictReceiverCutoff z) (roughY atom.scale)‖ ≤
      (generalLinearLogFactor hShiu atom * atom.scale) *
        collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5))) atom.scale z := by
  let γ := discardedFactorGamma atom (strictReceiverCutoff z) (roughY atom.scale)
  let S := atom.physicalFactorModuli.filter (fun ell => γ ell ≠ 0)
  let T := (Icc 1 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))).filter
    (fun ell => roughY atom.scale < (zSmoothPart z ell : ℝ))
  have hsub : S ⊆ T := by
    intro ell hell
    exact actual_linear_discard_modulus_mem_collapsed_filter atom hA hσ hc0 hphysical z hz
      (mem_filter.mp hell).1 (mem_filter.mp hell).2
  have hscale : 0 ≤ generalLinearLogFactor hShiu atom * atom.scale :=
    mul_nonneg (generalLinearLogFactor_nonneg hShiu atom (by linarith)) (by linarith)
  rw [discardedSource_eq_actual_modulus_fibres]
  calc
    _ ≤ ∑ ell ∈ atom.physicalFactorModuli, ‖γ ell‖ * ‖deletedModulusDiscrepancy atom ell‖ := by
      simpa only [norm_mul] using norm_sum_le
        (s := atom.physicalFactorModuli) (f := fun ell => γ ell * deletedModulusDiscrepancy atom ell)
    _ = ∑ ell ∈ S, ‖γ ell‖ * ‖deletedModulusDiscrepancy atom ell‖ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro ell hell
      by_cases hγ : γ ell = 0 <;> simp [hγ]
    _ ≤ ∑ ell ∈ S, (generalLinearLogFactor hShiu atom * atom.scale) *
        ((ell.divisors.card : ℝ) ^ 4 / (ell : ℝ)) := by
      apply sum_le_sum
      intro ell hell
      have hT := mem_Icc.mp (mem_filter.mp (hsub hell)).1
      have hcop := discardedFactorGamma_support_primitive atom hA _ _ ell (mem_filter.mp hell).2
      have hg := discardedFactorGamma_norm_le_tau_cube atom hA _ _ ell hT.1
      have hd := original_general_beta_deletedModulus_primitive_return atom hA hShiu hx hlarge
        hthreshold ell hT.1 hcop hT.2
      calc
        _ ≤ (ell.divisors.card : ℝ) ^ 3 *
            ((generalLinearLogFactor hShiu atom * atom.scale) * ((ell.divisors.card : ℝ) / ell)) :=
          mul_le_mul hg hd (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (generalLinearLogFactor hShiu atom * atom.scale) *
        ∑ ell ∈ S, (ell.divisors.card : ℝ) ^ 4 / (ell : ℝ) := by rw [mul_sum]
    _ ≤ (generalLinearLogFactor hShiu atom * atom.scale) *
        ∑ ell ∈ T, (ell.divisors.card : ℝ) ^ 4 / (ell : ℝ) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hscale
    _ = _ := rfl

def generalLinearConstant {B : ℕ}
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ)) : ℝ :=
  2 * momentConstant hShiu * (8 : ℝ) ^ (2 ^ (B + 1) : ℕ)

/-- B and A precede one common threshold. Every original atom, moving
signed residue, modulus, and coefficient sequence is quantified AFTER it.
There is no beta truncation, kappa cap, or assumed final discard bound. -/
theorem original_general_beta_linear_discard_log_payment
    (B : ℕ)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 < X ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom), MediumAdmissible B σ κ c0 atom →
        0 ≤ σ → 0 < c0 → X ≤ atom.scale →
          ‖discardedSource atom (strictReceiverCutoff (roughZ atom.scale)) (roughY atom.scale)‖ ≤
            C * atom.scale / Real.log atom.scale ^ A := by
  let E : ℕ := 2 ^ (B + 1)
  obtain ⟨Xp, hXp, hpay⟩ := exists_collapsed_smooth_tail_arbitrary_log 4 (A + (E : ℝ))
    (add_nonneg hA (Nat.cast_nonneg _))
  let C := generalLinearConstant hShiu
  have hC : 0 < C := by
    have := momentConstant_pos hShiu
    dsimp [C, generalLinearConstant]
    positivity
  let X := max Xp (max (3 * hShiu.X0)
    (max ((3 : ℝ) ^ (9 : ℕ) + 1) (max ((10 : ℝ) ^ (10 : ℕ)) (Real.exp 1 + 1))))
  have hXp1 : 1 < Xp := (Real.one_lt_exp.mpr (Real.exp_pos 1)).trans hXp
  refine ⟨C, hC, X, hXp1.trans_le (le_max_left _ _), ?_⟩
  intro σ κ c0 atom hadm hσ hc0 hx
  have hxp : Xp ≤ atom.scale := (le_max_left _ _).trans hx
  have hrest := (le_max_right _ _).trans hx
  have hthreshold : 3 * hShiu.X0 ≤ atom.scale := (le_max_left _ _).trans hrest
  have hlarge0 : (3 : ℝ) ^ (9 : ℕ) + 1 ≤ atom.scale :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hphysical : (10 : ℝ) ^ (10 : ℕ) ≤ atom.scale :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hexp : Real.exp 1 + 1 ≤ atom.scale :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hx6 : 6 ≤ atom.scale := by norm_num at hlarge0; linarith
  have hxpos : 0 < atom.scale := by linarith
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ atom.scale by linarith)
  have hlogpos : 0 < Real.log atom.scale := by linarith
  have hlog8 : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
  have h8 : Real.log (8 * atom.scale) ≤ 8 * Real.log atom.scale := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hxpos.ne']
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hfactor : generalLinearLogFactor hShiu atom ≤ C * Real.log atom.scale ^ E := by
    have hmc := (momentConstant_pos hShiu).le
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog8 h8 E)
      (show 0 ≤ 2 * momentConstant hShiu by positivity)
    simpa only [generalLinearLogFactor, C, generalLinearConstant, E, mul_pow, mul_assoc] using hm
  have htail := hpay atom.scale hxp
  have htail0 : 0 ≤ collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))
      atom.scale (roughZ atom.scale) := by
    unfold collapsedSmoothTail
    exact sum_nonneg (fun _ _ => by positivity)
  have hpow : Real.log atom.scale ^ E * Real.log atom.scale ^ (-(A + (E : ℝ))) =
      1 / Real.log atom.scale ^ A := by
    calc
      _ = Real.log atom.scale ^ (E : ℝ) *
          Real.log atom.scale ^ (-(A + (E : ℝ))) := by rw [Real.rpow_natCast]
      _ = Real.log atom.scale ^ (-A) := by
        rw [← Real.rpow_add hlogpos]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_neg hlogpos.le, one_div]
  calc
    _ ≤ (generalLinearLogFactor hShiu atom * atom.scale) *
        collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))
          atom.scale (roughZ atom.scale) :=
      original_general_beta_linear_discard_le_collapsed_arithmetic atom hadm hσ hc0 hShiu hx6
        (by linarith) hthreshold hphysical _ (Real.rpow_nonneg hxpos.le _)
    _ ≤ (C * Real.log atom.scale ^ E * atom.scale) *
        Real.log atom.scale ^ (-(A + (E : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfactor hxpos.le) htail htail0 (by positivity)
    _ = _ := by
      calc
        _ = (C * atom.scale) *
            (Real.log atom.scale ^ E * Real.log atom.scale ^ (-(A + (E : ℝ)))) := by ring
        _ = _ := by rw [hpow]; ring

end
end ImbalancedChen.Part3.OriginalLinearGeneralBetaPayment20261102
