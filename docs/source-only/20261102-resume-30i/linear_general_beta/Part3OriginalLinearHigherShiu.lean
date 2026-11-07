import ImbalancedChen.Part3OriginalLinearDivisorMoment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual positive physical product image is covered by the existing
four original Shiu windows, now at every fixed divisor order C. All
native X,H,q,b gates are proved. The sole external input is the existing
PrimitiveShiuTauBoundary C alpha kappa, with its original Euler factor.
-/

namespace ImbalancedChen.Part3.OriginalLinearHigherShiu20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalLinearDivisorMoment20261102
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open MediumPrimitiveShiuWindow20261028 MediumPrimitiveShiuEuler20261028

theorem divisorProgressionMoment_le_four_windows
    {B : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hx : 6 ≤ atom.scale)
    (C ell : ℕ) (hell : 0 < ell) :
    divisorProgressionMoment C atom ell ≤
      ∑ j ∈ range 4, ∑ v ∈ dyadicWindow atom j,
        if Nat.ModEq ell v (naturalResidue atom.residue ell) then
          (v.divisors.card : ℝ) ^ C else 0 := by
  let F : ℕ → ℝ := fun v =>
    if Nat.ModEq ell v (naturalResidue atom.residue ell) then
      (v.divisors.card : ℝ) ^ C else 0
  have hF (v : ℕ) : 0 ≤ F v := by dsimp [F]; split_ifs <;> positivity
  have hpoint (v : ℕ) (hv : v ∈ psiMNImage atom) :
      F v ≤ ∑ j ∈ range 4, if v ∈ dyadicWindow atom j then F v else 0 := by
    obtain ⟨j, hj, hvj⟩ := psiMNImage_has_window hA hx hv
    have hs := single_le_sum
      (fun k (_hk : k ∈ range 4) => show 0 ≤
        (if v ∈ dyadicWindow atom k then F v else 0) by split_ifs <;> positivity) hj
    simpa only [if_pos hvj] using hs
  calc
    _ = ∑ v ∈ psiMNImage atom, F v := by
      unfold divisorProgressionMoment
      simp only [movingResidue_nat_iff atom.residue ell _ hell, F]
    _ ≤ ∑ v ∈ psiMNImage atom, ∑ j ∈ range 4,
        if v ∈ dyadicWindow atom j then F v else 0 := sum_le_sum hpoint
    _ = ∑ j ∈ range 4, ∑ v ∈ (psiMNImage atom).filter
        (fun v => v ∈ dyadicWindow atom j), F v := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      exact sum_le_sum_of_subset_of_nonneg
        (fun v hv => (mem_filter.mp hv).2) (fun v _ _ => hF v)

def momentWindowBudget {C : ℕ} {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary C α κ) (atom : MediumAtom) (ell j : ℕ) : ℝ :=
  hShiu.A * (dyadicStart atom j : ℝ) / (ell.totient : ℝ) /
    Real.log (dyadicStart atom j) *
      Real.exp ((2 : ℝ) ^ C *
        ∑ p ∈ (range (dyadicStart atom j + 1)).filter
          (fun p => p.Prime ∧ ¬p ∣ ell), (1 : ℝ) / p)

theorem divisorProgressionMoment_le_originalShiu
    {B C : ℕ} {σ κ c0 α κS : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hx : 6 ≤ atom.scale)
    (hShiu : PrimitiveShiuTauBoundary C α κS)
    (ell : ℕ) (hell : 0 < ell) (hcop : ell.Coprime atom.residue.natAbs)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale atom : ℝ))
    (hmod : (ell : ℝ) < (firstWindowScale atom : ℝ) ^ (1 - α)) :
    divisorProgressionMoment C atom ell ≤
      ∑ j ∈ range 4, momentWindowBudget hShiu atom ell j := by
  have hKpos := (firstWindowScale_bounds atom hx).2.2
  have hKone : (1 : ℝ) ≤ firstWindowScale atom := by exact_mod_cast hKpos
  have hcopb := naturalResidue_coprime atom.residue ell hell hcop
  refine (divisorProgressionMoment_le_four_windows hA hx C ell hell).trans ?_
  apply sum_le_sum
  intro j hj
  have hpow1 : 1 ≤ (2 : ℕ) ^ j := by
    have hpos : 0 < (2 : ℕ) ^ j := by positivity
    omega
  have hstart : firstWindowScale atom ≤ dyadicStart atom j := by
    dsimp [dyadicStart]
    simpa only [one_mul] using Nat.mul_le_mul_right (firstWindowScale atom) hpow1
  have hstartR : (firstWindowScale atom : ℝ) ≤ dyadicStart atom j := by exact_mod_cast hstart
  have hXone : (1 : ℝ) ≤ dyadicStart atom j := hKone.trans hstartR
  have hXpos : 0 < dyadicStart atom j := hKpos.trans_le hstart
  have hκ : (dyadicStart atom j : ℝ) ^ κS ≤ (dyadicStart atom j : ℝ) := by
    calc
      _ ≤ (dyadicStart atom j : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hXone (by linarith [hShiu.kappa_half])
      _ = _ := by simp
  have hα : (ell : ℝ) < (dyadicStart atom j : ℝ) ^ (1 - α) :=
    hmod.trans_le (Real.rpow_le_rpow (by positivity) hstartR
      (by linarith [hShiu.alpha_half]))
  exact hShiu.bound (dyadicStart atom j) (dyadicStart atom j) ell
    (naturalResidue atom.residue ell) (hthreshold.trans hstartR) hXpos hell hκ
    (Nat.le_refl _) hα hcopb

theorem reciprocal_totient_le_tau_over_self (ell : ℕ) (hell : 0 < ell) :
    (1 : ℝ) / ell.totient ≤ (ell.divisors.card : ℝ) / ell := by
  have hphi : (0 : ℝ) < ell.totient := by exact_mod_cast Nat.totient_pos.mpr hell
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  apply (div_le_div_iff₀ hphi hellR).mpr
  simpa only [one_mul] using (div_le_iff₀ hphi).mp
    (totient_ratio_le_divisor_count ell hell)

/-- A harmless extra logarithm avoids subtracting one from the Euler
exponent: the denominator is bounded by 1/log 2 on every actual window. -/
theorem momentWindowBudget_le_log
    {C : ℕ} {α κ : ℝ} (hShiu : PrimitiveShiuTauBoundary C α κ)
    (atom : MediumAtom) (hx : 6 ≤ atom.scale) (ell : ℕ) (hell : 0 < ell)
    (j : ℕ) (hj : j ∈ range 4) :
    momentWindowBudget hShiu atom ell j ≤
      (hShiu.A * uniformEulerConstant C / Real.log 2 *
        Real.log (8 * atom.scale) ^ (2 ^ C : ℕ) *
        ((ell.divisors.card : ℝ) / ell)) * (dyadicStart atom j : ℝ) := by
  have hb := dyadicStart_bounds atom hx j hj
  have hX2 : (2 : ℝ) ≤ dyadicStart atom j := by exact_mod_cast hb.1
  have hXpos : (0 : ℝ) < dyadicStart atom j := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogLower : Real.log 2 ≤ Real.log (dyadicStart atom j) :=
    Real.log_le_log (by norm_num) hX2
  have hlogX : 0 < Real.log (dyadicStart atom j) := hlog2.trans_le hlogLower
  have hXupper : (dyadicStart atom j : ℝ) ≤ 8 * atom.scale := by
    have hcast : (dyadicStart atom j : ℝ) ≤ 8 * (firstWindowScale atom : ℝ) := by
      exact_mod_cast hb.2
    linarith [(firstWindowScale_bounds atom hx).2.1]
  have hlogUpper := Real.log_le_log hXpos hXupper
  have hcast : ((2 ^ C : ℕ) : ℝ) = (2 : ℝ) ^ C := by norm_cast
  have hEuler : Real.exp ((2 : ℝ) ^ C *
      ∑ p ∈ (range (dyadicStart atom j + 1)).filter
        (fun p => p.Prime ∧ ¬p ∣ ell), (1 : ℝ) / p) ≤
      uniformEulerConstant C * Real.log (dyadicStart atom j) ^ (2 ^ C : ℕ) := by
    simpa only [← hcast, Real.rpow_natCast] using
      uniformEulerConstant_bound C (dyadicStart atom j) ell hb.1
  have hEuler' : Real.exp ((2 : ℝ) ^ C *
      ∑ p ∈ (range (dyadicStart atom j + 1)).filter
        (fun p => p.Prime ∧ ¬p ∣ ell), (1 : ℝ) / p) ≤
      uniformEulerConstant C * Real.log (8 * atom.scale) ^ (2 ^ C : ℕ) := by
    apply hEuler.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlogX.le hlogUpper _) (uniformEulerConstant_pos C).le
  have hphi : (0 : ℝ) < ell.totient := by exact_mod_cast Nat.totient_pos.mpr hell
  have hrecLog : (1 : ℝ) / Real.log (dyadicStart atom j) ≤ 1 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2 hlogLower
  have hApos := hShiu.A_pos
  have hEpos := uniformEulerConstant_pos C
  have hlog8 : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
  unfold momentWindowBudget
  calc
    _ = (hShiu.A * (dyadicStart atom j : ℝ)) * (1 / (ell.totient : ℝ)) *
        (1 / Real.log (dyadicStart atom j)) *
          Real.exp ((2 : ℝ) ^ C *
            ∑ p ∈ (range (dyadicStart atom j + 1)).filter
              (fun p => p.Prime ∧ ¬p ∣ ell), (1 : ℝ) / p) := by ring
    _ ≤ (hShiu.A * (dyadicStart atom j : ℝ)) *
        ((ell.divisors.card : ℝ) / ell) * (1 / Real.log 2) *
          (uniformEulerConstant C * Real.log (8 * atom.scale) ^ (2 ^ C : ℕ)) := by
      apply mul_le_mul _ hEuler' (Real.exp_nonneg _) (by positivity)
      apply mul_le_mul _ hrecLog (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (reciprocal_totient_le_tau_over_self ell hell)
        (by positivity)
    _ = _ := by ring

def momentConstant {C : ℕ} {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary C α κ) : ℝ :=
  (15 / 2 : ℝ) * hShiu.A * uniformEulerConstant C / Real.log 2

theorem momentConstant_pos {C : ℕ} {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary C α κ) : 0 < momentConstant hShiu := by
  have := hShiu.A_pos
  have := uniformEulerConstant_pos C
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold momentConstant
  positivity

def momentLogBudget {C : ℕ} {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary C α κ) (atom : MediumAtom) (ell : ℕ) : ℝ :=
  (momentConstant hShiu * atom.scale * Real.log (8 * atom.scale) ^ (2 ^ C : ℕ)) *
    ((ell.divisors.card : ℝ) / ell)

theorem sum_momentWindowBudget_le
    {C : ℕ} {α κ : ℝ} (hShiu : PrimitiveShiuTauBoundary C α κ)
    (atom : MediumAtom) (hx : 6 ≤ atom.scale) (ell : ℕ) (hell : 0 < ell) :
    (∑ j ∈ range 4, momentWindowBudget hShiu atom ell j) ≤
      momentLogBudget hShiu atom ell := by
  have hK := firstWindowScale_bounds atom hx
  have hsum : (∑ j ∈ range 4, (dyadicStart atom j : ℝ)) =
      15 * (firstWindowScale atom : ℝ) := by
    norm_num [sum_range_succ, dyadicStart, Nat.cast_mul] <;> ring
  have hApos := hShiu.A_pos
  have hEpos := uniformEulerConstant_pos C
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog8 : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ∑ j ∈ range 4,
        (hShiu.A * uniformEulerConstant C / Real.log 2 *
          Real.log (8 * atom.scale) ^ (2 ^ C : ℕ) *
          ((ell.divisors.card : ℝ) / ell)) * (dyadicStart atom j : ℝ) := by
      exact sum_le_sum (fun j hj => momentWindowBudget_le_log hShiu atom hx ell hell j hj)
    _ = (hShiu.A * uniformEulerConstant C / Real.log 2 *
        Real.log (8 * atom.scale) ^ (2 ^ C : ℕ) *
        ((ell.divisors.card : ℝ) / ell)) * (15 * (firstWindowScale atom : ℝ)) := by
      rw [← mul_sum, hsum]
    _ ≤ (hShiu.A * uniformEulerConstant C / Real.log 2 *
        Real.log (8 * atom.scale) ^ (2 ^ C : ℕ) *
        ((ell.divisors.card : ℝ) / ell)) * (15 * (atom.scale / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK.2.1 (by norm_num))
        (by positivity)
    _ = _ := by unfold momentLogBudget momentConstant; ring

theorem divisorProgressionMoment_le_logBudget
    {B C : ℕ} {σ κ c0 α κS : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B σ κ c0 atom) (hx : 6 ≤ atom.scale)
    (hShiu : PrimitiveShiuTauBoundary C α κS)
    (ell : ℕ) (hell : 0 < ell) (hcop : ell.Coprime atom.residue.natAbs)
    (hthreshold : hShiu.X0 ≤ (firstWindowScale atom : ℝ))
    (hmod : (ell : ℝ) < (firstWindowScale atom : ℝ) ^ (1 - α)) :
    divisorProgressionMoment C atom ell ≤ momentLogBudget hShiu atom ell :=
  (divisorProgressionMoment_le_originalShiu hA hx hShiu ell hell hcop hthreshold hmod).trans
    (sum_momentWindowBudget_le hShiu atom hx ell hell)

end
end ImbalancedChen.Part3.OriginalLinearHigherShiu20261102
