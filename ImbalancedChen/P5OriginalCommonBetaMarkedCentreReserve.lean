import ImbalancedChen.P5OriginalCommonBetaMarkedSmoothFibre

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The literal ORIGINAL-source-filtered common-beta geometric correction has
fixed mesh amplitude and strict153/256 support. Its entire centre error
is negligible in singularNormalization. No thinness argument, AP saving,
or identification with a future independent outer-box coefficient occurs.
-/
namespace ImbalancedChen.P5Z.OriginalCommonBetaMarkedCentreReserve
noncomputable section
open Filter Topology Classical
open scoped BigOperators
open U1011OriginalMaskSmoothBoxRealization (Row)
open OriginalJointPresievedCompiler OriginalCommonBetaActualParameters
open OriginalCommonBetaMarkedSmoothFibre

def errorSupport (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  (jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E).filter
    (fun q => errorSigma inner S m N eta nu epsilon fine δ E q ≠ 0)

def markedCentre (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E,
    markedSmoothSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q

def errorCentre (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ jointSupport m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) E,
    errorSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q

/-- The actual difference of centre corrections, with precisely the
same original common-beta source, coefficient carrier and physical q. -/
theorem errorCentre_eq_difference (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) :
    errorCentre inner S m N eta nu epsilon fine δ E =
      markedCentre inner S m N eta nu epsilon fine δ E -
        jointCentre m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) E := by
  unfold errorCentre markedCentre jointCentre
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold errorSigma
  ring

theorem errorCentre_eq_active (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (nu epsilon : ℝ) (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) :
    errorCentre inner S m N eta nu epsilon fine δ E =
      ∑ q ∈ errorSupport inner S m N eta nu epsilon fine δ E,
        errorSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q := by
  unfold errorCentre errorSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : errorSigma inner S m N eta nu epsilon fine δ E q = 0 <;> simp [hz]

/-- Complete actual marked smooth-centre error: the mesh multiplicity is
fixed, while the physical support exponent remains strictly below one. -/
theorem abs_errorCentre_le_power_log {m N : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget m eta nu) (inner : Bool) (S : Finset Row)
    (fine : ℕ) (δ : ℝ) (E : ℕ × ℕ → Prop) :
    |errorCentre inner S m N eta nu epsilon fine δ E| ≤
      (geometricCost S m fine + 1) * (N : ℝ) ^ (153 / 256 : ℝ) *
        (Real.log (N : ℝ) / Real.log 2) := by
  let A := errorSupport inner S m N eta nu epsilon fine δ E
  let C := geometricCost S m fine + 1
  have hC : 0 ≤ C := by dsimp [C]; linarith [geometricCost_nonneg S m fine]
  have hsub : A ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ))) := by
    intro q hq
    have hactive := (Finset.mem_filter.mp hq).2
    have hs := errorSigma_arithmetic_support hN heta hnu he heBudget inner S fine δ E hactive
    exact Finset.mem_Icc.mpr ⟨hs.1, Nat.le_floor hs.2.2.2.le⟩
  have hcard : (A.card : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
    calc
      _ ≤ ((Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) : ℝ) := by simp
      _ ≤ (N : ℝ) ^ (153 / 256 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hNpos : 0 < N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_pos (by exact_mod_cast hN)).le (Real.log_pos (by norm_num)).le
  have hpoint (q : ℕ) (hq : q ∈ A) :
      |errorSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q| ≤
        C * (Real.log (N : ℝ) / Real.log 2) := by
    have ha := errorSigma_abs_le hN heta hnu he heBudget inner S fine δ E q
    have hc := (chenCentrePrimeAPCount_le_divisorCount N N q).trans (chenPrimeDivisorCount_le_log N hNpos)
    rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N q)]
    exact mul_le_mul ha hc (chenCentrePrimeAPCount_nonneg N N q) hC
  calc
    _ = |∑ q ∈ A, errorSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q| := by
      rw [errorCentre_eq_active]
    _ ≤ ∑ q ∈ A, |errorSigma inner S m N eta nu epsilon fine δ E q * chenCentrePrimeAPCount N N q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ A, C * (Real.log (N : ℝ) / Real.log 2) := Finset.sum_le_sum hpoint
    _ = (A.card : ℝ) * (C * (Real.log (N : ℝ) / Real.log 2)) := by simp
    _ ≤ (N : ℝ) ^ (153 / 256 : ℝ) * (C * (Real.log (N : ℝ) / Real.log 2)) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hC hlog)
    _ = _ := by dsimp [C]; ring

/-- Meshes and the ORIGINAL finite adopted row set precede the common
threshold. This pays every literal width and both sides, uniformly in E,
physical precision and the already-fixed admissible common beta pair. -/
theorem eventually_marked_smooth_centre_paid (S : Finset Row) (m fine : ℕ)
    (reserve : ℝ) (hreserve : 0 < reserve) :
    ∀ᶠ N : ℕ in atTop, ∀ inner : Bool, ∀ δ : ℝ, ∀ eta : ℚ, 0 < eta →
      ∀ nu epsilon : ℝ, 0 < nu → 0 < epsilon → epsilon < epsilonBudget m eta nu →
        ∀ E : ℕ × ℕ → Prop,
          |markedCentre inner S m N eta nu epsilon fine δ E -
            jointCentre m N eta ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * epsilon)) E| ≤
              reserve * singularNormalization N := by
  have hp := eventually_powerLog_le_singularNormalization
    ((geometricCost S m fine + 1) / Real.log 2) (153 / 256 : ℝ) 1 (by norm_num) reserve hreserve
  filter_upwards [hp, eventually_ge_atTop (2 : ℕ)] with N hpower hN
  intro inner δ eta heta nu epsilon hnu he heBudget E
  rw [← errorCentre_eq_difference]
  exact (abs_errorCentre_le_power_log (by omega) heta hnu he heBudget inner S fine δ E).trans (by
    simpa only [pow_one, mul_div_assoc, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpower)

end
end ImbalancedChen.P5Z.OriginalCommonBetaMarkedCentreReserve
