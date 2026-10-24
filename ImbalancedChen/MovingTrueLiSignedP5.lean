import ImbalancedChen.CurrentChenUpsilon9TrueLiMass
import ImbalancedChen.ActualLowerNormalizedRhoError
import ImbalancedChen.PowerErrorBudget

/-! Source-only, uncompiled. Uniform moving true-li transport for the same
signed physical density. The real-variable li limit is reused unchanged.
No sharp L1 estimate or signed distribution theorem is assumed. -/

namespace ImbalancedChen.P5S1MovingTrueLi

noncomputable section

open Filter Topology
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The finite absolute coefficient mass is retained literally. -/
theorem abs_physicalDensity_le (S : Finset ℕ) (rho : ℕ → ℝ) :
    |physicalDensitySum S rho| ≤ physicalDensitySum S (fun q => |rho q|) := by
  unfold physicalDensitySum
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro q _
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]

/-- One threshold precedes every real moving endpoint above N^a. -/
theorem eventually_uniform_relative_error (a delta : ℝ) (ha : 0 < a)
    (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N : ℝ) ^ a ≤ x →
      0 ≤ trueLogarithmicIntegral x - x / Real.log x ∧
        trueLogarithmicIntegral x - x / Real.log x ≤ delta * (x / Real.log x) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((eventually_currentChenUpsilon9_trueLi_real_le delta hdelta).and
      (eventually_ge_atTop (4 : ℝ)))
  have hlarge : ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop X)
  filter_upwards [hlarge] with N hN
  intro x hx
  obtain ⟨hupper, hfour⟩ := hX x (hN.trans hx)
  have hlower := div_log_le_liuLogarithmicIntegral (by linarith : (2 : ℝ) ≤ x)
  constructor
  · linarith only [hlower]
  · nlinarith only [hupper]

/-- Signed main-term replacement is controlled by the genuine finite
absolute rho/totient sum, with no sign assumption on the coefficient. -/
theorem eventually_uniform_finite_main_error (a delta : ℝ) (ha : 0 < a)
    (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N : ℝ) ^ a ≤ x →
      ∀ S : Finset ℕ, ∀ rho : ℕ → ℝ,
        |trueLogarithmicIntegral x * physicalDensitySum S rho -
          (x / Real.log x) * physicalDensitySum S rho| ≤
          delta * (x / Real.log x) * physicalDensitySum S (fun q => |rho q|) := by
  filter_upwards [eventually_uniform_relative_error a delta ha hdelta]
    with N hN
  intro x hx S rho
  obtain ⟨hlo, hhi⟩ := hN x hx
  have hright : 0 ≤ delta * (x / Real.log x) := hlo.trans hhi
  calc
    _ = |trueLogarithmicIntegral x - x / Real.log x| * |physicalDensitySum S rho| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (delta * (x / Real.log x)) * |physicalDensitySum S rho| := by
      rw [abs_of_nonneg hlo]
      exact mul_le_mul_of_nonneg_right hhi (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_physicalDensity_le S rho) hright

/-- Between N^a and N the logarithmic scale has no small denominator. -/
theorem moving_div_log_le {N : ℕ} {a x : ℝ} (hN : 2 ≤ N) (ha : 0 < a)
    (hax : (N : ℝ) ^ a ≤ x) (hxN : x ≤ (N : ℝ)) :
    x / Real.log x ≤ (N : ℝ) / (a * Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hxp : 0 < x := (Real.rpow_pos_of_pos hNp a).trans_le hax
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hlogs := Real.log_le_log (Real.rpow_pos_of_pos hNp a) hax
  rw [Real.log_rpow hNp] at hlogs
  have hlogx : 0 < Real.log x := (mul_pos ha hlogN).trans_le hlogs
  exact (div_le_div_of_nonneg_right hxN hlogx.le).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos ha hlogN) hlogs)

/-- Generic H-scale transport uses only an absolute bound on the signed
density. The actual causal producer below discharges that bound. -/
theorem eventually_uniform_main_error_H (a M eta : ℝ) (ha : 0 < a)
    (hM : 0 < M) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ x D : ℝ,
      (N : ℝ) ^ a ≤ x → x ≤ (N : ℝ) →
      |D| ≤ M * singularSeries N / Real.log (N : ℝ) →
      |trueLogarithmicIntegral x * D - (x / Real.log x) * D| ≤
        eta * singularNormalization N := by
  let delta : ℝ := eta * a / M
  have hdelta : 0 < delta := div_pos (mul_pos heta ha) hM
  filter_upwards [eventually_uniform_relative_error a delta ha hdelta,
    eventually_ge_atTop (2 : ℕ)] with N hli hN
  intro x D hax hxN hD
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hxlog := moving_div_log_le hN ha hax hxN
  obtain ⟨hli0, hli1⟩ := hli x hax
  have hbase : 0 ≤ (N : ℝ) / (a * Real.log (N : ℝ)) := by positivity
  calc
    _ = |trueLogarithmicIntegral x - x / Real.log x| * |D| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (delta * (x / Real.log x)) * |D| := by
      rw [abs_of_nonneg hli0]
      exact mul_le_mul_of_nonneg_right hli1 (abs_nonneg _)
    _ ≤ (delta * ((N : ℝ) / (a * Real.log (N : ℝ)))) * |D| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxlog hdelta.le) (abs_nonneg _)
    _ ≤ (delta * ((N : ℝ) / (a * Real.log (N : ℝ)))) *
        (M * singularSeries N / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hD (mul_nonneg hdelta.le hbase)
    _ = eta * singularNormalization N := by
      dsimp [delta]
      unfold singularNormalization
      field_simp [ha.ne', hM.ne', hlogN.ne']
      <;> ring

/-- The strict S1 endpoint remains in the complete moving interval.
The ceiling and its natural subtraction are treated explicitly. -/
theorem eventually_strict_endpoint_window (a tau : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (htau0 : 0 ≤ tau) (htau1 : tau < 1) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ a ≤ (⌈(1 - tau) * (N : ℝ)⌉₊ - 1 : ℕ) ∧
        ((⌈(1 - tau) * (N : ℝ)⌉₊ - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
  have hsmall₁ : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (1 - a) ≤ (1 - tau) / 2 := by
    have h := tendsto_nat_log_pow_div_rpow 0 (sub_pos.mpr ha1)
    have hs : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ (1 - a) < (1 - tau) / 2 := by
      simpa only [pow_zero] using h.eventually
        (eventually_lt_nhds (half_pos (sub_pos.mpr htau1)))
    exact hs.mono (fun _ h => h.le)
  have hsmall₂ : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ≤ (1 - tau) / 2 := by
    have h := tendsto_nat_log_pow_div_rpow 0 (by norm_num : (0 : ℝ) < 1)
    have hs : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) < (1 - tau) / 2 := by
      simpa only [pow_zero, Real.rpow_one] using h.eventually
        (eventually_lt_nhds (half_pos (sub_pos.mpr htau1)))
    exact hs.mono (fun _ h => h.le)
  filter_upwards [hsmall₁, hsmall₂, eventually_ge_atTop (2 : ℕ)]
    with N hsmall₁N hsmall₂N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hratio : (N : ℝ) ^ a / (N : ℝ) = 1 / (N : ℝ) ^ (1 - a) := by
    rw [Real.rpow_sub hNp, Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hNp a).ne', hNp.ne']
  rw [← hratio] at hsmall₁N
  have hsum : (N : ℝ) ^ a + 1 ≤ (1 - tau) * (N : ℝ) := by
    have h₁ := (div_le_iff₀ hNp).mp hsmall₁N
    have h₂ := (div_le_iff₀ hNp).mp hsmall₂N
    nlinarith only [h₁, h₂]
  have ht : 0 ≤ (1 - tau) * (N : ℝ) :=
    mul_nonneg (sub_pos.mpr htau1).le hNp.le
  have hceil1 : 1 ≤ ⌈(1 - tau) * (N : ℝ)⌉₊ := by
    have h := (Real.rpow_pos_of_pos hNp a).le
    exact_mod_cast (show (1 : ℝ) ≤ (⌈(1 - tau) * (N : ℝ)⌉₊ : ℝ) from
      (by linarith only [hsum, h] : (1 : ℝ) ≤ (1 - tau) * (N : ℝ)).trans (Nat.le_ceil _))
  have hmcast : ((⌈(1 - tau) * (N : ℝ)⌉₊ - 1 : ℕ) : ℝ) =
      (⌈(1 - tau) * (N : ℝ)⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
  rw [hmcast]
  constructor
  · linarith only [hsum, Nat.le_ceil ((1 - tau) * (N : ℝ))]
  · have hceil := Nat.ceil_lt_add_one ht
    have htauN := mul_nonneg htau0 hNp.le
    nlinarith only [hceil, htauN]

/-- An absolute bound on a signed rough density follows from its literal
absolute reciprocal-totient sum, before any attachment or asymptotic. -/
theorem abs_roughDensity_le (S : Finset ℕ) (c : ℕ → ℝ) :
    |reciprocalTotientDensity S c| ≤ reciprocalTotientDensity S (fun q => |c q|) := by
  simpa only [physicalDensitySum, reciprocalTotientDensity] using
    abs_physicalDensity_le S c

/-- The actual signed causal density has an O(C_N/log N) envelope, uniform
in the retention policy. This derives cancellation-aware scale control from
the proved attachment loss, Euler bound and actual rough absolute mass. -/
theorem exists_causal_signed_density_envelope
    (nu r epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ e : ℝ, 0 < e ∧ e < 1 / 8 ∧ e < epsilonMax ∧ e ^ 2 ≤ r ∧
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ N : ℕ in atTop, Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
        ∀ retainEven : List ℕ → Bool,
          let w := (N : ℝ) ^ (nu * e ^ 2)
          let z := (N : ℝ) ^ (nu * r)
          let L := (N : ℝ) ^ (nu * e)
          |physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
            (actualLowerSmallRoughRho retainEven N cap w z L)| ≤
              M * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨e, he, he8, heMax, her, N₀, _hN₀, hloss⟩ :=
    exists_actualLowerSmallRoughRho_density_error_le_target_reserve
      nu r 1 epsilonMax hnu hr (by norm_num) hepsilonMax
  obtain ⟨B, hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨K, hK, hRough⟩ := exists_fixedEvenRoughAbsoluteDensity_le_powerParameters
  let M : ℝ := 2 * B * r / (nu * e ^ 4) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨e, he, he8, heMax, her, M, hM, ?_⟩
  have hfour : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (nu * e ^ 2) :=
    ((tendsto_rpow_atTop (mul_pos hnu (sq_pos_of_pos he))).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)
  have hlargeLog : ∀ᶠ N : ℕ in atTop,
      K / (e ^ 2 * nu) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hfour, hlargeLog, eventually_ge_atTop N₀,
    eventually_ge_atTop (2 : ℕ)] with N hfourN hlargeLogN hN₀ hN
  intro hEven cap hcap retainEven
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hwcap : (N : ℝ) ^ (nu * e ^ 2) ≤ (cap : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNr.le
      (mul_le_mul_of_nonneg_left her hnu.le)).trans hcap
  have hV := (actualSmallEulerProduct_pos N cap ((N : ℝ) ^ (nu * e ^ 2)) hEven).le
  have hVbound := hEuler N cap (by omega) hEven
    ((N : ℝ) ^ (nu * e ^ 2)) hfourN hwcap
  rw [Real.log_rpow hNp] at hVbound
  have hw2 : 2 ≤ ((N : ℝ) ^ nu) ^ (e ^ 2) := by
    rw [← Real.rpow_mul hNp.le]
    linarith only [hfourN]
  have hRbound := hRough retainEven N cap hEven ((N : ℝ) ^ nu) e r
    (Real.one_lt_rpow hNr hnu) he her hw2
  simp only [← Real.rpow_mul hNp.le, Real.log_rpow hNp] at hRbound
  have hden : K ≤ e ^ 2 * (nu * Real.log (N : ℝ)) := by
    have h := (div_le_iff₀ (mul_pos (sq_pos_of_pos he) hnu)).mp hlargeLogN
    nlinarith only [h]
  have hfrac : K / (e ^ 2 * (nu * Real.log (N : ℝ))) ≤ 1 :=
    (div_le_one (by positivity : 0 < e ^ 2 * (nu * Real.log (N : ℝ)))).mpr hden
  have hRbound₂ :
      reciprocalTotientDensity
        (fixedEvenRoughSupport retainEven N cap ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)))
        (fun q => |fixedEvenRoughCoefficient retainEven N cap
          ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)) q|) ≤ 2 * r / e ^ 2 := by
    calc
      _ ≤ (r / e ^ 2) * (1 + K / (e ^ 2 * (nu * Real.log (N : ℝ)))) := hRbound
      _ ≤ (r / e ^ 2) * 2 := mul_le_mul_of_nonneg_left
        (by linarith only [hfrac]) (div_nonneg hr.le (sq_nonneg e))
      _ = _ := by ring
  have hRabs := abs_roughDensity_le
    (fixedEvenRoughSupport retainEven N cap ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)))
    (fixedEvenRoughCoefficient retainEven N cap ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)))
  have hRlo := mul_le_mul_of_nonneg_left (abs_le.mp hRabs).1 hV
  have hRhi := mul_le_mul_of_nonneg_left (abs_le.mp hRabs).2 hV
  have hError := hloss N hN₀ hEven cap hcap retainEven
  dsimp only at hError ⊢
  simp only [one_mul] at hError
  have hscale : 0 ≤ singularSeries N / Real.log (N : ℝ) :=
    div_nonneg (singularSeries_pos N).le hlogN.le
  have hD : |physicalDensitySum
      (actualLowerSmallRoughModuli retainEven N cap
        ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)))
      (actualLowerSmallRoughRho retainEven N cap
        ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)) ((N : ℝ) ^ (nu * e)))| ≤
      actualSmallEulerProduct N cap ((N : ℝ) ^ (nu * e ^ 2)) *
        reciprocalTotientDensity
          (fixedEvenRoughSupport retainEven N cap ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)))
          (fun q => |fixedEvenRoughCoefficient retainEven N cap
            ((N : ℝ) ^ (nu * e ^ 2)) ((N : ℝ) ^ (nu * r)) q|) +
        singularSeries N / Real.log (N : ℝ) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hRlo, hRhi, hError.1, hError.2, hscale]
  calc
    _ ≤ _ := hD
    _ ≤ actualSmallEulerProduct N cap ((N : ℝ) ^ (nu * e ^ 2)) * (2 * r / e ^ 2) +
        singularSeries N / Real.log (N : ℝ) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hRbound₂ hV) _
    _ ≤ (B * singularSeries N / ((nu * e ^ 2) * Real.log (N : ℝ))) * (2 * r / e ^ 2) +
        singularSeries N / Real.log (N : ℝ) :=
      add_le_add_right (mul_le_mul_of_nonneg_right hVbound (by positivity)) _
    _ = M * singularSeries N / Real.log (N : ℝ) := by
      dsimp [M]
      field_simp [he.ne', hnu.ne', hlogN.ne']
      <;> ring

/-- For the actual causal rho, true-li replacement costs an arbitrarily
small H reserve, uniformly in all real endpoints in [N^a,N]. The precision
is selected before the requested error reserve and before the policy. -/
theorem exists_causal_uniform_main_error_H
    (nu r a epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (ha : 0 < a) (hepsilonMax : 0 < epsilonMax) :
    ∃ e : ℝ, 0 < e ∧ e < 1 / 8 ∧ e < epsilonMax ∧ e ^ 2 ≤ r ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
        ∀ retainEven : List ℕ → Bool, ∀ x : ℝ,
          (N : ℝ) ^ a ≤ x → x ≤ (N : ℝ) →
          let w := (N : ℝ) ^ (nu * e ^ 2)
          let z := (N : ℝ) ^ (nu * r)
          let L := (N : ℝ) ^ (nu * e)
          let D := physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
            (actualLowerSmallRoughRho retainEven N cap w z L)
          |trueLogarithmicIntegral x * D - (x / Real.log x) * D| ≤
            eta * singularNormalization N := by
  obtain ⟨e, he, he8, heMax, her, M, hM, hbound⟩ :=
    exists_causal_signed_density_envelope nu r epsilonMax hnu hr hepsilonMax
  refine ⟨e, he, he8, heMax, her, ?_⟩
  intro eta heta
  filter_upwards [hbound, eventually_uniform_main_error_H a M eta ha hM heta]
    with N hboundN hmainN
  intro hEven cap hcap retainEven x hax hxN
  exact hmainN x _ hax hxN (hboundN hEven cap hcap retainEven)

/-- Literal adopted original first row, including its strict original-prime
endpoint ceil((1-tau)N)-1 and its actual a=417/5000 prime cutoff. There is no
fixed-N substitution, no endpoint rounding loss hidden in an assumption,
and no desired L1 lower estimate in the type. -/
theorem exists_original_initial_strict_endpoint_main_error_H
    (epsilonMax : ℝ) (hepsilonMax : 0 < epsilonMax) :
    ∃ e : ℝ, 0 < e ∧ e < 1 / 8 ∧ e < epsilonMax ∧
      e ^ 2 ≤ (417 / 5000 : ℝ) / (249 / 448 : ℝ) ∧
      ∀ tau : ℝ, 0 ≤ tau → tau < 1 → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ N : ℕ in atTop, Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (cap : ℝ) →
          ∀ retainEven : List ℕ → Bool,
            let x : ℝ := ((⌈(1 - tau) * (N : ℝ)⌉₊ - 1 : ℕ) : ℝ)
            let w := (N : ℝ) ^ ((249 / 448 : ℝ) * e ^ 2)
            let z := (N : ℝ) ^ (417 / 5000 : ℝ)
            let L := (N : ℝ) ^ ((249 / 448 : ℝ) * e)
            let D := physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
              (actualLowerSmallRoughRho retainEven N cap w z L)
            |trueLogarithmicIntegral x * D - (x / Real.log x) * D| ≤
              eta * singularNormalization N := by
  have hexp : (249 / 448 : ℝ) * ((417 / 5000 : ℝ) / (249 / 448 : ℝ)) =
      (417 / 5000 : ℝ) := by norm_num
  obtain ⟨e, he, he8, heMax, her, hmain⟩ :=
    exists_causal_uniform_main_error_H (249 / 448) ((417 / 5000) / (249 / 448))
      (417 / 5000) epsilonMax (by norm_num) (by norm_num) (by norm_num) hepsilonMax
  refine ⟨e, he, he8, heMax, her, ?_⟩
  intro tau htau0 htau1 eta heta
  filter_upwards [hmain eta heta,
    eventually_strict_endpoint_window (417 / 5000) tau
      (by norm_num) (by norm_num) htau0 htau1] with N hmainN hwindowN
  intro hEven cap hcap retainEven
  have hcap' : (N : ℝ) ^ ((249 / 448 : ℝ) *
      ((417 / 5000 : ℝ) / (249 / 448 : ℝ))) ≤ (cap : ℝ) := by
    simpa only [hexp] using hcap
  simpa only [hexp] using hmainN hEven cap hcap' retainEven
    (((⌈(1 - tau) * (N : ℝ)⌉₊ - 1 : ℕ) : ℝ)) hwindowN.1 hwindowN.2

end

end ImbalancedChen.P5S1MovingTrueLi
