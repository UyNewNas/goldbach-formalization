import ImbalancedChen.P2OriginalElevenFullModulusOmittedCover
import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.SmallRosserErrorLimit
import ImbalancedChen.RoughPowerParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complete SMALL and RESIDUAL-MODULUS summation for the actual eleven-prefix
omitted divisor cover.  The small beta densities are summed with their
original signs before taking absolute values.  The remaining divisor mass
is the true finite rough Euler product, bounded by the existing classical
inverse-interval theorem.  Its constant is retained in the normalization.
This proves a signed DENSITY bound, not an AP count/discrepancy bound.
-/

namespace ImbalancedChen.P2OriginalElevenAttachedOmittedDensity
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthOmittedArithmeticMass P2OriginalElevenFullModulusOmittedCover

def attachedDensity (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum (omittedModuli ret c n N cap w z) (omittedRho ret c n N cap w z L)

def restrictedDensity (ret : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (S : Finset ℕ) : ℝ :=
  physicalDensitySum (smallRoughModuli (actualSmallRosserSupport N cap w) S)
    (smallRoughRho (actualSmallRosserSupport N cap w) S (fixedRoughCoefficient ret N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L))

theorem attachedDensity_eq_actual (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ) (w z L : ℝ) :
    attachedDensity ret c n N cap w z L =
      ∑ q ∈ omittedModuli ret c n N cap w z, actualSmallRoughRho ret N cap w z L q /
        (Nat.totient q : ℝ) := by
  simpa only [attachedDensity,physicalDensitySum,div_eq_mul_inv] using
    omitted_actual_test_eq ret c n N cap w z L (fun q => (Nat.totient q : ℝ)⁻¹)

theorem attachedDensity_eq_signed_small (ret : List ℕ → Bool) (c : Cell)
    (n N cap : ℕ) (w z L : ℝ) :
    attachedDensity ret c n N cap w z L =
      signSensitiveReciprocalTotientDensity (omittedRough ret c n N cap w z)
        (fixedRoughCoefficient ret N cap w z)
        (actualSmallRosserMinusDensity N cap w L) (actualSmallRosserPlusDensity N cap w L) := by
  exact physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
    (fun _ hb => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z
      (omittedRough_subset ret c n N cap w z hb)) _ _ _

/-- A finite bound after all original small factors have already been
summed.  B bounds their SIGNED densities, not their absolute coefficients. -/
theorem abs_attachedDensity_le (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ)
    (w z L B : ℝ) (hB : 0 ≤ B)
    (hminus : |actualSmallRosserMinusDensity N cap w L| ≤ B)
    (hplus : |actualSmallRosserPlusDensity N cap w L| ≤ B) :
    |attachedDensity ret c n N cap w z L| ≤ B * omittedMass c n N * residualMass N cap w z := by
  rw [attachedDensity_eq_signed_small]
  have hrow (b : ℕ) :
      |fixedRoughCoefficient ret N cap w z b / (Nat.totient b : ℝ) *
        (if 0 ≤ fixedRoughCoefficient ret N cap w z b then
          actualSmallRosserPlusDensity N cap w L else actualSmallRosserMinusDensity N cap w L)| ≤
        B * (1 / (Nat.totient b : ℝ)) := by
    have htest : |if 0 ≤ fixedRoughCoefficient ret N cap w z b then
        actualSmallRosserPlusDensity N cap w L else actualSmallRosserMinusDensity N cap w L| ≤ B := by
      split_ifs <;> assumption
    rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (|fixedRoughCoefficient ret N cap w z b| / (Nat.totient b : ℝ))*B :=
        mul_le_mul_of_nonneg_left htest (by positivity)
      _ ≤ (1 / (Nat.totient b : ℝ))*B := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (fixedRoughCoefficient_abs_le_one ret N cap w z b)
          (Nat.cast_nonneg _)) hB
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∑ b ∈ omittedRough ret c n N cap w z,
        |fixedRoughCoefficient ret N cap w z b / (Nat.totient b : ℝ) *
          if 0 ≤ fixedRoughCoefficient ret N cap w z b then
            actualSmallRosserPlusDensity N cap w L else actualSmallRosserMinusDensity N cap w L| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ omittedRough ret c n N cap w z, B * (1 / (Nat.totient b : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hrow b)
    _ = B * ∑ b ∈ omittedRough ret c n N cap w z, 1 / (Nat.totient b : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ B * (omittedMass c n N * residualMass N cap w z) :=
      mul_le_mul_of_nonneg_left (omittedRough_mass_le ret c n N cap w z) hB
    _ = _ := by ring

/-- Every actual subcarrier of the divisor cover obeys the same bound;
signed density itself is not asserted to be monotone under restriction. -/
theorem abs_restrictedDensity_le (ret : List ℕ → Bool) (c : Cell) (n N cap : ℕ)
    (w z L B : ℝ) (S : Finset ℕ) (hS : S ⊆ omittedRough ret c n N cap w z) (hB : 0 ≤ B)
    (hminus : |actualSmallRosserMinusDensity N cap w L| ≤ B)
    (hplus : |actualSmallRosserPlusDensity N cap w L| ≤ B) :
    |restrictedDensity ret N cap w z L S| ≤ B * omittedMass c n N * residualMass N cap w z := by
  have heq : restrictedDensity ret N cap w z L S =
      signSensitiveReciprocalTotientDensity S (fixedRoughCoefficient ret N cap w z)
        (actualSmallRosserMinusDensity N cap w L) (actualSmallRosserPlusDensity N cap w L) :=
    physicalDensitySum_smallRoughRho_eq_signSensitive
      (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
      (fun _ hb => fixedRoughSupport_roughPrimeSupportedAt ret N cap w z
        (omittedRough_subset ret c n N cap w z (hS hb))) _ _ _
  rw [heq]
  calc
    _ ≤ ∑ b ∈ S, |fixedRoughCoefficient ret N cap w z b / (Nat.totient b : ℝ) *
        if 0 ≤ fixedRoughCoefficient ret N cap w z b then
          actualSmallRosserPlusDensity N cap w L else actualSmallRosserMinusDensity N cap w L| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ S, B * (1 / (Nat.totient b : ℝ)) := by
      apply Finset.sum_le_sum
      intro b hb
      have ht : |if 0 ≤ fixedRoughCoefficient ret N cap w z b then
          actualSmallRosserPlusDensity N cap w L else actualSmallRosserMinusDensity N cap w L| ≤ B := by
        split_ifs <;> assumption
      rw [abs_mul,abs_div,abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (|fixedRoughCoefficient ret N cap w z b| / (Nat.totient b : ℝ))*B :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        _ ≤ (1 / (Nat.totient b : ℝ))*B := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (fixedRoughCoefficient_abs_le_one ret N cap w z b)
            (Nat.cast_nonneg _)) hB
        _ = _ := mul_comm _ _
    _ = B * ∑ b ∈ S, 1 / (Nat.totient b : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ B * ∑ b ∈ omittedRough ret c n N cap w z, 1 / (Nat.totient b : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)) hB
    _ ≤ B * (omittedMass c n N * residualMass N cap w z) :=
      mul_le_mul_of_nonneg_left (omittedRough_mass_le ret c n N cap w z) hB
    _ = _ := by ring

theorem residualMass_nonneg (N cap : ℕ) (w z : ℝ) : 0 ≤ residualMass N cap w z := by
  apply Finset.sum_nonneg
  intro r hr
  positivity

theorem residualMass_eq_euler (N cap : ℕ) (w z : ℝ) :
    residualMass N cap w z = ∏ p ∈ roughPrimeFinset N cap w z, (1 + 1 / ((p : ℝ)-1)) := by
  exact reciprocalTotient_sum_divisors_primeProduct N _
    (fun p hp => (mem_roughPrimeFinset.mp hp).2.1)
    (fun p hp => (mem_roughPrimeFinset.mp hp).2.1.coprime_iff_not_dvd.mpr
      (mem_roughPrimeFinset.mp hp).2.2.1)

/-- This bound is for ALL actual residual divisors, not merely for one
unit-bounded coefficient at a fixed residual modulus. -/
theorem exists_residualMass_power_envelope :
    ∃ K : ℝ, 1 < K ∧ ∀ (N cap : ℕ), Even N → ∀ epsilon r : ℝ,
      1 < N → 0 < epsilon → epsilon^2 ≤ r → 2 ≤ (N : ℝ)^(epsilon^2) →
      residualMass N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ≤
        (r/epsilon^2) * (1 + K/(epsilon^2 * Real.log (N : ℝ))) := by
  obtain ⟨K,hK,hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K,hK,?_⟩
  intro N cap hEven epsilon r hN he her hw
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hwz := Real.rpow_le_rpow_of_exponent_le hN1.le her
  have hprime : ∀ p ∈ roughPrimeFinset N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r),
      p.Prime ∧ 2 < p := fun p hp => roughPrimeFinset_odd_of_even hEven hp
  have h := hinterval _ hprime ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) hw hwz
    (fun p hp => (mem_roughPrimeFinset.mp hp).2.2.2)
  rw [residualMass_eq_euler]
  have hle := roughPrime_eulerProduct_le_inverseProduct N cap
    ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) hEven
  apply hle.trans
  rw [roughPower_log_ratio hNpos (Real.log_pos hN1).ne' he.ne',Real.log_rpow hNpos] at h
  exact h

/-- A fixed beta/rough parameter has a genuine constant after both full
modulus sums and Euler normalization.  No final density theorem is an input. -/
theorem exists_attached_normalization_envelope (epsilon r : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (c : Cell) (n : ℕ) (S : Finset ℕ),
        S ⊆ omittedRough ret c n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) →
        |restrictedDensity ret N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon) S| ≤
          A * (singularSeries N / Real.log (N : ℝ)) * omittedMass c n N := by
  obtain ⟨B,hB,hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C,K,hC,hK,hsmall⟩ := exists_actualSmallRosser_density_sandwich
  obtain ⟨D₀,hD₀,hsmall⟩ := hsmall epsilon he he8
  obtain ⟨Kr,hKr,hresidual⟩ := exists_residualMass_power_envelope
  let E₀ := C * Real.exp (-(1/epsilon))
  let M := E₀ + 1
  let R := r/epsilon^2 + 1
  let A := (B/epsilon^2) * (1+M) * R
  have hM : 0 < M := by dsimp [M,E₀]; positivity
  have hr : 0 < r := (sq_pos_of_pos he).trans_le her
  have hR : 0 < R := by dsimp [R]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hE : Tendsto (fun N : ℕ => actualSmallRosserDensityError C K (N : ℝ) epsilon)
      atTop (𝓝 E₀) := (tendsto_actualSmallRosserDensityError C K epsilon he).comp
        tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => epsilon^2 * Real.log (N : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (sq_pos_of_pos he)
  have hQ : Tendsto (fun N : ℕ => (r/epsilon^2)*(1+Kr/(epsilon^2*Real.log (N : ℝ))))
      atTop (𝓝 (r/epsilon^2)) := by
    simpa only [add_zero,mul_one] using ((hlog.const_div_atTop Kr).const_add 1).const_mul (r/epsilon^2)
  have hpower : Tendsto (fun N : ℕ => (N : ℝ)^(epsilon^2)) atTop atTop :=
    (tendsto_rpow_atTop (sq_pos_of_pos he)).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ D₀ ≤ (N : ℝ) ∧
      4 ≤ (N : ℝ)^(epsilon^2) ∧ actualSmallRosserDensityError C K (N : ℝ) epsilon < M ∧
      (r/epsilon^2)*(1+Kr/(epsilon^2*Real.log (N : ℝ))) < R := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D₀),
      hpower.eventually (eventually_ge_atTop (4 : ℝ)),
      hE.eventually (gt_mem_nhds (show E₀ < M by dsimp [M]; linarith)),
      hQ.eventually (gt_mem_nhds (show r/epsilon^2 < R by dsimp [R]; linarith))]
      with N hN hD hw hE hQ
    exact ⟨hN,hD,hw,hE,hQ⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨A,hA,max 2 N₀,le_max_left _ _,?_⟩
  intro N hN hEven cap hcap ret c n S hS
  obtain ⟨hN2,hD,hw,hE,hQ⟩ := hN₀ N ((le_max_right _ _).trans hN)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogN := Real.log_pos hN1
  have hnorm : 0 < singularSeries N / Real.log (N : ℝ) := div_pos (singularSeries_pos N) hlogN
  let V := actualSmallEulerProduct N cap ((N : ℝ)^(epsilon^2))
  let E := actualSmallRosserDensityError C K (N : ℝ) epsilon
  have hV := actualSmallEulerProduct_pos N cap ((N : ℝ)^(epsilon^2)) hEven
  have hE0 : 0 ≤ E := by dsimp [E,actualSmallRosserDensityError]; positivity
  have hVE : 0 ≤ V*E := mul_nonneg hV.le hE0
  have hs := hsmall (N : ℝ) hD N cap hEven
  have hminus : |actualSmallRosserMinusDensity N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^epsilon)| ≤
      V*(1+E) := by
    apply abs_le.mpr
    constructor
    · have := hs.1
      dsimp only at this
      nlinarith
    · exact hs.2.1.trans (by nlinarith)
  have hplus : |actualSmallRosserPlusDensity N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^epsilon)| ≤
      V*(1+E) := by
    apply abs_le.mpr
    exact ⟨(by have := hs.2.2.1; dsimp only at this; nlinarith),hs.2.2.2.1⟩
  have hbound := abs_restrictedDensity_le ret c n N cap _ _ _ (V*(1+E)) S hS
    (by positivity) hminus hplus
  have hwcap := (Real.rpow_le_rpow_of_exponent_le hN1.le her).trans hcap
  have hVbound := hEuler N cap (by omega) hEven ((N : ℝ)^(epsilon^2)) hw hwcap
  rw [Real.log_rpow hNpos] at hVbound
  have hres := (hresidual N cap hEven epsilon r (by omega) he her (by linarith)).trans hQ.le
  have hres0 := residualMass_nonneg N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r)
  have hfactor : V*(1+E)*residualMass N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ≤
      A*(singularSeries N / Real.log (N : ℝ)) := by
    calc
      _ ≤ V*(1+M)*R := mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith : 1+E ≤ 1+M) hV.le) hres
        hres0 (by positivity)
      _ ≤ (B * singularSeries N / (epsilon^2 * Real.log (N : ℝ)))*(1+M)*R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hVbound (by positivity)) hR.le
      _ = _ := by dsimp [A]; field_simp [he.ne',hlogN.ne'] <;> ring
  calc
    _ ≤ (V*(1+E))*omittedMass c n N*residualMass N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) := hbound
    _ = (V*(1+E)*residualMass N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r))*omittedMass c n N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (omittedMass_nonneg c n N)

/-- The entire actual small-factor/residual-modulus SIGNED DENSITY
remainder has an arbitrarily small C_N/log N reserve.  The cutoff and
all parameters are fixed before any target N or policy is supplied. -/
theorem exists_full_attached_density_payment (epsilon r eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (c : Cell) (S : Finset ℕ),
        S ⊆ omittedRough ret c n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) →
        |restrictedDensity ret N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon) S| <
          eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨A,hA,M,hM,hbound⟩ := exists_attached_normalization_envelope epsilon r he he8 her
  obtain ⟨n₀,T,hT,hmass⟩ := exists_common_omittedMass_rectangle (eta/A) (div_pos heta hA)
  refine ⟨n₀,max M T,hM.trans (le_max_left _ _),?_⟩
  intro n hn N hN hEven cap hcap ret c S hS
  have hNm := (le_max_left _ _).trans hN
  have hNt := (le_max_right _ _).trans hN
  have hN2 := hM.trans hNm
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hnorm := div_pos (singularSeries_pos N) hlog
  have hm := hmass n hn N hNt c
  have hs := mul_lt_mul_of_pos_left hm (mul_pos hA hnorm)
  have heq : (A*(singularSeries N/Real.log (N : ℝ)))*(eta/A) =
      eta*singularSeries N/Real.log (N : ℝ) := by field_simp [hA.ne'] <;> ring
  rw [heq] at hs
  exact (hbound N hNm hEven cap hcap ret c n S hS).trans_lt hs

end
end ImbalancedChen.P2OriginalElevenAttachedOmittedDensity
