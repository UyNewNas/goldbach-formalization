import ImbalancedChen.MovingWeightTransport
import ImbalancedChen.ChenQuotientLevelGeometry

/-!
# Continuous weights at the actual moving quotient-row levels

The proved uniform quotient-level geometry puts both the actual sieve
parameter and its logarithmic profile into one fixed compact interval,
with an explicitly positive padding radius. A fixed continuous sieve
factor can therefore be transported inside any nonnegative weighted sum
whose total mass is eventually bounded.

That mass bound is an explicit input. No prime or prime-pair harmonic
estimate, sieve inequality, or Chen coefficient is asserted here. Labels
are retained, so this applies equally to primes and ordered prime pairs.

Held source candidate: compilation, kernel replay, and axiom audit pending.
-/

namespace ImbalancedChen

noncomputable section
open Filter Topology
open scoped BigOperators

/-- A fixed positive padding is sufficient for one closed interval to
contain both moving and model coordinates, uniformly over every positive
multiplier in the entire fixed power range. No lower-sieve positivity
gate, such as a parameter at least two, is claimed. -/
theorem eventually_chenQuotientRosserT_profile_mem_fixed_interval
    (B beta a rho : ℝ) (hbeta : beta < 1 / 2) (ha : 0 < a) (hrho : 0 < rho) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ,
      0 < b → (b : ℝ) ≤ (N : ℝ) ^ beta →
      chenQuotientRosserT B a N b ∈
        Set.Icc (((1 / 2 : ℝ) - beta) / a - rho) ((1 / 2 : ℝ) / a + rho) ∧
      (((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a) ∈
        Set.Icc (((1 / 2 : ℝ) - beta) / a - rho) ((1 / 2 : ℝ) / a + rho) := by
  filter_upwards [eventually_chenQuotientRosserT_profile B beta a hbeta ha rho hrho,
    eventually_ge_atTop (2 : ℕ)] with N hprofile hN
  intro b hb hbpower
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hu0 : 0 ≤ Real.log (b : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Real.log_nonneg hb1) hlog.le
  have hlogb := Real.log_le_log hbpos hbpower
  rw [Real.log_rpow (lt_trans zero_lt_one hN1) beta] at hlogb
  have hubeta : Real.log (b : ℝ) / Real.log (N : ℝ) ≤ beta :=
    (div_le_iff₀ hlog).mpr hlogb
  have hylo : ((1 / 2 : ℝ) - beta) / a ≤
      ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a :=
    div_le_div_of_nonneg_right (by linarith) ha.le
  have hyhi : ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a ≤
      (1 / 2 : ℝ) / a :=
    div_le_div_of_nonneg_right (by linarith) ha.le
  obtain ⟨hleft, hright⟩ := abs_lt.mp (hprofile b hb hbpower)
  constructor
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- The moving sieve factor may be replaced by its logarithmic profile
inside any eventually bounded nonnegative label mass. The power-range
condition retains every label rather than pooling or deleting rows. -/
theorem tendsto_chenQuotientRosserT_weighted_profile_error
    {ι : Type*} (T : ℕ → Finset ι) (b : ℕ → ι → ℕ) (w : ℕ → ι → ℝ)
    (B beta a rho M : ℝ) (F : ℝ → ℝ)
    (hbeta : beta < 1 / 2) (ha : 0 < a) (hrho : 0 < rho) (hM : 0 ≤ M)
    (hF : ContinuousOn F
      (Set.Icc (((1 / 2 : ℝ) - beta) / a - rho) ((1 / 2 : ℝ) / a + rho)))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i ∈ T N,
      0 < b N i ∧ (b N i : ℝ) ≤ (N : ℝ) ^ beta)
    (hw : ∀ᶠ N : ℕ in atTop, ∀ i ∈ T N, 0 ≤ w N i)
    (hmass : ∀ᶠ N : ℕ in atTop, (∑ i ∈ T N, w N i) ≤ M) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ T N, w N i * F (chenQuotientRosserT B a N (b N i))) -
        ∑ i ∈ T N, w N i *
          F (((1 / 2 : ℝ) - Real.log (b N i : ℝ) / Real.log (N : ℝ)) / a))
      atTop (𝓝 0) := by
  apply tendsto_nonneg_weighted_comp_sub_zero_of_compact T w
    (fun N i => chenQuotientRosserT B a N (b N i))
    (fun N i => ((1 / 2 : ℝ) - Real.log (b N i : ℝ) / Real.log (N : ℝ)) / a)
    (Set.Icc (((1 / 2 : ℝ) - beta) / a - rho) ((1 / 2 : ℝ) / a + rho))
    F M isCompact_Icc hF hM hw hmass
  · filter_upwards [hb,
      eventually_chenQuotientRosserT_profile_mem_fixed_interval B beta a rho hbeta ha hrho]
      with N hNb hmem
    intro i hi
    exact hmem (b N i) (hNb i hi).1 (hNb i hi).2
  · intro delta hdelta
    filter_upwards [hb,
      eventually_chenQuotientRosserT_profile B beta a hbeta ha delta hdelta]
      with N hNb hprofile
    intro i hi
    exact hprofile (b N i) (hNb i hi).1 (hNb i hi).2

/-- An independently established weighted logarithmic-profile limit gives
the same limit at the actual natural quotient-row levels. In particular,
this theorem does not assume the requested moving-level conclusion. -/
theorem tendsto_chenQuotientRosserT_weighted_of_profile
    {ι : Type*} (T : ℕ → Finset ι) (b : ℕ → ι → ℕ) (w : ℕ → ι → ℝ)
    (B beta a rho M L : ℝ) (F : ℝ → ℝ)
    (hbeta : beta < 1 / 2) (ha : 0 < a) (hrho : 0 < rho) (hM : 0 ≤ M)
    (hF : ContinuousOn F
      (Set.Icc (((1 / 2 : ℝ) - beta) / a - rho) ((1 / 2 : ℝ) / a + rho)))
    (hb : ∀ᶠ N : ℕ in atTop, ∀ i ∈ T N,
      0 < b N i ∧ (b N i : ℝ) ≤ (N : ℝ) ^ beta)
    (hw : ∀ᶠ N : ℕ in atTop, ∀ i ∈ T N, 0 ≤ w N i)
    (hmass : ∀ᶠ N : ℕ in atTop, (∑ i ∈ T N, w N i) ≤ M)
    (hfixed : Tendsto (fun N : ℕ =>
      ∑ i ∈ T N, w N i *
        F (((1 / 2 : ℝ) - Real.log (b N i : ℝ) / Real.log (N : ℝ)) / a))
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ =>
      ∑ i ∈ T N, w N i * F (chenQuotientRosserT B a N (b N i)))
      atTop (𝓝 L) := by
  have herror := tendsto_chenQuotientRosserT_weighted_profile_error
    T b w B beta a rho M F hbeta ha hrho hM hF hb hw hmass
  simpa only [sub_add_cancel, zero_add] using herror.add hfixed

end

end ImbalancedChen
