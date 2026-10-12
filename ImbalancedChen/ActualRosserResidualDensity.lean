import ImbalancedChen.ActualRosserCompactNormalization

/-!
# Actual Rosser densities at variable residual levels

Pairs in this module are ordered `(beta,u)`: the level is `N^beta` and
prime cutoff is `N^u`. The continuous pullback `(beta,u) -> (u,beta/u)`
transports proved compact density estimates. Every threshold precedes
all later targets, parameter pairs and covering caps. Exact logarithmic
identities then permit arbitrary positive prefix products and least-prime
cutoffs depending on the target. No rounding changes the literal level.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory

/-- Residual exponent coordinates to outer exponent and sieve residual. -/
def rosserResidualParameters (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1 / p.2)

theorem continuousOn_rosserResidualParameters
    (T : Set (ℝ × ℝ)) (hpos : ∀ p ∈ T, 0 < p.2) :
    ContinuousOn rosserResidualParameters T :=
  continuous_snd.continuousOn.prodMk
    (continuous_fst.continuousOn.div continuous_snd.continuousOn
      (fun p hp => (hpos p hp).ne'))

/-- Canonical-cap uniform convergence gives a threshold for every complete cap. -/
theorem exists_actualSmallRosserPlusDensity_compact_normalized_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N -
          (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
            suzukiContinuousUpperFactor p.2| < eta := by
  have hlim := tendstoUniformlyOn_actualSmallRosserPlusDensity_normalized S hS hparam
    (fun N p => Nat.ceil ((N : ℝ) ^ p.1))
    (Filter.Eventually.of_forall (fun N p _hp => Nat.le_ceil ((N : ℝ) ^ p.1)))
  have hev := Metric.tendstoUniformlyOn_iff.mp hlim eta heta
  simp only [Filter.eventually_inf_principal] at hev
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven p hp cap hcap
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have h := hN1 N ((le_max_left _ _).trans hN) ⟨by omega, hEven⟩ p hp
  have hcapEq : actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) =
      actualSmallRosserPlusDensity N (Nat.ceil ((N : ℝ) ^ p.1)) ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) := by
    rw [actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N cap hEven _ _ hcap,
      actualSmallRosserPlusDensity_eq_b8_mainSum_natCeil N _ hEven _ _ (Nat.le_ceil _)]
  rw [hcapEq]
  simpa only [Real.dist_eq, abs_sub_comm] using h

/-- The same actual plus density, uniformly at residual exponent pairs. -/
theorem exists_actualSmallRosserPlusDensity_residual_compact_close_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.2) -
            suzukiContinuousUpperFactor (p.1 / p.2)| < eta := by
  let S := rosserResidualParameters '' T
  have hS : IsCompact S := hT.image_of_continuousOn
    (continuousOn_rosserResidualParameters T (fun p hp => (hparam p hp).1))
  have hs : ∀ q ∈ S, 0 < q.1 ∧ 1 < q.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨(hparam p hp).1, (one_lt_div (hparam p hp).1).mpr (hparam p hp).2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_compact_close_threshold S hS hs eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven (rosserResidualParameters p)
    (Set.mem_image_of_mem _ hp) cap hcap
  simpa only [rosserResidualParameters, div_mul_cancel₀ _ (hparam p hp).1.ne'] using h

/-- The same actual plus density, uniformly at residual exponent pairs. -/
theorem exists_actualSmallRosserPlusDensity_residual_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
            Real.log (N : ℝ) / singularSeries N -
            (2 * Real.exp (-Real.eulerMascheroniConstant) / p.2) *
              suzukiContinuousUpperFactor (p.1 / p.2)| < eta := by
  let S := rosserResidualParameters '' T
  have hS : IsCompact S := hT.image_of_continuousOn
    (continuousOn_rosserResidualParameters T (fun p hp => (hparam p hp).1))
  have hs : ∀ q ∈ S, 0 < q.1 ∧ 1 < q.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨(hparam p hp).1, (one_lt_div (hparam p hp).1).mpr (hparam p hp).2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_compact_normalized_threshold S hS hs eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven (rosserResidualParameters p)
    (Set.mem_image_of_mem _ hp) cap hcap
  simpa only [rosserResidualParameters, div_mul_cancel₀ _ (hparam p hp).1.ne'] using h

theorem tendstoUniformlyOn_actualSmallRosserPlusDensity_residual_ratio
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ T, (N : ℝ) ^ p.2 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserPlusDensity N (cap N p) ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) /
          actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.2))
      (fun p => suzukiContinuousUpperFactor (p.1 / p.2))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) T := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_close_threshold T hT hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

theorem tendstoUniformlyOn_actualSmallRosserPlusDensity_residual_normalized
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ T, (N : ℝ) ^ p.2 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserPlusDensity N (cap N p) ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
          Real.log (N : ℝ) / singularSeries N)
      (fun p => (2 * Real.exp (-Real.eulerMascheroniConstant) / p.2) *
        suzukiContinuousUpperFactor (p.1 / p.2))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) T := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_normalized_threshold T hT hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

/-- Canonical-cap uniform convergence gives a threshold for every complete cap. -/
theorem exists_actualSmallRosserMinusDensity_compact_normalized_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N -
          (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
            suzukiContinuousLowerFactor p.2| < eta := by
  have hlim := tendstoUniformlyOn_actualSmallRosserMinusDensity_normalized S hS hparam
    (fun N p => Nat.ceil ((N : ℝ) ^ p.1))
    (Filter.Eventually.of_forall (fun N p _hp => Nat.le_ceil ((N : ℝ) ^ p.1)))
  have hev := Metric.tendstoUniformlyOn_iff.mp hlim eta heta
  simp only [Filter.eventually_inf_principal] at hev
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨max N1 2, le_max_right _ _, ?_⟩
  intro N hN hEven p hp cap hcap
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have h := hN1 N ((le_max_left _ _).trans hN) ⟨by omega, hEven⟩ p hp
  have hcapEq : actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) =
      actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ p.1)) ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) := by
    rw [actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N cap hEven _ _ hcap,
      actualSmallRosserMinusDensity_eq_b8_mainSum_natCeil N _ hEven _ _ (Nat.le_ceil _)]
  rw [hcapEq]
  simpa only [Real.dist_eq, abs_sub_comm] using h

/-- The same actual minus density, uniformly at residual exponent pairs. -/
theorem exists_actualSmallRosserMinusDensity_residual_compact_close_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) /
            actualSmallEulerProduct N cap ((N : ℝ) ^ p.2) -
            suzukiContinuousLowerFactor (p.1 / p.2)| < eta := by
  let S := rosserResidualParameters '' T
  have hS : IsCompact S := hT.image_of_continuousOn
    (continuousOn_rosserResidualParameters T (fun p hp => (hparam p hp).1))
  have hs : ∀ q ∈ S, 0 < q.1 ∧ 2 ≤ q.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨(hparam p hp).1, (le_div_iff₀ (hparam p hp).1).mpr (hparam p hp).2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_compact_close_threshold S hS hs eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven (rosserResidualParameters p)
    (Set.mem_image_of_mem _ hp) cap hcap
  simpa only [rosserResidualParameters, div_mul_cancel₀ _ (hparam p hp).1.ne'] using h

/-- The same actual minus density, uniformly at residual exponent pairs. -/
theorem exists_actualSmallRosserMinusDensity_residual_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserMinusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
            Real.log (N : ℝ) / singularSeries N -
            (2 * Real.exp (-Real.eulerMascheroniConstant) / p.2) *
              suzukiContinuousLowerFactor (p.1 / p.2)| < eta := by
  let S := rosserResidualParameters '' T
  have hS : IsCompact S := hT.image_of_continuousOn
    (continuousOn_rosserResidualParameters T (fun p hp => (hparam p hp).1))
  have hs : ∀ q ∈ S, 0 < q.1 ∧ 2 ≤ q.2 := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨(hparam p hp).1, (le_div_iff₀ (hparam p hp).1).mpr (hparam p hp).2⟩
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_compact_normalized_threshold S hS hs eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven (rosserResidualParameters p)
    (Set.mem_image_of_mem _ hp) cap hcap
  simpa only [rosserResidualParameters, div_mul_cancel₀ _ (hparam p hp).1.ne'] using h

theorem tendstoUniformlyOn_actualSmallRosserMinusDensity_residual_ratio
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ T, (N : ℝ) ^ p.2 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserMinusDensity N (cap N p) ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) /
          actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.2))
      (fun p => suzukiContinuousLowerFactor (p.1 / p.2))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) T := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_residual_compact_close_threshold T hT hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

theorem tendstoUniformlyOn_actualSmallRosserMinusDensity_residual_normalized
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ T, (N : ℝ) ^ p.2 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserMinusDensity N (cap N p) ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
          Real.log (N : ℝ) / singularSeries N)
      (fun p => (2 * Real.exp (-Real.eulerMascheroniConstant) / p.2) *
        suzukiContinuousLowerFactor (p.1 / p.2))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) T := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_residual_compact_normalized_threshold T hT hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, N0 ≤ N :=
    (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

/-- Exact logarithmic recovery of a positive real cutoff. -/
theorem residual_rpow_log_div (N y : ℝ) (hN : 1 < N) (hy : 0 < y) :
    N ^ (Real.log y / Real.log N) = y := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN)]
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  rw [mul_div_cancel₀ _ hlog, Real.exp_log hy]

/-- The real residual level, without any alteration of its strict ceiling. -/
theorem residual_rpow_level_div (N P lambda : ℝ) (hN : 1 < N) (hP : 0 < P) :
    N ^ (lambda - Real.log P / Real.log N) = N ^ lambda / P := by
  rw [Real.rpow_sub (zero_lt_one.trans hN), residual_rpow_log_div N P hN hP]

/-- Coordinate extraction for a quotient level and a positive cutoff. -/
def actualRosserQuotientParameters (N P y lambda : ℝ) : ℝ × ℝ :=
  (lambda - Real.log P / Real.log N, Real.log y / Real.log N)

theorem actualRosserQuotientParameters_exact (N P y lambda : ℝ)
    (hN : 1 < N) (hP : 0 < P) (hy : 0 < y) :
    N ^ (actualRosserQuotientParameters N P y lambda).1 = N ^ lambda / P ∧
      N ^ (actualRosserQuotientParameters N P y lambda).2 = y :=
  ⟨residual_rpow_level_div N P lambda hN hP, residual_rpow_log_div N y hN hy⟩

/-- One threshold handles all later positive prefix products and cutoffs
whose extracted exponents lie in the fixed legal compact set. -/
theorem exists_actualSmallRosserPlusDensity_quotient_compact_close_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) /
              actualSmallEulerProduct N cap y -
            suzukiContinuousUpperFactor
              ((actualRosserQuotientParameters (N : ℝ) P y lambda).1 /
                (actualRosserQuotientParameters (N : ℝ) P y lambda).2)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_close_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda hP hy hparamN cap hcap
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ := actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNreal hP hy
  have h := hbound N hN hEven (actualRosserQuotientParameters (N : ℝ) P y lambda)
    hparamN cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

/-- One threshold handles all later positive prefix products and cutoffs
whose extracted exponents lie in the fixed legal compact set. -/
theorem exists_actualSmallRosserPlusDensity_quotient_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
              Real.log (N : ℝ) / singularSeries N -
            (2 * Real.exp (-Real.eulerMascheroniConstant) /
                (actualRosserQuotientParameters (N : ℝ) P y lambda).2) *
              suzukiContinuousUpperFactor
                ((actualRosserQuotientParameters (N : ℝ) P y lambda).1 /
                  (actualRosserQuotientParameters (N : ℝ) P y lambda).2)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_normalized_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda hP hy hparamN cap hcap
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ := actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNreal hP hy
  have h := hbound N hN hEven (actualRosserQuotientParameters (N : ℝ) P y lambda)
    hparamN cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

/-- One threshold handles all later positive prefix products and cutoffs
whose extracted exponents lie in the fixed legal compact set. -/
theorem exists_actualSmallRosserMinusDensity_quotient_compact_close_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserMinusDensity N cap y ((N : ℝ) ^ lambda / P) /
              actualSmallEulerProduct N cap y -
            suzukiContinuousLowerFactor
              ((actualRosserQuotientParameters (N : ℝ) P y lambda).1 /
                (actualRosserQuotientParameters (N : ℝ) P y lambda).2)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_residual_compact_close_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda hP hy hparamN cap hcap
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ := actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNreal hP hy
  have h := hbound N hN hEven (actualRosserQuotientParameters (N : ℝ) P y lambda)
    hparamN cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

/-- One threshold handles all later positive prefix products and cutoffs
whose extracted exponents lie in the fixed legal compact set. -/
theorem exists_actualSmallRosserMinusDensity_quotient_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 2 * p.2 ≤ p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserMinusDensity N cap y ((N : ℝ) ^ lambda / P) *
              Real.log (N : ℝ) / singularSeries N -
            (2 * Real.exp (-Real.eulerMascheroniConstant) /
                (actualRosserQuotientParameters (N : ℝ) P y lambda).2) *
              suzukiContinuousLowerFactor
                ((actualRosserQuotientParameters (N : ℝ) P y lambda).1 /
                  (actualRosserQuotientParameters (N : ℝ) P y lambda).2)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserMinusDensity_residual_compact_normalized_threshold T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda hP hy hparamN cap hcap
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ := actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNreal hP hy
  have h := hbound N hN hEven (actualRosserQuotientParameters (N : ℝ) P y lambda)
    hparamN cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

end

end ImbalancedChen
