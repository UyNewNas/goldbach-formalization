import ImbalancedChen.ActualRosserInitialResidualSaving
import ImbalancedChen.ActualRosserCubeReduction
import ImbalancedChen.P1FourthNearOneKernel

/-!
# Two-sided uniformity of the actual upper density on the closed legal domain

SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The `t > 1` perturbation from `P1ActualUpperNearOneBound` supplies a genuine
finite bound at the wall, but by itself is an upper estimate.  The stronger
two-sided result here uses the existing exact first-cube reduction of the
same literal coefficient and density.  If `beta <= 3*u`, reducing the cutoff
from `N^u` to `N^(beta/3)` preserves the actual density exactly, at the same
strict level `N^beta`.  The reduced residual is three, so the existing
two-sided compact theorem applies without an endpoint problem.

The closed near-one piece and the closed piece above residual two are
compact separately.  One common target threshold patches their genuine
two-sided estimates.  The continuous target is exactly the existing
`P1FourthNearOneKernel.closedUpper`, so no second extension is introduced.
The full compact and quotient suppliers require only `u <= beta` and retain
the exact singular series, logarithm, cap and quotient level.

This candidate depends on the separate source-only kernel module named in
the imports.  No compiler, audit, numerical replay, Git operation or actual
source edit was run for this file.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory
open OriginalU2CoupledRecurrenceSourceOnly

/-- On the closed near-one branch the continuous target is exactly the
same rational normalization as the cube-reduced actual density. -/
theorem p1_normalized_closedUpper_initial
    (beta u : ℝ) (hu : 0 < u) (hbeta : 0 < beta) (hbetaU : beta ≤ 2 * u) :
    (2 * Real.exp (-Real.eulerMascheroniConstant) / u) *
      P1FourthNearOneKernel.closedUpper (beta / u) = 4 / beta := by
  have hs2 : beta / u ≤ 2 := (div_le_iff₀ hu).mpr hbetaU
  rw [P1FourthNearOneKernel.closedUpper, if_pos hs2]
  calc
    (2 * Real.exp (-Real.eulerMascheroniConstant) / u) * (A / (beta / u)) =
        ((2 * Real.exp (-Real.eulerMascheroniConstant)) * A) / beta := by
      field_simp [hu.ne', hbeta.ne'] <;> ring
    _ = 4 / beta := by rw [P1FourthNearOneKernel.normalization]

/-- The exact first-cube reduction upgrades the existing residual-three
compact supplier to every compact set with `0 < beta <= 3*u`, including
all residuals at and below one.  Both sides of the error are supplied by
the proved compact theorem after an actual density identity. -/
theorem exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ 0 < p.1 ∧ p.1 ≤ 3 * p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
            Real.log (N : ℝ) / singularSeries N - 4 / p.1| < eta := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 / 3)
  let U : Set (ℝ × ℝ) := f '' T
  have hf : Continuous f := continuous_fst.prodMk (continuous_fst.div_const 3)
  have hU : IsCompact U := hT.image hf
  have hUparam : ∀ q ∈ U, 0 < q.2 ∧ q.2 < q.1 ∧ q.1 ≤ 3 * q.2 := by
    rintro q ⟨p, hp, rfl⟩
    have hbeta := (hparam p hp).2.1
    change 0 < p.1 / 3 ∧ p.1 / 3 < p.1 ∧ p.1 ≤ 3 * (p.1 / 3)
    constructor
    · positivity
    constructor <;> linarith
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_actualSmallRosserPlusDensity_initial_compact_normalized_threshold
      U hU hUparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have hNreal : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hcapReduced : (N : ℝ) ^ (p.1 / 3) ≤ (cap : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNreal.le
      (by linarith [(hparam p hp).2.2])).trans hcap
  have h := hbound N hN hEven (f p) (Set.mem_image_of_mem f hp) cap hcapReduced
  change |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ (p.1 / 3))
      ((N : ℝ) ^ p.1) * Real.log (N : ℝ) / singularSeries N - 4 / p.1| < eta at h
  rw [actualSmallRosserPlusDensity_power_eq_cubeCutoff N cap hNreal
    (hparam p hp).2.2]
  exact h

/-- The actual normalized upper density has a genuine two-sided uniform
supplier on every compact set in the CLOSED residual domain `u <= beta`.
No strict margin above one is present.  The two closed parameter pieces
use the same real coefficient and the same normalization. -/
theorem exists_p1_actualSmallRosserPlusDensity_closed_residual_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ p.1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ T, ∀ cap : ℕ, (N : ℝ) ^ p.2 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.2) ((N : ℝ) ^ p.1) *
            Real.log (N : ℝ) / singularSeries N -
          (2 * Real.exp (-Real.eulerMascheroniConstant) / p.2) *
            P1FourthNearOneKernel.closedUpper (p.1 / p.2)| < eta := by
  let Tlo : Set (ℝ × ℝ) := T ∩ {p : ℝ × ℝ | p.1 ≤ 2 * p.2}
  let Thi : Set (ℝ × ℝ) := T ∩ {p : ℝ × ℝ | 2 * p.2 ≤ p.1}
  have hloClosed : IsClosed {p : ℝ × ℝ | p.1 ≤ 2 * p.2} :=
    isClosed_le continuous_fst (continuous_const.mul continuous_snd)
  have hhiClosed : IsClosed {p : ℝ × ℝ | 2 * p.2 ≤ p.1} :=
    isClosed_le (continuous_const.mul continuous_snd) continuous_fst
  have hTlo : IsCompact Tlo := hT.inter_right hloClosed
  have hThi : IsCompact Thi := hT.inter_right hhiClosed
  have hloParam : ∀ p ∈ Tlo, 0 < p.2 ∧ 0 < p.1 ∧ p.1 ≤ 3 * p.2 := by
    intro p hp
    have hu := (hparam p hp.1).1
    have hub := (hparam p hp.1).2
    exact ⟨hu, hu.trans_le hub, by linarith [hp.2]⟩
  have hhiParam : ∀ p ∈ Thi, 0 < p.2 ∧ p.2 < p.1 := by
    intro p hp
    have hu := (hparam p hp.1).1
    exact ⟨hu, by linarith [hp.2]⟩
  obtain ⟨L, hL, hlo⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold
      Tlo hTlo hloParam eta heta
  obtain ⟨H, _hH, hhi⟩ :=
    exists_actualSmallRosserPlusDensity_residual_compact_normalized_threshold
      Thi hThi hhiParam eta heta
  refine ⟨max L H, hL.trans (le_max_left _ _), ?_⟩
  intro N hN hEven p hp cap hcap
  have hu := (hparam p hp).1
  have hbeta : 0 < p.1 := hu.trans_le (hparam p hp).2
  by_cases hpLo : p.1 ≤ 2 * p.2
  · have h := hlo N ((le_max_left _ _).trans hN) hEven p ⟨hp, hpLo⟩ cap hcap
    rw [p1_normalized_closedUpper_initial p.1 p.2 hu hbeta hpLo]
    exact h
  · have hpHi : 2 * p.2 ≤ p.1 := le_of_not_ge hpLo
    have h := hhi N ((le_max_right _ _).trans hN) hEven p ⟨hp, hpHi⟩ cap hcap
    have hs : 1 < p.1 / p.2 := (one_lt_div hu).mpr (by linarith)
    rw [P1FourthNearOneKernel.closedUpper_eq_actual hs]
    exact h

/-- Parameter form with `(u,s)`, valid uniformly on arbitrary compact
sets with `u > 0` and `s >= 1`, including any closed strip `[1,S]`. -/
theorem exists_p1_actualSmallRosserPlusDensity_closed_compact_normalized_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 ≤ p.2)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
            ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N -
          (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
            P1FourthNearOneKernel.closedUpper p.2| < eta := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 * p.1, p.1)
  let T : Set (ℝ × ℝ) := f '' S
  have hf : Continuous f := (continuous_snd.mul continuous_fst).prodMk continuous_fst
  have hT : IsCompact T := hS.image hf
  have hTparam : ∀ q ∈ T, 0 < q.2 ∧ q.2 ≤ q.1 := by
    rintro q ⟨p, hp, rfl⟩
    have hu := (hparam p hp).1
    have hs := (hparam p hp).2
    change 0 < p.1 ∧ p.1 ≤ p.2 * p.1
    refine ⟨hu, ?_⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hu.le
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_residual_compact_normalized_threshold
      T hT hTparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  have h := hbound N hN hEven (f p) (Set.mem_image_of_mem f hp) cap hcap
  change |actualSmallRosserPlusDensity N cap ((N : ℝ) ^ p.1)
      ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N -
    (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
      P1FourthNearOneKernel.closedUpper ((p.2 * p.1) / p.1)| < eta at h
  simpa only [mul_div_cancel_right₀ _ (hparam p hp).1.ne'] using h

/-- Uniform convergence of the literal normalized actual coefficients to
the continuous closed upper profile.  Covering caps may vary with both
the target and the parameters. -/
theorem tendstoUniformlyOn_p1_actualSmallRosserPlusDensity_closed_normalized
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 ≤ p.2)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserPlusDensity N (cap N p) ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N)
      (fun p => (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
        P1FourthNearOneKernel.closedUpper p.2)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨N0, _hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_compact_normalized_threshold
      S hS hparam eta heta
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      N0 ≤ N := (eventually_ge_atTop N0).filter_mono inf_le_left
  have heven : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      0 < N ∧ Even N := by
    simp only [Filter.eventually_inf_principal]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [hlarge, heven, hcap] with N hN hEven hcapN
  intro p hp
  simpa only [Real.dist_eq, abs_sub_comm] using
    hbound N hN hEven.2 p hp (cap N p) (hcapN p hp)

/-- The closed compact supplier at the exact quotient parameters.  This
retains the original `N^lambda / P` level and its strict natural ceiling;
the legality assumption is non-strict at `s = 1`. -/
theorem exists_p1_actualSmallRosserPlusDensity_closed_quotient_compact_normalized_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hparam : ∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ p.1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ P y lambda : ℝ, 0 < P → 0 < y →
        actualRosserQuotientParameters (N : ℝ) P y lambda ∈ T →
        ∀ cap : ℕ, y ≤ (cap : ℝ) →
          |actualSmallRosserPlusDensity N cap y ((N : ℝ) ^ lambda / P) *
              Real.log (N : ℝ) / singularSeries N -
            (2 * Real.exp (-Real.eulerMascheroniConstant) /
                (actualRosserQuotientParameters (N : ℝ) P y lambda).2) *
              P1FourthNearOneKernel.closedUpper
                ((actualRosserQuotientParameters (N : ℝ) P y lambda).1 /
                  (actualRosserQuotientParameters (N : ℝ) P y lambda).2)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_residual_compact_normalized_threshold
      T hT hparam eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven P y lambda hP hy hparamN cap hcap
  have hNreal : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  obtain ⟨hlevel, hcut⟩ :=
    actualRosserQuotientParameters_exact (N : ℝ) P y lambda hNreal hP hy
  have h := hbound N hN hEven (actualRosserQuotientParameters (N : ℝ) P y lambda)
    hparamN cap (by simpa only [hcut] using hcap)
  simpa only [hlevel, hcut] using h

end

end ImbalancedChen
