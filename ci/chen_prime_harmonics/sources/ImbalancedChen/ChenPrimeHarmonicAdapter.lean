/-
SPDX-License-Identifier: Apache-2.0

HELD, UNCOMPILED CONSUMER CANDIDATE. No Lean/Lake execution, kernel replay,
axiom audit, publication, or owned-core integration was performed here.

Reuses MathlibNt.SieveTheory.Arithmetic.MertensTheorem from the approved
ordinary270 supplier at subfish-zhou/goldbach-lean commit
09b97db5764ade1246bfb77206baa1b124760958. Its 66 production-module closure
is already a subset of ordinary270. The unchanged upstream Apache-2.0
license is retained beside this file. No held742 extension is imported.

This consumer changes neither the supplier theorem nor its analytic proof.
It pays the two endpoint atoms, reciprocal-denominator change, and varying
centre-prime exclusion before applying the genuine continuous-test limit.
-/
import ImbalancedChen.ChenPrimeHarmonicFinite
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

namespace ImbalancedChen.ChenPrimeHarmonicAdapter

noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

/-- The literal single-prime main sum, with [N^a,N^c), the actual primitive
centre mask, and the correct prime totient denominator p-1. -/
def chenSinglePrimeHarmonicSum (f : ℝ → ℝ) (a c : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ c),
    f (Real.log (p : ℝ) / Real.log (N : ℝ)) / ((p : ℝ) - 1)

private theorem log_coordinate_mem_Icc {N p : ℕ} {a c : ℝ}
    (hN : 2 ≤ N) (hpa : (N : ℝ) ^ a ≤ (p : ℝ))
    (hpc : (p : ℝ) ≤ (N : ℝ) ^ c) :
    Real.log (p : ℝ) / Real.log (N : ℝ) ∈ Set.Icc a c := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hp : (0 : ℝ) < p := (Real.rpow_pos_of_pos hNpos a).trans_le hpa
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hNpos a) hpa
  have hhi := Real.log_le_log hp hpc
  rw [Real.log_rpow hNpos a] at hlo
  rw [Real.log_rpow hNpos c] at hhi
  exact ⟨(le_div_iff₀ (Real.log_pos hN1)).mpr hlo,
    (div_le_iff₀ (Real.log_pos hN1)).mpr hhi⟩

/-- The supplier window is exactly (N^a,N^c], including integral endpoints.
The upper exponent gate puts its complete carrier inside the actual prefix. -/
theorem chenPrimeHarmonicSupplierWindow_eq (N : ℕ) (a c : ℝ)
    (hN : 2 ≤ N) (hc : c ≤ 1) :
    chenPrimeHarmonicSupplierWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ c) =
      (Finset.Ioc (MathlibNt.SieveTheory.MertensTheorem.rpowFloor N a)
        (MathlibNt.SieveTheory.MertensTheorem.rpowFloor N c)).filter Nat.Prime := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hupper : (N : ℝ) ^ c ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hc
  ext p
  constructor
  · intro hp
    obtain ⟨hpN, hpa, hpc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨MathlibNt.SieveTheory.MertensTheorem.mem_Ioc_rpowFloor_iff.mpr ⟨hpa, hpc⟩,
        (mem_chenPrimePrefix.mp hpN).2⟩
  · intro hp
    obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpc⟩ := MathlibNt.SieveTheory.MertensTheorem.mem_Ioc_rpowFloor_iff.mp hpI
    have hpN : p ≤ N := by exact_mod_cast hpc.trans hupper
    exact Finset.mem_filter.mpr ⟨mem_chenPrimePrefix.mpr ⟨hpN, hpprime⟩, hpa, hpc⟩

/-- Genuine continuous-test harmonic limit for the actual single-prime
selector. The varying centre exclusions and all three finite corrections
are proved negligible, rather than included as an analytic premise. -/
theorem tendsto_chenSinglePrimeHarmonicSum {a c : ℝ}
    (ha : 0 < a) (hac : a < c) (hc : c ≤ 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a c)) :
    Tendsto (chenSinglePrimeHarmonicSum f a c) atTop
      (𝓝 (∫ u in a..c, f u / u)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ u ∈ Set.Icc a c, |f u| ≤ M := by
    intro u hu
    have huC : |f u| ≤ C := by simpa only [Real.norm_eq_abs] using hC u hu
    exact huC.trans (le_max_left _ _)
  let E : ℕ → ℝ := fun N =>
    (2 * M) * (Real.log (N : ℝ) / Real.log 2) / (N : ℝ) ^ a +
      6 * M / (N : ℝ) ^ a
  have hdecay : Tendsto E atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ =>
        (2 * M / Real.log 2) * ((Real.log (N : ℝ)) ^ 1 / (N : ℝ) ^ a) +
          (6 * M) * ((Real.log (N : ℝ)) ^ 0 / (N : ℝ) ^ a))
        atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        ((tendsto_nat_log_pow_div_rpow 1 ha).const_mul (2 * M / Real.log 2)).add
          ((tendsto_nat_log_pow_div_rpow 0 ha).const_mul (6 * M))
    apply h.congr'
    exact Filter.Eventually.of_forall (fun N => by
      dsimp [E]
      simp only [pow_one, pow_zero]
      ring)
  have hsupplier :=
    MathlibNt.SieveTheory.MertensTheorem.tendsto_weightedPrimeReciprocalLogSum ha hac hf
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  filter_upwards [Metric.tendsto_nhds.mp hsupplier (epsilon / 2) (half_pos hepsilon),
    hdecay.eventually (gt_mem_nhds (half_pos hepsilon)),
    hpower.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (2 : ℕ)]
    with N hs he hA hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hAU : (N : ℝ) ^ a < (N : ℝ) ^ c :=
    Real.rpow_lt_rpow_of_exponent_lt hN1 hac
  have hfinite := chenSinglePrimeHarmonic_difference_le N
    (fun p => f (Real.log (p : ℝ) / Real.log (N : ℝ)))
    (by omega : 0 < N) hA hAU hM
    (fun p _ hpa hpc => hbound _ (log_coordinate_mem_Icc hN hpa hpc))
  rw [chenPrimeHarmonicSupplierWindow_eq N a c hN hc] at hfinite
  change |chenSinglePrimeHarmonicSum f a c N -
      MathlibNt.SieveTheory.MertensTheorem.weightedPrimeReciprocalLogSum f N a c| ≤ E N
    at hfinite
  rw [Real.dist_eq] at hs ⊢
  have htriangle := abs_sub_le (chenSinglePrimeHarmonicSum f a c N)
    (MathlibNt.SieveTheory.MertensTheorem.weightedPrimeReciprocalLogSum f N a c)
    (∫ u in a..c, f u / u)
  linarith

/-- The same limit with the genuine Euler-totient denominator needed by
quotient AP main terms. No prime denominator is replaced approximately. -/
theorem tendsto_chenSinglePrimeTotientLogSum {a c : ℝ}
    (ha : 0 < a) (hac : a < c) (hc : c ≤ 1)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a c)) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ c),
        f (Real.log (p : ℝ) / Real.log (N : ℝ)) / (Nat.totient p : ℝ))
      atTop (𝓝 (∫ u in a..c, f u / u)) := by
  apply (tendsto_chenSinglePrimeHarmonicSum ha hac hc hf).congr'
  apply Filter.Eventually.of_forall
  intro N
  unfold chenSinglePrimeHarmonicSum
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]

end

end ImbalancedChen.ChenPrimeHarmonicAdapter
