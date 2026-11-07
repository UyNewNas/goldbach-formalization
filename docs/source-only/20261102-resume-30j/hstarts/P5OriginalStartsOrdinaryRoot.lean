import ImbalancedChen.P5OriginalStartsCommonBetaCount
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.ActualRosserLowerLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal ordinary ROOT density at the original cap 249/448 (and at
fixed buffered caps) is evaluated from the genuine same-weight lower
Rosser density theorem. This is not the already supplied BV initial mean
whose limiting level is 1/2. At the h start the actual canonical factor
lies in its first interval; at the a start the full canonical factor is
retained. No enhanced h defect is added to either empty-prefix start.
The causal third/fourth/fifth changes are still separate original inputs.
-/

namespace ImbalancedChen.P5OriginalStartsOrdinaryRoot

noncomputable section
open Filter Topology
open scoped Classical
open P5OriginalStartsCommonBetaCount
open MathlibNt.SieveTheory

def plainPolicy (beta : ℝ) (N : ℕ) : List ℕ → Bool :=
  fun pre => decide (ordinaryRosserPrefixAdmissible true ((N:ℝ)^beta) pre)

def plainDensity (beta : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedEvenRoughSupport (plainPolicy beta N) N (commonCap N) 0 z)
    (fixedEvenRoughCoefficient (plainPolicy beta N) N (commonCap N) 0 z)

def ordinaryRootConstant (beta u : ℝ) : ℝ :=
  (2*Real.exp (-Real.eulerMascheroniConstant)/u)*suzukiContinuousLowerFactor (beta/u)

def groupedOrdinaryRootConstant (beta : ℝ) : ℝ :=
  3*ordinaryRootConstant beta (417/5000)+ordinaryRootConstant beta (19/125)

/-- Exact source dictionary for the actual even-exit root. -/
theorem plainDensity_eq_actualRosser {N : ℕ} (hN : 1<N)
    {beta z : ℝ} (hb : 0<beta) (hz : z≤(N:ℝ)^beta) :
    plainDensity beta N z =
      actualSmallRosserMinusDensity N (commonCap N) z ((N:ℝ)^beta) := by
  rw [plainDensity,←evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity]
  have hN1 : (1:ℝ)<N := by exact_mod_cast hN
  have h := firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity
    true N (commonCap N) z ((N:ℝ)^beta) (Real.one_lt_rpow hN1 hb) (fun _ => hz)
  simpa only [ordinaryParityRosserPolicy,if_true,plainPolicy,
    evenFirstExitRetainedPolynomial] using h

/-- The actual root density is supplied analytically, without a limit,
density bound or distribution premise. The common cap is already derived. -/
theorem tendsto_plain_start_density {u beta : ℝ} (hu : 0<u)
    (huH : u≤19/125) (h2u : 2*u≤beta) :
    Tendsto (fun N : ℕ => plainDensity beta N ((N:ℝ)^u)*
      Real.log (N:ℝ)/singularSeries N)
      (atTop ⊓ principal {N : ℕ | 0<N ∧ Even N})
      (𝓝 (ordinaryRootConstant beta u)) := by
  have hb : 0<beta := by linarith
  have hs : 2≤beta/u := (le_div_iff₀ hu).mpr h2u
  have hcap : ∀ᶠ N : ℕ in atTop ⊓ principal {N : ℕ | 0<N ∧ Even N},
      (N:ℝ)^u≤(commonCap N:ℝ) := by
    filter_upwards [(eventually_ge_atTop (1:ℕ)).filter_mono inf_le_left] with N hN
    have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
    exact (Real.rpow_le_rpow_of_exponent_le hN1 huH).trans (Nat.le_ceil _)
  have hlim := tendsto_actualSmallRosserMinusDensity_normalized u hu (beta/u) hs commonCap hcap
  rw [div_mul_cancel₀ beta hu.ne'] at hlim
  change Tendsto _ _ (𝓝 (ordinaryRootConstant beta u)) at hlim
  apply hlim.congr'
  filter_upwards [(eventually_ge_atTop (2:ℕ)).filter_mono inf_le_left] with N hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  rw [plainDensity_eq_actualRosser (by omega : 1<N) hb
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : u≤beta))]

/-- Both genuine root densities, with their original multiplicity 3+1,
converge together. Fixed buffers beta<nu are admitted as well. -/
theorem tendsto_grouped_plain_density {beta : ℝ} (hb : 2*(19/125:ℝ)≤beta) :
    Tendsto (fun N : ℕ =>
      (3*plainDensity beta N (cutoffA N)+plainDensity beta N (cutoffH N))*
        Real.log (N:ℝ)/singularSeries N)
      (atTop ⊓ principal {N : ℕ | 0<N ∧ Even N})
      (𝓝 (groupedOrdinaryRootConstant beta)) := by
  have ha := tendsto_plain_start_density (u:=417/5000) (beta:=beta)
    (by norm_num) (by norm_num) (by linarith only [hb])
  have hh := tendsto_plain_start_density (u:=19/125) (beta:=beta)
    (by norm_num) le_rfl hb
  have hlim := (ha.const_mul 3).add hh
  change Tendsto _ _ (𝓝 (groupedOrdinaryRootConstant beta)) at hlim
  apply hlim.congr'
  exact Eventually.of_forall (fun N => by dsimp [cutoffA,cutoffH]; ring)

/-- A real threshold for the literal nu=249/448 ordinary root, before
the even target. This supplies a root density, not the higher causal
originalGroupedStarts endpoint and not a signed-distribution estimate. -/
theorem original_root_density_threshold (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N : ℕ,N0≤N → Even N →
      |(3*plainDensity ordinaryNu N (cutoffA N)+plainDensity ordinaryNu N (cutoffH N))*
          Real.log (N:ℝ)/singularSeries N-groupedOrdinaryRootConstant ordinaryNu|<eta := by
  have hlim := tendsto_grouped_plain_density (beta:=ordinaryNu) (by norm_num [ordinaryNu])
  have hnear := (Metric.tendsto_nhds.mp hlim) eta heta
  simp only [Real.dist_eq,Filter.eventually_inf_principal,Set.mem_setOf_eq] at hnear
  obtain ⟨T,hT⟩ := eventually_atTop.mp hnear
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro N hN hEven
  exact hT N ((le_max_right _ _).trans hN) ⟨by omega,hEven⟩

/-- Only the h root is in the first lower interval. The a root remains
the full Suzuki source factor; no invalid first-strip substitution occurs. -/
theorem original_h_root_constant :
    ordinaryRootConstant ordinaryNu (19/125) =
      4*Real.log (ordinaryNu/(19/125:ℝ)-1)/ordinaryNu := by
  have hstrip : 2≤ordinaryNu/(19/125:ℝ) ∧ ordinaryNu/(19/125:ℝ)≤4 := by
    norm_num [ordinaryNu]
  rw [ordinaryRootConstant,
    suzukiContinuousLowerFactor_firstInterval_eq _ hstrip.1 hstrip.2,Real.exp_neg]
  field_simp [ordinaryNu,Real.exp_ne_zero] <;> ring

end
end ImbalancedChen.P5OriginalStartsOrdinaryRoot
