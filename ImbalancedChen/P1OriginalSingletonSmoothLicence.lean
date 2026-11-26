import ImbalancedChen.P1OriginalSingletonPointwiseData
import ImbalancedChen.P5LicensedOriginalIntegerProfile

open scoped ContDiff

/-!
Historical smooth singleton licence, separated from occurrence derivative budgets.
All nine declaration blocks below retain their exact original bytes and names.
They use the eighteen declarations already owned by P1OriginalSingletonPointwiseData.
Source intervals and complementary historical-provider postimages are recorded in
docs/p1/20261125/p15-original-atlas-proper-power/SMOOTH_EXTRACTION.json.
This source adoption does not assert compilation or mathematical acceptance.
-/

namespace ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators

theorem eta_smooth : ContDiff ℝ ∞ eta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

end
end ImbalancedChen.P5Z.ActualEtaPsiOccurrenceBudget

namespace ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget

theorem chi_smooth : ContDiff ℝ ∞ chi := contDiff_const.sub eta_smooth

theorem chiLog_smooth : ContDiff ℝ ∞ chiLog := chi_smooth.comp Real.contDiff_exp


end
end ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily

namespace ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget ActualSingletonPrimeTestFamily
open LicensedOriginalIntegerProfile

def integerWeight (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℕ) : ℝ :=
  profile beta delta N (fun i => (u i : ℝ))

theorem scaledChi_smooth (delta : ℝ) : ContDiff ℝ ∞ (scaledChi delta) :=
  chiLog_smooth.comp (contDiff_id.div_const delta)

theorem profile_eventually_zero (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ)
    (hu : u 0 ≤ 0) : profile beta delta N =ᶠ[𝓝 u] 0 := by
  by_cases hN : 2 ≤ N
  · have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
    have hopen : IsOpen {x : Fin 1 → ℝ | x 0 < (N : ℝ)^beta} :=
      isOpen_lt (continuous_apply 0) continuous_const
    filter_upwards [hopen.mem_nhds (hu.trans_lt hA)] with x hx
    exact profile_zero_below beta delta hN x hx.le
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem profile_smooth (beta delta : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (profile beta delta N) := by
  by_cases hN : 2 ≤ N
  · apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : 0 < u 0
    · have hlog : ContDiffAt ℝ ∞ (fun x : Fin 1 → ℝ => Real.log (x 0)) u :=
        (Real.contDiffAt_log hu.ne').comp u (contDiff_apply ℝ ℝ 0).contDiffAt
      have hraw := ((eta_smooth.comp
        ((contDiff_apply ℝ ℝ 0).div_const _)).contDiffAt).mul
        ((scaledChi_smooth delta).contDiffAt.comp u (hlog.sub contDiffAt_const))
      have hopen : IsOpen {x : Fin 1 → ℝ | 0 < x 0} :=
        isOpen_lt continuous_const (continuous_apply 0)
      have heq : profile beta delta N =ᶠ[𝓝 u]
          (fun x => eta (x 0 / (N : ℝ)^beta) *
            scaledChi delta (Real.log (x 0) - Real.log (N : ℝ))) := by
        filter_upwards [hopen.mem_nhds hu] with x hx
        simp only [profile, if_pos hN, if_pos hx]
      exact hraw.congr_of_eventuallyEq heq
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin 1 → ℝ => (0 : ℝ)) u).
        congr_of_eventuallyEq (profile_eventually_zero beta delta N u (le_of_not_gt hu))
  · simp only [profile, if_neg hN]
    exact contDiff_const

def singletonLicence (beta delta : ℝ) (N : ℕ) : Licence 1 (integerWeight beta delta N) where
  ambient := profile beta delta N
  smooth := profile_smooth beta delta N
  agrees_on_primes := by intro u hu; rfl


end
end ImbalancedChen.P5Z.ActualSingletonLogCollarFamily

namespace ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators

def actualLicence (kappa : ℝ) (B N : ℕ) :=
  P5Z.ActualSingletonLogCollarFamily.singletonLicence (1-kappa)
    (P5Z.ActualSingletonLogCollarFamily.logWidth B N) N


end
end ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer
