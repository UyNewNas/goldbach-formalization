import ImbalancedChen.Part3WeightedPrimeIntervalSW
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A frozen C1 profile is evaluated at n/T, on the literal real interval
(u,v] inside [T,2T]. Its derivative has size D/T and the physical interval
has length at most T. Thus the derivative integral costs D, uniformly in
the moving scale and endpoints. Compactness supplies M,D from the actual
profile on [1,2]; no weighted SW or coefficient-distribution input occurs.
-/

namespace ImbalancedChen.Part3.ScaledPrimeProfileSW20261026b

noncomputable section
open Classical Finset MeasureTheory
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open WeightedPrimeIntervalSW20261026b

def scaledProfile (Phi : ℝ → ℝ) (T x : ℝ) : ℝ := Phi (x/T)

theorem scaledProfile_hasDerivAt {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) (T x : ℝ) :
    HasDerivAt (scaledProfile Phi T) (deriv Phi (x/T)/T) x := by
  have hd : Differentiable ℝ Phi := hPhi.differentiable (by norm_num)
  simpa only [scaledProfile, one_div, div_eq_mul_inv] using
    (hd (x/T)).hasDerivAt.comp x ((hasDerivAt_id x).div_const T)

theorem deriv_scaledProfile {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) (T x : ℝ) :
    deriv (scaledProfile Phi T) x = deriv Phi (x/T)/T :=
  (scaledProfile_hasDerivAt hPhi T x).deriv

theorem continuous_deriv_scaledProfile {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) (T : ℝ) :
    Continuous (deriv (scaledProfile Phi T)) := by
  have heq : deriv (scaledProfile Phi T) = fun x => deriv Phi (x/T)/T :=
    funext (deriv_scaledProfile hPhi T)
  rw [heq]
  exact ((hPhi.continuous_deriv_one).comp (continuous_id.div_const T)).div_const T

private theorem normalized_mem {T u v t : ℝ} (hT : 0 < T)
    (hTu : T ≤ u) (hv : v ≤ 2*T) (ht : t ∈ Set.Icc u v) :
    t/T ∈ Set.Icc (1 : ℝ) 2 := by
  constructor
  · exact (le_div_iff₀ hT).mpr (by linarith [ht.1])
  · exact (div_le_iff₀ hT).mpr (ht.2.trans hv)

/-- The actual Abel multiplier of a scaled profile is bounded by its
fixed C1 norm on the normalized interval. Both endpoints are retained. -/
theorem scaledProfile_variation_le {Phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ 1 Phi) {M D T u v : ℝ}
    (hM : ∀ y ∈ Set.Icc (1 : ℝ) 2, |Phi y| ≤ M)
    (hD : ∀ y ∈ Set.Icc (1 : ℝ) 2, |deriv Phi y| ≤ D)
    (hD0 : 0 ≤ D) (hT : 0 < T) (hTu : T ≤ u) (huv : u ≤ v)
    (hv : v ≤ 2*T) :
    |scaledProfile Phi T v| +
      (∫ t in Set.Ioc u v, |deriv (scaledProfile Phi T) t|) ≤ M+D := by
  have hend : |scaledProfile Phi T v| ≤ M :=
    hM _ (normalized_mem hT hTu hv ⟨huv,le_rfl⟩)
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioc u v) :
      |deriv (scaledProfile Phi T) t| ≤ D/T := by
    rw [deriv_scaledProfile hPhi, abs_div, abs_of_pos hT]
    exact div_le_div_of_nonneg_right
      (hD _ (normalized_mem hT hTu hv ⟨ht.1.le,ht.2⟩)) hT.le
  have hfi : IntegrableOn (fun t => |deriv (scaledProfile Phi T) t|)
      (Set.Ioc u v) := by
    simpa only [Real.norm_eq_abs] using
      ((continuous_deriv_scaledProfile hPhi T).norm.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self)
  have hconst : IntegrableOn (fun _ : ℝ => D/T) (Set.Ioc u v) :=
    continuous_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hInt : (∫ t in Set.Ioc u v, |deriv (scaledProfile Phi T) t|) ≤ D := by
    calc
      _ ≤ ∫ _t in Set.Ioc u v, D/T :=
        setIntegral_mono_on hfi hconst measurableSet_Ioc hpoint
      _ = (v-u)*(D/T) := by
        rw [← intervalIntegral.integral_of_le huv, intervalIntegral.integral_const,
          smul_eq_mul]
      _ ≤ T*(D/T) := mul_le_mul_of_nonneg_right
        (by linarith : v-u ≤ T) (div_nonneg hD0 hT.le)
      _ = D := by field_simp [hT.ne']
  exact add_le_add hend hInt

/-- Every fixed C1 dyadic profile supplies a true prime SW family. The
constant precedes the scale, both real endpoints and every d,h,b. -/
theorem scaled_prime_profile_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T u v : ℝ,
      1 ≤ T → T ≤ u → u ≤ v → v ≤ 2*T →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (primeSWInterval u v)
        (weightedPrimeCoefficient (scaledProfile Phi T)) d h b| ≤
        C*T*(fouvryTau 2 h : ℝ) / Real.log (2*T)^B := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous.continuousOn
  obtain ⟨D0,hD0⟩ := (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 2)).exists_bound_of_continuousOn
    hPhi.continuous_deriv_one.continuousOn
  let M : ℝ := max M0 1
  let D : ℝ := max D0 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hD1 : 1 ≤ D := le_max_right _ _
  have hM (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : |Phi y| ≤ M := by
    have hh : |Phi y| ≤ M0 := by simpa only [Real.norm_eq_abs] using hM0 y hy
    exact hh.trans (le_max_left _ _)
  have hD (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2) : |deriv Phi y| ≤ D := by
    have hh : |deriv Phi y| ≤ D0 := by simpa only [Real.norm_eq_abs] using hD0 y hy
    exact hh.trans (le_max_left _ _)
  obtain ⟨C,hC,hSW⟩ := weighted_prime_interval_SW B
  refine ⟨C*(M+D),mul_pos hC (by linarith),?_⟩
  intro T u v hT hTu huv hv d h hd hh b hb
  have hTpos : 0 < T := by linarith
  have hvar := scaledProfile_variation_le hPhi hM hD
    (by linarith : 0 ≤ D) hTpos hTu huv hv
  have hraw := hSW T u v hT hTu huv hv (scaledProfile Phi T)
    (fun t ht => (scaledProfile_hasDerivAt hPhi T t).differentiableAt)
    (continuous_deriv_scaledProfile hPhi T).integrableOn_Icc d h hd hh b hb
  have hlog : 0 < Real.log (2*T) := Real.log_pos (by linarith)
  have hE : 0 ≤ C*T*(fouvryTau 2 h : ℝ) / Real.log (2*T)^B := by positivity
  calc
    _ ≤ _ := hraw
    _ ≤ (C*T*(fouvryTau 2 h : ℝ) / Real.log (2*T)^B)*(M+D) :=
      mul_le_mul_of_nonneg_left hvar hE
    _ = _ := by ring

end
end ImbalancedChen.Part3.ScaledPrimeProfileSW20261026b
