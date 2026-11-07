import ImbalancedChen.P2OriginalElevenNuOmittedPayment
import ImbalancedChen.P5OriginalCommonPositivePresieve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual H positive-presieve caller chooses epsilon ONCE at D=N^nu.
The I omitted payment is then applied to that very epsilon and the same
original policy8, z, rho and Q.  Choosing the auxiliary rough coordinate
r/nu changes neither epsilon nor the physical rough ceiling N^r.
-/
namespace ImbalancedChen.P2OriginalElevenNuPhysicalCaller
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P4AOriginalVariableFifthPhysicalLedger
open P2OriginalElevenCompactGatedPolicy P2OriginalElevenLocalizedFullQDifference
open P2OriginalElevenActualOmittedMeanPayment P2OriginalElevenNuOmittedPayment
open P2OriginalElevenNuDensityEnvelope P5OriginalCommonPositivePresieve

/-- One epsilon, omission index and target threshold for the ACTUAL
positive-presieve physical rho and both original omitted AP sources.
For the archived H caller put r=19/96.  The beta reserve and omitted-mean
reserve remain separate, and the entire AP count remains unpaid. -/
theorem exists_common_presieve_and_original_omission
    (nu r b kappa etaBeta etaMean epsilonMax : ℝ)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hr : 0 < r)
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b)))
    (hetaBeta : 0 < etaBeta) (hetaMean : 0 < etaMean) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      nu*epsilon^2 ≤ r ∧ ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
          ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
            let w := (N : ℝ)^(nu*epsilon^2)
            let z := (N : ℝ)^r
            let L := (N : ℝ)^(nu*epsilon)
            let T := manuscriptHalfProductCutoff kappa N
            1 < w ∧ w ≤ z ∧ w ≤ L ∧ (N : ℝ)^nu ≤ (N : ℝ) ∧
              normalize N (physicalDensitySum (moduli d N cap w z) (rho d N cap w z L)) ≤
                normalize N (raw (policy8 d (N : ℝ)) N cap 0 z)+etaBeta ∧
              |actualDeltaMean d n N cap w z L b T| < etaMean*singularNormalization N ∧
              |realPhysicalDistributionError b N T
                  (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
                  (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) -
                realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L)| <
                |actualDeltaCount d n N cap w z L b T|+etaMean*singularNormalization N := by
  have hnr : nu*(r/nu) = r := by field_simp [hnu.ne'] <;> ring
  obtain ⟨epsilon,he,he8,heMax,her,Nbeta,hNbeta,hbeta⟩ :=
    exists_common_positive_presieve_reserve nu (r/nu) etaBeta epsilonMax
      hnu (div_pos hr hnu) hetaBeta hepsilonMax
  have her' : nu*epsilon^2 ≤ r := by
    calc
      _ ≤ nu*(r/nu) := mul_le_mul_of_nonneg_left her hnu.le
      _ = r := hnr
  obtain ⟨nMean,Nmean,hNmean,hmean⟩ :=
    exists_actual_omitted_nu_mean_payment nu epsilon r b kappa etaMean
      hnu he he8 her' hb hb1 hkappa hgap hetaMean
  obtain ⟨nAP,Nap,hNap,hap⟩ :=
    exists_two_actual_nu_AP_count_reduction nu epsilon r b kappa etaMean
      hnu he he8 her' hb hb1 hkappa hgap hetaMean
  refine ⟨epsilon,he,he8,heMax,her',max nMean nAP,
    max Nbeta (max Nmean Nap),hNbeta.trans (le_max_left _ _),?_⟩
  intro n hn N hN hEven cap hcap d
  have hNb := (le_max_left Nbeta (max Nmean Nap)).trans hN
  have hNm := (le_max_left Nmean Nap).trans ((le_max_right Nbeta (max Nmean Nap)).trans hN)
  have hNa := (le_max_right Nmean Nap).trans ((le_max_right Nbeta (max Nmean Nap)).trans hN)
  have hnm := (le_max_left nMean nAP).trans hn
  have hna := (le_max_right nMean nAP).trans hn
  have hN2 := hNbeta.trans hNb
  have hc : (N : ℝ)^(nu*(r/nu)) ≤ (cap : ℝ) := by simpa only [hnr] using hcap
  have hs := hbeta N hNb hEven cap hc d .eighth
  dsimp only at hs
  simp only [hnr] at hs
  have hphysical := hs.2.2.2.2
  change normalize N (physicalDensitySum
      (moduli d N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r))
      (rho d N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^(nu*epsilon)))) ≤
    normalize N (raw (policy8 d (N : ℝ)) N cap 0 ((N : ℝ)^r))+etaBeta at hphysical
  have hcuts := schedule_cutoffs nu epsilon r hnu hnu1 he he8 her' hN2 hcap
  dsimp only
  exact ⟨hcuts.2.2.1,hcuts.2.2.2.1,hcuts.2.2.2.2.1,hcuts.2.1,
    hphysical,hmean n hnm N hNm hEven cap hcap d,hap n hna N hNa hEven cap hcap d⟩

end
end ImbalancedChen.P2OriginalElevenNuPhysicalCaller
