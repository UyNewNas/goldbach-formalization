import ImbalancedChen.P1OriginalSingletonPointwiseData
import ImbalancedChen.P1Full87TrueDPolicyDelta
import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPan

/-!
The three original historical-middle definitions, unchanged. This is a
source-layer separation so that their proper-power comparison can be
checked independently of the remaining smoothing/Atlas providers.
See HISTORICAL_POINTWISE_EXTRACTION.json for exact original byte bindings.
-/
namespace ImbalancedChen.P1Full87HistoricalMiddleSmoothing
noncomputable section
open Classical
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P5CanonicalTentNarrowSingletonTransfer (fullSmoothWeight)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)

def remainingModuli (B : ℝ) (N : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  Q.filter (fun d => panModulusCutoff N B < d ∧ (d : ℝ) < (N : ℝ)^(599/1000 : ℝ))

def smoothRemaining (B kappa : ℝ) (N : ℕ) (Q : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  Part3.primeProductSignedError 1 (2*N) N (remainingModuli B N Q) c
    (fullSmoothWeight kappa 6 N)

def policyRemaining (B kappa : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  smoothRemaining B kappa N (trueDDeltaSupport old fresh N cap w z)
    (trueDDeltaRho old fresh N cap w z L)

end
end ImbalancedChen.P1Full87HistoricalMiddleSmoothing
