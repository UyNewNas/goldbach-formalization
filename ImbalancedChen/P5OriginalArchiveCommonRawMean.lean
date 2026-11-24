import ImbalancedChen.P5OriginalCommonFifthPhysicalCaller
import ImbalancedChen.P5OriginalFifthArchiveActualMean

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The F common-carrier literal mean now has the actual common rough-density
caller proved in G. This is a fixed-data arithmetic convergence/error for
the genuine policy4-minus-policy5 difference, with the original cutoff 0.
The signed beta correction is kept separately in PhysicalCaller. No full
adopted data, changing-mesh compact schedule or reserve is presumed.
-/
namespace ImbalancedChen.P5OriginalArchiveCommonRawMean
noncomputable section
open Filter Topology
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P5OriginalCommonRefinedConstructor
open P4AOriginalVariableFifthPhysicalLedger
open P1HistoricalFifthCommonPolicyInputs
open P5OriginalCommonFifthPhysicalCaller P5OriginalFifthArchiveFiniteIdentity
open P5OriginalFifthArchiveActualMean

def normalizedRawDifference (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) : ℝ :=
  let d := sourceData rows4 licensed4 e q chi omega
  (raw (policy4 d (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) -
    raw (policy5 d (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) *
      Real.log (N : ℝ) / singularSeries N

theorem normalizedRawDifference_eq_literalCharge
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) :
    normalizedRawDifference rows4 licensed4 e q chi omega N cap =
      commonLiteralCharge rows4 licensed4 e q chi omega N cap ((N : ℝ) ^ (19 / 96 : ℝ)) := by
  unfold normalizedRawDifference
  rw [raw_fourth_sub_fifth_eq_actualCharge _ N cap hN,
    normalized_actualCharge_eq_literalCharge]
  rfl

theorem tendsto_actual_common_rawDifference
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => normalizedRawDifference rows4 licensed4 e q chi omega N (cap N))
      P1OriginalFifthMovingScaleLimit.evenTargets
      (𝓝 (archiveFifthIntegral rows4 licensed4 e q chi omega)) := by
  apply (tendsto_commonLiteralCharge_actual_integral rows4 licensed4 e he q chi omega
    homega homegaRho cap hcap).congr'
  filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono
    (show P1OriginalFifthMovingScaleLimit.evenTargets ≤ atTop from inf_le_left)] with N hN
  exact (normalizedRawDifference_eq_literalCharge rows4 licensed4 e q chi omega N (cap N)
    (by exact_mod_cast hN)).symm

theorem eventually_actual_common_rawDifference_error
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      |normalizedRawDifference rows4 licensed4 e q chi omega N (cap N) -
        archiveFifthIntegral rows4 licensed4 e q chi omega| < eta := by
  simpa only [Real.dist_eq] using Metric.tendsto_nhds.1
    (tendsto_actual_common_rawDifference rows4 licensed4 e he q chi omega
      homega homegaRho cap hcap) eta heta

end
end ImbalancedChen.P5OriginalArchiveCommonRawMean
