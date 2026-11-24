import ImbalancedChen.P5OriginalFifthArchiveFiniteIdentity
import ImbalancedChen.P1ActualVariableFifthFullMean

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The source-specific finite identity transfers the existing proved actual
variable-fifth mean, including its genuine positive-cutoff approximation
and arithmetic small-last-prime tail, to the common-carrier literal
charge. No desired mean or tail bound is assumed. The resulting threshold
is for FIXED source data. It is not uniform in a changing common mesh,
and does not install the original adopted P4 bank, identify all87, or
identify a literal charge with the final beta-attached physical density.
-/
namespace ImbalancedChen.P5OriginalFifthArchiveActualMean
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive
open P5OriginalFifthArchiveFiniteIdentity

def archiveFifthIntegral (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) : ℝ :=
  P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral e chi (refinedMesh q) omega
    rows4 licensed4 (globalOwners e q chi omega) (licensedRows e q chi omega)

theorem tendsto_commonLiteralCharge_actual_integral
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => commonLiteralCharge rows4 licensed4 e q chi omega N (cap N)
        ((N : ℝ) ^ (19 / 96 : ℝ)))
      P1OriginalFifthMovingScaleLimit.evenTargets
      (𝓝 (archiveFifthIntegral rows4 licensed4 e q chi omega)) := by
  have heq : (fun N : ℕ => commonLiteralCharge rows4 licensed4 e q chi omega N (cap N)
      ((N : ℝ) ^ (19 / 96 : ℝ))) =
      (fun N : ℕ => P1ActualVariableFifthGlobalSourceAssembly.normalizedSaving
        e chi (refinedMesh q) omega rows4 licensed4
        (globalOwners e q chi omega) (licensedRows e q chi omega) N (cap N)) := by
    funext N
    exact commonLiteralCharge_eq_normalized_original_saving rows4 licensed4 e q chi omega
      N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
  rw [heq]
  exact P1ActualVariableFifthFullMean.tendsto_normalizedSaving_fullSelectedIntegral
    e he chi (refinedMesh q) omega homega homegaRho rows4 licensed4
    (globalOwners e q chi omega) (licensedRows e q chi omega) cap hcap

/-- A genuine same-charge arithmetic error, paid by the independent full
actual mean theorem rather than included as an input field. -/
theorem eventually_commonLiteralCharge_error
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      |commonLiteralCharge rows4 licensed4 e q chi omega N (cap N)
          ((N : ℝ) ^ (19 / 96 : ℝ)) -
        archiveFifthIntegral rows4 licensed4 e q chi omega| < eta := by
  simpa only [Real.dist_eq] using Metric.tendsto_nhds.1
    (tendsto_commonLiteralCharge_actual_integral rows4 licensed4 e he q chi omega
      homega homegaRho cap hcap) eta heta

end
end ImbalancedChen.P5OriginalFifthArchiveActualMean
