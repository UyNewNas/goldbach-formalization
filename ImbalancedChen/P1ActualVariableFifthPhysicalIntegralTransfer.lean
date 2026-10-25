import ImbalancedChen.P1ActualVariableFifthFullMean
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The same physical counting rho receives the two ACTUAL untruncated
correction integrals with one reserve. Epsilon is chosen before all row
tables; the eventual threshold may depend on their actual integral means.
No upper-density target, numerical certificate or final K is assumed. -/

namespace ImbalancedChen.P1ActualVariableFifthPhysicalIntegralTransfer
noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
open P1OriginalFifthMovingScaleLimit P1ActualVariableFifthFullMean

def totalIntegral (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) : ℝ :=
  P1OriginalVariableFourthFullActiveIntegral.fullActiveIntegral e chi m omega rows4 licensed4 +
    P1ActualVariableFifthUntruncatedDomination.fullSelectedIntegral
      e chi m omega rows4 licensed4 J5 rows5

/-- One physical reserve and the true two-stage analytic correction. The
moduli and coefficient on the left are exactly those in the actual count. -/
theorem exists_attached_normalized_le_originalThird_sub_totalIntegral
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax)
    (hrho : nu * r = (19 / 96 : ℝ)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ r ∧
      ∀ (e : ℚ), 0 ≤ e → ∀ (chi : ℝ) (m : ℕ) (omega : ℝ),
      0 < omega → omega < (19 / 96 : ℝ) →
      logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2 →
      ∀ (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
        (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (cap : ℕ → ℕ),
      (∀ᶠ N : ℕ in evenTargets, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) →
      ∀ᶠ N : ℕ in evenTargets,
        physicalDensitySum
            (attachedUpperModuli nu r epsilon
              (fun N => policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false) cap N)
            (attachedUpperCoefficient nu r epsilon
              (fun N => policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false) cap N) *
            Real.log (N : ℝ) / singularSeries N ≤
          P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
              e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ)) *
              Real.log (N : ℝ) / singularSeries N -
            totalIntegral e chi m omega rows4 licensed4 J5 rows5 + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    N₀, hN₀, hsupply⟩ :=
    P4AOriginalVariableFifthPhysicalLedger.exists_original_fifth_physical_le_causal_ledger
      nu r (eta / 2) epsilonMax hnu hr (by positivity) hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, ?_⟩
  intro e he chi m omega homega homegaRho hmesh rows4 licensed4 J5 rows5 cap hcap
  let L := totalIntegral e chi m omega rows4 licensed4 J5 rows5
  have h4 := P1OriginalVariableFourthFullSourceMean.tendsto_normalizedActualSaving_fullActiveIntegral
    e he chi m omega homega homegaRho hmesh rows4 licensed4 cap hcap
  have h5 := tendsto_normalizedSaving_fullSelectedIntegral
    e he chi m omega homega homegaRho rows4 licensed4 J5 rows5 cap hcap
  have hlow := (h4.add h5).eventually
    (lt_mem_nhds (show L - eta / 2 < L by linarith))
  filter_upwards [hlow, hcap,
    (eventually_ge_atTop N₀).filter_mono (show evenTargets ≤ atTop from inf_le_left),
    (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (eventually_mem_principal _).filter_mono inf_le_right)] with N hl hc hn heN
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hS := singularSeries_pos N
  have hs := hsupply N hn heN.2 (cap N) (by simpa only [hrho] using hc)
    e chi m omega rows4 licensed4 J5 rows5
  dsimp only at hs
  rw [hrho] at hs
  let A := P1OriginalFourthFifthTotalTupleSource.originalThirdRetained
    e chi m omega N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
  let S4 := actualHistoricalFourthSaving (initialPolicy (e : ℝ) m (N : ℝ))
    (rawLevel (e : ℝ) chi m omega (N : ℝ))
    (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows4 licensed4)
    N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
  let S5 := actualFifthSaving e chi m omega rows4 licensed4 J5 rows5
    N (cap N) ((N : ℝ) ^ (19 / 96 : ℝ))
  let P := P4AOriginalVariableFifthPhysicalLedger.physical
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ))
    ((N : ℝ) ^ (nu * epsilon))
  change L - eta / 2 < S4 * Real.log (N : ℝ) / singularSeries N +
    S5 * Real.log (N : ℝ) / singularSeries N at hl
  change P ≤ A - S4 - S5 + (eta / 2) * singularSeries N / Real.log (N : ℝ) at hs
  rw [P4AOriginalVariableFifthPhysicalLedger.counting_attachment_is_same_physical
    e chi m omega rows4 licensed4 J5 rows5 nu r epsilon cap N, hrho]
  have hnorm := mul_le_mul_of_nonneg_right hs (div_nonneg hlog.le hS.le)
  have hright : (A - S4 - S5 + (eta / 2) * singularSeries N / Real.log (N : ℝ)) *
      (Real.log (N : ℝ) / singularSeries N) =
      A * Real.log (N : ℝ) / singularSeries N - S4 * Real.log (N : ℝ) / singularSeries N -
        S5 * Real.log (N : ℝ) / singularSeries N + eta / 2 := by
    field_simp [hlog.ne', hS.ne']
    ring
  rw [hright] at hnorm
  change P * Real.log (N : ℝ) / singularSeries N ≤
    A * Real.log (N : ℝ) / singularSeries N - L + eta
  calc
    _ = P * (Real.log (N : ℝ) / singularSeries N) := by ring
    _ ≤ _ := hnorm
    _ ≤ _ := by linarith

end
end ImbalancedChen.P1ActualVariableFifthPhysicalIntegralTransfer
