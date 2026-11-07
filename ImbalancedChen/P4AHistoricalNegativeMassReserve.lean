import ImbalancedChen.P4AHistoricalSameRhoAttachment
import ImbalancedChen.P4AHistoricalOneReserveDifference

/-!
# P4A: direct reserve for the negative-mass attachment correction

The correction is controlled directly by the actual small Rosser gap and
the actual absolute rough-mass envelope. No difference of two attachment
error estimates is used. The same epsilon precedes both policies, target,
cap, and large threshold. For fixed epsilon the scalar envelope has an
exponential floor; only the epsilon-first arbitrary-reserve statement is
asserted. Presieve projection corrections remain exact finite sums.

SOURCE ONLY: this candidate and its draft imports have not been compiled.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators

theorem p4aNegativeRoughMass_le_absoluteDensity
    (S : Finset ℕ) (c : ℕ → ℝ) :
    p4aNegativeRoughMass S c ≤ reciprocalTotientDensity S (fun d => |c d|) := by
  unfold p4aNegativeRoughMass reciprocalTotientDensity
  apply Finset.sum_le_sum
  intro d _hd
  by_cases hc : 0 ≤ c d
  · rw [if_pos hc]
    exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  · rw [if_neg hc, abs_of_nonpos (le_of_not_ge hc)]

/-- Nonnegative masses in the same interval have diameter one envelope. -/
theorem p4a_negativeMassDifference_abs_le
    (SA SB : Finset ℕ) (a b : ℕ → ℝ) (Q : ℝ)
    (hA : reciprocalTotientDensity SA (fun d => |a d|) ≤ Q)
    (hB : reciprocalTotientDensity SB (fun d => |b d|) ≤ Q) :
    |p4aNegativeRoughMass SA a - p4aNegativeRoughMass SB b| ≤ Q := by
  have hAn := p4aNegativeRoughMass_nonneg SA a
  have hBn := p4aNegativeRoughMass_nonneg SB b
  have hAu := (p4aNegativeRoughMass_le_absoluteDensity SA a).trans hA
  have hBu := (p4aNegativeRoughMass_le_absoluteDensity SB b).trans hB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def p4aReserveNegativeMass (retain : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : ℝ :=
  p4aNegativeRoughMass (fixedRoughSupport retain N cap w z)
    (fixedRoughCoefficient retain N cap w z)

def p4aNegativeMassCorrection (old new : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  (p4aReserveNegativeMass old N cap w z - p4aReserveNegativeMass new N cap w z) *
    (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
      HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L)

/-- The attachment defect consists of a signed raw-density term and the
literal negative-mass correction, with one shared small Rosser gap. -/
theorem p4a_physicalDifference_sub_eulerRaw_eq
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    (p4aReservePhysicalDensity old N cap w z L -
        p4aReservePhysicalDensity new N cap w z L) -
      actualSmallEulerProduct N cap w *
        (p4aReserveRawDensity old N cap w z - p4aReserveRawDensity new N cap w z) =
    (p4aReserveRawDensity old N cap w z - p4aReserveRawDensity new N cap w z) *
      (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
        actualSmallEulerProduct N cap w) +
      p4aNegativeMassCorrection old new N cap w z L := by
  unfold p4aReservePhysicalDensity
  rw [actualSmallRoughRho_density_eq, actualSmallRoughRho_density_eq,
    p4a_signSensitiveDensity_eq_raw_add_negativeMass,
    p4a_signSensitiveDensity_eq_raw_add_negativeMass]
  unfold p4aReserveRawDensity p4aNegativeMassCorrection p4aReserveNegativeMass
    HistoricalPrefixCapData.p4aSmallPlusDensity
    HistoricalPrefixCapData.p4aSmallMinusDensity
  ring

/-- Projection is separate from the small-weight defect. In particular no
small reserve for the projection-correction difference is inferred. -/
theorem p4a_physicalDifference_sub_fullRaw_eq
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hwz : w ≤ z) :
    (p4aReservePhysicalDensity old N cap w z L -
        p4aReservePhysicalDensity new N cap w z L) -
      (p4aReserveRawDensity old N cap 0 z - p4aReserveRawDensity new N cap 0 z) =
    (p4aReserveRawDensity old N cap w z - p4aReserveRawDensity new N cap w z) *
      (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
        actualSmallEulerProduct N cap w) +
      p4aNegativeMassCorrection old new N cap w z L -
      (p4aActualPresieveCorrection old N cap w z -
        p4aActualPresieveCorrection new N cap w z) := by
  have hphysical := p4a_physicalDifference_sub_eulerRaw_eq old new N cap w z L
  have hprojection := p4a_presievedDifference_eq_full_sub_corrections
    old new N cap w z hwz
  linarith

/-- The same exact formula at the manuscript normalization. The projection
term remains visible with its own sign and normalization. -/
theorem p4a_physicalDifference_sub_fullRaw_normalized_eq
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hwz : w ≤ z) :
    ((p4aReservePhysicalDensity old N cap w z L -
        p4aReservePhysicalDensity new N cap w z L) -
      (p4aReserveRawDensity old N cap 0 z - p4aReserveRawDensity new N cap 0 z)) *
        Real.log (N : ℝ) / singularSeries N =
    (p4aReserveRawDensity old N cap w z - p4aReserveRawDensity new N cap w z) *
      (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
        actualSmallEulerProduct N cap w) * Real.log (N : ℝ) / singularSeries N +
      p4aNegativeMassCorrection old new N cap w z L *
        Real.log (N : ℝ) / singularSeries N -
      (p4aActualPresieveCorrection old N cap w z -
        p4aActualPresieveCorrection new N cap w z) *
        Real.log (N : ℝ) / singularSeries N := by
  rw [p4a_physicalDifference_sub_fullRaw_eq old new N cap w z L hwz]
  ring

/-- Direct finite estimate; its premises will be supplied by the actual
Rosser sandwich and the actual rough envelope, not by a target-error premise. -/
theorem p4a_negativeMassCorrection_abs_le_gap_envelope
    (old new : List ℕ → Bool) (N cap : ℕ) (w z L V E Q : ℝ)
    (hgap0 : 0 ≤ HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
      HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L)
    (hgap : HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
      HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L ≤ 2 * V * E)
    (hA : reciprocalTotientDensity (fixedRoughSupport old N cap w z)
      (fun d => |fixedRoughCoefficient old N cap w z d|) ≤ Q)
    (hB : reciprocalTotientDensity (fixedRoughSupport new N cap w z)
      (fun d => |fixedRoughCoefficient new N cap w z d|) ≤ Q) :
    |p4aNegativeMassCorrection old new N cap w z L| ≤ (2 * V * E) * Q := by
  have hmass := p4a_negativeMassDifference_abs_le _ _ _ _ Q hA hB
  have hQ : 0 ≤ Q := (abs_nonneg _).trans hmass
  unfold p4aNegativeMassCorrection p4aReserveNegativeMass
  rw [abs_mul, abs_of_nonneg hgap0]
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hmass hgap0).trans
    (mul_le_mul_of_nonneg_left hgap hQ)

/-- The real fixed-epsilon limit is the limit of the proved envelope.
It is generally nonzero, so this is not a fixed-epsilon vanishing claim. -/
theorem tendsto_p4a_negativeMassCorrection_normalizedEnvelope
    (B C K Krough r epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun D : ℝ => (2 * B / epsilon ^ 2) *
      actualSmallRosserDensityError C K D epsilon * (r / epsilon ^ 2) *
        (1 + Krough / (epsilon ^ 2 * Real.log D))) atTop
      (𝓝 ((2 * B / epsilon ^ 2) * (C * Real.exp (-(1 / epsilon))) *
        (r / epsilon ^ 2))) := by
  exact tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope
    (2 * B) C K Krough r epsilon hepsilon

/-- Positivity of the envelope's floor does not assert positivity of the
actual correction; it records why this supplier cannot prove fixed-epsilon o(1). -/
theorem p4a_negativeMassCorrection_normalizedEnvelope_floor_pos
    (B C r epsilon : ℝ) (hB : 0 < B) (hC : 0 < C)
    (hr : 0 < r) (hepsilon : 0 < epsilon) :
    0 < (2 * B / epsilon ^ 2) * (C * Real.exp (-(1 / epsilon))) *
      (r / epsilon ^ 2) := by
  positivity

/-- Epsilon is chosen before the target, cap, and pair of policies. The
proof multiplies the actual Rosser gap by the actual negative-mass diameter. -/
theorem exists_p4a_negativeMassCorrection_le_normalized_reserve
    (r eta epsilonMax : ℝ) (hr : 0 < r) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ N cap : ℕ, 0 < N → Even N →
          D ^ (epsilon ^ 2) ≤ (cap : ℝ) → ∀ old new : List ℕ → Bool,
            |p4aNegativeMassCorrection old new N cap
              (D ^ (epsilon ^ 2)) (D ^ r) (D ^ epsilon)| ≤
                eta * singularSeries N / Real.log D := by
  obtain ⟨B, _hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, _hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  obtain ⟨Krough, hKrough, hrough⟩ :=
    exists_fixedRoughAbsoluteDensity_le_powerParameters
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, hfloor⟩ :=
    exists_normalizedSmallRosser_epsilon_absorbing (2 * B) C r eta epsilonMax
      hr heta hepsilonMax
  have hlimit := tendsto_p4a_negativeMassCorrection_normalizedEnvelope
    B C K Krough r epsilon hepsilon
  have hsmall : ∀ᶠ D : ℝ in atTop,
      (2 * B / epsilon ^ 2) * actualSmallRosserDensityError C K D epsilon *
        (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) < eta :=
    (tendsto_order.1 hlimit).2 eta hfloor
  obtain ⟨Dscalar, hDscalar⟩ := eventually_atTop.mp
    (hsmall.and (eventually_four_le_smallRosserPower epsilon hepsilon))
  obtain ⟨Dsieve, hDsieve, hsieve⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Dsieve Dscalar, hDsieve.trans (le_max_left _ _), ?_⟩
  intro D hD N cap hNpos hN hcap old new
  have hDs : Dsieve ≤ D := (le_max_left _ _).trans hD
  have hDt : Dscalar ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := by linarith
  have hDpos : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hV := actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hN
  have hVbound := hEuler N cap hNpos hN (D ^ (epsilon ^ 2))
    (hDscalar D hDt).2 hcap
  rw [Real.log_rpow hDpos] at hVbound
  have hE : 0 ≤ actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have hQ : 0 ≤ (r / epsilon ^ 2) *
      (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
    have : 0 < Krough := by linarith
    positivity
  have hs := hsieve D hDs N cap hN
  dsimp only at hs
  have hgap0 : 0 ≤ HistoricalPrefixCapData.p4aSmallPlusDensity N cap
      (D ^ (epsilon ^ 2)) (D ^ epsilon) -
      HistoricalPrefixCapData.p4aSmallMinusDensity N cap
        (D ^ (epsilon ^ 2)) (D ^ epsilon) := by
    change 0 ≤ actualSmallRosserPlusDensity N cap _ _ -
      actualSmallRosserMinusDensity N cap _ _
    linarith [hs.2.1, hs.2.2.1]
  have hgap : HistoricalPrefixCapData.p4aSmallPlusDensity N cap
      (D ^ (epsilon ^ 2)) (D ^ epsilon) -
      HistoricalPrefixCapData.p4aSmallMinusDensity N cap
        (D ^ (epsilon ^ 2)) (D ^ epsilon) ≤
      2 * actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon := by
    exact hs.2.2.2.2
  have hbound := p4a_negativeMassCorrection_abs_le_gap_envelope old new N cap
    (D ^ (epsilon ^ 2)) (D ^ r) (D ^ epsilon)
    (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)))
    (actualSmallRosserDensityError C K D epsilon)
    ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))
    hgap0 hgap
    (hrough old N cap hN D epsilon r hD1 hepsilon hepsilonr)
    (hrough new N cap hN D epsilon r hD1 hepsilon hepsilonr)
  have hnorm : 0 ≤ singularSeries N / Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  calc
    |p4aNegativeMassCorrection old new N cap
        (D ^ (epsilon ^ 2)) (D ^ r) (D ^ epsilon)| ≤
      (2 * actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
        ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D))) := hbound
    _ = actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
      (2 * actualSmallRosserDensityError C K D epsilon *
        ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))) := by ring
    _ ≤ (B * singularSeries N / (epsilon ^ 2 * Real.log D)) *
      (2 * actualSmallRosserDensityError C K D epsilon *
        ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))) :=
      mul_le_mul_of_nonneg_right hVbound (by positivity)
    _ = (singularSeries N / Real.log D) *
      ((2 * B / epsilon ^ 2) * actualSmallRosserDensityError C K D epsilon *
        (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D))) := by
      field_simp
      <;> ring
    _ ≤ (singularSeries N / Real.log D) * eta :=
      mul_le_mul_of_nonneg_left (hDscalar D hDt).1.le hnorm
    _ = eta * singularSeries N / Real.log D := by ring

/-- The manuscript target scale, with the full rough cutoff covered. -/
theorem exists_p4a_negativeMassCorrection_le_target_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ old new : List ℕ → Bool,
            |p4aNegativeMassCorrection old new N cap
              ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
                ((N : ℝ) ^ (nu * epsilon))| ≤
              eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      D₀, _hD₀, hbound⟩ := exists_p4a_negativeMassCorrection_le_normalized_reserve
    r (eta * nu) epsilonMax hr (mul_pos heta hnu) hepsilonMax
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge, hNlarge⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop D₀))
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Nlarge 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap old new
  have hNlarge' : Nlarge ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNnonneg : (0 : ℝ) ≤ N := hNposR.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwcap : ((N : ℝ) ^ nu) ^ (epsilon ^ 2) ≤ (cap : ℝ) := by
    rw [← Real.rpow_mul hNnonneg]
    exact (Real.rpow_le_rpow_of_exponent_le hN1
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)).trans hcap
  have h := hbound ((N : ℝ) ^ nu) (hNlarge N hNlarge')
    N cap hNpos hEven hwcap old new
  simp only [← Real.rpow_mul hNnonneg, Real.log_rpow hNposR] at h
  have hcancel : (eta * nu) * singularSeries N / (nu * Real.log (N : ℝ)) =
      eta * singularSeries N / Real.log (N : ℝ) := by
    field_simp [ne_of_gt hnu]
  rw [hcancel] at h
  exact h

/-- Literal normalized correction; the shared epsilon and threshold still
precede both policies. This follows from the direct correction supplier. -/
theorem exists_p4a_negativeMassCorrection_normalized_abs_le
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ old new : List ℕ → Bool,
            |p4aNegativeMassCorrection old new N cap
                ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
                ((N : ℝ) ^ (nu * epsilon)) *
              Real.log (N : ℝ) / singularSeries N| ≤ eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_negativeMassCorrection_le_target_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap old new
  have h := hbound N hN hEven cap hcap old new
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hS := singularSeries_pos N
  rw [abs_div, abs_mul, abs_of_pos hlog, abs_of_pos hS]
  apply (div_le_iff₀ hS).mpr
  have h' := mul_le_mul_of_nonneg_right h hlog.le
  have hcancel : (eta * singularSeries N / Real.log (N : ℝ)) *
      Real.log (N : ℝ) = eta * singularSeries N := by
    field_simp [ne_of_gt hlog]
  rw [hcancel] at h'
  exact h'

namespace HistoricalPrefixCapData

/-- Directly exposes the two terms in the historical attachment defect. -/
theorem p4a_historicalPhysicalDifference_sub_eulerRaw_eq
    (D : HistoricalPrefixCapData) (oldStage newStage : P4AHistoricalStage)
    (N cap : ℕ) (w z L : ℝ) :
    (D.p4aHistoricalPhysicalDensity oldStage N cap w z L -
        D.p4aHistoricalPhysicalDensity newStage N cap w z L) -
      actualSmallEulerProduct N cap w *
        (D.p4aHistoricalRawDensity oldStage N cap w z -
          D.p4aHistoricalRawDensity newStage N cap w z) =
      (D.p4aHistoricalRawDensity oldStage N cap w z -
        D.p4aHistoricalRawDensity newStage N cap w z) *
          (p4aSmallPlusDensity N cap w L - actualSmallEulerProduct N cap w) +
      (D.p4aHistoricalNegativeMass oldStage N cap w z -
        D.p4aHistoricalNegativeMass newStage N cap w z) *
          (p4aSmallPlusDensity N cap w L - p4aSmallMinusDensity N cap w L) := by
  rw [D.p4a_historicalPhysicalDifference_eq]
  ring

end HistoricalPrefixCapData

/-- The historical stages are supplied by the very same direct reserve,
uniformly in the cap data and in the selected pair of stages. -/
theorem exists_p4a_historicalNegativeMassCorrection_normalized_abs_le
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (D : HistoricalPrefixCapData) (oldStage newStage : P4AHistoricalStage),
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            |(D.p4aHistoricalNegativeMass oldStage N cap w z -
                D.p4aHistoricalNegativeMass newStage N cap w z) *
                (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
                  HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L) *
                Real.log (N : ℝ) / singularSeries N| ≤ eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_negativeMassCorrection_normalized_abs_le
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D oldStage newStage
  exact hbound N hN hEven cap hcap
    (D.p4aHistoricalPolicy (N : ℝ) oldStage false)
    (D.p4aHistoricalPolicy (N : ℝ) newStage false)

end

end ImbalancedChen
