import ImbalancedChen.P3OriginalU5RoundedCommonParameters
import ImbalancedChen.ActualLowerFirstExitDensityProjection

/-!
# Normalized row-density reserve for the original rounded U5 coefficient

The full-policy projection, exact rough rounding loss and signed beta gap
refer to the same enumeration cap and policy. After beta selects epsilon,
the rough budget absorbs the Euler factor at that epsilon.
-/

namespace ImbalancedChen.P3OriginalU5NormalizedDensityReserve

noncomputable section
open scoped Classical Topology
open Filter
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P2LowerFiniteCellRounding («universe» raw coefficient roundingLoss roundingLoss_exact)
open P2LowerFiniteCellBetaCompiler (raw_density_on_universe)
open P3OriginalU5RoundedCountInsertion (roundedSupport roundedRho)
open P3OriginalU5RoundedCommonParameters (betaGap)
open P3OriginalU5WarmRoundingPayment (exists_uniform_selected_U5_roundingLoss_lt)
open P3OriginalU5RoundedUniformModulusCap (exists_uniform_finer_rounded_U5_modulus_cap)
open P3OriginalU5RoundedBetaReserve (exists_beta_error_le_target_reserve)
open P5OriginalU5CausalFinite
  (attachmentNu attachment_gates cutoff fullDensity pairSupport smallCutoff smallLevel)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- The finite projection loses the small Euler factor times the exact
rough rounding loss, followed by the signed gap of the same rounded rho. -/
theorem fullDensity_sub_roundingLoss_sub_betaGap_le
    (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool)
    (hwz : smallCutoff N epsilon ≤ cutoff N) :
    fullDensity N keep -
        actualSmallEulerProduct N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) *
          roundingLoss keep N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) tau -
        betaGap N epsilon tau keep ≤
      physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau keep) := by
  let cap := Nat.ceil (cutoff N)
  let w := smallCutoff N epsilon
  let z := cutoff N
  let V := actualSmallEulerProduct N cap w
  let A := reciprocalTotientDensity («universe» N cap w z) (raw keep N cap w z)
  let C := reciprocalTotientDensity («universe» N cap w z) (coefficient keep N cap w z tau)
  let D := physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau keep)
  have hproj : fullDensity N keep ≤ V * A := by
    dsimp only [A]
    rw [raw_density_on_universe]
    exact fixedEvenRoughDensity_presieveProjection keep N cap w z hwz
  have hexact : A - C = roundingLoss keep N cap w z tau :=
    roundingLoss_exact keep N cap w z tau
  change fullDensity N keep - V * roundingLoss keep N cap w z tau - (V * C - D) ≤ D
  rw [← hexact]
  calc
    _ ≤ V * A - V * (A - C) - (V * C - D) :=
      sub_le_sub_right (sub_le_sub_right hproj _) _
    _ = D := by ring

/-- One epsilon, fine-mesh bound and target threshold work for every
subsequent even target, original receiver, bank, supported pair and finer
positive mesh. The density and complete-modulus bound use the same rho. -/
theorem exists_rounded_U5_normalized_density_reserve
    (mesh : ℕ) (kappa epsilonMax : ℝ) (hkappa : 0 < kappa) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon < 1 / 272 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → Even N →
          ∀ (R : PairRange) (bank : CandidateBank mesh),
            ∀ t ∈ pairSupport N, ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
              fullDensity N (selectedPolicy R bank (1 / 1000) false N t) -
                  kappa * singularSeries N / Real.log (N : ℝ) ≤
                physicalDensitySum (roundedSupport N epsilon)
                  (roundedRho N epsilon tau (selectedPolicy R bank (1 / 1000) false N t)) ∧
              ∀ k : ℕ, roundedRho N epsilon tau
                  (selectedPolicy R bank (1 / 1000) false N t) k ≠ 0 →
                (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨B, hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  have hproduct : attachmentNu * (417 / 1360 : ℝ) = (417 / 5000 : ℝ) := by
    norm_num [attachmentNu]
  obtain ⟨epsilon, hepsilon, hepsilon8, hrequest, _hepsilonr, Nbeta, hNbeta, hbeta⟩ :=
    exists_beta_error_le_target_reserve attachmentNu (417 / 1360) (kappa / 2)
      (min epsilonMax (1 / 272)) hnu (by norm_num) (half_pos hkappa)
      (lt_min hmax (by norm_num))
  have hepsilonMax := hrequest.trans_le (min_le_left _ _)
  have hepsilon272 := hrequest.trans_le (min_le_right _ _)
  let etaBox := kappa * attachmentNu * epsilon ^ 2 / (2 * B)
  have hetaBox : 0 < etaBox := by
    dsimp only [etaBox]
    positivity
  have halloc : attachmentNu * epsilon ≤ ((1 / 1000 : ℚ) : ℝ) := by
    calc
      attachmentNu * epsilon ≤ attachmentNu * (1 / 272 : ℝ) :=
        mul_le_mul_of_nonneg_left hepsilon272.le hnu.le
      _ = ((1 / 1000 : ℚ) : ℝ) := by norm_num [attachmentNu]
  have hcut : attachmentNu * epsilon ^ 2 < (417 / 5000 : ℝ) := by
    calc
      attachmentNu * epsilon ^ 2 < attachmentNu * (1 / 8 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hepsilon8 hepsilon.le (by norm_num)) hnu
      _ < (417 / 5000 : ℝ) := by norm_num [attachmentNu]
  have hb : (0 : ℚ) ≤ 1 / 1000 := by norm_num
  obtain ⟨tauBox, htauBox, Nbox, _hNbox, hbox⟩ :=
    exists_uniform_selected_U5_roundingLoss_lt mesh epsilon hepsilon hcut etaBox hetaBox
  obtain ⟨tauSupport, htauSupport, hsupport⟩ :=
    exists_uniform_finer_rounded_U5_modulus_cap (1 / 1000) hb le_rfl epsilon hepsilon halloc
  have homega : 0 < attachmentNu * epsilon ^ 2 := mul_pos hnu (pow_pos hepsilon 2)
  have htend : Tendsto (fun N : ℕ => smallCutoff N epsilon) atTop atTop :=
    (tendsto_rpow_atTop homega).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nfour, hfour⟩ := eventually_atTop.mp (htend.eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272,
    min tauBox tauSupport, lt_min htauBox htauSupport, max Nbeta (max Nbox Nfour),
    hNbeta.trans (le_max_left _ _), ?_⟩
  intro N hN hEven R bank t ht tau htau hsmall
  have hNb : Nbeta ≤ N := (le_max_left _ _).trans hN
  have hNboxfour : max Nbox Nfour ≤ N := (le_max_right _ _).trans hN
  have hNx : Nbox ≤ N := (le_max_left _ _).trans hNboxfour
  have hNf : Nfour ≤ N := (le_max_right _ _).trans hNboxfour
  have hN2 : 2 ≤ N := hNbeta.trans hNb
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNrpos := zero_lt_one.trans hNr
  let keep := selectedPolicy R bank (1 / 1000) false N t
  let cap := Nat.ceil (cutoff N)
  let V := actualSmallEulerProduct N cap (smallCutoff N epsilon)
  let loss := roundingLoss keep N cap (smallCutoff N epsilon) (cutoff N) tau
  have hwz := (attachment_gates hN2 hepsilon hepsilon8).2.2
  have hV : 0 ≤ V := (actualSmallEulerProduct_pos N cap (smallCutoff N epsilon) hEven).le
  have hVupper : V ≤ B * singularSeries N / ((attachmentNu * epsilon ^ 2) * Real.log (N : ℝ)) := by
    have h := hEuler N cap (by omega) hEven (smallCutoff N epsilon) (hfour N hNf)
      (hwz.trans (Nat.le_ceil _))
    rwa [smallCutoff, Real.log_rpow hNrpos] at h
  have hloss : loss < etaBox := hbox N hNx hEven R bank (1 / 1000) hb le_rfl
    t ht cap tau htau (hsmall.trans (min_le_left _ _))
  have hboxPaid : V * loss ≤ (kappa / 2) * singularSeries N / Real.log (N : ℝ) := by
    calc
      V * loss ≤ V * etaBox := mul_le_mul_of_nonneg_left hloss.le hV
      _ ≤ (B * singularSeries N / ((attachmentNu * epsilon ^ 2) * Real.log (N : ℝ))) *
          etaBox := mul_le_mul_of_nonneg_right hVupper hetaBox.le
      _ = _ := by
        dsimp only [etaBox]
        field_simp [hB.ne', hnu.ne', hepsilon.ne', (Real.log_pos hNr).ne']
  have hcap : (N : ℝ) ^ (attachmentNu * (417 / 1360 : ℝ)) ≤ (cap : ℝ) := by
    rw [hproduct]
    exact Nat.le_ceil _
  have hbetaPaid : betaGap N epsilon tau keep ≤
      (kappa / 2) * singularSeries N / Real.log (N : ℝ) := by
    have h := (hbeta N hNb hEven cap hcap keep tau).2
    rw [hproduct] at h
    exact h
  refine ⟨?_, hsupport tau htau (hsmall.trans (min_le_right _ _)) R mesh bank N hN2 t ht⟩
  have hledger : fullDensity N keep - V * loss - betaGap N epsilon tau keep ≤
      physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau keep) :=
    fullDensity_sub_roundingLoss_sub_betaGap_le N epsilon tau keep hwz
  change fullDensity N keep - kappa * singularSeries N / Real.log (N : ℝ) ≤
    physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau keep)
  have hpaid : V * loss + betaGap N epsilon tau keep ≤
      kappa * singularSeries N / Real.log (N : ℝ) := by
    calc
      _ ≤ (kappa / 2) * singularSeries N / Real.log (N : ℝ) +
          (kappa / 2) * singularSeries N / Real.log (N : ℝ) := add_le_add hboxPaid hbetaPaid
      _ = _ := by ring
  rw [sub_sub] at hledger
  exact (sub_le_sub_left hpaid (fullDensity N keep)).trans hledger

end
end ImbalancedChen.P3OriginalU5NormalizedDensityReserve
