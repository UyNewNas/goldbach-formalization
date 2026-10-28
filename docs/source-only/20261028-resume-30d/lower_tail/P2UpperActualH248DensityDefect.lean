import ImbalancedChen.P2UpperActualSelectedClampReserve
import ImbalancedChen.P5ZU1011SameRhoNativePrimeBoxDensity
import ImbalancedChen.ActualRosserInitialResidualSaving

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The actual ordinary native rho has its OWN ordinary-F density limit.
An explicit, unpaid density defect is retained when the H248 cost is
inserted into the original count decomposition. On physical queries in
[2,101/50), the ordinary density limit is strictly larger than that cost.
This is a coefficient implementation boundary, not a manuscript counterexample.
-/

namespace ImbalancedChen.P2UpperActualH248DensityDefect

noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open P5Z U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox)
open U1011SameRhoNativePrimeMeanTransport U1011SameRhoNativePrimeBoxDensity
open U1011OriginalSixteenJointNearCapModulusConvolution

def tableCost (n N : ℕ) (eta : ℚ) (t : Four) : ℝ :=
  U1011OriginalSixteenNearCapBoxProfiles.nativeCost
    (selectedPolicy n N t) (ownerBox n N t) eta

def densityScale (N : ℕ) : ℝ := singularSeries N / Real.log (N : ℝ)

def tableHarmonic (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    tableCost n N eta t / (Nat.totient (fullPrefix t) : ℝ)

/-- A literal same-row residual. It is not a premise asserting that the
ordinary native coefficient has the enhanced H248 density. -/
def densityDefect (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    (ownerDensity n N eta (coordinates N t) - densityScale N * tableCost n N eta t) /
      (Nat.totient (fullPrefix t) : ℝ)

theorem actual_density_eq_table_add_defect {n N : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E) =
      densityScale N * tableHarmonic n N eta E + densityDefect n N eta E := by
  have hs : physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E) =
      ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
        ownerDensity n N eta (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
    rw [physicalDensity_eq_actual_native_harmonic hN heta E]
    simp only [JointNearCapPrimeReserve.jointMass, ordinaryKeep,
      U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples,
      U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, Finset.sum_filter]
  rw [hs]
  unfold tableHarmonic densityDefect
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [div_eq_mul_inv]
  ring

/-- The original fallback count and same-sigma signed PP term are retained.
The new displayed defect is a genuine outstanding term, not silently zero. -/
theorem eventually_original_count_with_H248_defect
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ∀ eta : ℚ, 0 < eta → ∀ E : ℕ × ℕ → Prop,
      currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
        (∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,
          U11Adaptive.weight N t) +
        piMass N * (densityScale N * tableHarmonic n N eta E + densityDefect n N eta E) +
        singletonPP n N eta E + epsilon * singularNormalization N := by
  filter_upwards [eventually_original_count_upper_primitivePP epsilon hepsilon,
    eventually_gt_atTop (1 : ℕ)] with N hupper hN
  intro n eta heta E
  have hh := hupper n eta heta E
  rw [piMain, actual_density_eq_table_add_defect hN heta E] at hh
  exact hh

theorem H248_two_pos : 0 < Part5UpperTables.H248 2 := by
  have h := U1011H248Clamp.H248_max_two_of_le (s := (2 : ℝ)) le_rfl
  simp only [max_self] at h
  rw [h]
  norm_num [Part5OriginalUpsilon5CausalDictionary.floorValue, Part5UpperTables.H248Numerators]

/-- Exact initial-range defect of the actual ordinary Rosser coefficient.
Its positive H248 correction is absent from that coefficient's own limit. -/
theorem ordinaryLimit_sub_tableCost_eq (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta)
    (hq : (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) ≤ 3) :
    ordinaryLimit p B eta - U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B eta =
      4 * Part5UpperTables.H248
        ((U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
          (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ)) /
        (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) := by
  have hp := actual_cell_density_parameters p B eta hB hw hcert heta
  have hR := (one_lt_div hp.1).mp hp.2
  have hR3 := (div_le_iff₀ hp.1).mp hq
  have heq := normalized_suzukiUpperFactor_initial
    (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ)
    (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) hp.1 hR hR3
  rw [ordinaryLimit, heq]
  unfold U1011OriginalSixteenNearCapBoxProfiles.nativeCost
  ring

theorem certified_near_clamp_density_gap_pos (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta)
    (hq : (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) ∈
        Ico (2 : ℝ) (101 / 50)) :
    0 < ordinaryLimit p B eta - U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B eta := by
  rw [ordinaryLimit_sub_tableCost_eq p B eta hB hw hcert heta (by linarith [hq.2])]
  have hH := H248_two_pos.trans_le (BufferedOrdinaryClamp.H248_two_le_right hq)
  have hp := actual_cell_density_parameters p B eta hB hw hcert heta
  have hR : (0 : ℝ) < U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta :=
    hp.1.trans ((one_lt_div hp.1).mp hp.2)
  exact div_pos (mul_pos (by norm_num) hH) hR

/-- This limit consumes the actual proved ordinary-density supplier,
not an H248 mean assumption. -/
theorem tendsto_actual_cell_density_minus_tableCost (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) :
    Tendsto (fun N : ℕ => cellDensity p B eta N * Real.log (N : ℝ) / singularSeries N -
      U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B eta)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (ordinaryLimit p B eta - U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B eta)) :=
  (tendsto_actual_certified_cell_density p B eta hB hw hcert heta).sub tendsto_const_nhds

/-- A certified ordinary native row near the clamp cannot by itself
provide an eventual density <= its enhanced table score. This pinpoints
the missing enhanced coefficient/mean connection without denying the
manuscript's different enhanced sieve construction. -/
theorem not_eventually_ordinary_density_le_H248_cost (p : Policy) (B : Box) (eta : ℚ)
    (hB : B.Valid) (hw : 0 < B.lo 3) (hcert : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta)
    (hq : (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B eta : ℝ) /
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent p B eta : ℝ) ∈
        Ico (2 : ℝ) (101 / 50)) :
    ¬ (∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      cellDensity p B eta N * Real.log (N : ℝ) / singularSeries N ≤
        U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B eta) := by
  letI := positiveEvenNatAtTop_neBot
  intro hevent
  have hgap := certified_near_clamp_density_gap_pos p B eta hB hw hcert heta hq
  have hpos := (tendsto_actual_cell_density_minus_tableCost p B eta hB hw hcert heta).eventually
    (lt_mem_nhds hgap)
  obtain ⟨N, hNpos, hNle⟩ := (hpos.and hevent).exists
  linarith

end
end ImbalancedChen.P2UpperActualH248DensityDefect
