import ImbalancedChen.Part3OriginalTwoChartRawMass
import ImbalancedChen.Part3ZActualPrimaryDyadicAssembly

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Assemble the actual level-dependent raw n mass over all original keys.
The spectral inputs and the explicit raw-sieve price remain outstanding. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalAllKeysRawMass20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open ActualCompletedSquarePushforwardSourceOnly
open FixedRhoPrimarySignedFiniteSourceOnly
open OriginalMaskedOuterEnergy20261102
open OriginalCompletedReciprocalSource20261102
open OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalExceptionalPostRemovalPair20261113 (levels rowMass rowLength)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open OriginalOppositeBlockExceptionalBound20261120 (rawChartN rawChartCost)
open OriginalTwoChartRawMass20261120
  (actualOutputMass two_chart_row_mass_eq_actual two_chart_rawN_le_original_mass
    rawChartOuterWeight two_chart_raw_cost_le_original_mass)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
  (block block_subset finite_beta_energy_assembly)

/-- This is the actual joint-output carrier of the nonzero original source. -/
def allOutput (D : OriginalData) : Finset Output :=
  (nonzeroSource (originalSource D)).image output

def globalMass (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : ℝ :=
  ∑ zy ∈ allOutput D,
    ‖jointBeta D r (nonzeroSource (originalSource D)) zy‖^2

theorem outputCarrier_subset_all (D : OriginalData) (k : BlockKey) :
    outputCarrier D k ⊆ allOutput D := by
  intro zy hzy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzy
  exact Finset.mem_image.mpr ⟨s, block_subset D.block.atom.residue (originalSource D) k hs, rfl⟩

theorem blockBeta_zero_outside (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (zy : Output) (hout : zy ∉ outputCarrier D k) :
    blockBeta D r k zy = 0 := by
  by_contra hb
  exact hout (beta_ne_zero_mem_image hb)

theorem actualOutputMass_eq_all_carrier (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) :
    actualOutputMass D r k = ∑ zy ∈ allOutput D, ‖blockBeta D r k zy‖^2 := by
  classical
  unfold actualOutputMass
  apply Finset.sum_subset (outputCarrier_subset_all D k)
  intro zy _ hout
  simp [blockBeta_zero_outside D r k zy hout]

/-- Exact finite assembly: output fibres, not source summands, are disjoint.
Original source multiplicities remain inside jointBeta. -/
theorem all_key_mass_eq_global (D : OriginalData) (r : ZMod (prefixPeriod D.key)) :
    (∑ k ∈ originalKeys D, actualOutputMass D r k) = globalMass D r := by
  classical
  calc
    _ = ∑ k ∈ originalKeys D, ∑ zy ∈ allOutput D, ‖blockBeta D r k zy‖^2 := by
      apply Finset.sum_congr rfl
      intro k _
      exact actualOutputMass_eq_all_carrier D r k
    _ = globalMass D r := by
      have h := finite_beta_energy_assembly D.block.atom.residue
        (originalSource D) (D.lambda r) D.omega (allOutput D)
      simpa only [globalMass, originalKeys, blockBeta, primaryBlock, jointBeta] using h.symm

/-- Both actual physical level charts across all actual primary keys account
for exactly one nonzero original joint-output energy. -/
theorem all_key_two_chart_row_mass_eq_global (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) :
    (∑ k ∈ originalKeys D,
      ((∑ z : ↥(levels D k false), rowMass D r k z.val) +
       (∑ z : ↥(levels D k true), rowMass D r k z.val))) = globalMass D r := by
  classical
  calc
    _ = ∑ k ∈ originalKeys D, actualOutputMass D r k := by
      apply Finset.sum_congr rfl
      intro k _
      exact two_chart_row_mass_eq_actual D r k
    _ = globalMass D r := all_key_mass_eq_global D r

/-- A uniform scalar bound on the actual key weights pays the actual
energies. No common coefficient sequence or spectral bound is assumed. -/
theorem weighted_key_mass_le (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (w : BlockKey → ℝ) (B : ℝ)
    (hB : ∀ k ∈ originalKeys D, w k ≤ B) :
    (∑ k ∈ originalKeys D, w k * actualOutputMass D r k) ≤ B * globalMass D r := by
  classical
  calc
    _ ≤ ∑ k ∈ originalKeys D, B * actualOutputMass D r k := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_right (hB k hk)
      unfold actualOutputMass
      exact Finset.sum_nonneg (fun zy _ => sq_nonneg _)
    _ = B * globalMass D r := by rw [← Finset.mul_sum, all_key_mass_eq_global]

/-- The original raw sieve factor remains explicit in the scalar bound.
It is not replaced by a post-removal or level-averaged estimate. -/
theorem weighted_all_keys_rawN_le (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (w : BlockKey → ℝ) (B : ℝ)
    (hw : ∀ k ∈ originalKeys D, 0 ≤ w k)
    (hcost : ∀ k ∈ originalKeys D,
      w k * (2*sieveConstant*(1+
        (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false)) ≤ B) :
    (∑ k ∈ originalKeys D, w k * (rawChartN D r k false + rawChartN D r k true)) ≤
      B * globalMass D r := by
  classical
  calc
    _ ≤ ∑ k ∈ originalKeys D,
        (w k * (2*sieveConstant*(1+
          (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false))) *
            actualOutputMass D r k := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_left (two_chart_rawN_le_original_mass D r k) (hw k hk)
      simpa only [mul_assoc] using h
    _ ≤ B * globalMass D r := weighted_key_mass_le D r _ B hcost

/-- The actual two J-weighted costs, with the phase of each physical
chart fixed independently, can be assembled over all original keys once
their explicit scalar prices have a uniform bound. -/
theorem all_keys_two_chart_raw_cost_le (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (j : ℕ) (M B : ℝ)
    (B₀ ω₀ B₁ ω₁ : BlockKey → ℝ)
    (hcost : ∀ k ∈ originalKeys D,
      max (rawChartOuterWeight D k false j M (B₀ k) (ω₀ k))
          (rawChartOuterWeight D k true j M (B₁ k) (ω₁ k)) *
        (2*sieveConstant*(1+
          (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false)) ≤ B) :
    (∑ k ∈ originalKeys D,
      (rawChartCost D r k false j M (B₀ k) (ω₀ k) +
       rawChartCost D r k true j M (B₁ k) (ω₁ k))) ≤ B * globalMass D r := by
  classical
  calc
    _ ≤ ∑ k ∈ originalKeys D,
      (max (rawChartOuterWeight D k false j M (B₀ k) (ω₀ k))
           (rawChartOuterWeight D k true j M (B₁ k) (ω₁ k)) *
        (2*sieveConstant*(1+
          (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D false))) *
        actualOutputMass D r k := by
      apply Finset.sum_le_sum
      intro k _
      have h := two_chart_raw_cost_le_original_mass D r k j M
        (B₀ k) (ω₀ k) (B₁ k) (ω₁ k)
      simpa only [mul_assoc] using h
    _ ≤ B * globalMass D r := weighted_key_mass_le D r _ B hcost

end ImbalancedChen.Part3.OriginalAllKeysRawMass20261120
end
