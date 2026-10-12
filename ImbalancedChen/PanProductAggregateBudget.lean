import ImbalancedChen.PanProductLiuBridge

/-!
# Aggregate Liu--Pan budget on the physical product-strip moduli

This file performs the finite aggregation step left open by the exact
product-prefix bridge.  The physical divisor set consists of the positive
moduli at most `D` which are coprime to the fixed additive target `N`.
Whenever `D` lies below a Liu--Pan cutoff, this set is a subset of the full
cutoff interval.  Since every `MaxL` term is nonnegative, the physical sum may
be enlarged without a cardinality factor.

Applying the pinned aggregate theorem at both closed product endpoints then
bounds the literal strict-lower/closed-upper strip error.  All endpoint gates
are retained separately: the theorem does not manufacture the dynamic
product-strip geometry needed by the manuscript.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Finset

open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

/-- Positive physical moduli through `D`, restricted by coprimality with the
fixed additive target. -/
def panPhysicalModuli (N D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)

@[simp] theorem mem_panPhysicalModuli {N D d : ℕ} :
    d ∈ panPhysicalModuli N D ↔ 1 ≤ d ∧ d ≤ D ∧ Nat.Coprime d N := by
  simp [panPhysicalModuli, and_assoc]

/-- The actual physical modulus set embeds in an endpoint's full analytic
cutoff as soon as the displayed modulus gate holds. -/
theorem panPhysicalModuli_subset_cutoff
    {N Y D : ℕ} {B : ℝ}
    (hD : D ≤ panModulusCutoff Y B) :
    panPhysicalModuli N D ⊆ Finset.Icc 1 (panModulusCutoff Y B) := by
  intro d hd
  rcases mem_panPhysicalModuli.mp hd with ⟨hd1, hdD, _⟩
  exact Finset.mem_Icc.mpr ⟨hd1, hdD.trans hD⟩

/-- A literal `MaxL` is nonnegative, including the empty-residue fallback. -/
private theorem panProduct_intervalMaxL_nonneg
    (main : ℝ → ℝ) (Y A₁ A₂ d : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  classical
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  by_cases hS : (unitResidues d).Nonempty
  · rw [dif_pos hS]
    have hmem :
        ((unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|)).max'
            (Finset.image_nonempty.mpr hS) ∈
          (unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|) :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
    rw [← hl]
    exact abs_nonneg _
  · rw [dif_neg hS]

/-- The unconditional pinned Liu--Pan aggregate, applied twice, controls the
literal product-strip error on every physical modulus.  Coprimality is only
with the fixed target `N`; no coprimality with either endpoint is assumed.

The eight endpoint hypotheses are intentionally not compressed: a later
dynamic `(r,r*q)` grid must prove them for both `Y₀` and `Y₁`. -/
theorem panProductStrip_physical_boundedAggregate_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧
      ∃ B : ℝ, 0 ≤ B ∧
      ∃ N₀ : ℕ,
        ∀ {Y₀ Y₁ D A₁ A₂ N : ℕ},
          N₀ ≤ Y₀ →
          N₀ ≤ Y₁ →
          Y₀ ≤ Y₁ →
          (A₂ : ℝ) ≤ (Y₀ : ℝ) ^ (2 / 3 : ℝ) →
          (A₂ : ℝ) ≤ (Y₁ : ℝ) ^ (2 / 3 : ℝ) →
          Real.log (Y₀ : ℝ) ^ (2 * B) ≤ A₁ →
          Real.log (Y₁ : ℝ) ^ (2 * B) ≤ A₁ →
          D ≤ panModulusCutoff Y₀ B →
          D ≤ panModulusCutoff Y₁ B →
          ∑ d ∈ panPhysicalModuli N D,
            |panProductStripAnalyticError
              (liuLogarithmicIntegral (2 / Real.log 2))
              A₁ A₂ Y₀ Y₁ N d| ≤
            C * ((Y₁ : ℝ) / Real.log (Y₁ : ℝ) ^ U +
              (Y₀ : ℝ) / Real.log (Y₀ : ℝ) ^ U) := by
  obtain ⟨C, hC, B, hB, N₀, hagg⟩ :=
    panProductPrimeIndicatorMaxL_boundedAggregate_log_saving U hU
  refine ⟨C, hC, B, hB, N₀, ?_⟩
  intro Y₀ Y₁ D A₁ A₂ N hN₀ hN₁ hY hA₂₀ hA₂₁ hA₁₀ hA₁₁ hD₀ hD₁
  let E₀ : ℕ → ℝ := fun d =>
    liuMainPanCoprimeIntervalMaxL
      (liuLogarithmicIntegral (2 / Real.log 2))
      Y₀ A₁ A₂ d (fun r => if Nat.Prime r then (1 : ℝ) else 0)
  let E₁ : ℕ → ℝ := fun d =>
    liuMainPanCoprimeIntervalMaxL
      (liuLogarithmicIntegral (2 / Real.log 2))
      Y₁ A₁ A₂ d (fun r => if Nat.Prime r then (1 : ℝ) else 0)
  have hagg₀ :
      ∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₀ B), E₀ d ≤
        C * (Y₀ : ℝ) / Real.log (Y₀ : ℝ) ^ U := by
    simpa only [E₀] using hagg Y₀ hN₀ A₁ A₂ hA₂₀ hA₁₀
  have hagg₁ :
      ∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₁ B), E₁ d ≤
        C * (Y₁ : ℝ) / Real.log (Y₁ : ℝ) ^ U := by
    simpa only [E₁] using hagg Y₁ hN₁ A₁ A₂ hA₂₁ hA₁₁
  have hpoint : ∀ d ∈ panPhysicalModuli N D,
      |panProductStripAnalyticError
        (liuLogarithmicIntegral (2 / Real.log 2))
        A₁ A₂ Y₀ Y₁ N d| ≤ E₁ d + E₀ d := by
    intro d hd
    rcases mem_panPhysicalModuli.mp hd with ⟨hd1, _, hdN⟩
    simpa only [E₀, E₁] using
      (abs_panProductStripAnalyticError_target_le_two_MaxL
        (liuLogarithmicIntegral (2 / Real.log 2))
        A₁ A₂ Y₀ Y₁ N d hY hd1 hdN)
  have hsum₀ :
      ∑ d ∈ panPhysicalModuli N D, E₀ d ≤
        ∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₀ B), E₀ d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (panPhysicalModuli_subset_cutoff hD₀) ?_
    intro d _ _
    exact panProduct_intervalMaxL_nonneg
      (liuLogarithmicIntegral (2 / Real.log 2)) Y₀ A₁ A₂ d
      (fun r => if Nat.Prime r then (1 : ℝ) else 0)
  have hsum₁ :
      ∑ d ∈ panPhysicalModuli N D, E₁ d ≤
        ∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₁ B), E₁ d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (panPhysicalModuli_subset_cutoff hD₁) ?_
    intro d _ _
    exact panProduct_intervalMaxL_nonneg
      (liuLogarithmicIntegral (2 / Real.log 2)) Y₁ A₁ A₂ d
      (fun r => if Nat.Prime r then (1 : ℝ) else 0)
  calc
    ∑ d ∈ panPhysicalModuli N D,
        |panProductStripAnalyticError
          (liuLogarithmicIntegral (2 / Real.log 2))
          A₁ A₂ Y₀ Y₁ N d| ≤
        ∑ d ∈ panPhysicalModuli N D, (E₁ d + E₀ d) := by
          exact Finset.sum_le_sum hpoint
    _ = (∑ d ∈ panPhysicalModuli N D, E₁ d) +
          ∑ d ∈ panPhysicalModuli N D, E₀ d := by
            rw [Finset.sum_add_distrib]
    _ ≤ (∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₁ B), E₁ d) +
          ∑ d ∈ Finset.Icc 1 (panModulusCutoff Y₀ B), E₀ d :=
            add_le_add hsum₁ hsum₀
    _ ≤ C * (Y₁ : ℝ) / Real.log (Y₁ : ℝ) ^ U +
          C * (Y₀ : ℝ) / Real.log (Y₀ : ℝ) ^ U :=
            add_le_add hagg₁ hagg₀
    _ = C * ((Y₁ : ℝ) / Real.log (Y₁ : ℝ) ^ U +
          (Y₀ : ℝ) / Real.log (Y₀ : ℝ) ^ U) := by
            ring

end

end ImbalancedChen
