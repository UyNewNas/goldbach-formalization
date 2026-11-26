import ImbalancedChen.PanProductResidueBudget
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate

/-!
# Exact bridge from product prefixes to the Liu--Pan `MaxL` interface

This file identifies the finite product-prefix error used by the manuscript
adapter with the error sum in the pinned `goldbach-lean` Pan development.  It
also proves that the physical residue `N % d` belongs to the supplier's
canonical primitive residue family, and hence is controlled by its residue
maximum.  The two-prefix identity then bounds one strict-lower/closed-upper
product strip by the sum of the two endpoint `MaxL` values.

No scale hypothesis or aggregate estimate is hidden here.  Applying the
external logarithmic-saving theorem still requires its hypotheses separately
at both product endpoints.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Finset

open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

/-- The local one-fibre count is definitionally the pinned supplier's closed
product-prefix count. -/
@[simp] theorem panProductPrefixFibreAPCount_eq_primesInAPBelow
    (Y r a d : ℕ) :
    panProductPrefixFibreAPCount Y r a d =
      (primesInAPBelow Y r d a : ℝ) := by
  rfl

/-- The two projects use the same canonical reduced-residue representatives. -/
theorem finiteReducedResidues_eq_unitResidues (d : ℕ) :
    finiteReducedResidues d = unitResidues d := by
  rfl

/-- For a primitive residue, the local prefix error is exactly the pinned
Liu--Pan coprime interval sum with the modulus-independent prime indicator. -/
theorem panProductPrefixAnalyticError_eq_liuMainPanCoprimeIntervalSum
    (main : ℝ → ℝ) (A₁ A₂ Y a d : ℕ)
    (ha : Nat.Coprime a d) :
    panProductPrefixAnalyticError main A₁ A₂ Y a d =
      liuMainPanCoprimeIntervalSum main Y A₁ A₂ d a
        (fun r => if Nat.Prime r then (1 : ℝ) else 0) := by
  classical
  rw [panProductPrefixAnalyticError_eq_sum main A₁ A₂ Y a d ha]
  unfold liuMainPanCoprimeIntervalSum
  apply Finset.sum_congr rfl
  intro r _
  by_cases hrd : Nat.Coprime r d
  · simp only [if_pos hrd]
    rw [panProductPrefixFibreAPCount_eq_primesInAPBelow]
    unfold liuScaledAPError
    rfl
  · simp [hrd]

/-- Every member of the supplier's primitive residue family is bounded by
its literal finite maximum. -/
theorem abs_liuMainPanCoprimeIntervalSum_le_MaxL
    {main : ℝ → ℝ} {Y A₁ A₂ d a : ℕ} {f : ℕ → ℝ}
    (ha : a ∈ unitResidues d) :
    |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d a f| ≤
      liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  classical
  have hS : (unitResidues d).Nonempty := ⟨a, ha⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  have hmem :
      |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d a f| ∈
        (unitResidues d).image
          (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|) :=
    Finset.mem_image_of_mem _ ha
  exact Finset.le_max' _ _ hmem

/-- The physical target gives a canonical supplier residue at every positive
modulus coprime to that target.  Coprimality is with `N`, not with the moving
product endpoint. -/
theorem target_mod_mem_unitResidues
    {N d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    N % d ∈ unitResidues d := by
  rw [← finiteReducedResidues_eq_unitResidues]
  exact target_mod_mem_finiteReducedResidues N d
    (lt_of_lt_of_le Nat.zero_lt_one hd) hdN.symm

/-- One local product prefix at the physical target residue is bounded by the
pinned Liu--Pan residue maximum. -/
theorem abs_panProductPrefixAnalyticError_target_le_MaxL
    (main : ℝ → ℝ) (A₁ A₂ Y N d : ℕ)
    (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    |panProductPrefixAnalyticError main A₁ A₂ Y N d| ≤
      liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d
        (fun r => if Nat.Prime r then (1 : ℝ) else 0) := by
  rw [← panProductPrefixAnalyticError_residue_mod
    main A₁ A₂ Y N d]
  rw [panProductPrefixAnalyticError_eq_liuMainPanCoprimeIntervalSum
    main A₁ A₂ Y (N % d) d]
  · exact abs_liuMainPanCoprimeIntervalSum_le_MaxL
      (target_mod_mem_unitResidues hd hdN)
  · exact ((mem_finiteReducedResidues (N % d) d).mp
      (target_mod_mem_finiteReducedResidues N d
        (lt_of_lt_of_le Nat.zero_lt_one hd) hdN.symm)).2

/-- A physical product strip is bounded by the two exact endpoint `MaxL`
values.  This is the finite bridge needed before invoking the aggregate
theorem twice, once at each endpoint. -/
theorem abs_panProductStripAnalyticError_target_le_two_MaxL
    (main : ℝ → ℝ) (A₁ A₂ Y₀ Y₁ N d : ℕ)
    (hY : Y₀ ≤ Y₁) (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    |panProductStripAnalyticError main A₁ A₂ Y₀ Y₁ N d| ≤
      liuMainPanCoprimeIntervalMaxL main Y₁ A₁ A₂ d
          (fun r => if Nat.Prime r then (1 : ℝ) else 0) +
        liuMainPanCoprimeIntervalMaxL main Y₀ A₁ A₂ d
          (fun r => if Nat.Prime r then (1 : ℝ) else 0) := by
  exact (abs_panProductStripAnalyticError_le
    main A₁ A₂ Y₀ Y₁ N d hY).trans
      (add_le_add
        (abs_panProductPrefixAnalyticError_target_le_MaxL
          main A₁ A₂ Y₁ N d hd hdN)
        (abs_panProductPrefixAnalyticError_target_le_MaxL
          main A₁ A₂ Y₀ N d hd hdN))

/-- The pinned unconditional aggregate theorem specialized to the exact
modulus-independent coefficient occurring in the product-prefix expansion.
This discharges the supplier's global coefficient hypothesis, while retaining
all endpoint, interval and modulus-cutoff gates verbatim. -/
theorem panProductPrimeIndicatorMaxL_boundedAggregate_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧
      ∃ B : ℝ, 0 ≤ B ∧
      ∃ N₀ : ℕ,
        ∀ N ≥ N₀, ∀ A₁ A₂ : ℕ,
          (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
          Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
          ∑ d ∈ Finset.Icc 1 (panModulusCutoff N B),
            liuMainPanCoprimeIntervalMaxL
              (liuLogarithmicIntegral (2 / Real.log 2))
              N A₁ A₂ d
              (fun r => if Nat.Prime r then (1 : ℝ) else 0) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, h⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  exact ⟨C, hC, B, hB, N₀, fun N hN A₁ A₂ hA₂ hA₁ =>
    h N hN A₁ A₂
      (fun r => if Nat.Prime r then (1 : ℝ) else 0)
      hA₂ hA₁ abs_panProductPrimeIndicator_le_one⟩

end

end ImbalancedChen
