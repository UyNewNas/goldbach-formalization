import ImbalancedChen.Part5OriginalH430FrozenClassicalRootAP

/-! Insert the pooled classical estimate into the actual two-band source.
The enhanced U3 and U4 AP coefficients, the entire original H430 price,
and the separate 430-stage recursion keep their original levels. -/
namespace ImbalancedChen.Part5OriginalH430U34PaidClassicalRoot
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P5CanonicalUpperCancellation (upperA)
open Part5UpperTables.OriginalU34 (tailCutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OwnedRootCounts Part5OriginalH430RootRosserSurplus
open Part5OriginalH430OwnedRootRosserBalance Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430FrozenClassicalRootAP (classical_tail_AP_log_saving)

def U3Upper (N n m : ℕ) (τ ε : ℝ) : ℝ :=
  ∑ c : RootKey n m, ∑ p ∈ rootFibre N n m .U3 τ c,
    let Q := cellQ N n c.1
    let s := queryAt c
    let z := cutoff Q p s
    (upperA s + ε) * thetaAtom N Q p +
      (if tailCutoff ≤ physicalPrime N p then 0 else signedAP N p Q z) -
      surplus N p Q z - firstPrimeMass N Q s p

theorem original_U3_signed_split {N n m : ℕ} {τ : ℝ} (ε : ℝ)
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    bandUpper N n m .U3 τ ε = U3Upper N n m τ ε +
      ∑ p ∈ classicalBand N, signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) := by
  let f : ℕ → ℝ := fun p => if tailCutoff ≤ physicalPrime N p then
    signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) else 0
  have hsum : (∑ c : RootKey n m, ∑ p ∈ rootFibre N n m .U3 τ c, f p) =
      ∑ p ∈ classicalBand N, signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) := by
    rw [classicalBand, sum_filter]
    exact Finset.sum_fiberwise_of_maps_to (s := originalBand N .U3)
      (t := Finset.univ) (g := keyAt N n m .U3 τ) (fun _ _ => Finset.mem_univ _) f
  rw [← hsum]
  unfold bandUpper U3Upper
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hgeo := original_fibre_geometry hN hτ hτ' hn hp
  have hc := (Finset.mem_filter.mp hp).2
  dsimp only [f, cutoffAt]
  rw [hc, ← hgeo.1]
  split_ifs <;> ring

/-- Uniform in both resolutions, including the nonzero structural clamp.
The complete signed AP is gone from the actual classical U3 interval;
one error O_K(N/log^K N) is paid for all its p and all its boxes. -/
theorem original_U34_with_classical_root_AP_paid {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) (K : ℕ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ,
      1/((n:ℝ)+1) ≤ 11/384 →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        U3Upper N n m τ ε + bandUpper N n m .U4 τ ε + C*(N:ℝ)/Real.log (N:ℝ)^K := by
  obtain ⟨C, hC, hAP⟩ := classical_tail_AP_log_saving hτ hτ' K hK
  obtain ⟨T, h4, hT⟩ := original_U34_at_signed_root_AP he
  refine ⟨C, hC, ?_⟩
  filter_upwards [hAP, eventually_ge_atTop T] with N hAP hN
  intro hEven n m hn
  have h2 : 2 ≤ N := by omega
  have h := hT N hN hEven n m τ hτ.le hτ' hn
  rw [original_U3_signed_split ε h2 hτ.le hτ' hn] at h
  have hu :
      (∑ p ∈ classicalBand N, signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ)) ≤
        C*(N:ℝ)/Real.log (N:ℝ)^K :=
    (sum_le_sum (fun p _ => le_abs_self (signedAP N p (rootQ N n .U3 τ p)
      (cutoffAt N n m p τ)))).trans (hAP n m hn)
  linarith only [h, hu]

end
end ImbalancedChen.Part5OriginalH430U34PaidClassicalRoot
