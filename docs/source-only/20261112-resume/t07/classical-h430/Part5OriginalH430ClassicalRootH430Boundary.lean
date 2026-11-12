import ImbalancedChen.Part5OriginalH430ClassicalRootOrdinaryMean
import ImbalancedChen.Part5OriginalH430ClassicalRootCredits

/-! Arithmetic endpoint for the original classical U3 roots. The genuine
count plus its two finite credits has ordinary price Θ, in summed
absolute error. At the original table price, only a lower bound for
these actual credits against H430·Θ remains. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRootH430Boundary
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2Selected430CausalOccurrenceExporter (iterate)
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (floorValue)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430FrozenTableRootMass (frozenQuery)
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedReads
open Part5OriginalH430OwnedRootCounts Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RootIntervalTheta Part5OriginalH430ClassicalRootThetaPayment
open Part5OriginalH430RootRosserSurplus (signedAP)
open Part5OriginalH430SameQCanonicalMains (model)
open Part5OriginalH430ClassicalRootCredits
open Part5OriginalH430ClassicalRootPriceGeometry
open Part5OriginalH430ClassicalRootOrdinaryMean

def rootDifference (N n p : ℕ) (τ : ℝ) : ℝ :=
  ((originalReceiver N p).card:ℝ) + cubeCredit N n p τ - thetaAtom N (rootQ N n .U3 τ p) p

/-- Only the two original sets appear in the conclusion. The single
classical AP pool is used once per estimate, and the compact ordinary
main is paid proportionally to the atoms in that very set. -/
theorem actual_classical_and_clamp_distance {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N, |rootDifference N n p τ|) ≤ ε * classicalMass N n τ ∧
      (∑ p ∈ clampPrimes N, |rootDifference N n p τ|) ≤ ε * clampMass N n τ := by
  have hhalf : 0 < ε/2 := by linarith
  filter_upwards [classical_root_main_close hhalf, complete_classical_AP_le_clamp_theta hτ hτ' hhalf,
    eventually_ge_atTop (4:ℕ)] with N hmain hAP hN
  intro hEven n hn
  let θ := fun p => thetaAtom N (rootQ N n .U3 τ p) p
  let D := fun p => signedAP N p (rootQ N n .U3 τ p) (cutoffAt N n 0 p τ)
  have h2 : 2 ≤ N := by omega
  have hs := clamp_subset_classical h2
  have row (p : ℕ) (hp : p ∈ classicalBand N) :
      |rootDifference N n p τ| ≤ (ε/2)*θ p + |D p| := by
    have hx := (original_classical_credit (m := 0) h2 hτ.le hτ' hn hp).2
    have heq : rootDifference N n p τ =
        (model true N (rootQ N n .U3 τ p) p (cutoffAt N n 0 p τ) - θ p) + D p := by
      unfold rootDifference
      change ((originalReceiver N p).card:ℝ) + cubeCredit N n p τ - θ p = _
      rw [hx]
      dsimp only [D]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add_right (hmain hEven n 0 τ hτ.le hτ' hn p hp) _)
  have pay (B : Finset ℕ) (hB : B ⊆ classicalBand N) (hθ : clampMass N n τ ≤ ∑ p ∈ B, θ p) :
      (∑ p ∈ B, |rootDifference N n p τ|) ≤ ε*(∑ p ∈ B, θ p) := by
    have ha : (∑ p ∈ B, |D p|) ≤ (ε/2)*(∑ p ∈ B, θ p) :=
      (sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => abs_nonneg _)).trans
        ((hAP n 0 hn).trans (mul_le_mul_of_nonneg_left hθ hhalf.le))
    have hh := sum_le_sum (s := B) (fun p hp => row p (hB hp))
    rw [sum_add_distrib, ← mul_sum] at hh
    linarith only [hh, ha]
  exact ⟨pay _ (fun _ h => h) (clampMass_le_classicalMass hN hτ.le hτ' hn),
    pay _ hs le_rfl⟩

/-- Full original archive price at the original scalar, including all
knots. The difference between the real count gap and the table charge
less the integer credits is small in L¹ over the whole band. -/
theorem archived_classical_H430_gap {τ ε : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N,
        let s := frozenQuery n .U3 τ (physicalPrime N p)
        let θ := thetaAtom N (rootQ N n .U3 τ p) p
        |(((originalReceiver N p).card:ℝ) - (upperAmplitude s - H430 s)*θ) -
          (H430 s*θ - cubeCredit N n p τ)|) ≤ ε*classicalMass N n τ := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he, eventually_ge_atTop (2:ℕ)]
    with N hdist hN
  intro hEven n hn
  apply le_trans ?_ (hdist hEven n hn).1
  apply le_of_eq
  apply sum_congr rfl
  intro p hp
  dsimp only
  rw [(actual_classical_amplitudes (m := 0) hN hτ.le hτ' hn hp).1]
  congr 1
  unfold rootDifference
  ring

/-- The finite history version keeps the actual generation-430 selected
owner and evaluates its old scalar at the source argument. The endpoint
used by the ordinary polynomial stays in that same closed cell. -/
theorem selected_classical_H430_gap {τ ε : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N,
        let c := keyAt N n m .U3 τ p
        let θ := thetaAtom N (rootQ N n .U3 τ p) p
        |(((originalReceiver N p).card:ℝ) - (P5CanonicalUpperCancellation.upperA (queryAt c) -
          ownerFloor c)*θ) -
          (requestValue (iterate 430) (rootRequest N n .U3 τ p)*θ - cubeCredit N n p τ)|) ≤
        ε*classicalMass N n τ := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he, eventually_ge_atTop (2:ℕ)]
    with N hdist hN
  intro hEven n m hn
  apply le_trans ?_ (hdist hEven n hn).1
  apply le_of_eq
  apply sum_congr rfl
  intro p hp
  let c := keyAt N n m .U3 τ p
  have hc : p ∈ rootFibre N n m .U3 τ c := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,rfl⟩
  have hg := original_fibre_geometry hN hτ.le hτ' hn hc
  have hh : ownerFloor c = requestValue (iterate 430) (rootRequest N n .U3 τ p) := by
    cases h : c.2.1 with
    | none => simpa only [ownerFloor, h] using (hg.2.2.2.2.2 h).symm
    | some i => simpa only [ownerFloor, h] using (hg.2.2.2.2.1 i h).2.2.symm
  dsimp only
  rw [(actual_classical_amplitudes (m := m) hN hτ.le hτ' hn hp).2, hh]
  congr 1
  unfold rootDifference
  ring

/-- The two adjacent entries are read directly from the printed 200-entry
array. This checks two vector projections and uses the old knot-min rule. -/
theorem archive_clamp_price :
    H430 2 = (37052565421922458792801:ℝ)/(2:ℝ)^80 := by
  have h49 : H430Numerators 49 = (37052565421922458792801:ℤ) := rfl
  have h50 : H430Numerators 50 = (37052565421922458792801:ℤ) := rfl
  simp only [H430_two_eq_adjacent_min, floorValue, h49, h50, min_self] <;> norm_num

/-- The live selected table also demands a strictly positive gain on
the same original clamp, independently of any equality between the
complete live and serialized arrays. Retention proves only a price. -/
theorem selected_clamp_price_lower {N n p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hp : p ∈ clampPrimes N) :
    (1/50:ℝ) ≤ requestValue (iterate 430) (rootRequest N n .U3 τ p) := by
  have hret (i : Fin 200) (g : ℕ) : P2Selected430CausalOccurrenceExporter.seed true i ≤ iterate g true i := by
    induction g with
    | zero => exact le_rfl
    | succ g ih => exact ih.trans (Part5OriginalH430DecisionProvenance.iterate_le_succ g true i)
  have hfloor (i : Fin 200) (hi : i.val < 60) :
      (1/50:ℝ) ≤ floorValue (iterate 430 true) i := by
    have h0 : (1/50:ℝ) ≤ floorValue (P2Selected430CausalOccurrenceExporter.seed true) i := by
      norm_num [floorValue, P2Selected430CausalOccurrenceExporter.seed, P2Selected430LiteralActionData.q, hi]
    exact h0.trans (div_le_div_of_nonneg_right (by exact_mod_cast hret i 430) (by positivity))
  have hs := (clamp_physical_level (by omega : 1<N) hτ hτ' hp (n := n)).2
  have hk : (2:ℝ) ∈ P5OriginalFeedbackTableKernels.tableAtomSet false (.inr clampKnot) := by
    norm_num [P5OriginalFeedbackTableKernels.tableAtomSet, upperAtomSet, clampKnot,
      Part5OriginalUpsilon5CausalDictionary.floorGrid]
  have hmin (v : Fin 200 → ℤ) :
      Part5OriginalUpsilon5CausalDictionary.floorAtomValue v (.inr clampKnot) =
        min (floorValue v 49) (floorValue v 50) := by
    norm_num [Part5OriginalUpsilon5CausalDictionary.floorAtomValue,
      Part5OriginalUpsilon5CausalDictionary.floorKnotValue, clampKnot]
  change (1/50:ℝ) ≤ P5OriginalFeedbackTableKernels.tableFunction false (iterate 430 true)
    (frozenQuery n .U3 τ (physicalPrime N p))
  rw [hs, Part5OriginalH430ClosedOwner.tableFunction_at_atom _ hk, hmin]
  exact le_min (hfloor 49 (by decide)) (hfloor 50 (by decide))

/-- Positive main-order charge on a genuine subfamily, uniformly through
arbitrarily fine choices. Its coefficient comes solely from the printed
knot, its lower mass solely from the actual outer-prime interval. -/
theorem archive_clamp_charge_positive :
    let c := ((37052565421922458792801:ℝ)/(2:ℝ)^80)*(4*Real.log (834/833:ℝ))
    0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ ≤ 1/12 →
      1/((n:ℝ)+1) ≤ 11/384 → c*singularNormalization N ≤ H430 2 * clampMass N n τ := by
  obtain ⟨hi, hpos⟩ := uniform_clamp_witness
  rw [ideal_clamp_mass] at hi
  have hlog : 0 < Real.log (834/833:ℝ) := Real.log_pos (by norm_num)
  have hcoef : 0 < (37052565421922458792801:ℝ)/(2:ℝ)^80 := by positivity
  refine ⟨by dsimp only; positivity, ?_⟩
  filter_upwards [hpos] with N hmass
  intro n τ hτ hτ' hn
  have h := hmass n τ hτ hτ' hn
  rw [ideal_clamp_mass] at h
  rw [archive_clamp_price]
  convert mul_le_mul_of_nonneg_left h hcoef.le using 1 <;> ring

/-- The specific old closed-knot price is compared to the two integer
credits on the full original interval. The sign still needed for an
upper count is sum(credit) ≥ H430(2)·Θ up to relative error. -/
theorem actual_clamp_H430_gap {τ ε : ℝ} (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      |((∑ p ∈ clampPrimes N, ((originalReceiver N p).card:ℝ)) -
          (1-H430 2)*clampMass N n τ) -
        (H430 2*clampMass N n τ - ∑ p ∈ clampPrimes N, cubeCredit N n p τ)| ≤
        ε*clampMass N n τ := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he] with N hdist
  intro hEven n hn
  have heq : ((∑ p ∈ clampPrimes N, ((originalReceiver N p).card:ℝ)) -
        (1-H430 2)*clampMass N n τ) -
      (H430 2*clampMass N n τ - ∑ p ∈ clampPrimes N, cubeCredit N n p τ) =
      ∑ p ∈ clampPrimes N, rootDifference N n p τ := by
    simp only [rootDifference, clampMass, sum_sub_distrib, sum_add_distrib]
    ring
  rw [heq]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hdist hEven n hn).2

end
end ImbalancedChen.Part5OriginalH430ClassicalRootH430Boundary
