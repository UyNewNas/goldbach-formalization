import ImbalancedChen.Part5OriginalH430ClassicalRootPriceGeometry
import ImbalancedChen.Part5OriginalH430PairExactUpperPolynomial

/-! The original marked prime families, their true integer quotients and
their two nonnegative credits. On the entire classical branch the sum
of the credits is unchanged at the first-cube cutoff, for every actual
prime and every common refinement. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRootCredits
noncomputable section
open Finset Real Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab markedPhi)
open P2ActualMarkedCountState (root_level_geometry)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ rootLevel)
open Part5OriginalH430RootIntervalTheta (clampLevel)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RootRosserSurplus
open Part5OriginalH430SameQCanonicalMains (model)
open Part5OriginalH430ClassicalRootPriceGeometry (actual_classical_queries)
open Part5OriginalH430PairExactUpperPolynomial (weightedUpper upper_polynomial_exact original_model_and_AP)

theorem classical_Q_exact {N n p : ℕ} {τ : ℝ} (hp : p ∈ classicalBand N) :
    rootQ N n .U3 τ p = (N:ℝ)^(clampLevel n τ) := by
  have ht := (Finset.mem_filter.mp hp).2
  have htotal : (sourceRoot .U3 τ (physicalPrime N p)).physical.total = 1/2-τ := by
    simp only [sourceRoot, sourceResidual, U3Residual, if_neg (not_lt.mpr ht), tailResidual]
    ring
  simp only [rootQ, rootLevel, htotal, clampLevel]

private theorem frozen_receiver_shell {N p : ℕ} {Q w : ℝ} (hp : p ∈ classicalBand N)
    (hz : cutoff Q p w ≤ (N:ℝ)^a) :
    (frozenCount N p (receiver N) (cutoff Q p w):ℝ) =
      ((originalReceiver N p).card:ℝ) + firstPrimeMass N Q w p := by
  have hb := (Finset.mem_filter.mp hp).1
  have hrough : ChenPrimeRough ((N:ℝ)^a) p := by
    intro q hq hqp
    rw [(Nat.prime_dvd_prime_iff_eq hq (original_band_prime hb).1).mp hqp]
    exact (Finset.mem_filter.mp hb).2.1
  have hbuc : (frozenCount N p (receiver N) (cutoff Q p w):ℝ) =
      (frozenCount N p (receiver N) ((N:ℝ)^a):ℝ) + firstPrimeMass N Q w p := by
    unfold firstPrimeMass
    exact_mod_cast frozen_selected_buchstab N p (receiver N) hz
  rwa [frozenCount_eq_original_count N p ((N:ℝ)^a) hrough] at hbuc

/-- Actual comparison family in one original owner/mesh class, including
empty ones. Its common Q is the same for all classical p. -/
theorem physical_marked_class {N n m : ℕ} {τ : ℝ} (c : RootKey n m)
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let B := (classicalBand N).filter (fun p => keyAt N n m .U3 τ p = c)
    let Q := (N:ℝ)^(clampLevel n τ)
    markedPhi N Q B id (fun _ => 1) (fun _ => receiver N) (queryAt c) =
        (∑ p ∈ B, ((originalReceiver N p).card:ℝ)) + ∑ p ∈ B, firstPrimeMass N Q (queryAt c) p ∧
      Theta N Q B (fun _ => 1) = ∑ p ∈ B, thetaAtom N (rootQ N n .U3 τ p) p := by
  dsimp only
  constructor
  · rw [markedPhi, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hp
    have hz := (classical_geometry (m := m) hN hτ hτ' hn hb).2.1
    rw [cutoffAt, classical_Q_exact hb, hc] at hz
    simpa only [id_eq, one_mul] using frozen_receiver_shell hb hz
  · rw [Theta_eq_sum_atoms]
    apply sum_congr rfl
    intro p hp
    rw [classical_Q_exact (Finset.mem_filter.mp hp).1, one_mul]

/-- The original positive unit-mark family has mass zero exactly on its
empty classes. This criterion gives no quantitative lower bound on a
moving nonempty class. -/
theorem original_class_zero_theta_iff_empty {N n m : ℕ} {τ : ℝ} (c : RootKey n m)
    (hN : 4 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let B := (classicalBand N).filter (fun p => keyAt N n m .U3 τ p = c)
    Theta N ((N:ℝ)^(clampLevel n τ)) B (fun _ => 1) = 0 ↔ B = ∅ := by
  let B := (classicalBand N).filter (fun p => keyAt N n m .U3 τ p = c)
  let θ := fun p => thetaAtom N (rootQ N n .U3 τ p) p
  have h2 : 2 ≤ N := by omega
  have ht (p : ℕ) (hp : p ∈ B) : 0 < θ p := by
    have hb := (Finset.mem_filter.mp hp).1
    have hpr := (original_band_prime (Finset.mem_filter.mp hb).1).1.pos
    have hR := (classical_geometry (m := m) h2 hτ hτ' hn hb).1
    have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    have hl := Real.log_pos hNr
    have hli : 0 < AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N :=
      (by positivity : (0:ℝ)<N/(2*Real.log (N:ℝ))).trans_le (box_trueLi_lower hN)
    have hφ : 0 < (Nat.totient p:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hpr)
    have hS := wuSingularSeries_pos (p*N) (Nat.mul_pos hpr (by omega))
    have hlog := Real.log_pos hR
    dsimp only [θ, thetaAtom]
    positivity
  rw [(physical_marked_class c h2 hτ hτ' hn).2]
  change (∑ p ∈ B, θ p) = 0 ↔ B = ∅
  constructor
  · intro hzero
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hsum := Finset.single_le_sum (fun q hq => (ht q hq).le) hp
    exact ((ht p hp).trans_le hsum).ne' hzero
  · intro hempty
    rw [hempty, Finset.sum_empty]

/-- The two original positive finite terms at one fixed cutoff per p.
The first sum ranges over prime receivers ℓ, and the second over the
actual least-prime shell below the original N^a. -/
def cubeCredit (N n p : ℕ) (τ : ℝ) : ℝ :=
  let Q := rootQ N n .U3 τ p
  surplus N p Q (cutoff Q p 3) + firstPrimeMass N Q 3 p

theorem cubeCredit_nonneg {N n p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    0 ≤ cubeCredit N n p τ := by
  have hg := (classical_geometry (m := 0) hN hτ hτ' hn hp).1
  have hd := root_level_geometry hg (by norm_num : (1:ℝ)≤3)
  exact add_nonneg (surplus_nonneg hd.1 hd.2) (firstPrimeMass_nonneg _ _ _ _)

/-- Exact source identity. This uses the first-cube invariance for the
entire polynomial, including its signed test at the full modulus p*r.
In particular the credit itself has no auxiliary query-mesh multiplicity. -/
theorem original_classical_credit {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    let Q := rootQ N n .U3 τ p
    let w := queryAt (keyAt N n m .U3 τ p)
    let z := cutoffAt N n m p τ
    surplus N p Q z + firstPrimeMass N Q w p = cubeCredit N n p τ ∧
      ((originalReceiver N p).card:ℝ) + cubeCredit N n p τ = model true N Q p z + signedAP N p Q z := by
  let Q := rootQ N n .U3 τ p
  let w := queryAt (keyAt N n m .U3 τ p)
  let z := cutoffAt N n m p τ
  let z₃ := cutoff Q p 3
  have hg := classical_geometry (m := m) hN hτ hτ' hn hp
  obtain ⟨hs, _, hsw, hw⟩ := actual_classical_queries (m := m) hN hτ hτ' hn hp
  have hw0 : 0 < w := (lt_of_lt_of_le (by norm_num) hs).trans_le hsw
  have hz : z₃ ≤ z := Real.rpow_le_rpow_of_exponent_le hg.1.le (one_div_le_one_div_of_le hw0 hw)
  have hpr := original_band_prime (Finset.mem_filter.mp hp).1
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcube : cutoff Q (1*p) 3 ≤ z := by simpa only [one_mul] using hz
  have hm : model true N Q p z = model true N Q p z₃ := by
    simpa only [one_mul] using
      (original_model_and_AP (N := N) (p := p) (n := n) .U3 τ (d := 1)
        zero_lt_one hpr.1 hpr.2 hQ hcube).1
  let g := fun r : ℕ =>
    finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N (p*r) +
      (((chenAdditivePrimeCarrier N).card:ℝ) -
        AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N -
        chenPrimeDivisorCount N (p*r))/(Nat.totient (p*r):ℝ)
  have hap : signedAP N p Q z = signedAP N p Q z₃ := by
    simpa only [one_mul, weightedUpper, signedAP, g] using
      (upper_polynomial_exact (N := N) (p := p) (n := n) .U3 τ (d := 1)
        zero_lt_one hpr.1 hpr.2 hQ hcube).2 g
  have hc := frozen_count_plus_surplus Q z hpr.2
  have hc₃ := frozen_count_plus_surplus Q z₃ hpr.2
  have hshell := frozen_receiver_shell (Q := Q) (w := w) hp hg.2.1
  have hshell₃ := frozen_receiver_shell (Q := Q) (w := 3) hp (hz.trans hg.2.1)
  change surplus N p Q z + firstPrimeMass N Q w p = surplus N p Q z₃ + firstPrimeMass N Q 3 p ∧
    ((originalReceiver N p).card:ℝ) + (surplus N p Q z₃ + firstPrimeMass N Q 3 p) =
      model true N Q p z + signedAP N p Q z
  change (frozenCount N p (receiver N) z:ℝ) =
    ((originalReceiver N p).card:ℝ) + firstPrimeMass N Q w p at hshell
  change (frozenCount N p (receiver N) z₃:ℝ) =
    ((originalReceiver N p).card:ℝ) + firstPrimeMass N Q 3 p at hshell₃
  constructor <;> linarith only [hc, hc₃, hshell, hshell₃, hm, hap]

end
end ImbalancedChen.Part5OriginalH430ClassicalRootCredits
