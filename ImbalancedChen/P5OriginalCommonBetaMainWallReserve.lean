import ImbalancedChen.P5OriginalFixedCommonBetaDensityEnvelope
import ImbalancedChen.P5ZU1011SameRhoNativePrimeBoxDensity
import ImbalancedChen.AffinePrimeWallReserve
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual constructed jointPresievedSigma, rather than the old all-prime
native sigma, receives a MAIN closed-wall reserve. Its common beta pair
is fixed before the requested tolerance and width. Both original source
bands, W, the literal E and every fullPrefix*r modulus are retained.
-/
namespace ImbalancedChen.P5Z.OriginalCommonBetaMainWallReserve
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy selectedPolicy ownerBox)
open U1011OriginalSixteenJointNearCapCompiler (ordinaryTuples)
open OriginalOrdinaryCommonBetaModel
open OriginalOrdinaryPresievedSigma OriginalOrdinaryPresievedDensityComparison
open OriginalJointCommonBetaModel OriginalCommonBetaActualParameters
open OriginalFixedCommonBetaDensityEnvelope
open U1011OriginalSixteenMixedGatePrimeTests

def smallCutoff (nu epsilon : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (nu * epsilon ^ 2)
def betaLevel (nu epsilon : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (nu * epsilon)

/-- The actual cell-static attached density, on the original log cube. -/
def ownerDensity (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ) (v : LogFour) : ℝ :=
  let Q := gridBox n (owner n v)
  let Z := U1011OriginalSixteenJointNearCapCompiler.rowZ (boxPolicy Q) Q eta N
  let D := U1011OriginalSixteenJointNearCapCompiler.rowD (boxPolicy Q) Q eta N
  physicalDensitySum (actualSmallRoughModuli (ordinaryRetainOdd D) N (Nat.ceil Z)
    (smallCutoff nu epsilon N) Z)
    (actualSmallRoughRho (ordinaryRetainOdd D) N (Nat.ceil Z)
      (smallCutoff nu epsilon N) Z (betaLevel nu epsilon N))

theorem ownerDensity_at_native (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ) (t : Four) :
    ownerDensity n N eta nu epsilon (coordinates N t) =
      rowDensity n N eta (smallCutoff nu epsilon N) (betaLevel nu epsilon N) t := rfl

def rowMain (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ) (t : Four) : ℝ :=
  (∑ r ∈ OriginalOrdinaryPresievedSigma.rowSupport n N eta (smallCutoff nu epsilon N) t,
    OriginalOrdinaryPresievedSigma.rowCoefficient n N eta (smallCutoff nu epsilon N)
      (betaLevel nu epsilon N) t r * (1 / (Nat.totient (fullPrefix t * r) : ℝ))) *
      Real.log (N : ℝ) / singularSeries N

/-- Exact physical row factorization for the NEW common-beta coefficient.
The prefix is split only after its genuine lowered-cutoff coprimality. -/
theorem rowMain_eq_density {n N : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ ordinaryTuples n N E) :
    rowMain n N eta nu epsilon t =
      (ownerDensity n N eta nu epsilon (coordinates N t) * Real.log (N : ℝ) / singularSeries N) /
        (Nat.totient (fullPrefix t) : ℝ) := by
  have hw := (parameters_on_joint_row hN heta hnu he heBudget ht).1
  have hs : (∑ r ∈ OriginalOrdinaryPresievedSigma.rowSupport n N eta (smallCutoff nu epsilon N) t,
      OriginalOrdinaryPresievedSigma.rowCoefficient n N eta (smallCutoff nu epsilon N)
        (betaLevel nu epsilon N) t r * (1 / (Nat.totient (fullPrefix t * r) : ℝ))) =
      rowDensity n N eta (smallCutoff nu epsilon N) (betaLevel nu epsilon N) t /
        (Nat.totient (fullPrefix t) : ℝ) := by
    unfold rowDensity physicalDensitySum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.totient_mul (joint_row_coprime_prefix hN heta ht hw hr), Nat.cast_mul]
    ring
  rw [rowMain, hs, ownerDensity_at_native]
  ring

def boundary {r : ℕ} (n N : ℕ) (eta : ℚ) (nu epsilon : ℝ) (E : ℕ × ℕ → Prop)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) : ℝ :=
  ∑ t ∈ ordinaryTuples n N E,
    if coordinates N t ∈ primeAffineWallStrip L c δ then |rowMain n N eta nu epsilon t| else 0

theorem boundary_eq_jointMass {r n N : ℕ} {eta : ℚ} {nu epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) (E : ℕ × ℕ → Prop)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) :
    boundary n N eta nu epsilon E L c δ =
      JointNearCapPrimeReserve.jointMass N E (U1011SameRhoNativePrimeBoxDensity.ordinaryKeep n N)
        (fun v => if v ∈ primeAffineWallStrip L c δ then
          |ownerDensity n N eta nu epsilon v * Real.log (N : ℝ) / singularSeries N| else 0) := by
  have hmass (f : LogFour → ℝ) :
      JointNearCapPrimeReserve.jointMass N E (U1011SameRhoNativePrimeBoxDensity.ordinaryKeep n N) f =
        ∑ t ∈ ordinaryTuples n N E, f (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
    simp only [JointNearCapPrimeReserve.jointMass, U1011SameRhoNativePrimeBoxDensity.ordinaryKeep,
      ordinaryTuples, U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, Finset.sum_filter]
  rw [hmass]
  unfold boundary
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hw : coordinates N t ∈ primeAffineWallStrip L c δ
  · rw [if_pos hw, if_pos hw, rowMain_eq_density hN heta hnu he heBudget ht,
      abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  · simp only [if_neg hw, zero_div]

/-- A fixed common pair supplies ONE density envelope before every later
wall family, width and E. This is the actual constructed coefficient. -/
theorem exists_common_boundary_envelope (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (nu epsilon : ℝ) (hnu : 0 < nu) (he : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ E : ℕ × ℕ → Prop, ∀ r : ℕ, ∀ L : Fin r → LogFour →L[ℝ] ℝ,
        ∀ c : Fin r → ℝ, ∀ δ : ℝ,
          boundary n N eta nu epsilon E L c δ ≤ C * actualPrimeAffineWallStripMass N
            (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) L c δ := by
  obtain ⟨C, hC, N0, hN0, hbound⟩ := exists_fixed_joint_row_density_envelope n eta heta nu epsilon hnu he heBudget
  refine ⟨C, hC, N0, hN0, ?_⟩
  intro N hN hEven E r L c δ
  have hN1 : 1 < N := by omega
  rw [boundary_eq_jointMass hN1 heta hnu he heBudget E L c δ,
    JointNearCapPrimeReserve.jointMass_eq_box hN1]
  unfold actualPrimeAffineWallStripMass
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 0 ≤ BufferedPrimeErrorPayment.weight q := actualPrimeBoxWeight_nonneg hq
  by_cases hk : JointNearCapPrimeReserve.jointKept N E (U1011SameRhoNativePrimeBoxDensity.ordinaryKeep n N) q
  · have ht : U1011OriginalSixteenNativeHarmonic.unslots q ∈ ordinaryTuples n N E :=
      Finset.mem_filter.mpr ⟨hk.1, hk.2⟩
    have hb : |ownerDensity n N eta nu epsilon (actualPrimeTupleLog N q) * Real.log (N : ℝ) /
        singularSeries N| ≤ C := by
      have hh := (hbound N hN hEven E _ ht).2
      change |ownerDensity n N eta nu epsilon
        (coordinates N (U1011OriginalSixteenNativeHarmonic.unslots q)) * Real.log (N : ℝ) /
          singularSeries N| ≤ C at hh
      simpa only [coordinates, U1011OriginalSixteenNativeHarmonic.slots_unslots] using hh
    by_cases hs : actualPrimeTupleLog N q ∈ primeAffineWallStrip L c δ
    · simp only [if_pos hk, if_pos hs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hw
    · simp only [if_pos hk, if_neg hs, mul_zero, le_refl]
  · simp only [if_neg hk]
    by_cases hs : actualPrimeTupleLog N q ∈ primeAffineWallStrip L c δ
    · simp only [if_pos hs]
      exact mul_nonneg hC.le hw
    · simp only [if_neg hs, mul_zero, le_refl]

/-- Common beta precision stays fixed: requested reserve -> fixed width
-> N, uniformly every original E. Equality prime atoms are retained. -/
theorem exists_common_beta_main_wall_reserve {r : ℕ}
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu epsilon : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (heBudget : epsilon < epsilonBudget n eta nu)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (reserve : ℝ) (hreserve : 0 < reserve) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ E : ℕ × ℕ → Prop, boundary n N eta nu epsilon E L c δ < reserve := by
  obtain ⟨C, hC, N1, hN1, henvelope⟩ := exists_common_boundary_envelope n eta heta nu epsilon hnu he heBudget
  obtain ⟨δ, hδ, N2, hN2, hmass⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0 : ℝ) < 417 / 5000) (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    L c hL (reserve / C) (div_pos hreserve hC)
  refine ⟨δ, hδ, max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN hEven E
  have hb := henvelope N ((le_max_left _ _).trans hN) hEven E r L c δ
  have hs := mul_lt_mul_of_pos_left (hmass N ((le_max_right _ _).trans hN)) hC
  have hc : C * (reserve / C) = reserve := by field_simp [hC.ne']
  rw [hc] at hs
  exact hb.trans_lt hs

end
end ImbalancedChen.P5Z.OriginalCommonBetaMainWallReserve
