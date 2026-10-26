import ImbalancedChen.P5ZU1011SameRhoNativePrimeBoxDensity
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests
import ImbalancedChen.AffinePrimeWallReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL cell-selected native Rosser divisor sum is performed before
taking an absolute value. Its normalized ordinary density is uniformly
bounded at fixed causal mesh and precision, by its proved finite-cell
Suzuki limits. Thus the actual signed MAIN boundary is paid on the prime
harmonic scale: epsilon, then fixed wall width, then N. This is not an
absolute-coefficient norm estimate. No AP/centre/PP boundary estimate is
claimed, and no independent beta replaces lambda+(e*d).
-/
namespace ImbalancedChen.P5Z.U1011SameRhoSignedDensityWallReserve
noncomputable section
open Set Filter Topology Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy)
open U1011OriginalSixteenJointNearCapCompiler
open U1011SameRhoNativePrimeBoxDensity
open U1011OriginalSixteenMixedGatePrimeTests

def envelope (n : ℕ) (eta : ℚ) : ℝ :=
  1 + ∑ j : Grid n, |ordinaryLimit (boxPolicy (gridBox n j)) (gridBox n j) eta|

theorem envelope_pos (n : ℕ) (eta : ℚ) : 0 < envelope n eta := by
  have hs : 0 ≤ ∑ j : Grid n, |ordinaryLimit (boxPolicy (gridBox n j)) (gridBox n j) eta| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  unfold envelope
  linarith

/-- A proved common envelope for the true normalized native density,
uniform in E and the original tuple. No density bound is a premise. -/
theorem eventually_owner_density_envelope (n : ℕ) (eta : ℚ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ E : ℕ × ℕ → Prop, ∀ t ∈ ordinaryTuples n N E,
        |ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N| ≤
          envelope n eta := by
  filter_upwards [eventually_uniform_native_owner_density n eta heta 1 (by norm_num)] with N hN
  intro E t ht
  have hclose := hN E t ht
  have hlim : |ownerLimit n eta (coordinates N t)| ≤
      ∑ j : Grid n, |ordinaryLimit (boxPolicy (gridBox n j)) (gridBox n j) eta| := by
    exact Finset.single_le_sum (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (owner n (coordinates N t)))
  calc
    _ = |(ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
        ownerLimit n eta (coordinates N t)) + ownerLimit n eta (coordinates N t)| := by
      congr 1
      ring
    _ ≤ |ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N -
        ownerLimit n eta (coordinates N t)| + |ownerLimit n eta (coordinates N t)| := abs_add _ _
    _ ≤ envelope n eta := add_le_add hclose.le hlim

/-- Actual native divisor main, retaining its complete physical modulus
fullPrefix*t and its signed coefficient before absolute value. -/
def boundary {r : ℕ} (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) : ℝ :=
  ∑ t ∈ ordinaryTuples n N E,
    if coordinates N t ∈ primeAffineWallStrip L c δ then
      |(∑ d ∈ support n N eta t, coefficient n N eta t d *
        (1 / (Nat.totient (fullPrefix t * d) : ℝ))) * Real.log (N : ℝ) / singularSeries N|
    else 0

theorem boundary_eq_actual_native_density {r n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) :
    boundary n N eta E L c δ =
      JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) (fun v =>
        if v ∈ primeAffineWallStrip L c δ then
          |ownerDensity n N eta v * Real.log (N : ℝ) / singularSeries N| else 0) := by
  have hmass (f : LogFour → ℝ) :
      JointNearCapPrimeReserve.jointMass N E (ordinaryKeep n N) f =
        ∑ t ∈ ordinaryTuples n N E, f (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) := by
    simp only [JointNearCapPrimeReserve.jointMass, ordinaryKeep, ordinaryTuples,
      U1011OriginalSixteenJointNativeCompiler.ordinaryTuples, Finset.sum_filter]
  rw [hmass]
  unfold boundary
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hw : coordinates N t ∈ primeAffineWallStrip L c δ
  · rw [if_pos hw, if_pos hw, native_row_reciprocalTotient_density hN heta ht]
    have heq : ownerDensity n N eta (coordinates N t) / (Nat.totient (fullPrefix t) : ℝ) *
        Real.log (N : ℝ) / singularSeries N =
        (ownerDensity n N eta (coordinates N t) * Real.log (N : ℝ) / singularSeries N) /
          (Nat.totient (fullPrefix t) : ℝ) := by ring
    rw [heq, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  · simp only [if_neg hw, zero_div]

/-- The same original native MAIN boundary, including arithmetic walls,
costs at most its raw closed-strip prime mass times the proved envelope. -/
theorem eventually_boundary_le_prime_wall_mass {r : ℕ}
    (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (δ : ℝ) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ E : ℕ × ℕ → Prop, boundary n N eta E L c δ ≤
        envelope n eta * actualPrimeAffineWallStripMass N
          (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) L c δ := by
  filter_upwards [eventually_owner_density_envelope n eta heta,
    (eventually_gt_atTop (1 : ℕ)).filter_mono inf_le_left] with N hbound hN
  intro E
  rw [boundary_eq_actual_native_density hN heta E L c δ,
    JointNearCapPrimeReserve.jointMass_eq_box hN]
  unfold actualPrimeAffineWallStripMass
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 0 ≤ BufferedPrimeErrorPayment.weight q := actualPrimeBoxWeight_nonneg hq
  by_cases hk : JointNearCapPrimeReserve.jointKept N E (ordinaryKeep n N) q
  · have ht : U1011OriginalSixteenNativeHarmonic.unslots q ∈ ordinaryTuples n N E :=
      Finset.mem_filter.mpr ⟨hk.1, hk.2⟩
    have hb : |ownerDensity n N eta (actualPrimeTupleLog N q) * Real.log (N : ℝ) /
        singularSeries N| ≤ envelope n eta := by
      simpa only [coordinates, U1011OriginalSixteenNativeHarmonic.slots_unslots] using hbound E _ ht
    by_cases hs : actualPrimeTupleLog N q ∈ primeAffineWallStrip L c δ
    · simp only [if_pos hk, if_pos hs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hw
    · simp only [if_pos hk, if_neg hs, mul_zero, le_refl]
  · simp only [if_neg hk]
    by_cases hs : actualPrimeTupleLog N q ∈ primeAffineWallStrip L c δ
    · simp only [if_pos hs]
      exact mul_nonneg (envelope_pos n eta).le hw
    · simp only [if_neg hs, mul_zero, le_refl]

/-- Prescribed epsilon precedes positive strip width, which precedes one
common arithmetic threshold. Original E and sigma are never replaced.
This controls the MAIN only; signed AP/centre discrepancies remain OPEN. -/
theorem exists_actual_native_density_wall_reserve {r : ℕ}
    (n : ℕ) (eta : ℚ) (heta : 0 < eta)
    (L : Fin r → LogFour →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        ∀ E : ℕ × ℕ → Prop, boundary n N eta E L c δ < epsilon := by
  have hC := envelope_pos n eta
  obtain ⟨δ, hδ, N₀, hN₀, hstrip⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0 : ℝ) < 417 / 5000)
    (by norm_num : (417 / 5000 : ℝ) < 59 / 250)
    L c hL (epsilon / envelope n eta) (div_pos hepsilon hC)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_boundary_le_prime_wall_mass n eta heta L c δ,
    (eventually_ge_atTop N₀).filter_mono inf_le_left] with N hbound hN
  intro E
  have hsmall := mul_lt_mul_of_pos_left (hstrip N hN) hC
  have hcancel : envelope n eta * (epsilon / envelope n eta) = epsilon := by
    field_simp [hC.ne']
  rw [hcancel] at hsmall
  exact (hbound E).trans_lt hsmall

/-- Actual mixed circuits need no false nonzero-form premise: zero
tautologies/contradictions have no geometric wall and are excluded exactly
by the already proved proper-row reduction. -/
theorem exists_mixed_circuit_density_wall_reserve {ι : Type*} [Fintype ι]
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (g : ι → U1011OriginalSixteenEligibilityState.MixedGate)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
        ∀ E : ℕ × ℕ → Prop,
          boundary n N eta E (reducedForms g) (reducedBounds g) δ < epsilon :=
  exists_actual_native_density_wall_reserve n eta heta (reducedForms g) (reducedBounds g)
    (reducedForms_ne_zero g) epsilon hepsilon

end
end ImbalancedChen.P5Z.U1011SameRhoSignedDensityWallReserve
