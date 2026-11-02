import ImbalancedChen.P2EnhancedUnitSourceMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedQuadrature
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The native nonunit quadrature has a fixed compact phi interval. Its
threshold is transported to the actual enhanced scale Q/d using the
original fixed positive residual floor. Positivity of the residual is
NOT used to infer alpha >= 2. The latter remains a separate source gate.
The original sigma, d-dependent alpha and true-li Theta are unchanged.
-/

namespace ImbalancedChen.P2EnhancedNonunitPhysicalQuadrature
noncomputable section
open Real Filter Finset Set MeasureTheory Wu2008DoubleSieve
open P2EnhancedSwitchedTrueNormalization
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open scoped Classical BigOperators Topology

/-- A fixed residual floor gives a fixed alpha ceiling. The lower gate
is deliberately absent: it is not a consequence of these assumptions. -/
theorem trueAlpha_le_inv_floor {N d : ℕ} {Q eta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (heta : 0 < eta)
    (hscale : (N : ℝ)^eta ≤ Q/d) : trueAlpha N Q d ≤ 1/eta := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR : 1 < Q/d := (one_lt_rpow hNr heta).trans_le hscale
  have hX : (0 : ℝ) < (N : ℝ)/d := div_pos hN0 hd0
  have hlogX : log ((N : ℝ)/d) ≤ log (N : ℝ) :=
    log_le_log hX (div_le_self hN0.le hd1)
  have hlogR := log_le_log (rpow_pos_of_pos hN0 eta) hscale
  rw [log_rpow hN0] at hlogR
  unfold trueAlpha
  apply (div_le_div_iff₀ (log_pos hR) heta).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlogX heta.le]

theorem physical_alpha_mem {N d : ℕ} {Q eta : ℝ}
    (hN : 1 < N) (hd : 0 < d) (heta : 0 < eta)
    (hscale : (N : ℝ)^eta ≤ Q/d) (ha : 2 ≤ trueAlpha N Q d) :
    trueAlpha N Q d ∈ Icc 2 (max 2 (1/eta)) :=
  ⟨ha, (trueAlpha_le_inv_floor hN hd heta hscale).trans (le_max_right _ _)⟩

/-- The actual causal logarithmic floor supplies the scale condition
without changing Q or any mark. The alpha gate is still independent. -/
theorem scale_floor_of_residual {N d : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (hd : 0 < d)
    (hfloor : eta ≤ residualExponent N d nu) :
    (N : ℝ)^eta ≤ (N : ℝ)^nu/d := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply (log_le_log_iff (rpow_pos_of_pos hN0 eta)
    (div_pos (rpow_pos_of_pos hN0 nu) hd0)).mp
  rw [log_rpow hN0, residual_log hN hd]
  nlinarith [mul_le_mul_of_nonneg_left hfloor
    (log_pos (by exact_mod_cast hN : (1 : ℝ) < N)).le]

def closedPrime {m : ℕ} {F : Type*} [Fintype F]
    (j : Fin (m+1)) (C : F → Fin (m+1) → ℝ)
    (R alpha : ℝ) (gamma : F → ℝ) : ℝ :=
  ∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f *
    (if ∀ q, (∑ i, C q i * gridCoordinates R f i) ≤ gamma q
      then HighNonunitLegal.G j alpha (gridCoordinates R f) else 0)

def closedIntegral {m : ℕ} {F : Type*} [Fintype F]
    (j : Fin (m+1)) (C : F → Fin (m+1) → ℝ)
    (alpha : ℝ) (gamma : F → ℝ) : ℝ :=
  ∫ t in continuousCube (m+1),
    (if ∀ q, (∑ i, C q i * t i) ≤ gamma q
      then HighNonunitLegal.G j alpha t else 0) * continuousDensity t

/-- All moving affine intercepts, Q, d and the true alpha follow the
same N threshold. Equality atoms remain in the closed prime sum. -/
theorem physical_closed_rows_uniform (m : ℕ) {F : Type*} [Fintype F]
    (j : Fin (m+1)) (C : F → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ i, 1 ≤ |C q i|)
    {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      0 < d → (N : ℝ)^eta ≤ Q/d → 2 ≤ trueAlpha N Q d →
      ∀ gamma : F → ℝ,
        |closedPrime j C (Q/d) (trueAlpha N Q d) gamma -
          closedIntegral j C (trueAlpha N Q d) gamma| < epsilon := by
  obtain ⟨R0, _, hquad⟩ := HighNonunitMasked.uniform_finite_rows m j C hC
    (max 2 (1/eta)) (le_max_left _ _) epsilon he
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T0, le_max_left _ _, ?_⟩
  intro N hN Q d hd hscale ha gamma
  have hN1 : 1 < N := by omega
  exact hquad (Q/d) ((hT0 N ((le_max_right _ _).trans hN)).trans hscale)
    (trueAlpha N Q d) (physical_alpha_mem hN1 hd heta hscale ha) gamma

/-- Native reciprocal-prime mass cap transported before moving Q,d.
This is the paid scalar-Buchstab error source, not a mass assumption. -/
theorem physical_prime_mass {eta : ℝ} (heta : 0 < eta) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ d : ℕ,
      (N : ℝ)^eta ≤ Q/d → ∀ n : ℕ,
      ∀ S : Finset (Fin n → primeSlabPrimes (Q/d)),
        (∑ f ∈ S, primeSlabWeight (Q/d) f) ≤ 5^n := by
  obtain ⟨R0, hmass⟩ := eventually_atTop.mp SecondFunctionalUnitFiniteKernel.mass_eventually
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T0, le_max_left _ _, ?_⟩
  intro N hN Q d hscale n S
  exact hmass (Q/d) ((hT0 N ((le_max_right _ _).trans hN)).trans hscale) n S

/-- Reuse the existing positive same-Theta lift. No total mass is
cancelled; gamma may retain a different original word at every mark. -/
theorem physical_closed_rows_theta (m : ℕ) {F : Type*} [Fintype F]
    (j : Fin (m+1)) (C : F → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ i, 1 ≤ |C q i|)
    {eta epsilon : ℝ} (heta : 0 < eta) (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ,
      ∀ D : Finset ℕ, ∀ sigma : ℕ → ℝ, ∀ gamma : ℕ → F → ℝ,
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, (N : ℝ)^eta ≤ Q/d) →
      (∀ d ∈ D, 2 ≤ trueAlpha N Q d) →
      |(∑ d ∈ D, sigma d * thetaAtom N Q d *
          closedPrime j C (Q/d) (trueAlpha N Q d) (gamma d)) -
        (∑ d ∈ D, sigma d * thetaAtom N Q d *
          closedIntegral j C (trueAlpha N Q d) (gamma d))| ≤
        epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hquad⟩ := physical_closed_rows_uniform m j C hC heta he
  refine ⟨T, hT, ?_⟩
  intro N hN Q D sigma gamma hd hsigma hscale ha
  have hN4 := hT.trans hN
  have hR (d : ℕ) (hm : d ∈ D) : 1 < Q/d :=
    (one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
  exact P2OriginalPositiveSameQMassLift.finite_positive_theta_error hN4 Q D sigma _ _
    hd hsigma hR (fun d hm => (hquad N hN Q d (hd d hm)
      (hscale d hm) (ha d hm) (gamma d)).le)

end
end ImbalancedChen.P2EnhancedNonunitPhysicalQuadrature
