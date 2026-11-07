import ImbalancedChen.P5ZU1011BufferedPrimeErrorPayment

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
True uniform physical upper-error reserve for ORIGINAL16 actual prime
weights. Paid proper-wall strips and Mertens mass bound choose parameters
before EVERY moving keep mask and tuple-dependent physical buffer map.
This is a positive-error bound, NOT a moving-mask convergence assertion.
-/

namespace ImbalancedChen.P5Z.BufferedPrimeReserve

noncomputable section

open Set Filter Topology
open scoped BigOperators
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenKnotPayment U1011AdaptivePrimeError
open BufferedActualSixteenError BufferedPrimeErrorPayment

def BufferSup (N : ℕ) (η : ℝ) (τ ξ ρ : BufferMap) : Prop :=
  ∀ (p : Policy) (t : Tuple), t ∈ tuples N →
    0 ≤ τ p t ∧ τ p t ≤ η ∧ 0 ≤ ξ p t ∧ ξ p t ≤ η ∧ 0 ≤ ρ p t ∧ ρ p t ≤ η

/-- No cost reserve, mean, arithmetic wall mass or H-correctness is
supplied. All actual scalar errors, the 4681 proper wall family, and the
prime harmonic mass are paid by their proved source theorems internally.
The ENTIRE clamp region remains in every actual pointwise comparison. -/
theorem exists_uniform_physical_prime_reserve (ε : ℝ) (he : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ, 0 < η ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
        (τ ξ ρ : BufferMap), BufferSup N η τ ξ ρ →
          totalError N mask keep τ ξ ρ < ε ∧
            (∀ p : Policy, policyError N mask keep τ ξ ρ p < ε) ∧
            envelopeError N mask keep τ ξ ρ < ε := by
  have hB : 0 < badCostBound := badCostBound_pos
  have hC : 0 ≤ originalCubeMassBound := by
    unfold originalCubeMassBound
    positivity
  have hC1 : 0 < originalCubeMassBound + 1 := by linarith only [hC]
  let e : ℝ := ε / (100 * (originalCubeMassBound + 1))
  have he0 : 0 < e := by dsimp only [e]; positivity
  obtain ⟨δ, hd, Nwall, hNwall, hwall⟩ := exists_uniform_masked_strip_reserve
    (ε / (100 * badCostBound)) (by positivity)
  obtain ⟨Nmass, hNmass⟩ := eventually_atTop.mp eventually_originalCube_mass_bounded
  refine ⟨δ, hd, scale δ e, scale_pos hd he0, max Nwall (max Nmass 2), ?_, ?_⟩
  · exact (le_max_right Nmass 2).trans (le_max_right _ _)
  · intro N hN mask keep τ ξ ρ hbuffers
    have hNW : Nwall ≤ N := (le_max_left _ _).trans hN
    have hNM : Nmass ≤ N := (le_max_left Nmass 2).trans ((le_max_right _ _).trans hN)
    have hsmall : SmallOn N δ e τ ξ ρ := by
      intro t ht p
      exact hbuffers p t ht
    have hMass := hNmass N hNM
    have hStrip := hwall N hNW keep δ hd.le le_rfl
    have hGood : e * actualPrimeBoxMass N
        (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) ≤ ε / 100 := by
      have hh := mul_le_mul_of_nonneg_left hMass he0.le
      have hBudget : e * (originalCubeMassBound + 1) = ε / 100 := by
        dsimp only [e]
        field_simp [hC1.ne']
        <;> ring
      have hExtra : e * originalCubeMassBound ≤ e * (originalCubeMassBound + 1) := by
        nlinarith only [he0]
      exact hh.trans (hExtra.trans_eq hBudget)
    have hBad : badCostBound * maskedStripMass N keep δ < ε / 100 := by
      have hh := mul_lt_mul_of_pos_left hStrip hB
      have hBudget : badCostBound * (ε / (100 * badCostBound)) = ε / 100 := by
        field_simp [hB.ne']
        <;> ring
      simpa only [hBudget] using hh
    have hPayment : payment N keep δ e < ε / 50 := by
      dsimp only [payment]
      linarith only [hGood, hBad]
    have hPayEps : payment N keep δ e < ε := hPayment.trans (by linarith only [he])
    have hTotal := totalError_le_payment N mask keep hd he0 τ ξ ρ hsmall
    have hTotalSmall : 17 * payment N keep δ e < ε := by linarith only [hPayment, he]
    refine ⟨hTotal.trans_lt hTotalSmall, ?_, ?_⟩
    · intro p
      exact (policyError_le_payment N mask keep hd he0 τ ξ ρ hsmall p).trans_lt hPayEps
    · exact (envelopeError_le_payment N mask keep hd he0 τ ξ ρ hsmall).trans_lt hPayEps

end

end ImbalancedChen.P5Z.BufferedPrimeReserve
