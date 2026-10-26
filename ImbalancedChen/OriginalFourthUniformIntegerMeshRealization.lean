import ImbalancedChen.OriginalFourthCanonicalIntegerEndpoints
import ImbalancedChen.P1OriginalVariableFourthDescendantLevel

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Actual original finite endpoint realization with the parameter order
closed. The original rough exponent gives the rank bound from the actual
retained state and its original cap ceiling. A positive width and a single
finite logarithmic mesh are then chosen BEFORE N. Every later actual
original source state receives canonical natural upper endpoints, full
buffered square support and a uniform finite word bound.

Neither a rank ceiling, endpoint inflation, nor endpoint support is an
input. Native policy, raw-Q3 seed, original ordered maximum, target prime
deletion and physical rough cutoff remain unchanged. This supplies finite
geometric licensing only; the external distribution and authentic archived
twenty-two-stage history witnesses remain OPEN.
-/

namespace ImbalancedChen.OriginalFourthUniformIntegerMeshRealization20261026b

noncomputable section
open Filter Topology
open scoped Classical
open HistoricalThirdCoarse VariableEnvelope P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFourthPhysicalOwnedModulusSupport20261026b
open OriginalFourthOwnedEndpointBuffer20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- The rank ceiling is derived from the real original source state,
its physical rough lower endpoint and its actual retained cap. -/
theorem actual_original_rank_bound (he : 0 ≤ e) (rho : ℝ) (hrho : 0 < rho)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (hrough : (N : ℝ) ^ rho ≤ w)
    (weight : ℕ → ℝ) (rank : ℕ) (hrank : 4 ≤ rank) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    rank ≤ actualRoughVectorRankBound rho := by
  have hlen : state.selectedPrefix.reverse.length = rank := by
    rw [List.length_reverse]
    exact firstExitDepthFrontier_selected_length rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hne : state.selectedPrefix.reverse ≠ [] := by
    intro hn
    have hh := congrArg List.length hn
    simp only [List.length_nil, hlen] at hh
    omega
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  have hphysical := actual_owned_frontier_dwell records e chi m omega licensed
    N cap hN.le w z weight rank hrank state hstate
  change actualDwellSupport
    ((N : ℝ) ^ ownedExponent records e chi m omega (N : ℝ) licensed
      state.selectedPrefix) state.selectedPrefix.reverse at hphysical
  have hinit := P1OriginalVariableFourthDescendantLevel.producer_exponent4_le_initial
    e chi he m omega (N : ℝ) (fourthFamily records) licensed
    (rosserAncestor 4 state.selectedPrefix)
  change ownedExponent records e chi m omega (N : ℝ) licensed state.selectedPrefix ≤
    initial e at hinit
  have hceiling : initial e ≤ (5 / 8 : ℝ) := by
    dsimp [initial, extendedDistributionCap]
    linarith
  have hr := actualRoughPrimeVector_length_le hN hrho (hinit.trans hceiling)
    state.selectedPrefix.reverse hne
    (fun p hp => (mem_roughPrimeUniverse_prime (hsub.subset hp)).pos)
    (fun p hp => hrough.trans (mem_roughPrimeUniverse_lower (hsub.subset hp))) hphysical
  rwa [hlen] at hr

/-- A positive width and ONE mesh precede all targets, caps, source
histories, rows and integer endpoints. The source's rank ceiling and all
natural endpoint bounds are conclusions from its actual arithmetic data. -/
theorem exists_actual_uniform_integer_endpoint_realization
    (he : 0 < e) (rho : ℝ) (hrho : 0 < rho) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ,
      tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ e ∧
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (rank : ℕ), 4 ≤ rank → ∀ state : FirstExitDepthState ℕ,
          state ∈ firstExitDepthFrontier rank
            (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
            weight [] true 1 (roughPrimeUniverse N cap w z) →
          (∀ p ∈ state.selectedPrefix.reverse, p ≤ integerUpper n N p) ∧
          actualDwellSupport
            ((N : ℝ) ^ (ownedExponent records e chi m omega (N : ℝ) licensed
              state.selectedPrefix + e))
            (state.selectedPrefix.reverse.map (integerUpper n N)) ∧
          Fintype.card (Fin rank → Fin 3) ≤ 3 ^ actualRoughVectorRankBound rho := by
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := e / (2 * ((R : ℝ) + 1))
  have hRpos : 0 < (R : ℝ) + 1 := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hwidthEq : tau * ((R : ℝ) + 1) = e / 2 := by
    dsimp [tau]
    field_simp [hRpos.ne']
    <;> ring
  have hwidth : tau * ((R : ℝ) + 1) ≤ e := by rw [hwidthEq]; linarith
  obtain ⟨n, _hstep, hcanonical⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨tau, htau, n, hwidth, ?_⟩
  filter_upwards [hcanonical, eventually_ge_atTop (2 : ℕ)] with N hcanonicalN hN
  intro cap w z hrough hz weight rank hrank state hstate
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hbound : rank ≤ R := actual_original_rank_bound records e chi m omega licensed
    he.le rho hrho N cap hNr w z hrough weight rank hrank state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse N cap w z) state hstate
  have hendpoints (p : ℕ) (hp : p ∈ state.selectedPrefix.reverse) :
      p ≤ integerUpper n N p ∧
        (integerUpper n N p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ) := by
    have hmem := hsub.subset hp
    exact hcanonicalN p (mem_roughPrimeUniverse_prime hmem).pos
      ((mem_roughPrimeUniverse_upper hmem).trans_le hz)
  refine ⟨fun p hp => (hendpoints p hp).1, ?_, ?_⟩
  · exact actual_uniform_endpoint_buffer records e chi m omega licensed
      N cap hNr w z tau htau.le R hwidth weight rank hrank hbound state hstate
      (integerUpper n N) (fun p hp => (hendpoints p hp).2)
  · simpa using
      Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hbound

end
end ImbalancedChen.OriginalFourthUniformIntegerMeshRealization20261026b
