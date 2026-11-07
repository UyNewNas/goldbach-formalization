import ImbalancedChen.OriginalFifthRetainedSelectedTailSupport
import ImbalancedChen.OriginalFourthCanonicalIntegerEndpoints
import ImbalancedChen.P1OriginalVariableFifthFullModulusBound

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The actual native fifth retained leaf supplies ALL prefix and tail square
tests at its own physical Q5. A rank bound is derived from this support,
the original global ceiling and physical roughness. One natural endpoint
mesh, width and eventual threshold are then fixed before N. Their complete
endpoint cost fits e/2 above the ORIGINAL physical fifth exponent.

No hSupport, rank ceiling, endpoint-size premise, replacement policy, or
new ancestor cap is assumed. The physical Q5 in the source policy remains
unchanged. This result covers the fifth source; OLD density terms retain
their own separate original carriers and are not inferred from this leaf.
-/

namespace ImbalancedChen.OriginalFifthCanonicalEndpointSupport20261026b

noncomputable section
open Filter Topology
open scoped Classical
open HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation
open OriginalFifthRetainedSelectedTailSupport20261026b
open OriginalFourthCanonicalIntegerEndpoints20261026b

def physicalExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (L : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (rows5 : Finset (FifthRow m)) (leaf : FirstExitLeaf ℕ) : ℝ :=
  exponent5 e chi m omega N rows4 L J rows5 (rosserAncestor 5 leaf.selected)

theorem actual_fifth_rank_bound
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (L : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (rows5 : Finset (FifthRow m))
    (rho : ℝ) (hrho : 0 < rho) (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ)
    (hrough : (N : ℝ) ^ rho ≤ w) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) rows4 L J rows5)
      weight [] true 1 (roughPrimeUniverse N cap w z)) (hlen : 5 ≤ leaf.selected.length) :
    leaf.selected.length ≤ actualRoughVectorRankBound rho := by
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) rows4 L J rows5)
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hne : leaf.selected.reverse ≠ [] := by
    intro hz
    have hh := congrArg List.length hz
    simp only [List.length_reverse, List.length_nil] at hh
    omega
  have hs := retained_native_support_at_actual_Q5 e chi m omega rows4 L J rows5
    N cap w z heupper hN weight leaf hleaf hlen
  have hcap := P1OriginalVariableFifthFullModulusBound.exponent5_le_initial
    e he chi m omega (N : ℝ) rows4 L J rows5 (rosserAncestor 5 leaf.selected)
  have hceiling : initial (e : ℝ) ≤ (5 / 8 : ℝ) := by
    have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
    dsimp [initial, extendedDistributionCap]
    linarith
  have hb := actualRoughPrimeVector_length_le hN hrho (hcap.trans hceiling)
    leaf.selected.reverse hne
    (fun p hp => (mem_roughPrimeUniverse_prime (hsub.subset hp)).pos)
    (fun p hp => hrough.trans (mem_roughPrimeUniverse_lower (hsub.subset hp))) hs
  simpa only [List.length_reverse] using hb

/-- A finite mesh and rounding threshold are chosen BEFORE every source
leaf, arithmetic target and endpoint. ALL chronological tests are paid. -/
theorem exists_actual_fifth_endpoint_realization
    (e : ℚ) (he : 0 < e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (L : ProducerRow → Prop)
    (J : Finset (Fin 5 → Fin (m + 1))) (rows5 : Finset (FifthRow m))
    (rho : ℝ) (hrho : 0 < rho) (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ n : ℕ,
      tau * ((actualRoughVectorRankBound rho : ℝ) + 1) ≤ (e : ℝ) / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (cap : ℕ) (w z : ℝ),
        (N : ℝ) ^ rho ≤ w → z ≤ (N : ℝ) ^ (19 / 96 : ℝ) →
        ∀ (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ),
          leaf ∈ firstExitRetainedLeaves (policy5 e chi m omega (N : ℝ) rows4 L J rows5)
            weight [] true 1 (roughPrimeUniverse N cap w z) →
          5 ≤ leaf.selected.length →
          (∀ p ∈ leaf.selected.reverse, p ≤ integerUpper n N p) ∧
          actualDwellSupport
            ((N : ℝ) ^ (physicalExponent e chi m omega (N : ℝ) rows4 L J rows5 leaf + (e : ℝ) / 2))
            (leaf.selected.reverse.map (integerUpper n N)) ∧
          Fintype.card (Fin leaf.selected.length → Fin 3) ≤ 3 ^ actualRoughVectorRankBound rho := by
  let R := actualRoughVectorRankBound rho
  let tau : ℝ := (e : ℝ) / (4 * ((R : ℝ) + 1))
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hRpos : 0 < (R : ℝ) + 1 := by positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hbudget : tau * ((R : ℝ) + 1) ≤ (e : ℝ) / 2 := by
    have hid : tau * ((R : ℝ) + 1) = (e : ℝ) / 4 := by
      dsimp [tau]
      field_simp [hRpos.ne']
      <;> ring
    rw [hid]
    linarith
  obtain ⟨n, _hmesh, hendpoint⟩ := exists_uniform_canonical_endpoints tau htau
  refine ⟨tau, htau, n, hbudget, ?_⟩
  filter_upwards [hendpoint, eventually_ge_atTop (2 : ℕ)] with N hbound hN
  intro cap w z hrough hz weight leaf hleaf hlen
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using firstExitRetainedLeaves_selected_reverse_sublist
      (policy5 e chi m omega (N : ℝ) rows4 L J rows5)
      weight [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hrank : leaf.selected.reverse.length ≤ R := by
    rw [List.length_reverse]
    exact actual_fifth_rank_bound e he.le chi m omega rows4 L J rows5 rho hrho
      N cap hNr w z hrough heupper weight leaf hleaf hlen
  have hep (p : ℕ) (hp : p ∈ leaf.selected.reverse) :
      p ≤ integerUpper n N p ∧ (integerUpper n N p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ) := by
    have hm := hsub.subset hp
    exact hbound p (mem_roughPrimeUniverse_prime hm).pos
      ((mem_roughPrimeUniverse_upper hm).trans_le hz)
  have hsupport := retained_native_support_at_actual_Q5 e chi m omega rows4 L J rows5
    N cap w z heupper hNr weight leaf hleaf hlen
  change actualDwellSupport
    ((N : ℝ) ^ physicalExponent e chi m omega (N : ℝ) rows4 L J rows5 leaf)
    leaf.selected.reverse at hsupport
  refine ⟨fun p hp => (hep p hp).1, ?_, ?_⟩
  · apply actualDwellSupport_upper_inflation hNr htau.le id (integerUpper n N)
      leaf.selected.reverse hrank (fun p hp => (hep p hp).2)
    · simpa using hsupport
    · linarith
  · have hrank' : leaf.selected.length ≤ actualRoughVectorRankBound rho := by
      simpa only [List.length_reverse] using hrank
    simpa using Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hrank'

end
end ImbalancedChen.OriginalFifthCanonicalEndpointSupport20261026b
