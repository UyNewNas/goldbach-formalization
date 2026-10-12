import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Coordinate bounds for compact sieve parameter sets

A compact subset of the legal domain stays away from its excluded outer
and upper-sieve endpoints. The lower-sieve endpoint may be retained.
Empty sets are allowed in both bounds.
-/

namespace ImbalancedChen

theorem exists_compact_positive_first_coordinate_bounds
    (S : Set (ℝ × ℝ)) (hS : IsCompact S) (hpos : ∀ p ∈ S, 0 < p.1) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p ∈ S, p.1 ∈ Set.Icc a b := by
  obtain ⟨a, ha, hlo⟩ := hS.exists_forall_le' continuous_fst.continuousOn hpos
  obtain ⟨b, hhi⟩ := hS.bddAbove_image continuous_fst.continuousOn
  exact ⟨a, b, ha, fun p hp => ⟨hlo p hp, hhi (Set.mem_image_of_mem _ hp)⟩⟩

theorem exists_compact_strict_second_coordinate_bounds
    (S : Set (ℝ × ℝ)) (hS : IsCompact S) (c : ℝ) (hpos : ∀ p ∈ S, c < p.2) :
    ∃ a b : ℝ, c < a ∧ ∀ p ∈ S, p.2 ∈ Set.Icc a b := by
  obtain ⟨a, ha, hlo⟩ := hS.exists_forall_le' continuous_snd.continuousOn hpos
  obtain ⟨b, hhi⟩ := hS.bddAbove_image continuous_snd.continuousOn
  exact ⟨a, b, ha, fun p hp => ⟨hlo p hp, hhi (Set.mem_image_of_mem _ hp)⟩⟩

end ImbalancedChen
