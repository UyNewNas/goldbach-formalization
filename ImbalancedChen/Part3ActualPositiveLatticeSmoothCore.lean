import ImbalancedChen.Part3CommonSmoothCutoff
import Mathlib.Tactic

/-!
# Original positive lattice smooth mass: minimal recovered core

The original provider is Part3ActualPositiveLatticeSmoothCover (Git blob
 a094a3dcd2b43124f42e8219e2b1b6ef9ac26cb4), already present as a pinned provider
in the accepted P3.2 source tree. Only the eight tight-support facts required by
the existing full-b-support argument and the finite smooth-mass definitions
are restored here. Their original namespaces and declaration bodies are kept.

The original Packet abbreviation is recovered from
Part3ActualSeparatedRowFiniteMatcher (blob c90d4709b3dde3704006ddb8b959c5dc85bcb60a).
Its unrelated outer-carrier and root-packet implementation is not imported.

The full positive lattice cover, its actual packet-image domination, the
original FixedBlock/OriginalData constructor and any analytic estimates remain
outside this small recovered module. This file introduces no new mathematical
lemma and no replacement carrier or cutoff.
-/

namespace ImbalancedChen.Part3.CommonSmoothCutoff

noncomputable section
open Set
open scoped SchwartzMap

-- BEGIN recovered tight_real_support
theorem dyadicCutoff_tsupport_eq_tight :
    tsupport dyadicCutoff = Icc (1 / 2 : ℝ) (5 / 2) := by
  change tsupport (dyadicBump : ℝ → ℝ) = _
  rw [dyadicBump.tsupport_eq]
  ext x
  change |x - 3 / 2| ≤ 1 ↔ 1 / 2 ≤ x ∧ x ≤ 5 / 2
  rw [abs_le]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
-- END recovered tight_real_support

-- BEGIN recovered tight_schwartz_support
theorem dyadicCutoffSchwartz_tsupport_eq_tight :
    tsupport (dyadicCutoffSchwartz : ℝ → ℂ) = Icc (1 / 2 : ℝ) (5 / 2) := by
  have hs : Function.support (dyadicCutoffSchwartz : ℝ → ℂ) =
      Function.support dyadicCutoff := by
    ext x
    simp only [Function.mem_support, dyadicCutoffSchwartz_apply,
      ne_eq, Complex.ofReal_eq_zero]
  change closure (Function.support (dyadicCutoffSchwartz : ℝ → ℂ)) = _
  rw [hs]
  exact dyadicCutoff_tsupport_eq_tight
-- END recovered tight_schwartz_support

-- BEGIN recovered tight_nonzero_support
theorem dyadicCutoffSchwartz_mem_tight_of_ne_zero {x : ℝ}
    (hx : dyadicCutoffSchwartz x ≠ 0) : x ∈ Icc (1 / 2 : ℝ) (5 / 2) := by
  rw [← dyadicCutoffSchwartz_tsupport_eq_tight]
  exact subset_closure hx
-- END recovered tight_nonzero_support

-- BEGIN recovered nonpositive_argument_zero
theorem dyadicCutoffSchwartz_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    dyadicCutoffSchwartz x = 0 := by
  by_contra hn
  have hlo := (dyadicCutoffSchwartz_mem_tight_of_ne_zero hn).1
  linarith
-- END recovered nonpositive_argument_zero

-- BEGIN recovered physical_nonzero_bounds
theorem physical_cutoff_nonzero_bounds {C c : ℝ} (hC : 0 < C)
    (hc : dyadicCutoffSchwartz (c / C) ≠ 0) :
    C / 2 ≤ c ∧ c ≤ 5 * C / 2 := by
  obtain ⟨hlo, hhi⟩ := dyadicCutoffSchwartz_mem_tight_of_ne_zero hc
  have hl := (le_div_iff₀ hC).mp hlo
  have hu := (div_le_iff₀ hC).mp hhi
  constructor <;> linarith
-- END recovered physical_nonzero_bounds

-- BEGIN recovered physical_nonpositive_scale
theorem physical_cutoff_nonpos_scale {C c : ℝ} (hC : C ≤ 0) (hc : 0 ≤ c) :
    dyadicCutoffSchwartz (c / C) = 0 := by
  apply dyadicCutoffSchwartz_eq_zero_of_nonpos
  exact div_nonpos_of_nonneg_of_nonpos hc hC
-- END recovered physical_nonpositive_scale

-- BEGIN recovered physical_nonzero_nonnegative_modulus
theorem physical_cutoff_nonzero_nonneg_modulus {C c : ℝ} (hc : 0 ≤ c)
    (hn : dyadicCutoffSchwartz (c / C) ≠ 0) :
    0 < C ∧ 0 < c ∧ C / 2 ≤ c ∧ c ≤ 5 * C / 2 := by
  have hC : 0 < C := by
    by_contra h
    exact hn (physical_cutoff_nonpos_scale (le_of_not_gt h) hc)
  obtain ⟨hlo, hhi⟩ := physical_cutoff_nonzero_bounds hC hn
  exact ⟨hC, by linarith, hlo, hhi⟩
-- END recovered physical_nonzero_nonnegative_modulus

-- BEGIN recovered physical_nonzero_natural_modulus
theorem physical_cutoff_nonzero_nat_modulus {C : ℝ} {c : ℕ}
    (hn : dyadicCutoffSchwartz ((c : ℝ) / C) ≠ 0) :
    0 < C ∧ 0 < c ∧ C / 2 ≤ (c : ℝ) ∧ (c : ℝ) ≤ 5 * C / 2 := by
  obtain ⟨hC, hc, hlo, hhi⟩ :=
    physical_cutoff_nonzero_nonneg_modulus (Nat.cast_nonneg c) hn
  exact ⟨hC, by exact_mod_cast hc, hlo, hhi⟩
-- END recovered physical_nonzero_natural_modulus

end
end ImbalancedChen.Part3.CommonSmoothCutoff

namespace ImbalancedChen.Part3.ActualFixedFeaturePacketPushforwardSourceOnly

-- BEGIN recovered original_packet_alias
abbrev Packet := (ℕ × ℕ) × ℤ
-- END recovered original_packet_alias

end ImbalancedChen.Part3.ActualFixedFeaturePacketPushforwardSourceOnly

namespace ImbalancedChen.Part3.ActualPositiveLatticeSmoothCoverSourceOnly

noncomputable section
open Classical Finset CommonSmoothCutoff ActualFixedFeaturePacketPushforwardSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

-- BEGIN recovered original_packet_box
def packetBox (B C F : ℝ) : Finset Packet :=
  ((Ioc 0 (Nat.floor (5*B)) ×ˢ Ioc 0 (Nat.floor (10*C))) ×ˢ
    Icc (Int.ceil (-F)) (Int.floor F)).filter (fun k => k.1.1.Coprime k.1.2 ∧ k.2 ≠ 0)
-- END recovered original_packet_box

-- BEGIN recovered original_smooth_mass
def smoothMass (M N : ℝ) (L : Finset Packet) (J : Packet → ℂ) : ℝ :=
  ∑ k ∈ L, scaledDyadicCutoff M k.1.1 * scaledDyadicCutoff N k.1.2 * ‖J k‖^2
-- END recovered original_smooth_mass

-- BEGIN recovered original_six_smooth_mass
def sixSmoothMass (B C : ℝ) (L : Finset Packet) (J : Packet → ℂ) : ℝ :=
  smoothMass B C L J + smoothMass B (2*C) L J + smoothMass B (4*C) L J +
    smoothMass (2*B) C L J + smoothMass (2*B) (2*C) L J + smoothMass (2*B) (4*C) L J
-- END recovered original_six_smooth_mass

-- BEGIN recovered original_smooth_mass_lattice
theorem smoothMass_lattice (M N B C F : ℝ) (J : Packet → ℂ) :
    smoothMass M N (packetBox B C F) J =
      ∑ b ∈ Ioc 0 (Nat.floor (5*B)), ∑ c ∈ Ioc 0 (Nat.floor (10*C)),
        ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
          if b.Coprime c ∧ f ≠ 0 then
            scaledDyadicCutoff M b * scaledDyadicCutoff N c * ‖J ((b,c),f)‖^2 else 0 := by
  simp only [smoothMass, packetBox, sum_filter, sum_product]
-- END recovered original_smooth_mass_lattice

end
end ImbalancedChen.Part3.ActualPositiveLatticeSmoothCoverSourceOnly
