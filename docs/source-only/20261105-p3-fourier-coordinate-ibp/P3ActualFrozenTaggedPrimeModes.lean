import ImbalancedChen.P3ActualFrozenEuclideanPairing
import ImbalancedChen.P3ActualFrozenComplexGroupGamma

/-!
P3.6 / pinned PP completion §4 (F): ORIGINAL slot-ID -> physical ordered
prime tuple Fourier mode, without quotienting or sorting positional weights.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Unlike a label-word permutation, the position-aware pairing below retains
each original Fin n slot ID. A physical prime tuple has one prime for EACH
ID in the given frozen word; unequal lengths explicitly give zero rather
than silently discarding an end of a zip. This proves the actual realized
tuple phase and one-bound, not a global W_T Fourier representation.
It does not claim every original PP atom has been mapped to this box.
-/

namespace ImbalancedChen.P3ActualFrozenTaggedPrimeModes
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.P3PhysicalOriginalW
open ImbalancedChen.P3ActualFrozenOriginalSlotPhase

/-- Phase contributed by the prime at one ORIGINAL ID. A repeated prime
value in two different IDs still sees different U_i and eta_i. -/
def taggedPrimePhase {n : ℕ} (eta U : Fin n → ℝ)
    (i : Fin n) (prime : ℕ) : ℂ :=
  originalSlotPhase eta (slotLog U (fun _ => (prime : ℝ))) i

/-- Ordered, ID-aware phase. The zero base case is used only for pairs
whose lists have the same length in the group mode below. -/
def positionalPhaseSum {n : ℕ} (eta U : Fin n → ℝ) :
    List (Fin n) → List ℕ → ℂ
  | i :: ids, p :: ps =>
      taggedPrimePhase eta U i p + positionalPhaseSum eta U ids ps
  | _, _ => 0

/-- An ACTUAL ordered group positional multiplier, with an explicit
length guard. It is NOT a function of the complete product only. -/
def positionalGroupMode {n : ℕ} (eta U : Fin n → ℝ)
    (ids : List (Fin n)) (ps : List ℕ) : ℂ :=
  if ps.length = ids.length then
    Complex.exp (positionalPhaseSum eta U ids ps)
  else 0

/-- The local physical prime phase is exactly the original slotLog phase
at the same original slot identity. No prime-value distinctness is used. -/
theorem taggedPrimePhase_realized {n : ℕ}
    (eta U : Fin n → ℝ) (values : Fin n → ℕ) (i : Fin n) :
    taggedPrimePhase eta U i (values i) =
      originalSlotPhase eta
        (slotLog U (fun j => (values j : ℝ))) i := by
  rfl

/-- Reindex the REALIZED ordered prime tuple into the actual ID finset.
Nodup is required only for the ID list, not for prime VALUES or labels.
The empty physical word is included. -/
theorem positionalPhaseSum_realized {n : ℕ}
    (eta U : Fin n → ℝ) (values : Fin n → ℕ)
    (ids : List (Fin n)) :
    ids.Nodup →
      positionalPhaseSum eta U ids (ids.map values) =
        ∑ i ∈ ids.toFinset,
          originalSlotPhase eta
            (slotLog U (fun j => (values j : ℝ))) i := by
  induction ids with
  | nil =>
      intro _
      simp [positionalPhaseSum]
  | cons i ids ih =>
      intro h
      obtain ⟨hi, htail⟩ := List.nodup_cons.mp h
      have hphase := taggedPrimePhase_realized eta U values i
      simpa [positionalPhaseSum, hi, hphase] using
        congrArg (fun z : ℂ => taggedPrimePhase eta U i (values i) + z)
          (ih htail)

/-- Therefore the constructed multiplier on the genuine ordered prime
tuple equals the ACTUAL physical frozen-word Fourier inverse character. -/
theorem positionalGroupMode_realized {n : ℕ}
    (eta U : Fin n → ℝ) (values : Fin n → ℕ)
    (ids : List (Fin n)) (hids : ids.Nodup) :
    positionalGroupMode eta U ids (ids.map values) =
      physicalWordCharacter ids eta
        (slotLog U (fun i => (values i : ℝ))) := by
  have hsum := positionalPhaseSum_realized eta U values ids hids
  simpa [positionalGroupMode, physicalWordCharacter] using
    congrArg Complex.exp hsum

/-- Every individual tagged-prime phase has zero real part, for ALL
positive/negative frequencies and without assuming U_i>0. -/
theorem taggedPrimePhase_re_zero {n : ℕ}
    (eta U : Fin n → ℝ) (i : Fin n) (p : ℕ) :
    (taggedPrimePhase eta U i p).re = 0 := by
  simp [taggedPrimePhase, originalSlotPhase, slotLog]

/-- The exact ordered summed exponent remains purely imaginary. -/
theorem positionalPhaseSum_re_zero {n : ℕ}
    (eta U : Fin n → ℝ) (ids : List (Fin n)) (ps : List ℕ) :
    (positionalPhaseSum eta U ids ps).re = 0 := by
  induction ids generalizing ps with
  | nil =>
      cases ps <;> simp [positionalPhaseSum]
  | cons i ids ih =>
      cases ps with
      | nil => simp [positionalPhaseSum]
      | cons p ps =>
          simp [positionalPhaseSum, taggedPrimePhase_re_zero, ih ps]

/-- The positional multiplier required by physicalComplexLabelGamma is
automatically one-bounded on ANY physical tuple, including mismatched
lengths (which have weight zero). This is not a bound on the PP error. -/
theorem positionalGroupMode_norm_le_one {n : ℕ}
    (eta U : Fin n → ℝ) (ids : List (Fin n)) (ps : List ℕ) :
    ‖positionalGroupMode eta U ids ps‖ ≤ 1 := by
  by_cases h : ps.length = ids.length
  · simp [positionalGroupMode, h, Complex.norm_exp,
      positionalPhaseSum_re_zero]
  · simp [positionalGroupMode, h]

/-- Same one-bound, at EACH of the three genuine endpoint-frozen ID words;
this is the exact hypothesis needed by the existing physical complex
gamma coefficient lemma, once the full label-word compiler is connected. -/
theorem actual_frozen_positional_modes_one_bound {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (eta U : Fin n → ℝ) (ps₀ ps₁ ps₂ : List ℕ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    (‖positionalGroupMode eta U slots.1 ps₀‖ ≤ 1) ∧
    (‖positionalGroupMode eta U slots.2.1 ps₁‖ ≤ 1) ∧
    (‖positionalGroupMode eta U slots.2.2 ps₂‖ ≤ 1) := by
  exact ⟨positionalGroupMode_norm_le_one _ _ _ _,
    positionalGroupMode_norm_le_one _ _ _ _,
    positionalGroupMode_norm_le_one _ _ _ _⟩

/-- Fully constructed physical THREE-group mode for realized original
prime assignments, not an assumption of separated weights. The words are
computed by the ACTUAL frozen allocator and the identical original IDs
follow their primes through all three multipliers. -/
theorem actual_frozen_original_prime_mode_factors {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta U : Fin n → ℝ) (values : Fin n → ℕ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    originalSlotCharacter eta (slotLog U (fun i => (values i : ℝ))) =
      positionalGroupMode eta U slots.1 (slots.1.map values) *
        (positionalGroupMode eta U slots.2.1 (slots.2.1.map values) *
          positionalGroupMode eta U slots.2.2 (slots.2.2.map values)) := by
  dsimp only
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  have hperm : (slots.1 ++ slots.2.1 ++ slots.2.2).Perm
      (p 0 :: p 1 :: p 2 :: tail) :=
    actualFrozenSelectedPairSlots_perm D A yz upper p tail
  have htotal : (slots.1 ++ slots.2.1 ++ slots.2.2).Nodup :=
    hperm.nodup_iff.mpr hnodup
  obtain ⟨h₀, h₂₃, _⟩ := List.nodup_append.mp htotal
  obtain ⟨h₁, h₂, _⟩ := List.nodup_append.mp h₂₃
  have hbase :
      originalSlotCharacter eta (slotLog U (fun i => (values i : ℝ))) =
        physicalWordCharacter slots.1 eta (slotLog U (fun i => (values i : ℝ))) *
          (physicalWordCharacter slots.2.1 eta (slotLog U (fun i => (values i : ℝ))) *
            physicalWordCharacter slots.2.2 eta (slotLog U (fun i => (values i : ℝ)))) :=
    actual_frozen_original_phase_from_words
      D A yz upper p tail hnodup hcover eta
        (slotLog U (fun i => (values i : ℝ)))
  rw [← positionalGroupMode_realized eta U values slots.1 h₀,
      ← positionalGroupMode_realized eta U values slots.2.1 h₁,
      ← positionalGroupMode_realized eta U values slots.2.2 h₂] at hbase
  exact hbase

end
end ImbalancedChen.P3ActualFrozenTaggedPrimeModes
