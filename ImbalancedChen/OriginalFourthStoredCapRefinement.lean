import ImbalancedChen.StoredHistoricalBoxPermit
import ImbalancedChen.P1OriginalFifthRawBoxGateSoundness

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing storedBoxCapCheck already accepts an arbitrary rational
ceiling. The exact buffered ceiling is min nu (qVLo(sum lo,sum hi)-2e).
No renamed copy of that constructor is introduced here.

NEW: a passing stored parent cap remains the SAME passing cap on EVERY
nested rational child box, with its original old cap and selected mask.
Its strict buffered full/selected gates persist. Recomputing a child's
midpoint may give another number; no midpoint equality is asserted.
All box/cap/buffer parameters precede N. External original distribution
licences are not inferred by this geometric refinement theorem.
-/

namespace ImbalancedChen.OriginalFourthStoredCapRefinement20261026b

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1OriginalPrefixRowDecodeSoundness
open P2OriginalFourthCapProducerInterface
open P1OriginalFifthRawBoxGateSoundness

/-- Reuses the existing rational gate monotonicity and tent-interval
narrowing suppliers. The old cap and selected mask are kept fixed. -/
theorem selectedCapUpper_narrower {n : ℕ} (I : Finset (Fin n))
    (nu nu' : ℚ) (lo hi lo' hi' : Fin n → ℚ)
    (hnu : nu ≤ nu') (hl : ∀ i, lo i ≤ lo' i) (hu : ∀ i, hi' i ≤ hi i) :
    selectedCapUpper I nu lo hi ≤ selectedCapUpper I nu' lo' hi' := by
  apply min_le_min hnu
  apply qVLo_mono_narrower
  · exact Finset.sum_le_sum (fun i _ => hl i)
  · exact Finset.sum_le_sum (fun i _ => hu i)

/-- Every nested child accepts the SAME stored rational cap. This does
not replace the stored value by an independently recomputed midpoint. -/
theorem stored_cap_check_narrower {n : ℕ} (I : Finset (Fin n))
    (old nu nu' cap : ℚ) (lo hi lo' hi' : Fin n → ℚ)
    (hnu : nu ≤ nu') (hl : ∀ i, lo i ≤ lo' i) (hu : ∀ i, hi' i ≤ hi i)
    (hc : storedBoxCapCheck I old nu lo hi cap = true) :
    storedBoxCapCheck I old nu' lo' hi' cap = true := by
  have hp := (storedBoxCapCheck_iff I old nu lo hi cap).mp hc
  apply (storedBoxCapCheck_iff I old nu' lo' hi' cap).mpr
  exact ⟨(selectedCapLower_mono_rat I old hu).trans_lt hp.1,
    hp.2.trans_le (selectedCapUpper_narrower I nu nu' lo hi lo' hi' hnu hl hu)⟩

/-- The original buffered ceiling also increases under refinement.
One parent permit therefore supplies every child and its strict 2e margin. -/
theorem same_buffered_cap_on_child {n : ℕ} (I : Finset (Fin n))
    (old nu e cap : ℚ) (lo hi lo' hi' : Fin n → ℚ)
    (hl : ∀ i, lo i ≤ lo' i) (hu : ∀ i, hi' i ≤ hi i)
    (hc : storedBoxCapCheck I old
      (min nu (qVLo (∑ i ∈ I, lo i) (∑ i ∈ I, hi i) - 2 * e)) lo hi cap = true) :
    storedBoxCapCheck I old
        (min nu (qVLo (∑ i ∈ I, lo' i) (∑ i ∈ I, hi' i) - 2 * e)) lo' hi' cap = true ∧
      cap + 2 * e < qVLo (∑ i ∈ I, lo' i) (∑ i ∈ I, hi' i) := by
  have ht : qVLo (∑ i ∈ I, lo i) (∑ i ∈ I, hi i) ≤
      qVLo (∑ i ∈ I, lo' i) (∑ i ∈ I, hi' i) :=
    qVLo_mono_narrower (Finset.sum_le_sum (fun i _ => hl i))
      (Finset.sum_le_sum (fun i _ => hu i))
  have hnu := min_le_min (le_refl nu) (sub_le_sub_right ht (2 * e))
  have hchild := stored_cap_check_narrower I old _ _ cap lo hi lo' hi' hnu hl hu hc
  refine ⟨hchild, ?_⟩
  have hhigh := ((storedBoxCapCheck_iff I old _ lo' hi' cap).mp hchild).2
  have hcnu : cap < min nu (qVLo (∑ i ∈ I, lo' i) (∑ i ∈ I, hi' i) - 2 * e) :=
    hhigh.trans_le (min_le_left _ _)
  have hbuf := hcnu.trans_le (min_le_right _ _)
  linarith

/-- A literal original fourth row, with its mask and lattice endpoints,
keeps one parent cap on every child. All four full squares and ALL
unselected complement squares lie below it; it lies strictly below the
actual buffered row candidate, not merely below the unbuffered tent. -/
theorem original_fourth_child_geometry (raw : FourthWireRow) (old nu e cap : ℚ)
    (lo hi : QEndpoint)
    (hl : ∀ i, raw.toProducerRow.lower i ≤ lo i)
    (hu : ∀ i, hi i ≤ raw.toProducerRow.upper i)
    (hc : storedBoxCapCheck raw.toProducerRow.selected old
      (min nu (qVLo (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.lower i)
        (∑ i ∈ raw.toProducerRow.selected, raw.toProducerRow.upper i) - 2 * e))
      raw.toProducerRow.lower raw.toProducerRow.upper cap = true)
    (t : Point) (htl : ∀ i, (lo i : ℝ) ≤ t i) (htu : ∀ i, t i ≤ (hi i : ℝ)) :
    t ∈ raw.toProducerRow.box ∧ (old : ℝ) < cap ∧ (cap : ℝ) < nu ∧
      (1 / 2 : ℝ) < cap ∧
      (∀ j, prefixSquareExpr t j < cap) ∧
      (∀ j ∉ raw.toProducerRow.selected, selectedSquareExpr raw.toProducerRow.selected t j < cap) ∧
      (cap : ℝ) < raw.toProducerRow.bufferedCandidate (e : ℝ) t := by
  obtain ⟨hchild, hbuffer⟩ := same_buffered_cap_on_child raw.toProducerRow.selected old nu e cap
    raw.toProducerRow.lower raw.toProducerRow.upper lo hi hl hu hc
  have hg := storedBoxCapCheck_sound raw.toProducerRow.selected old _ lo hi cap hchild t htl htu
  have hbox : t ∈ raw.toProducerRow.box := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (Rat.cast_le.mpr (hl i)).trans (htl i)
    · exact (htu i).trans (Rat.cast_le.mpr (hu i))
  have hcapnu : (cap : ℝ) < nu := by
    have hq : (min nu (qVLo (∑ i ∈ raw.toProducerRow.selected, lo i)
        (∑ i ∈ raw.toProducerRow.selected, hi i) - 2 * e) : ℚ) ≤ nu := min_le_left _ _
    exact hg.2.1.trans_le (Rat.cast_le.mpr hq)
  have hsumlo : ((∑ i ∈ raw.toProducerRow.selected, lo i : ℚ) : ℝ) ≤
      ∑ i ∈ raw.toProducerRow.selected, t i := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => htl i)
  have hsumhi : (∑ i ∈ raw.toProducerRow.selected, t i) ≤
      ((∑ i ∈ raw.toProducerRow.selected, hi i : ℚ) : ℝ) := by
    push_cast
    exact Finset.sum_le_sum (fun i _ => htu i)
  have hcast : (cap : ℝ) + 2 * (e : ℝ) <
      (qVLo (∑ i ∈ raw.toProducerRow.selected, lo i)
        (∑ i ∈ raw.toProducerRow.selected, hi i) : ℝ) := by exact_mod_cast hbuffer
  have htent := qVLo_le_v hsumlo hsumhi
  refine ⟨hbox, hg.1, hcapnu, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, ?_⟩
  rw [ProducerRow.bufferedCandidate_eq]
  linarith

end
end ImbalancedChen.OriginalFourthStoredCapRefinement20261026b
