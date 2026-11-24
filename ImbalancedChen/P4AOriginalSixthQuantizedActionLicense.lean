import ImbalancedChen.P4AOriginalSixthSquareRows

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Saved-sixth, eleven and nineteen-later source conditions provide the actual
square gates of their own masks. Their positive gate margins are explicitly
computed, then the existing quantizer is shown to preserve them. Actual
saved acceptance is NOT inferred from the existence of a row in the file.
The saved source's half floor is proved on the original below-mu prefix
range. Later comparisons still use the unrounded chronological current.
-/
namespace ImbalancedChen.P4AOriginalSixthQuantizedActionLicense
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1QuantizedActionLicense P1GuardFrozenFiniteCapAlgebra
open P1OriginalVariableFourthContinuation P4AOriginalCompleteSixthChronology
open P4AOriginalSixthSquareRows
open P4AOriginalFull87HistoryCore (width)

/-- Saved full and selected squares come from the ORIGINAL source tests.
Its half floor comes from W, not an assumed positive cap field. -/
theorem saved_lower_license (i : P4AOriginalSavedSixthArchive.Row) (t : Fin 6 → ℝ)
    (hs : P4AOriginalSavedSixthArchive.Source i t) (hthird : t 2 ≤ mu) :
    LowerLicense (slots (P4AOriginalSavedSixthArchive.selectedMask i)) t
      (P4AOriginalSavedSixthArchive.endpoint i t) := by
  rcases hs with ⟨_,_,_,_,_,hfull,hremaining,_,hgap⟩
  have hW := finiteMax_seed_le (Finset.Icc 1 31) (fun _ => True)
    (fun m => P4AOriginalSavedSixthArchive.oldPlane i m t)
    (Certificates.P2OriginalSixthElevenLogSemantics.W t)
  change Certificates.P2OriginalSixthElevenLogSemantics.W t ≤
    P4AOriginalSavedSixthArchive.oldUpper i t at hW
  have hh : (1 / 2 : ℝ) < Certificates.P2OriginalSixthElevenLogSemantics.W t := by
    dsimp [Certificates.P2OriginalSixthElevenLogSemantics.W, mu] at *
    linarith
  apply (lowerLicense_iff _ _ _).mpr
  exact ⟨(hh.trans_le hW).trans hgap,
    fun j => by rw [full_dictionary]; exact hfull j,
    fun j hj => by
      rw [remaining_dictionary]
      exact hremaining j ((not_mem_slots _ _).mp hj)⟩

theorem eleven_lower_license
    (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : Fin 6 → ℝ)
    (hs : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) :
    LowerLicense (slots c.selectedMask) t
      (Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) := by
  have h0 := hs.coordinates_pos (0 : Fin 6)
  have hh : (1 / 2 : ℝ) < Certificates.P2OriginalSixthElevenLogSemantics.R0 t := by
    dsimp [Certificates.P2OriginalSixthElevenLogSemantics.R0]
    linarith
  apply (lowerLicense_iff _ _ _).mpr
  exact ⟨(hh.trans_le hs.comparison).trans hs.positiveGap,
    fun j => by rw [full_dictionary]; exact hs.fullSquares j,
    fun j hj => by
      rw [remaining_dictionary]
      exact hs.remainingSquares j ((not_mem_slots _ _).mp hj)⟩

/-- A real later action supplies its original strict comparison improvement.
This is a conclusion from laterEligible, not from a comparison-only entry. -/
theorem later_lower_license (stage : ℕ) (current N : ℝ)
    (c : P4AOriginalSixthLaterLiteral.Cell) (pre : List ℕ)
    (he : laterEligible stage current N c pre) :
    LowerLicense (slots (P4AOriginalSixthLaterLiteral.mask c))
      (primeHistoryLogCoordinates N 6 pre)
      (P4AOriginalSixthLaterSemantics.endpoint c (primeHistoryLogCoordinates N 6 pre)) := by
  obtain ⟨_,_,hs,_,_,hgain⟩ := he
  obtain ⟨hf,hc⟩ := later_source_squares c _ hs
  exact (lowerLicense_iff _ _ _).mpr
    ⟨(later_comparison_half c _ hs).trans hgain,hf,hc⟩

/-- A strict old source gives a positive COMPUTED gate margin. A fixed
positive lower bound on that explicit margin permits one cofinal n for
all points and all actions carrying that bound. No uniform lower bound
on the untrimmed source is claimed. -/
theorem rounded_on_margin_stratum {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ)
    (M : ℝ) (hl : LowerLicense I t M) (hup : M ≤ v (∑ j ∈ I, t j))
    (delta : ℝ) (hd : 0 < delta) (hm : delta ≤ margin I t M)
    (n : ℕ) (hn : 4 * width n < delta) :
    LowerLicense I t (rounded n M : ℝ) ∧
      (∀ g : Gate k, gate I t g + delta / 2 < (rounded n M : ℝ)) ∧
      (rounded n M : ℝ) + width n ≤ v (∑ j ∈ I, t j) := by
  have hg : ∀ g : Gate k, gate I t g + delta ≤ M := by
    intro g
    have h := hm.trans (margin_le I t M g)
    linarith
  obtain ⟨hlo,hhi⟩ := rounded_licensed n I t M delta hd
    (hup.trans (v_le_cap _)) hg hn
  exact ⟨fun g => by have h := hlo g; linarith,hlo,hhi.trans hup⟩

/-- Pointwise cofinal admission is derived, not assumed. Its threshold
can depend on this source point; the uniform stratum statement above is
what may be used in a pre-N common mesh construction. -/
theorem eventually_rounded_licensed {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ)
    (M : ℝ) (hl : LowerLicense I t M) (hup : M ≤ v (∑ j ∈ I, t j)) :
    ∃ n0 : ℕ, ∀ n ≥ n0, LowerLicense I t (rounded n M : ℝ) ∧
      (rounded n M : ℝ) + width n ≤ v (∑ j ∈ I, t j) := by
  have hp := margin_pos hl
  obtain ⟨n0,hn0⟩ := exists_resolution (margin I t M) hp
  refine ⟨n0,?_⟩
  intro n hn
  have h := rounded_on_margin_stratum I t M hl hup (margin I t M) hp le_rfl n
    (by have h := hn0 n hn; have hw := P4AOriginalFull87HistoryCore.width_pos n; linarith)
  exact ⟨h.1,h.2.2⟩

theorem saved_quantized_licence (i : P4AOriginalSavedSixthArchive.Row) (t : Fin 6 → ℝ)
    (hs : P4AOriginalSavedSixthArchive.Source i t) (hthird : t 2 ≤ mu) :
    0 < margin (slots (P4AOriginalSavedSixthArchive.selectedMask i)) t
      (P4AOriginalSavedSixthArchive.endpoint i t) ∧
    ∃ n0 : ℕ, ∀ n ≥ n0,
      LowerLicense (slots (P4AOriginalSavedSixthArchive.selectedMask i)) t
        (rounded n (P4AOriginalSavedSixthArchive.endpoint i t) : ℝ) ∧
      (rounded n (P4AOriginalSavedSixthArchive.endpoint i t) : ℝ) + width n ≤
        v (∑ j ∈ slots (P4AOriginalSavedSixthArchive.selectedMask i), t j) := by
  have hl := saved_lower_license i t hs hthird
  refine ⟨margin_pos hl,eventually_rounded_licensed _ _ _ hl ?_⟩
  rw [sum_slots]
  exact le_rfl

theorem eleven_quantized_licence
    (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell) (t : Fin 6 → ℝ)
    (hs : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t) :
    0 < margin (slots c.selectedMask) t (Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) ∧
    ∃ n0 : ℕ, ∀ n ≥ n0,
      LowerLicense (slots c.selectedMask) t
        (rounded n (Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) : ℝ) ∧
      (rounded n (Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) : ℝ) + width n ≤
        v (∑ j ∈ slots c.selectedMask, t j) := by
  have hl := eleven_lower_license c t hs
  refine ⟨margin_pos hl,eventually_rounded_licensed _ _ _ hl ?_⟩
  rw [sum_slots,v_eq_min]
  exact (lt_min hs.selectedAscending (by
    dsimp only [C]
    linarith [hs.selectedDescending])).le

theorem later_quantized_licence (stage : ℕ) (current N : ℝ)
    (c : P4AOriginalSixthLaterLiteral.Cell) (pre : List ℕ)
    (he : laterEligible stage current N c pre) :
    let t := primeHistoryLogCoordinates N 6 pre
    0 < margin (slots (P4AOriginalSixthLaterLiteral.mask c)) t
      (P4AOriginalSixthLaterSemantics.endpoint c t) ∧
    ∃ n0 : ℕ, ∀ n ≥ n0,
      LowerLicense (slots (P4AOriginalSixthLaterLiteral.mask c)) t
        (rounded n (P4AOriginalSixthLaterSemantics.endpoint c t) : ℝ) ∧
      (rounded n (P4AOriginalSixthLaterSemantics.endpoint c t) : ℝ) + width n ≤
        v (∑ j ∈ slots (P4AOriginalSixthLaterLiteral.mask c), t j) := by
  dsimp only
  have hl := later_lower_license stage current N c pre he
  refine ⟨margin_pos hl,eventually_rounded_licensed _ _ _ hl ?_⟩
  rw [sum_slots]
  exact (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c _ he.2.2.1).le

end
end ImbalancedChen.P4AOriginalSixthQuantizedActionLicense
