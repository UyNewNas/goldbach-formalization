import ImbalancedChen.P1ActualUpperClosedParameterUniformity
import ImbalancedChen.P2OriginalSixthElevenLogSemantics

/-! The closed positive sixth-quotient window includes residual argument
one. The ordinary recurrence at its cube cutoff gives a common threshold
for both actual signed quantities throughout every changed stage. -/
namespace ImbalancedChen.P4AOriginalSixthClosedQuotients
noncomputable section
open Set Filter
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics (S6)

abbrev low : ℝ := 53/4608
abbrev high : ℝ := 1/5
theorem low_pos : 0<low := by norm_num

private def window : Set (ℝ × ℝ) :=
  (Icc low (3 * high) ×ˢ Icc low high) ∩ {q | q.1 ≤ 3 * q.2}

/-- A single ordinary Rosser threshold precedes every target, word,
rounded policy and selected cap. -/
theorem window_threshold (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (p : Fin 6 → ℕ), (∀ i, 0 < p i) → ∀ L : ℝ,
      let t := actualPrimeTupleLog N p
      low ≤ t 5 → t 5 ≤ high → t 5 ≤ L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t → L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t ≤ 3 * t 5 →
      ∀ cap : ℕ, p 5 ≤ cap →
        |actualSmallRosserPlusDensity N cap (p 5 : ℝ) ((N : ℝ)^L / (∏ i, p i : ℕ)) *
          Real.log (N : ℝ) / singularSeries N - 4 / (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t)| < eta := by
  have compact : IsCompact window := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  obtain ⟨N0,hN0,h⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold window compact
      (fun q hq => ⟨low_pos.trans_le hq.1.2.1, low_pos.trans_le hq.1.1.1, hq.2⟩) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp L
  dsimp only
  intro hcut hupper hlo hhi cap hcap
  let t := actualPrimeTupleLog N p
  have hpar : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 5 : ℝ) L =
      (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) := by
    change (L - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ), actualPrimeTupleLog N p 5) =
      (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 (actualPrimeTupleLog N p), actualPrimeTupleLog N p 5)
    rw [Certificates.P2OriginalSixthElevenLogSemantics.S6_eq_sum,actualPrimeTupleLog_sum_prod p hp]
  obtain ⟨hl,hc⟩ := actualRosserQuotientParameters_exact (N : ℝ) (∏ i, p i : ℕ) (p 5 : ℝ) L
    (by exact_mod_cast (show 1 < N by omega))
    (by exact_mod_cast Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hp i))
    (by exact_mod_cast hp 5)
  rw [hpar] at hl hc
  have hwin : (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) ∈ window :=
    ⟨⟨⟨hcut.trans hlo, hhi.trans (by change _ ≤ 3 * high; linarith)⟩, hcut, hupper⟩, hhi⟩
  have hcap' : (p 5 : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hh := h N hN hEven (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) hwin cap (by simpa only [hc] using hcap')
  simpa only [hl,hc] using hh

theorem difference_close (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ (p : Fin 6→ℕ),(∀j,0<p j) → ∀ (P M : ℝ),
    let t := actualPrimeTupleLog N p
    low≤t 5 → t 5≤high → t 5≤P-S6 t → P≤M → M-S6 t≤3*t 5 →
    ∀ cap : ℕ,p 5≤cap →
      |actualPrimeTupleInitialSaving N cap P M p-(4/(P-S6 t)-4/(M-S6 t))|<eta := by
  obtain ⟨N0,h0,hw⟩ := window_threshold (eta/2) (half_pos heta)
  refine ⟨N0,h0,?_⟩
  intro N hN hev p hp P M
  dsimp only
  intro hr hu hP hPM hM cap hcap
  let t := actualPrimeTupleLog N p
  have hm := hw N hN hev p hp M hr hu (hP.trans (sub_le_sub_right hPM _)) hM cap hcap
  have ho := hw N hN hev p hp P hr hu hP ((sub_le_sub_right hPM _).trans hM) cap hcap
  obtain ⟨hm1,hm2⟩ := abs_lt.mp hm
  obtain ⟨ho1,ho2⟩ := abs_lt.mp ho
  unfold actualPrimeTupleInitialSaving
  rw [sub_mul,sub_div]
  apply abs_lt.mpr
  constructor <;> linarith only [hm1,hm2,ho1,ho2]

theorem difference_lower (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ (p : Fin 6→ℕ),(∀j,0<p j) → ∀ (P M : ℝ),
    let t := actualPrimeTupleLog N p
    low≤t 5 → t 5≤high → t 5≤P-S6 t → P≤M → M-S6 t≤3*t 5 →
    ∀ cap : ℕ,p 5≤cap → -eta<actualPrimeTupleInitialSaving N cap P M p := by
  obtain ⟨N0,h0,h⟩ := difference_close eta heta
  refine ⟨N0,h0,?_⟩
  intro N hN hev p hp P M
  dsimp only
  intro hr hu hP hPM hM cap hcap
  let t := actualPrimeTupleLog N p
  have hi := (abs_lt.mp (h N hN hev p hp P M hr hu hP hPM hM cap hcap)).1
  have hpos : 0<P-S6 t := low_pos.trans_le (hr.trans hP)
  have hrec := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hpos (sub_le_sub_right hPM (S6 t))
  linarith only [hi,hrec]

end
end ImbalancedChen.P4AOriginalSixthClosedQuotients
