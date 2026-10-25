import ImbalancedChen.P1OriginalFifthEnvelopeTerminalReduction
import ImbalancedChen.ActualPrimeBoxMass

/-!
SOURCE_ONLY / UNCOMPILED.

An unconditional reciprocal-prime bound on every fixed positive terminal
exponent stratum of the original rank-four first-exit fifth carrier.  The
actual target-linked Mertens box theorem bounds the full prime box.  The
historical selected candidates on each genuine fifth joint cell form a
subset of that box.  This does not estimate the moving zero stratum.
-/

namespace ImbalancedChen.P1OriginalFifthPositiveStratumMass

noncomputable section

open Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthWeightedSourceReduction

def stratumCellMass (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega δ a : ℝ) (N cap : ℕ) (j : Label5 m) : ℝ :=
  ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
      (fun p => δ ≤ actualPrimeTupleLog N p 4 ∧
        actualPrimeTupleLog N p 4 < a ∧
        actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j),
    ∏ i, 1 / ((p i : ℝ) - 1)

def stratumSelectedMass (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega δ a : ℝ) (J5 : Finset (Label5 m))
    (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    stratumCellMass e chi m omega δ a N cap j

/-- Every selected original T3 tuple in a terminal stratum `t₄ ≥ δ`
lies in the complete five-dimensional target-linked prime box with *all*
coordinates at least `δ`.  The last-coordinate implication uses strict
ordering from the original historical joint-region dictionary. -/
theorem stratum_cell_subset_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega δ a : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) :
    (sourceCarrier e chi m omega N cap).filter
      (fun p => δ ≤ actualPrimeTupleLog N p 4 ∧
        actualPrimeTupleLog N p 4 < a ∧
        actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j) ⊆
      actualPrimeBoxTuples N (fun _ : Fin 5 => δ)
        (fun _ => (19 / 96 : ℝ)) := by
  intro p hp
  obtain ⟨hcarrier, hδ, _ha, ht⟩ := Finset.mem_filter.mp hp
  have hc : p ∈ candidates (e : ℝ) chi m omega N cap := by
    simpa only [sourceCarrier, candidates] using hcarrier
  have hg := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega
    N cap hN hcap p j ht).mp hc
  have hanti : StrictAnti (actualPrimeTupleLog N p) :=
    ((mem_jointRegion (e : ℝ) chi m omega j _).mp hg.2).2.1
  have hwhole : actualPrimeTupleLog N p ∈
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ))
        (fun _ => (19 / 96 : ℝ)) :=
    logPrimeMeshCell_subset_box (by norm_num) m j ht
  have hbox : actualPrimeTupleLog N p ∈
      logPrimeBox (fun _ : Fin 5 => δ)
        (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro i
    have hhi := (mem_logPrimeBox.mp hwhole i).2
    have hlo : δ ≤ actualPrimeTupleLog N p i := by
      fin_cases i
      · exact hδ.trans (hanti (by decide : (0 : Fin 5) < 4)).le
      · exact hδ.trans (hanti (by decide : (1 : Fin 5) < 4)).le
      · exact hδ.trans (hanti (by decide : (2 : Fin 5) < 4)).le
      · exact hδ.trans (hanti (by decide : (3 : Fin 5) < 4)).le
      · exact hδ
    exact ⟨hlo, hhi⟩
  exact (mem_actualPrimeBoxTuples_log_iff hN
    (fun _ : Fin 5 => δ) (fun _ => (19 / 96 : ℝ)) p).mpr
      ⟨fun i => ⟨(hg.1 i).1, (hg.1 i).2.1⟩, hbox⟩

/-- The fixed positive stratum is bounded by the genuine full-box
reciprocal-prime mass, without any prime-distribution assumption. -/
theorem stratumCellMass_le_primeBoxMass
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega δ a : ℝ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (j : Label5 m) :
    stratumCellMass e chi m omega δ a N cap j ≤
      actualPrimeBoxMass N (fun _ : Fin 5 => δ)
        (fun _ => (19 / 96 : ℝ)) := by
  unfold stratumCellMass actualPrimeBoxMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (stratum_cell_subset_prime_box e chi m omega δ a N cap hN hcap j)
  intro p hp _
  exact actualPrimeBoxWeight_nonneg hp

/-- A finite selected-cell estimate. Multiple selected labels are charged
separately, so no mesh-disjointness theorem is needed. -/
theorem stratumSelectedMass_le_card_mul_primeBoxMass
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega δ a : ℝ)
    (J5 : Finset (Label5 m))
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ)) :
    stratumSelectedMass e chi m omega δ a J5 N cap ≤
      ((selectedFifthCells e chi m omega J5).card : ℝ) *
        actualPrimeBoxMass N (fun _ : Fin 5 => δ)
          (fun _ => (19 / 96 : ℝ)) := by
  unfold stratumSelectedMass
  calc
    _ ≤ ∑ _j ∈ selectedFifthCells e chi m omega J5,
        actualPrimeBoxMass N (fun _ : Fin 5 => δ)
          (fun _ => (19 / 96 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact stratumCellMass_le_primeBoxMass
        e chi m omega δ a N cap hN hcap j
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The imported actual target-deleted Mertens supplier gives an explicit
fixed-stratum ceiling.  Its threshold may depend on `δ`; therefore this is
not uniform under `δ → 0` or a moving cutoff `a(N)`. -/
theorem eventually_fixed_stratum_primeBoxMass_bound
    (δ : ℝ) (hδ : 0 < δ) (hδρ : δ < (19 / 96 : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin 5 => δ)
        (fun _ => (19 / 96 : ℝ)) <
          (∏ _i : Fin 5, Real.log ((19 / 96 : ℝ) / δ)) + 1 := by
  have hlimit := tendsto_actualPrimeBoxMass
    (fun _ : Fin 5 => δ) (fun _ => (19 / 96 : ℝ))
    (fun _ => hδ) (fun _ => hδρ)
  exact hlimit.eventually (eventually_lt_nhds (by linarith))

/-- The resulting unconditional fixed-positive-stratum estimate holds for
every physical enumeration cap once it contains `N^(19/96)`.  This is a
true uniform-in-target statement for fixed `δ > 0`, but its threshold is
not uniform as `δ` approaches zero. -/
theorem eventually_fixed_positive_stratum_selected_bound
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega δ a : ℝ)
    (J5 : Finset (Label5 m)) (hδ : 0 < δ)
    (hδρ : δ < (19 / 96 : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      stratumSelectedMass e chi m omega δ a J5 N cap ≤
        ((selectedFifthCells e chi m omega J5).card : ℝ) *
          ((∏ _i : Fin 5, Real.log ((19 / 96 : ℝ) / δ)) + 1) := by
  filter_upwards [eventually_fixed_stratum_primeBoxMass_bound δ hδ hδρ,
    eventually_ge_atTop (2 : ℕ)] with N hbox hN cap hcap
  calc
    _ ≤ ((selectedFifthCells e chi m omega J5).card : ℝ) *
        actualPrimeBoxMass N (fun _ : Fin 5 => δ)
          (fun _ => (19 / 96 : ℝ)) :=
      stratumSelectedMass_le_card_mul_primeBoxMass
        e chi m omega δ a J5 N cap (by omega) hcap
    _ ≤ _ := mul_le_mul_of_nonneg_left hbox.le (Nat.cast_nonneg _)

end

end ImbalancedChen.P1OriginalFifthPositiveStratumMass
