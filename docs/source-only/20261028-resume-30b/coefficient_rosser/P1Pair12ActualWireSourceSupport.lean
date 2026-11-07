import ImbalancedChen.P1Pair12RetainedSignedSource
import ImbalancedChen.P2ActualFifthRaw31SupportCeiling
import ImbalancedChen.P1OriginalPrefixRowFiniteCheckSoundness
import ImbalancedChen.P1OriginalFullTableActualProducerAdapter
import ImbalancedChen.P1OriginalVariableFourthActiveOnly
import ImbalancedChen.P1OriginalVariableFifthFullModulusBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The numeric-mask dictionary already has a proof in the first-batch raw31
supplier; it is reused. Fourth Geometry now comes from the original rational
wire checker, with one literal archived row given as a closed finite proof.
An eligible actual fifth row supplies its original selected-third cell AND
the natural-prime rough activation. A strict actual fifth improvement must
have such a row, since an empty eligible maximum equals the inherited cap.
The unsupported branch is preserved explicitly in the source decomposition.
No assertion that all retained sixth prefixes have selected-third support is
made. All-pass/archive parse, fifth coverage, H5 and sixth licence stay open.
-/

namespace ImbalancedChen.P1Pair12ActualWireSourceSupport

noncomputable section
open Classical
open scoped BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalPrefixRowFiniteCheckSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics
open P1Pair12RetainedSignedSource

/-- Reconstruct the exact original wire fields; no gain or owner is added. -/
def rowWire (r : ProducerRow) : FourthWireRow := ⟨r.lo, r.hi, r.mask⟩

@[simp] theorem rowWire_toProducerRow (r : ProducerRow) :
    (rowWire r).toProducerRow = r := by cases r; rfl

/-- The licence is the actual source's finite rational geometry program.
The original ordered record bank is kept, rather than assumed all-pass. -/
def sourceGeometryFlag (r : ProducerRow) : Bool := fourthGeometryCheck (rowWire r)

theorem sourceGeometryFlag_sound (r : ProducerRow)
    (h : sourceGeometryFlag r = true) : r.Geometry := by
  have hr := fourthGeometryCheck_sound (rowWire r) h
  simpa only [rowWire_toProducerRow] using hr

/-- Literal row zero of the SHA-pinned original fourth NPZ. The external
row locator is provenance only; this theorem's input is the displayed
integer record and its source checker, not a stored numerical gain. -/
def originalFourthRow0 : FourthWireRow :=
  ⟨![14336, 13824, 13568, 13312], ![14848, 14336, 13824, 13440], 14⟩

theorem originalFourthRow0_check : fourthGeometryCheck originalFourthRow0 = true := by
  decide

theorem originalFourthRow0_geometry : originalFourthRow0.toProducerRow.Geometry :=
  fourthGeometryCheck_sound originalFourthRow0 originalFourthRow0_check

theorem originalFourthRow0_numeric_mask (t : Physical) :
    (∑ i ∈ originalFourthRow0.toProducerRow.selected,
      t (i.castLE (by omega : 4 ≤ 6))) = subsetSum 14 t := by
  exact P2ActualFifthRaw31SupportCeiling.producer_selected_sum_eq_raw31
    originalFourthRow0.toProducerRow originalFourthRow0_geometry t

/-- The selected fifth row's original whole-cell lower endpoint gives
natural-prime activation, including equality at the rough threshold. -/
theorem eligible_fifth_original_third_supported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 < N)
    (J5 : Finset (Label5 m)) (r : FifthRow m)
    (pre : List ℕ) (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p)
    (hr : eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre)) :
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  have hg := eligible_original_third_gate e chi m omega J5 r _ hr
  let j3 := historicalPrefixProject (by omega : 3 ≤ 5) r.cell
  have hj : j3 ∈ HistoricalThirdCoarse.cells (e : ℝ) chi m := hg.1
  have ht3 : primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) ∈
      logPrimeMeshCell 0 (19 / 96) m j3 := by
    rw [primeHistoryLogCoordinates_eq_historicalPrefixProject N (by omega : 3 ≤ 5) hlen]
    exact mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) hr.2.2
  have hlen3 : (rosserAncestor 3 pre).length = 3 := by
    rw [rosserAncestor_length, hlen]
    rfl
  have hpos3 : ∀ p ∈ rosserAncestor 3 pre, 0 < p := by
    intro p hp
    exact hpos p (List.mem_of_mem_drop hp)
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m j3 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m j3 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j3) 2
  have hrough : omega ≤ primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2 := by
    have h := hg.2
    change omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m j3 2 : ℝ) at h
    rw [hcast] at h
    exact h.trans (mem_logPrimeMeshCell.mp ht3 2).1
  have hactivation : HistoricalThirdCoarse.active omega N (rosserAncestor 3 pre) := by
    refine ⟨hlen3, ?_⟩
    have h := Real.rpow_le_rpow_of_exponent_le hN.le hrough
    rwa [rpow_primeHistoryLogCoordinates N hN hlen3 hpos3 (2 : Fin 3)] at h
  exact ⟨hactivation, j3, hj, ht3⟩

/-- A strict actual finite-maximum improvement supplies an eligible row;
its selected-third support is derived from the original row's own gates. -/
theorem fifth_strict_improvement_original_third_supported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 < N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (pre : List ℕ) (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p)
    (hgain : inherited4 e chi m omega N rows4 licensed4 pre <
      exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre) :
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  by_contra hs
  have hout : ∀ r ∈ rows5,
      ¬ eligible e chi m omega J5 r (primeHistoryLogCoordinates N 5 pre) := by
    intro r _hr heligible
    exact hs (eligible_fifth_original_third_supported e chi m omega N hN
      J5 r pre hlen hpos heligible)
  have heq := exponent5_outside e chi m omega N rows4 licensed4 J5 rows5 pre hout
  rw [heq] at hgain
  exact (lt_irrefl _) hgain

/-- Outside the genuine third support the fifth finite maximum is exactly
its inherited fourth value. This branch is kept in the signed source. -/
theorem fifth_eq_inherited_of_not_original_third_supported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ) (hN : 1 < N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))
    (pre : List ℕ) (hlen : pre.length = 5) (hpos : ∀ p ∈ pre, 0 < p)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre =
      inherited4 e chi m omega N rows4 licensed4 pre := by
  apply exponent5_outside e chi m omega N rows4 licensed4 J5 rows5 pre
  intro r _hr heligible
  exact hs (eligible_fifth_original_third_supported e chi m omega N hN
    J5 r pre hlen hpos heligible)

/-- Both unsupported branches have the literal Theta seed. Every fourth
producer candidate is strictly lower, so no overlapping row can change it. -/
theorem inherited4_eq_initial_of_unsupported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (pre : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    inherited4 e chi m omega N rows4 licensed4 pre = HistoricalThirdCoarse.initial (e : ℝ) := by
  have hseed : seedExponent (e : ℝ) chi m omega N (rosserAncestor 4 pre) =
      HistoricalThirdCoarse.initial (e : ℝ) := by
    unfold seedExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
    rw [rosserAncestor_nested 3 4 (by omega), if_neg hs]
  unfold inherited4 exponent4
  split_ifs
  · unfold profile4
    rw [hseed]
    apply finiteMax_eq_seed_of_dominated
    intro r _hr _heligible
    exact (P1OriginalVariableFourthActiveOnly.bufferedCandidate_lt_initial
      (e : ℝ) r _).le
  · exact hseed

/-- Even a fifth maximum with arbitrary overlapping candidates preserves
Theta exactly on inactive OR active-unselected original third ancestors. -/
theorem fifth_eq_initial_of_unsupported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (pre : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre =
      HistoricalThirdCoarse.initial (e : ℝ) := by
  have hfour := inherited4_eq_initial_of_unsupported
    e chi m omega N rows4 licensed4 pre hs
  unfold exponent5
  split_ifs
  · rw [hfour]
    apply finiteMax_eq_seed_of_dominated
    intro r _hr _heligible
    exact P1OriginalVariableFifthFullModulusBound.fifth_candidate_le_initial
      e r.selected _
  · exact hfour

/-- All actual fifth values that differ from the Theta fallback have real
selected-third support, including values inherited from a fourth update. -/
theorem fifth_noninitial_original_third_supported
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m)) (pre : List ℕ)
    (hne : exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre ≠
      HistoricalThirdCoarse.initial (e : ℝ)) :
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre) := by
  by_contra hs
  exact hne (fifth_eq_initial_of_unsupported e chi m omega N
    rows4 licensed4 J5 rows5 pre hs)

section ActualSource
variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
  (records4 : List FourthWireRow) (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- Same full record bank, with precisely the proved source-geometry flag.
No theorem that every archived row passes has been assumed or evaluated. -/
def wirePolicy5 (N : ℕ) : Bool → List ℕ → Bool :=
  policy5 e chi m omega (N : ℝ) (fourthFamily records4)
    (fun r => sourceGeometryFlag r = true) J5 rows5

def noninitial5 (N : ℕ) (pre : List ℕ) : Prop :=
  exponent5 e chi m omega (N : ℝ) (fourthFamily records4)
    (fun r => sourceGeometryFlag r = true) J5 rows5 (rosserAncestor 5 pre) ≠
      HistoricalThirdCoarse.initial (e : ℝ)

/-- This is a real arithmetic-source frontier, not a reciprocal-density
frontier premise. A noninitial cap proves support; original wire flags
prove Geometry; the first-batch raw31 dictionary proves every numeric mask. -/
theorem actual_wire_frontier_parent_ceiling
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 6
      (wirePolicy5 e chi m omega records4 J5 rows5 N)
      (fun _ : ℕ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (he : 0 ≤ e)
    (hc : PhysicalCell .pair12_fixed (primeHistoryLogCoordinates (N : ℝ) 6 state.selectedPrefix))
    (hne : noninitial5 e chi m omega records4 J5 rows5 N state.selectedPrefix) :
    P1ThirdFallbackSupport.supported (e : ℝ) chi m omega (N : ℝ)
        (rosserAncestor 3 state.selectedPrefix) ∧
      exponent5 e chi m omega (N : ℝ) (fourthFamily records4)
          (fun r => sourceGeometryFlag r = true) J5 rows5
          (rosserAncestor 5 state.selectedPrefix) ≤
        oldCap .pair12_fixed (primeHistoryLogCoordinates (N : ℝ) 6 state.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 6
    (wirePolicy5 e chi m omega records4 J5 rows5 N) (fun _ : ℕ => 1)
    [] (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hs := fifth_noninitial_original_third_supported e chi m omega
    (N : ℝ) (fourthFamily records4) (fun r => sourceGeometryFlag r = true)
    J5 rows5 (rosserAncestor 5 state.selectedPrefix) hne
  rw [rosserAncestor_nested 3 5 (by omega)] at hs
  refine ⟨hs, ?_⟩
  apply P2ActualFifthRaw31SupportCeiling.actual_fifth_exponent_le_raw31
    e chi m omega (N : ℝ) (fourthFamily records4)
    (fun r => sourceGeometryFlag r = true) J5 rows5
    .pair12_fixed state.selectedPrefix hlen hc he hs
  intro r _hr hflag
  exact sourceGeometryFlag_sound r hflag

private theorem list_sum_split {α : Type*} (states : List α) (P : α → Prop)
    [DecidablePred P] (F : α → ℝ) :
    (states.map F).sum = ((states.filter (fun x => decide (P x))).map F).sum +
      ((states.filter (fun x => decide (¬ P x))).map F).sum := by
  induction states with
  | nil => simp
  | cons s states ih =>
      by_cases hs : P s <;> simp [hs, ih] <;> ring

/-- The noninitial-cap/pair12 branch and its complement sum to the
entire same-rho update. No unsupported branch is discarded; inherited fourth updates are included. -/
theorem actual_wire_physical_change_split
    (fresh : Bool → List ℕ → Bool) (hfresh : ∀ pre, fresh true pre = true)
    (N cap mark : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    let R := wirePolicy5 e chi m omega records4 J5 rows5 N
    let Rnew := firstExitDepthSplicePolicy 6 R fresh
    let states := firstExitDepthFrontier 6 R (fun _ : ℕ => 1) [] true 1
      (roughPrimeUniverse N cap w z)
    let P := fun s : FirstExitDepthState ℕ =>
      noninitial5 e chi m omega records4 J5 rows5 N s.selectedPrefix ∧
        PhysicalCell .pair12_fixed (primeHistoryLogCoordinates (N : ℝ) 6 s.selectedPrefix)
    let delta := fun s : FirstExitDepthState ℕ =>
      signedTest fresh (fun _ => 1) (attachedLeafTest N cap mark w L G)
          s.selectedPrefix s.positive s.mass s.remaining -
        signedTest R (fun _ => 1) (attachedLeafTest N cap mark w L G)
          s.selectedPrefix s.positive s.mass s.remaining
    (∑ q ∈ actualSmallRoughModuli (Rnew false) N cap w z,
      actualSmallRoughRho (Rnew false) N cap w z L q * G (mark * q)) -
      (∑ q ∈ actualSmallRoughModuli (R false) N cap w z,
        actualSmallRoughRho (R false) N cap w z L q * G (mark * q)) =
      ((states.filter (fun x => decide (P x))).map delta).sum +
        ((states.filter (fun s => decide (¬ P s))).map delta).sum := by
  dsimp only
  rw [show wirePolicy5 e chi m omega records4 J5 rows5 N =
    policy5 e chi m omega (N : ℝ) (fourthFamily records4)
      (fun r => sourceGeometryFlag r = true) J5 rows5 from rfl]
  rw [actual_fifth_retained_six_physical_change e chi m omega
    (fourthFamily records4) (fun r => sourceGeometryFlag r = true) J5 rows5 fresh hfresh]
  exact list_sum_split _ _ _

end ActualSource
end
end ImbalancedChen.P1Pair12ActualWireSourceSupport
