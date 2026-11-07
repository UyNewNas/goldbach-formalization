import ImbalancedChen.P2ActualFifthRaw31SupportCeiling
import ImbalancedChen.RosserShortPrefixAdmissibility
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The positive fifth-parent guard is obtained from the actual selected third
lookup, not from the previous fifth ceiling.  Gamma contains its literal
one-variable interval lower bound.  That bound loses at most 3 chi / 2,
and the stored exponent loses another 2e.  A compact history buffer at
R0 therefore survives both actual inherited finite maxima.

For a literal six-prime history the three positive logarithmic margins
are converted to its exact first, third and fifth integer cube tests.
This constructs the fifth policy decision.  Together with the already
licensed first four selections and a genuine carrier sublist, it gives
an actual retained leaf selecting all six primes.  No fifth or sixth
retention premise is assumed.  The adopted global buffered coverage is
still an external implementation obligation, not asserted here.
-/

namespace ImbalancedChen.P2ActualFifthBufferedParentWitness

noncomputable section
open Classical
open scoped BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open Certificates.P2OriginalSixthElevenLogSemantics

def historyLoss (e chi : ℝ) : ℝ := 3 / 2 * chi + 2 * e

/-- All three strict cube margins are present in the same original
physical cell.  The common allowance is fixed from its physical history,
before asking whether any fifth row wins. -/
def parentAllowance (t : Physical) : ℝ :=
  min (3 / 256) (min (R0 t - H3 t) (R0 t - H5 t))

theorem parentAllowance_pos (c : Cell) (t : Physical) (hc : PhysicalCell c t) :
    0 < parentAllowance t := by
  unfold parentAllowance
  exact lt_min (by norm_num) (lt_min (sub_pos.mpr hc.history3) (sub_pos.mpr hc.history5))

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The actual selected third baseline, including a box crossing mu,
approximates R0 to 3chi/2 before its common 2e buffer.  It remains below
the actual fourth finite maximum on the same ancestor. -/
theorem actual_inherited_fourth_ge_buffered_R0
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre)) :
    R0 (primeHistoryLogCoordinates N 6 pre) - historyLoss (e : ℝ) chi ≤
      inherited4 e chi m omega N rows4 licensed4 (rosserAncestor 5 pre) := by
  let u := primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre)
  let t := primeHistoryLogCoordinates N 6 pre
  have hcoord0 : u 0 = t 0 := by
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 6) (0 : Fin 3)
  obtain ⟨j, hj, ht⟩ := hs.2
  have hb := inBox_of_cell ht
  have hwidth := ((mem_cells (e : ℝ) chi m j).mp hj).2.2.2.2.2
  have hw : ((box m j).ux : ℝ) - (box m j).lx ≤ chi := by
    have hq := (box m j).coordinate_widths_le.1
    have hcast : ((box m j).ux : ℝ) - (box m j).lx ≤
        ((box m j).width : ℝ) := by exact_mod_cast hq
    exact hcast.trans hwidth
  have herr := rationalInterval_v_error hb.1 hb.2.1
  have hx : u 0 ≤ VariableEnvelope.mu := by
    rw [hcoord0]
    exact hc.largest.le
  rw [v_eq_A hx] at herr
  have hbase : (qVLo (box m j).lx (box m j).ux : ℝ) ≤
      (gamma (e : ℝ) (box m j) : ℝ) := by
    exact_mod_cast baseline_le_gamma (e : ℝ) (box m j)
  have hthird : R0 t - historyLoss (e : ℝ) chi ≤ exponent (e : ℝ) chi m u := by
    rw [exponent_on_cell (e : ℝ) chi m u j hj ht]
    dsimp only [R0, historyLoss, levelExponent]
    rw [← hcoord0]
    dsimp only [A] at herr
    linarith
  have hanc : rosserAncestor 3 (rosserAncestor 4 (rosserAncestor 5 pre)) =
      rosserAncestor 3 pre := by
    rw [rosserAncestor_nested 3 4 (by omega), rosserAncestor_nested 3 5 (by omega)]
  have hseed : seedExponent (e : ℝ) chi m omega N
        (rosserAncestor 4 (rosserAncestor 5 pre)) = exponent (e : ℝ) chi m u := by
    change P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 (rosserAncestor 4 (rosserAncestor 5 pre))) = _
    rw [hanc, P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hs]
  have hmax := seedExponent_le_exponent4 (e : ℝ) chi m omega N rows4
    (producerEligible licensed4) (fun r => r.bufferedCandidate (e : ℝ))
    (rosserAncestor 4 (rosserAncestor 5 pre))
  rw [hseed] at hmax
  exact hthird.trans hmax

/-- A small physical history buffer gives the positive first, third and
fifth cube inequalities at the actual fifth finite maximum.  In
particular the positive H5 guard is proved here, not assumed. -/
theorem actual_fifth_three_cubes_of_history_buffer
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre))
    (hbuffer : historyLoss (e : ℝ) chi <
      parentAllowance (primeHistoryLogCoordinates N 6 pre)) :
    let t := primeHistoryLogCoordinates N 6 pre
    let lambda := exponent5 e chi m omega N rows4 licensed4 J5 rows5
      (rosserAncestor 5 pre)
    3 * t 0 < lambda ∧ H3 t < lambda ∧ H5 t < lambda := by
  dsimp only
  let t := primeHistoryLogCoordinates N 6 pre
  have hlow := actual_inherited_fourth_ge_buffered_R0 e chi m omega N rows4 licensed4
    c pre hlen hc hs
  have hmax := inherited4_le_exponent5 e chi m omega N rows4 licensed4 J5 rows5
    (rosserAncestor 5 pre)
  have hfirst : historyLoss (e : ℝ) chi < (3 / 256 : ℝ) :=
    hbuffer.trans_le (min_le_left _ _)
  have hthird : historyLoss (e : ℝ) chi < R0 t - H3 t :=
    hbuffer.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hfifth : historyLoss (e : ℝ) chi < R0 t - H5 t :=
    hbuffer.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hx := hc.largest
  have hfirstIdeal : 3 * t 0 + 3 / 256 < R0 t := by
    dsimp only [R0, Certificates.P2OriginalSixthElevenLogSemantics.mu] at *
    linarith
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The positive history guard and the previous raw31 ceiling are now
simultaneously about the same actual exponent5. -/
theorem actual_fifth_parent_interval
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (hbuffer : historyLoss (e : ℝ) chi <
      parentAllowance (primeHistoryLogCoordinates N 6 pre)) :
    H5 (primeHistoryLogCoordinates N 6 pre) <
        exponent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre) ∧
      exponent5 e chi m omega N rows4 licensed4 J5 rows5 (rosserAncestor 5 pre) ≤
        oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  exact ⟨(actual_fifth_three_cubes_of_history_buffer e chi m omega N rows4 licensed4
      J5 rows5 c pre hlen hc hs hbuffer).2.2,
    P2ActualFifthRaw31SupportCeiling.actual_fifth_exponent_le_raw31 e chi m omega N
      rows4 licensed4 J5 rows5 c pre hlen hc he hs hgeometry⟩

section LiteralPrimes

variable (p1 p2 p3 p4 p5 p6 : ℕ)

/-- For the literal actual prime history the buffered positive margins
construct the active rank-five Boolean decision. -/
theorem policy5_accepts_fifth_of_history_buffer
    (hN : 1 < N) (h6 : 0 < p6)
    (h65 : p6 < p5) (h54 : p5 < p4) (h43 : p4 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1]))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N [p3,p2,p1])
    (hbuffer : historyLoss (e : ℝ) chi <
      parentAllowance (primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1])) :
    policy5 e chi m omega N rows4 licensed4 J5 rows5 false [p5,p4,p3,p2,p1] = true := by
  let t := primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1]
  let lambda := exponent5 e chi m omega N rows4 licensed4 J5 rows5 [p5,p4,p3,p2,p1]
  have hs' : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N
      (rosserAncestor 3 [p6,p5,p4,p3,p2,p1]) := by
    simpa [rosserAncestor] using hs
  have htests := actual_fifth_three_cubes_of_history_buffer e chi m omega N
    rows4 licensed4 J5 rows5 c [p6,p5,p4,p3,p2,p1] (by simp) hc hs' hbuffer
  have htests' : 3 * t 0 < lambda ∧ H3 t < lambda ∧ H5 t < lambda := by
    simpa [t, lambda, rosserAncestor] using htests
  have hpos : ∀ p ∈ [p6,p5,p4,p3,p2,p1], 0 < p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hpow (i : Fin 6) : N ^ t i =
      (primeHistoryTuple 6 [p6,p5,p4,p3,p2,p1] i : ℝ) :=
    rpow_primeHistoryLogCoordinates N hN (by simp) hpos i
  have hpow1 : N ^ (3 * t 0) = (p1 : ℝ)^3 := by
    rw [mul_comm, Real.rpow_mul_natCast hN0.le, hpow 0]
    rfl
  have hpow3 : N ^ H3 t = (p1 : ℝ)*p2*p3^3 := by
    have hcube : N ^ (3 * t 2) = (p3 : ℝ)^3 := by
      rw [mul_comm, Real.rpow_mul_natCast hN0.le, hpow 2]
      rfl
    simp only [H3, Real.rpow_add hN0, hcube, hpow]
    rfl
  have hpow5 : N ^ H5 t =
      (([p5,p4,p3,p2,p1].prod : ℕ) : ℝ)*(p5 : ℝ)^2 := by
    have hcube : N ^ (3 * t 4) = (p5 : ℝ)^3 := by
      rw [mul_comm, Real.rpow_mul_natCast hN0.le, hpow 4]
      rfl
    simp only [H5, Real.rpow_add hN0, hcube, hpow]
    change (p1 : ℝ)*p2*p3*p4*(p5 : ℝ)^3 =
      (([p5,p4,p3,p2,p1].prod : ℕ) : ℝ)*(p5 : ℝ)^2
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, Nat.cast_one]
    ring
  have hc1 : (p1 : ℝ)^3 < N^lambda := by
    rw [← hpow1]
    exact (Real.rpow_lt_rpow_left_iff hN).mpr htests'.1
  have hc3 : (p1 : ℝ)*p2*p3^3 < N^lambda := by
    rw [← hpow3]
    exact (Real.rpow_lt_rpow_left_iff hN).mpr htests'.2.1
  have hc5 : (([p5,p4,p3,p2,p1].prod : ℕ) : ℝ)*(p5 : ℝ)^2 < N^lambda := by
    rw [← hpow5]
    exact (Real.rpow_lt_rpow_left_iff hN).mpr htests'.2.2
  have hadm := (ordinaryRosserPrefixAdmissible_upper_five_iff (N^lambda)
    p1 p2 p3 p4 p5 (by omega) h54 h43 h32 h21).mpr ⟨hc1,hc3,hc5⟩
  have hdecision := decide_eq_true hadm
  simpa [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
    frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, rosserAncestor, level5, lambda] using hdecision

/-- This is a genuine retained-prefix construction from an actual
carrier sublist.  The first four selections are the upstream licence;
the fifth decision is constructed above and the sixth upper decision
is the inactive even-parity decision. -/
theorem exists_retained_sixth_prefix_of_history_buffer
    (hN : 1 < N) (h6 : 0 < p6)
    (h65 : p6 < p5) (h54 : p5 < p4) (h43 : p4 < p3)
    (h32 : p3 < p2) (h21 : p2 < p1)
    (c : Cell)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1]))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N [p3,p2,p1])
    (hbuffer : historyLoss (e : ℝ) chi <
      parentAllowance (primeHistoryLogCoordinates N 6 [p6,p5,p4,p3,p2,p1]))
    (carrier : List ℕ) (h : ℕ → ℝ)
    (hsub : [p1,p2,p3,p4,p5,p6] <+ carrier)
    (hfirstFour : FirstExitValidSelection
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) [] true [p1,p2,p3,p4]) :
    ∃ leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) h [] true 1 carrier,
      leaf.selected = [p6,p5,p4,p3,p2,p1] := by
  have hfive := policy5_accepts_fifth_of_history_buffer e chi m omega N rows4 licensed4
    J5 rows5 p1 p2 p3 p4 p5 p6 hN h6 h65 h54 h43 h32 h21 c hc hs hbuffer
  have hsix : policy5 e chi m omega N rows4 licensed4 J5 rows5 true
      [p6,p5,p4,p3,p2,p1] = true := by
    simp [policy5, fifthCappedUpperPolicy, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy]
  have hvalid : FirstExitValidSelection
      (policy5 e chi m omega N rows4 licensed4 J5 rows5) [] true
      [p1,p2,p3,p4,p5,p6] := by
    simp only [FirstExitValidSelection, Bool.not_true, Bool.not_false] at hfirstFour ⊢
    exact ⟨hfirstFour.1, hfirstFour.2.1, hfirstFour.2.2.1,
      hfirstFour.2.2.2.1, hfive, hsix, trivial⟩
  obtain ⟨leaf, hleaf, heq⟩ := exists_firstExitRetainedLeaf_of_validSelection
    (policy5 e chi m omega N rows4 licensed4 J5 rows5) h hsub [] true 1 hvalid
  exact ⟨leaf, hleaf, by simpa using heq⟩

end LiteralPrimes
end
end ImbalancedChen.P2ActualFifthBufferedParentWitness
