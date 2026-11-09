import ImbalancedChen.P3HBHalfOpenPhysicalProductBridge
import Mathlib.Tactic

/-!
P3.6 — a genuinely SMOOTH three-way refinement of each original HB
six-axis dyadic rectangle. Source candidate; not compiled/kernel checked.
Frozen manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (ratio-two HB lower endpoints), §4 (F).
Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The previous two-way sharp half-open cut has a discontinuous seam at the
original base L. Instead use THREE overlapping smooth gates, built from
the SAME original chi, with no extra arbitrary source filter:
  g0(t)=chi(4t-2),
  g1(t)=chi(4t-3)-chi(4t-2),
  g2(t)=1-chi(4t-3).
They sum to 1 identically. On the support of psi(t)=chi(t)-chi(2t),
nonzero g0, g1, g2 respectively force t in
(1/2,1), (3/4,5/4), (1,2). Every subbox has upper/lower ratio <=2.

This source establishes one-dimensional C-infinity composition, finite
six-position tensor partition and geometric R/128 on actual factorTuples.
It does NOT yet bound uniform mixed derivatives, identify the final selected
physical W_T, compile, pay (S)/(F), or establish PP discrepancy.
-/

namespace ImbalancedChen.P3HBSmoothThreeWayRatioTwo
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBDyadicTensorPartition
open ImbalancedChen.P3HBDyadicRectangleEndpointAudit
open ImbalancedChen.P3HBRankAdaptiveRetainedSupport
open ImbalancedChen.P3HBHalfOpenPhysicalProductBridge
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords

/-- Smooth real-parameter three-way split, with no discontinuous indicator. -/
def smoothGate (chi : ℝ → ℂ) (t : ℝ) (a : Fin 3) : ℂ :=
  if a = 0 then chi (4 * t - 2)
  else if a = 1 then chi (4 * t - 3) - chi (4 * t - 2)
  else 1 - chi (4 * t - 3)

/-- The decomposition is exact BEFORE any modulus or signed error. -/
theorem smoothGate_sum (chi : ℝ → ℂ) (t : ℝ) :
    (∑ a : Fin 3, smoothGate chi t a) = 1 := by
  simp [Fin.sum_univ_succ, smoothGate]
  ring

/-- Smoothness follows from the actual cutoff's C-infinity regularity,
not from a sharp interval characteristic function. -/
theorem smoothGate_contDiff (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (a : Fin 3) :
    ContDiff ℝ ⊤ (fun t : ℝ => smoothGate chi t a) := by
  have ha : ContDiff ℝ ⊤ (fun t : ℝ => chi (4 * t - 2)) :=
    hchi.comp (by fun_prop)
  have hb : ContDiff ℝ ⊤ (fun t : ℝ => chi (4 * t - 3)) :=
    hchi.comp (by fun_prop)
  fin_cases a
  · simpa [smoothGate] using ha
  · simpa [smoothGate] using hb.sub ha
  · simpa [smoothGate] using (contDiff_const.sub hb)

/-- Original dyadic factor times a smooth three-way child. -/
def smoothCoord (chi : ℝ → ℂ) (x : ℝ) (j : ℕ) (a : Fin 3) : ℂ :=
  dyadicPiece chi x j * smoothGate chi (x / (2 : ℝ) ^ j) a

theorem smoothCoord_sum (chi : ℝ → ℂ) (x : ℝ) (j : ℕ) :
    (∑ a : Fin 3, smoothCoord chi x j a) = dyadicPiece chi x j := by
  simp [smoothCoord, ← Finset.mul_sum, smoothGate_sum]

theorem smoothCoord_contDiff (chi : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (j : ℕ) (a : Fin 3) :
    ContDiff ℝ ⊤ (fun x : ℝ => smoothCoord chi x j a) := by
  have harg : ContDiff ℝ ⊤ (fun x : ℝ => x / (2 : ℝ) ^ j) := by fun_prop
  have harg2 : ContDiff ℝ ⊤ (fun x : ℝ => 2 * x / (2 : ℝ) ^ j) := by fun_prop
  have hp : ContDiff ℝ ⊤ (fun x : ℝ => dyadicPiece chi x j) := by
    simpa only [dyadicPiece] using (hchi.comp harg).sub (hchi.comp harg2)
  exact hp.mul ((smoothGate_contDiff chi hchi a).comp harg)

/-- The actual lower endpoint of a smooth subbox of dyadic base 2^j. -/
def smoothLower (j : ℕ) (a : Fin 3) : ℝ :=
  if a = 0 then (2 : ℝ) ^ j / 2
  else if a = 1 then 3 * (2 : ℝ) ^ j / 4
  else (2 : ℝ) ^ j

private theorem lower_gate_lt_one (chi : ℝ → ℂ) (t : ℝ)
    (hlarge : ∀ u : ℝ, 2 ≤ u → chi u = 0)
    (hlive : smoothGate chi t 0 ≠ 0) : t < 1 := by
  by_contra h
  have htwo : (2 : ℝ) ≤ 4 * t - 2 := by linarith
  have hz : chi (4 * t - 2) = 0 := hlarge _ htwo
  exact hlive (by simpa [smoothGate] using hz)

private theorem middle_gate_window (chi : ℝ → ℂ) (t : ℝ)
    (hsmall : ∀ u : ℝ, u ≤ 1 → chi u = 1)
    (hlarge : ∀ u : ℝ, 2 ≤ u → chi u = 0)
    (hlive : smoothGate chi t 1 ≠ 0) :
    (3 : ℝ) / 4 < t ∧ t < 5 / 4 := by
  constructor
  · by_contra h
    have h1 : 4 * t - 3 ≤ (1 : ℝ) := by linarith
    have h2 : 4 * t - 2 ≤ (1 : ℝ) := by linarith
    have hz : smoothGate chi t 1 = 0 := by
      simp [smoothGate, hsmall _ h1, hsmall _ h2]
    exact hlive hz
  · by_contra h
    have h1 : (2 : ℝ) ≤ 4 * t - 3 := by linarith
    have h2 : (2 : ℝ) ≤ 4 * t - 2 := by linarith
    have hz : smoothGate chi t 1 = 0 := by
      simp [smoothGate, hlarge _ h1, hlarge _ h2]
    exact hlive hz

private theorem upper_gate_gt_one (chi : ℝ → ℂ) (t : ℝ)
    (hsmall : ∀ u : ℝ, u ≤ 1 → chi u = 1)
    (hlive : smoothGate chi t 2 ≠ 0) : 1 < t := by
  by_contra h
  have h1 : 4 * t - 3 ≤ (1 : ℝ) := by linarith
  have hz : smoothGate chi t 2 = 0 := by
    simp [smoothGate, hsmall _ h1]
  exact hlive hz

/-- A nonzero smooth child stays STRICTLY inside a ratio-two physical
interval. The middle interval has even smaller ratio 5/3. -/
theorem smoothCoord_live_box (chi : ℝ → ℂ) (x : ℝ) (j : ℕ)
    (a : Fin 3)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hlive : smoothCoord chi x j a ≠ 0) :
    smoothLower j a < x ∧ x < 2 * smoothLower j a := by
  let L : ℝ := (2 : ℝ) ^ j
  have hL : 0 < L := by dsimp [L]; positivity
  have hp : dyadicPiece chi x j ≠ 0 := by
    intro hz
    apply hlive
    simp [smoothCoord, hz]
  have hg : smoothGate chi (x / L) a ≠ 0 := by
    intro hz
    apply hlive
    simp [smoothCoord, L, hz]
  have hxhalf : L / 2 < x := by
    have hstrict : L < 2 * x := by
      by_contra h
      have hle : 2 * x ≤ L := le_of_not_gt h
      have hfirst : x / L ≤ 1 := (div_le_iff₀ hL).2 (by linarith)
      have hsecond : 2 * x / L ≤ 1 := (div_le_iff₀ hL).2 hle
      have hz1 : chi (x / (2 : ℝ) ^ j) = 1 :=
        hsmall _ (by simpa [L] using hfirst)
      have hz2 : chi (2 * x / (2 : ℝ) ^ j) = 1 :=
        hsmall _ (by simpa [L] using hsecond)
      have hzero : dyadicPiece chi x j = 0 := by
        simp [dyadicPiece, hz1, hz2]
      exact hp hzero
    linarith
  have hxhigh : x < 2 * L := by
    simpa [L] using dyadic_piece_lt_double_base chi x j hlarge hp
  fin_cases a
  · have h : x / L < 1 := lower_gate_lt_one chi _ hlarge (by simpa using hg)
    have hx : x < L := by
      have := (div_lt_iff₀ hL).mp h
      linarith
    constructor <;> simp only [smoothLower, if_pos rfl] <;> linarith
  · obtain ⟨hlo, hhi⟩ := middle_gate_window chi _ hsmall hlarge
      (by simpa using hg)
    have hlo' : (3 : ℝ) * L / 4 < x := by
      have := (lt_div_iff₀ hL).mp hlo
      linarith
    have hhi' : x < 5 * L / 4 := by
      have := (div_lt_iff₀ hL).mp hhi
      linarith
    constructor <;> simp only [smoothLower, if_neg (by decide : (1 : Fin 3) ≠ 0),
      if_pos rfl] <;> linarith
  · have h : 1 < x / L := upper_gate_gt_one chi _ hsmall (by simpa using hg)
    have hx : L < x := by
      have := (lt_div_iff₀ hL).mp h
      linarith
    constructor <;> simp only [smoothLower,
      if_neg (by decide : (2 : Fin 3) ≠ 0),
      if_neg (by decide : (2 : Fin 3) ≠ 1)] <;> linarith

/-- Three smooth sublabels in each of the six ORIGINAL positional slots. -/
def smoothChildren : Finset (Fin 6 → Fin 3) :=
  Finset.piFinset (fun _ : Fin 6 => (Finset.univ : Finset (Fin 3)))

def smoothTensor (chi : ℝ → ℂ) (label : Fin 6 → ℕ)
    (child : Fin 6 → Fin 3) (_marked hb : List ℕ) : ℂ :=
  ∏ i : Fin 6,
    smoothCoord chi (((hb.getD i.val 1 : ℕ) : ℝ)) (label i) (child i)

/-- The 3^6 smooth children restore the ORIGINAL positional tensor exactly.
In particular no HB label, ordered occurrence or coefficient is collapsed. -/
theorem smoothTensor_children_sum (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (marked hb : List ℕ) :
    (∑ child ∈ smoothChildren,
      smoothTensor chi label child marked hb) = hbDyadicCut chi label marked hb := by
  change (∑ child ∈ Finset.piFinset
      (fun _ : Fin 6 => (Finset.univ : Finset (Fin 3))),
      ∏ i : Fin 6,
        smoothCoord chi (((hb.getD i.val 1 : ℕ) : ℝ)) (label i) (child i)) = _
  rw [Finset.sum_prod_piFinset]
  simp_rw [smoothCoord_sum]
  rfl

/-- From actual factorTuples, not a guessed complete-product equality:
every live smooth child has the manuscript's R/128 lower envelope. -/
theorem actualHB_smooth_child_R128 (chi : ℝ → ℂ)
    (label : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (marked hb : List ℕ) (j n : ℕ) (R : ℝ)
    (hj : j ∈ Finset.range 3)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hR : 0 < R)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hgroup : chi ((n : ℝ) / R) - chi (2 * (n : ℝ) / R) ≠ 0)
    (hlive : smoothTensor chi label child marked hb ≠ 0) :
    R / 128 < ∏ i : Fin 6, smoothLower (label i) (child i) := by
  apply refined_two_to_one_R128_lower_envelope
    (fun i : Fin 6 => ((hb.getD i.val 1 : ℕ) : ℝ))
    (fun i : Fin 6 => smoothLower (label i) (child i)) R
  · intro i
    exact Nat.cast_nonneg _
  · intro i
    have hcoord : smoothCoord chi ((hb.getD i.val 1 : ℕ) : ℝ)
        (label i) (child i) ≠ 0 := by
      intro hz
      apply hlive
      unfold smoothTensor
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact (smoothCoord_live_box chi _ _ _ hsmall hlarge hcoord).2.le
  · have hwindow := original_group_dyadic_lower_window
      chi (n : ℝ) R hR hsmall hgroup
    simpa only [originalHB_paddedSix_product hj hhb] using hwindow

end ImbalancedChen.P3HBSmoothThreeWayRatioTwo
