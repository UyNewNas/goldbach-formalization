import ImbalancedChen.P1OriginalFifthRawBoxGateSoundness

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Correlated rational support-gate checks for the literal variable fifth
endpoint M_I(t)-2e. Each half/full/selected gate is SUBTRACTED
from each ascending/descending tent plane before coefficient-sign minimization.
The resulting lower bound is attained at its own box corner. No separated
supremum-gate/infimum-envelope bound, stored constant cap, or historical
all-pass assertion is substituted. A passing check constructs one explicit
positive rational margin valid throughout the complete closed raw box.
-/

namespace ImbalancedChen.P1OriginalFifthCorrelatedRawBoxGates
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open VariableEnvelope

abbrev Point5 := Fin 5 → ℝ
abbrev Endpoint5 := Fin 5 → ℚ

structure Affine5 where
  constant : ℚ
  coefficient : Fin 5 → ℚ

noncomputable def Affine5.eval (a : Affine5) (t : Point5) : ℝ :=
  a.constant + ∑ i, (a.coefficient i : ℝ) * t i

def Affine5.add (a b : Affine5) : Affine5 :=
  ⟨a.constant + b.constant, fun i => a.coefficient i + b.coefficient i⟩

def Affine5.sub (a b : Affine5) : Affine5 :=
  ⟨a.constant - b.constant, fun i => a.coefficient i - b.coefficient i⟩

def Affine5.lower (a : Affine5) (lo hi : Endpoint5) : ℚ :=
  a.constant + ∑ i, if 0 ≤ a.coefficient i then a.coefficient i * lo i
    else a.coefficient i * hi i

def Affine5.corner (a : Affine5) (lo hi : Endpoint5) : Endpoint5 :=
  fun i => if 0 ≤ a.coefficient i then lo i else hi i

def constantAffine (c : ℚ) : Affine5 := ⟨c, fun _ => 0⟩
def indicatorAffine (c : ℚ) (I : Finset (Fin 5)) : Affine5 :=
  ⟨0, fun i => if i ∈ I then c else 0⟩

def tentPlane (I : Finset (Fin 5)) (side : Bool) : Affine5 :=
  if side then (constantAffine (57 / 64)).add (indicatorAffine (-3 / 2) I)
  else (constantAffine (1 / 2)).add (indicatorAffine (1 / 2) I)

def halfGate : Affine5 := constantAffine (1 / 2)
def fullGate (j : Fin 5) : Affine5 :=
  (indicatorAffine 1 (Finset.univ.filter (fun i => i < j))).add (indicatorAffine 2 {j})
def selectedGate (I : Finset (Fin 5)) (j : Fin 5) : Affine5 :=
  ((indicatorAffine 1 I).add
    (indicatorAffine 1 (Finset.univ.filter (fun i => i < j ∧ i ∉ I)))).add
      (indicatorAffine 2 {j})

inductive Gate where
  | half
  | full (j : Fin 5)
  | selected (j : Fin 5)
  deriving DecidableEq, Fintype

def gateAllowed (I : Finset (Fin 5)) : Gate → Bool
  | .half => true
  | .full _ => true
  | .selected j => decide (j ∉ I)

def gateAffine (I : Finset (Fin 5)) : Gate → Affine5
  | .half => halfGate
  | .full j => fullGate j
  | .selected j => selectedGate I j

def gateRows (I : Finset (Fin 5)) : Finset (Bool × Gate) :=
  Finset.univ.filter (fun p => gateAllowed I p.2)

def gapValue (raw : FifthWireRow) (p : Bool × Gate) : ℚ :=
  ((tentPlane (maskSlots 5 raw.mask.toNat) p.1).sub
    (gateAffine (maskSlots 5 raw.mask.toNat) p.2)).lower raw.lower raw.upper

def gapValues (raw : FifthWireRow) : Finset ℚ :=
  (gateRows (maskSlots 5 raw.mask.toNat)).image (gapValue raw)

theorem gapValues_nonempty (raw : FifthWireRow) : (gapValues raw).Nonempty := by
  refine ⟨gapValue raw (false, .half), Finset.mem_image.mpr ⟨(false, .half), ?_, rfl⟩⟩
  simp [gateRows, gateAllowed]

/-- The uniform buffered margin is an actual finite rational minimum. -/
def gateMarginQ (e : ℚ) (raw : FifthWireRow) : ℚ :=
  (gapValues raw).min' (gapValues_nonempty raw) - 2 * e

def correlatedRawBoxRows (e : ℚ) (raw : FifthWireRow) : Prop :=
  0 < raw.grid ∧ 0 ≤ raw.mask ∧
    ∀ p ∈ gateRows (maskSlots 5 raw.mask.toNat), 2 * e < gapValue raw p

/-- Pure finite rational program, defined BEFORE Classical. -/
def correlatedRawBoxGateCheck (e : ℚ) (raw : FifthWireRow) : Bool :=
  @decide (correlatedRawBoxRows e raw) (by
    unfold correlatedRawBoxRows
    infer_instance)

def rawClosedBox (raw : FifthWireRow) : Set Point5 :=
  {t | ∀ i, (raw.lower i : ℝ) ≤ t i ∧ t i ≤ (raw.upper i : ℝ)}

noncomputable section
open Set
open scoped Classical
open P1OriginalVariableFifthContinuation

theorem Affine5.eval_add (a b : Affine5) (t : Point5) :
    (a.add b).eval t = a.eval t + b.eval t := by
  simp only [Affine5.eval, Affine5.add, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

theorem Affine5.eval_sub (a b : Affine5) (t : Point5) :
    (a.sub b).eval t = a.eval t - b.eval t := by
  simp only [Affine5.eval, Affine5.sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem Affine5.lower_le_eval (a : Affine5) (lo hi : Endpoint5) (t : Point5)
    (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (a.lower lo hi : ℝ) ≤ a.eval t := by
  have hs (i : Fin 5) :
      ((if 0 ≤ a.coefficient i then a.coefficient i * lo i
        else a.coefficient i * hi i : ℚ) : ℝ) ≤ (a.coefficient i : ℝ) * t i := by
    by_cases hc : 0 ≤ a.coefficient i
    · simp only [if_pos hc, Rat.cast_mul]
      exact mul_le_mul_of_nonneg_left (hl i) (by exact_mod_cast hc)
    · simp only [if_neg hc, Rat.cast_mul]
      exact mul_le_mul_of_nonpos_left (hu i) (by exact_mod_cast (le_of_not_ge hc))
  calc
    (a.lower lo hi : ℝ) = (a.constant : ℝ) + ∑ i,
      ((if 0 ≤ a.coefficient i then a.coefficient i * lo i
        else a.coefficient i * hi i : ℚ) : ℝ) := by
          simp only [Affine5.lower, Rat.cast_add, Rat.cast_sum]
    _ ≤ (a.constant : ℝ) + ∑ i, (a.coefficient i : ℝ) * t i :=
      add_le_add_left (Finset.sum_le_sum (fun i _ => hs i)) _
    _ = a.eval t := rfl

/-- The coefficient-sign lower bound is exact at its own minimizing corner. -/
theorem Affine5.eval_corner (a : Affine5) (lo hi : Endpoint5) :
    a.eval (fun i => (a.corner lo hi i : ℝ)) = (a.lower lo hi : ℝ) := by
  simp only [Affine5.eval, Affine5.lower, Rat.cast_add, Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hc : 0 ≤ a.coefficient i <;>
    simp [Affine5.corner, hc, Rat.cast_mul]

theorem Affine5.corner_in_box (a : Affine5) (lo hi : Endpoint5)
    (h : ∀ i, lo i ≤ hi i) (i : Fin 5) :
    (lo i : ℝ) ≤ (a.corner lo hi i : ℝ) ∧
      (a.corner lo hi i : ℝ) ≤ (hi i : ℝ) := by
  have hR : (lo i : ℝ) ≤ (hi i : ℝ) := Rat.cast_le.mpr (h i)
  by_cases hc : 0 ≤ a.coefficient i <;> simp [Affine5.corner, hc, hR]

theorem raw_endpoints_ordered (raw : FifthWireRow) (hg : 0 < raw.grid) (i : Fin 5) :
    raw.lower i ≤ raw.upper i := by
  have hgQ : (0 : ℚ) < raw.grid := by exact_mod_cast hg
  unfold FifthWireRow.lower FifthWireRow.upper
  exact div_le_div_of_nonneg_right (by linarith) hgQ.le

/-- Every correlated gap lower bound is attained INSIDE the raw closed
box. Thus the endpoint operation itself loses no coordinate correlation. -/
theorem gapValue_attained (raw : FifthWireRow) (hg : 0 < raw.grid) (p : Bool × Gate) :
    ∃ t ∈ rawClosedBox raw, (gapValue raw p : ℝ) =
      (tentPlane (maskSlots 5 raw.mask.toNat) p.1).eval t -
        (gateAffine (maskSlots 5 raw.mask.toNat) p.2).eval t := by
  let a := (tentPlane (maskSlots 5 raw.mask.toNat) p.1).sub
    (gateAffine (maskSlots 5 raw.mask.toNat) p.2)
  let t : Point5 := fun i => (a.corner raw.lower raw.upper i : ℝ)
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact a.corner_in_box raw.lower raw.upper (raw_endpoints_ordered raw hg) i
  · rw [← Affine5.eval_sub]
    exact (a.eval_corner raw.lower raw.upper).symm

theorem constantAffine_eval (c : ℚ) (t : Point5) :
    (constantAffine c).eval t = (c : ℝ) := by
  simp [constantAffine, Affine5.eval]

theorem indicatorAffine_eval (c : ℚ) (I : Finset (Fin 5)) (t : Point5) :
    (indicatorAffine c I).eval t = (c : ℝ) * ∑ i ∈ I, t i := by
  have hs : (∑ i : Fin 5, if i ∈ I then (c : ℝ) * t i else 0) =
      ∑ i ∈ I, (c : ℝ) * t i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  calc
    (indicatorAffine c I).eval t = ∑ i : Fin 5, if i ∈ I then (c : ℝ) * t i else 0 := by
      simp only [indicatorAffine, Affine5.eval, Rat.cast_zero, zero_add]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i ∈ I <;> simp [hi]
    _ = ∑ i ∈ I, (c : ℝ) * t i := hs
    _ = (c : ℝ) * ∑ i ∈ I, t i := (Finset.mul_sum _ _ _).symm

theorem tentPlane_eval (I : Finset (Fin 5)) (side : Bool) (t : Point5) :
    (tentPlane I side).eval t =
      if side then C (∑ i ∈ I, t i) else A (∑ i ∈ I, t i) := by
  cases side <;>
    simp [tentPlane, Affine5.eval_add, constantAffine_eval, indicatorAffine_eval, A, C]
  <;> ring

theorem halfGate_eval (t : Point5) : halfGate.eval t = 1 / 2 := by
  simp [halfGate, constantAffine_eval]

theorem fullGate_eval (j : Fin 5) (t : Point5) :
    (fullGate j).eval t = prefixSquareExpr t j := by
  simp [fullGate, Affine5.eval_add, indicatorAffine_eval, prefixSquareExpr]

theorem selectedGate_eval (I : Finset (Fin 5)) (j : Fin 5) (t : Point5) :
    (selectedGate I j).eval t = selectedSquareExpr I t j := by
  simp [selectedGate, Affine5.eval_add, indicatorAffine_eval, selectedSquareExpr]

theorem correlatedRawBoxGateCheck_sound (e : ℚ) (raw : FifthWireRow)
    (hc : correlatedRawBoxGateCheck e raw = true) : correlatedRawBoxRows e raw := by
  exact of_decide_eq_true hc

theorem gateMarginQ_pos (e : ℚ) (raw : FifthWireRow)
    (hc : correlatedRawBoxGateCheck e raw = true) : 0 < gateMarginQ e raw := by
  have hrows := (correlatedRawBoxGateCheck_sound e raw hc).2.2
  have hmin : 2 * e < (gapValues raw).min' (gapValues_nonempty raw) := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact hrows p hp
  dsimp [gateMarginQ]
  linarith

theorem gateMarginQ_le_gap (e : ℚ) (raw : FifthWireRow) (side : Bool) (g : Gate)
    (hg : gateAllowed (maskSlots 5 raw.mask.toNat) g = true) :
    gateMarginQ e raw + 2 * e ≤ gapValue raw (side, g) := by
  have hp : (side, g) ∈ gateRows (maskSlots 5 raw.mask.toNat) := by
    simp [gateRows, hg]
  have hmin := Finset.min'_le (gapValues raw) (gapValue raw (side, g))
    (Finset.mem_image.mpr ⟨(side, g), hp, rfl⟩)
  dsimp [gateMarginQ]
  linarith

/-- The SAME point occurs in the tent and the gate before minimization. -/
theorem gate_add_margin_le_candidate (e : ℚ) (raw : FifthWireRow) (g : Gate)
    (hg : gateAllowed (maskSlots 5 raw.mask.toNat) g = true)
    (t : Point5) (ht : t ∈ rawClosedBox raw) :
    (gateAffine (maskSlots 5 raw.mask.toNat) g).eval t + (gateMarginQ e raw : ℝ) ≤
      candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t := by
  have hside (side : Bool) :
      (gateAffine (maskSlots 5 raw.mask.toNat) g).eval t +
          (gateMarginQ e raw : ℝ) + 2 * (e : ℝ) ≤
        (tentPlane (maskSlots 5 raw.mask.toNat) side).eval t := by
    have hmargin : (gateMarginQ e raw : ℝ) + 2 * (e : ℝ) ≤
        (gapValue raw (side, g) : ℝ) := by
      exact_mod_cast gateMarginQ_le_gap e raw side g hg
    have hbound := ((tentPlane (maskSlots 5 raw.mask.toNat) side).sub
      (gateAffine (maskSlots 5 raw.mask.toNat) g)).lower_le_eval raw.lower raw.upper t
        (fun i => (ht i).1) (fun i => (ht i).2)
    rw [Affine5.eval_sub] at hbound
    change (gapValue raw (side, g) : ℝ) ≤ _ at hbound
    linarith
  have hA := hside false
  have hC := hside true
  rw [tentPlane_eval] at hA hC
  simp only [Bool.false_eq_true, if_false, if_true] at hA hC
  rw [candidate, envelope_eq_v, v_eq_min]
  exact (le_sub_iff_add_le).mpr (le_min hA hC)

/-- An explicit positive rational margin works for all literal support
gates throughout the FULL closed raw box. No actual row is checked here. -/
theorem correlatedRawBoxGateCheck_uniform_margin (e : ℚ) (raw : FifthWireRow)
    (hc : correlatedRawBoxGateCheck e raw = true) :
    0 < gateMarginQ e raw ∧ ∀ t ∈ rawClosedBox raw,
      (1 / 2 : ℝ) + (gateMarginQ e raw : ℝ) ≤
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t ∧
        (∀ j, prefixSquareExpr t j + (gateMarginQ e raw : ℝ) ≤
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t) ∧
        (∀ j ∉ maskSlots 5 raw.mask.toNat,
          selectedSquareExpr (maskSlots 5 raw.mask.toNat) t j + (gateMarginQ e raw : ℝ) ≤
            candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t) := by
  refine ⟨gateMarginQ_pos e raw hc, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [gateAffine, halfGate_eval] using
      gate_add_margin_le_candidate e raw .half rfl t ht
  · intro j
    simpa only [gateAffine, fullGate_eval] using
      gate_add_margin_le_candidate e raw (.full j) rfl t ht
  · intro j hj
    have hg : gateAllowed (maskSlots 5 raw.mask.toNat) (.selected j) = true := by
      simp [gateAllowed, hj]
    simpa only [gateAffine, selectedGate_eval] using
      gate_add_margin_le_candidate e raw (.selected j) hg t ht

theorem correlatedRawBoxGateCheck_support_gates (e : ℚ) (raw : FifthWireRow)
    (hc : correlatedRawBoxGateCheck e raw = true) (t : Point5) (ht : t ∈ rawClosedBox raw) :
    (1 / 2 : ℝ) < candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t ∧
      (∀ j, prefixSquareExpr t j < candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t) ∧
      (∀ j ∉ maskSlots 5 raw.mask.toNat,
        selectedSquareExpr (maskSlots 5 raw.mask.toNat) t j <
          candidate (e : ℝ) (maskSlots 5 raw.mask.toNat) t) := by
  obtain ⟨hd, hmargin⟩ := correlatedRawBoxGateCheck_uniform_margin e raw hc
  have hdR : (0 : ℝ) < gateMarginQ e raw := Rat.cast_pos.mpr hd
  have hm := hmargin t ht
  refine ⟨?_, ?_, ?_⟩
  · linarith [hm.1]
  · intro j
    linarith [hm.2.1 j]
  · intro j hj
    linarith [hm.2.2 j hj]

end
end ImbalancedChen.P1OriginalFifthCorrelatedRawBoxGates
