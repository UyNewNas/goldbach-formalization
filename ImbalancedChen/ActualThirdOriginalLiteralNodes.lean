import ImbalancedChen.ActualThirdOriginalWeightedCurvature

/-!
SOURCEONLY / UNCOMPILED / OPEN30. Literal original112-bit node construction.
Append after original-weights SOURCEONLY. The only remaining analytic input
is WeightedCellRemainders, concerning ACTUAL functions and their real endpoint
chords. It contains no array/node/query enclosure. Joint prefix induction
will use only strictly earlier nodes. n=16384,P=2^112,max=12 are unchanged.
-/
namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
noncomputable section
open Set MeasureTheory

/-- Original fixed-point interpretation, not a new precision. -/
def nodeValue (z : ℤ) : ℝ := (z : ℝ)/(originalWeightP : ℝ)

theorem nodeValue_add (x y : ℤ) : nodeValue (x+y)=nodeValue x+nodeValue y := by
  unfold nodeValue
  push_cast
  ring

theorem nodeValue_sub (x y : ℤ) : nodeValue (x-y)=nodeValue x-nodeValue y := by
  unfold nodeValue
  push_cast
  ring

private theorem nodeP_pos : (0 : ℝ) < (originalWeightP : ℝ) := by
  norm_num [originalWeightP]

private theorem node_ediv_le (x d : ℤ) (hd : 0 < d) :
    ((x/d : ℤ) : ℝ) ≤ (x : ℝ)/(d : ℝ) := by
  have hf : ⌊(x : ℚ)/(d : ℚ)⌋ = x/d := by
    simpa using Int.floor_div_cast_of_nonneg (k := ℚ) hd.le (x : ℚ)
  have h := Int.floor_le ((x : ℚ)/(d : ℚ))
  rw [hf] at h
  exact_mod_cast h

private theorem node_ceil_ge (x d : ℤ) (hd : 0 < d) :
    (x : ℝ)/(d : ℝ) ≤ ((-(-x/d) : ℤ) : ℝ) := by
  simpa only [Int.cast_neg, neg_div, neg_neg] using
    (neg_le_neg (node_ediv_le (-x) d hd))

/-- These are exactly the two outer divisions in ChordTable.__init__. -/
def nodeChordLo (j : ℕ) (a b : ℤ) : ℤ :=
  (a*originalWeight0Lo j+b*originalWeight1Lo j)/originalWeightP
def nodeChordHi (j : ℕ) (a b : ℤ) : ℤ :=
  -(-(a*originalWeight0Hi j+b*originalWeight1Hi j)/originalWeightP)

def nodeErrorDen (j : ℕ) : ℤ := 12*16384*(j : ℤ)*((j : ℤ)-16384)
def nodeError (j : ℕ) : ℤ := -(-originalWeightP/nodeErrorDen j)
def nodeErrorReal (j : ℕ) : ℝ := 1/(12*16384*(j : ℝ)*((j : ℝ)-16384))

theorem node_error_rounds_up (j : ℕ) (hj : 32768 ≤ j) :
    nodeErrorReal j ≤ nodeValue (nodeError j) := by
  have hjZ : (32768 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  have hd : 0 < nodeErrorDen j := by
    unfold nodeErrorDen
    have hJ : (0 : ℤ) < (j : ℤ) := by omega
    have hD : (0 : ℤ) < (j : ℤ)-16384 := by omega
    positivity
  have h := div_le_div_of_nonneg_right
    (node_ceil_ge originalWeightP (nodeErrorDen j) hd) nodeP_pos.le
  have he : ((originalWeightP : ℝ)/(nodeErrorDen j : ℝ))/(originalWeightP : ℝ) =
      nodeErrorReal j := by
    calc
      _ = ((originalWeightP : ℝ)/(originalWeightP : ℝ))/(nodeErrorDen j : ℝ) := by ring
      _ = _ := by
        rw [div_self nodeP_pos.ne']
        norm_num [nodeErrorDen, nodeErrorReal]
  rw [he] at h
  exact h

/-- Endpoint transport plus outer integer product rounding. All endpoint
premises concern prior nodes. The output concerns one weighted increment,
never the next target L/H value. Rounded weight signs are supplied. -/
theorem node_chord_transport (j : ℕ) (hj : 1 ≤ j)
    {l0 u0 l1 u1 : ℤ} {x y : ℝ}
    (hx : nodeValue l0 ≤ x ∧ x ≤ nodeValue u0)
    (hy : nodeValue l1 ≤ y ∧ y ≤ nodeValue u1) :
    nodeValue (nodeChordLo j l0 l1) ≤
      nodeValue (originalWeight0Lo j)*x+nodeValue (originalWeight1Lo j)*y ∧
    nodeValue (originalWeight0Hi j)*x+nodeValue (originalWeight1Hi j)*y ≤
      nodeValue (nodeChordHi j u0 u1) := by
  have hn := original_lower_weight_integers_nonneg j hj
  have hw := original_weight_112bit_enclosures j hj
  have hp := original_weights_positive j hj
  have hl0 : 0 ≤ nodeValue (originalWeight0Lo j) :=
    div_nonneg (by exact_mod_cast hn.1) nodeP_pos.le
  have hl1 : 0 ≤ nodeValue (originalWeight1Lo j) :=
    div_nonneg (by exact_mod_cast hn.2.1) nodeP_pos.le
  have hu0 : 0 ≤ nodeValue (originalWeight0Hi j) := hp.1.le.trans hw.1.2
  have hu1 : 0 ≤ nodeValue (originalWeight1Hi j) := hp.2.le.trans hw.2.1.2
  have hlo : nodeValue (nodeChordLo j l0 l1) ≤
      nodeValue (originalWeight0Lo j)*nodeValue l0+
      nodeValue (originalWeight1Lo j)*nodeValue l1 := by
    have h := div_le_div_of_nonneg_right
      (node_ediv_le (l0*originalWeight0Lo j+l1*originalWeight1Lo j)
        originalWeightP (by norm_num [originalWeightP])) nodeP_pos.le
    calc
      _ ≤ (((l0*originalWeight0Lo j+l1*originalWeight1Lo j : ℤ) : ℝ) /
          (originalWeightP : ℝ))/(originalWeightP : ℝ) := h
      _ = _ := by
        unfold nodeValue
        push_cast
        ring
  have hhi : nodeValue (originalWeight0Hi j)*nodeValue u0+
      nodeValue (originalWeight1Hi j)*nodeValue u1 ≤
      nodeValue (nodeChordHi j u0 u1) := by
    have h := div_le_div_of_nonneg_right
      (node_ceil_ge (u0*originalWeight0Hi j+u1*originalWeight1Hi j)
        originalWeightP (by norm_num [originalWeightP])) nodeP_pos.le
    calc
      _ = (((u0*originalWeight0Hi j+u1*originalWeight1Hi j : ℤ) : ℝ) /
          (originalWeightP : ℝ))/(originalWeightP : ℝ) := by
        unfold nodeValue
        push_cast
        ring
      _ ≤ _ := h
  exact ⟨hlo.trans (add_le_add (mul_le_mul_of_nonneg_left hx.1 hl0)
      (mul_le_mul_of_nonneg_left hy.1 hl1)),
    (add_le_add (mul_le_mul_of_nonneg_left hx.2 hu0)
      (mul_le_mul_of_nonneg_left hy.2 hu1)).trans hhi⟩

/-- Exact outstanding analytic supplier. The bounds refer only to real
functions, their actual endpoint chords and the original rational remainder.
No finite table, array element, checker flag or target enclosure occurs. -/
structure WeightedCellRemainders : Prop where
  lower : ∀ j : ℕ, 32768 ≤ j →
    (∫ u in cellLeft j..cellRight j,
      endpointChord L (cellLeft j) (cellRight j) u/u) ≤
      (∫ u in cellLeft j..cellRight j, L u/u) ∧
    (∫ u in cellLeft j..cellRight j, L u/u) ≤
      (∫ u in cellLeft j..cellRight j,
        endpointChord L (cellLeft j) (cellRight j) u/u)+nodeErrorReal j
  upper : ∀ j : ℕ, 49152 ≤ j →
    (∫ u in cellLeft j..cellRight j,
      endpointChord H (cellLeft j) (cellRight j) u/u)-nodeErrorReal j ≤
      (∫ u in cellLeft j..cellRight j, H u/u) ∧
    (∫ u in cellLeft j..cellRight j, H u/u) ≤
      (∫ u in cellLeft j..cellRight j,
        endpointChord H (cellLeft j) (cellRight j) u/u)

def delayedIndex (i : ℕ) : ℕ := i-16385

private theorem prev_cast (i : ℕ) (hi : 1 ≤ i) :
    ((i-1 : ℕ) : ℝ) = (i : ℝ)-1 := by
  rw [Nat.cast_sub hi]
  norm_num

private theorem delay_cast (i : ℕ) (hi : 16385 ≤ i) :
    (delayedIndex i : ℝ) = (i : ℝ)-16385 := by
  unfold delayedIndex
  rw [Nat.cast_sub hi]
  norm_num

theorem delayed_nodes_earlier (i : ℕ) (hi : 32769 ≤ i) :
    delayedIndex i < i ∧ delayedIndex i+1 < i ∧ i-1 < i := by
  unfold delayedIndex
  omega

theorem node_coupled_increment (i : ℕ) (hi : 49153 ≤ i) :
    (L (cellLeft i)-L (cellLeft (i-1)) =
      ∫ u in cellLeft (delayedIndex i)..cellRight (delayedIndex i), H u/u) ∧
    (H (cellLeft i)-H (cellLeft (i-1)) =
      ∫ u in cellLeft (delayedIndex i)..cellRight (delayedIndex i), L u/u) := by
  have hp := prev_cast i (by omega)
  have hj := delay_cast i (by omega)
  have ha : cellLeft (delayedIndex i) = ((i : ℝ)-16384-1)/16384 := by
    unfold cellLeft
    rw [hj]
    ring
  have hb : cellRight (delayedIndex i) = ((i : ℝ)-16384)/16384 := by
    unfold cellRight
    rw [hj]
    ring
  have hx : cellLeft (i-1) = ((i : ℝ)-1)/16384 := by
    unfold cellLeft
    rw [hp]
  rw [ha, hb, hx]
  exact original_grid_cell_recurrence i hi

/-- All initial logarithmic cells, not merely the first tiny interval. -/
theorem node_initial_log_increment (i : ℕ) (hi : 32769 ≤ i) (hi4 : i ≤ 65536) :
    L (cellLeft i)-L (cellLeft (i-1)) = originalCellLog (delayedIndex i) := by
  have hiR : (32769 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hi4R : (i : ℝ) ≤ 65536 := by exact_mod_cast hi4
  have hp := prev_cast i (by omega)
  have hj := delay_cast i (by omega)
  have ha2 : 2 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have ha4 : cellLeft i ≤ 4 := by dsimp [cellLeft]; linarith
  have hb2 : 2 ≤ cellLeft (i-1) := by dsimp [cellLeft]; rw [hp]; linarith
  have hb4 : cellLeft (i-1) ≤ 4 := by dsimp [cellLeft]; rw [hp]; linarith
  have haj : cellLeft i-1 = ((delayedIndex i : ℝ)+1)/16384 := by
    dsimp [cellLeft]
    rw [hj]
    ring
  have hbj : cellLeft (i-1)-1 = (delayedIndex i : ℝ)/16384 := by
    dsimp [cellLeft]
    rw [hp, hj]
    ring
  have hjpos : (0 : ℝ) < (delayedIndex i : ℝ) := by rw [hj]; linarith
  rw [L_eq_log ha2 ha4, L_eq_log hb2 hb4,
    ← Real.log_div (by linarith : cellLeft i-1 ≠ 0)
      (by linarith : cellLeft (i-1)-1 ≠ 0)]
  unfold originalCellLog
  rw [haj, hbj]
  congr 1
  field_simp [hjpos.ne']

private theorem L_node_monotone (i : ℕ) (hi : 32769 ≤ i) :
    L (cellLeft (i-1)) ≤ L (cellLeft i) := by
  have hp := prev_cast i (by omega)
  have hiR : (32769 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have ha : 2 ≤ cellLeft (i-1) := by dsimp [cellLeft]; rw [hp]; linarith
  have hb : 2 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have hab : cellLeft (i-1) ≤ cellLeft i := by dsimp [cellLeft]; rw [hp]; linarith
  exact mul_le_mul hab (lower_monotone ha hb hab) (lower_nonneg ha) (by linarith)

/-- A literal four-integer array entry. -/
structure OriginalNode where
  Llo : ℤ
  Lhi : ℤ
  Hlo : ℤ
  Hhi : ℤ

def initialNode : OriginalNode := ⟨0,0,originalWeightP,originalWeightP⟩

def NodeEncloses (z : OriginalNode) (i : ℕ) : Prop :=
  (nodeValue z.Llo ≤ L (cellLeft i) ∧ L (cellLeft i) ≤ nodeValue z.Lhi) ∧
  (nodeValue z.Hlo ≤ H (cellLeft i) ∧ H (cellLeft i) ≤ nodeValue z.Hhi)

/-- Exactly the original branches, signs, max and two product divisions.
No rounded node is supplied by an oracle; prior entries are read from old. -/
def originalNodeUpdate (i : ℕ) (old : ℕ → OriginalNode) : OriginalNode :=
  if i ≤ 32768 then initialNode else
  let p := old (i-1)
  let j := delayedIndex i
  { Llo := if i ≤ 65536 then p.Llo+originalLogLo j else
      max p.Llo (p.Llo+nodeChordLo j (old j).Hlo (old (j+1)).Hlo-nodeError j)
    Lhi := if i ≤ 65536 then p.Lhi+originalLogHi j else
      p.Lhi+nodeChordHi j (old j).Hhi (old (j+1)).Hhi
    Hlo := if i ≤ 49152 then originalWeightP else
      p.Hlo+nodeChordLo j (old j).Llo (old (j+1)).Llo
    Hhi := if i ≤ 49152 then originalWeightP else
      p.Hhi+nodeChordHi j (old j).Lhi (old (j+1)).Lhi+nodeError j }

/-- The initialized four arrays, then one exact update at each successive
index. Steps through2*n leave the initialized arrays unchanged. -/
def literalNodeState : ℕ → (ℕ → OriginalNode) :=
  Nat.rec (motive := fun _ => ℕ → OriginalNode)
    (fun _ => initialNode)
    (fun k old i =>
      if i=k+1 then originalNodeUpdate (k+1) old else old i)

/-- Exact finite arrays used by n=16384,maximum12. -/
def originalFinalNodes : ℕ → OriginalNode := literalNodeState 196608

theorem initialNode_encloses : NodeEncloses initialNode 32768 := by
  have hl : L (cellLeft 32768)=0 := by
    rw [show cellLeft 32768=(2 : ℝ) by norm_num [cellLeft],
      L_eq_log (by norm_num) (by norm_num)]
    norm_num
  have hh : H (cellLeft 32768)=1 := by
    rw [show cellLeft 32768=(2 : ℝ) by norm_num [cellLeft]]
    exact H_eq_one (by norm_num) (by norm_num)
  norm_num [NodeEncloses, initialNode, nodeValue, originalWeightP, hl, hh]

private theorem nodeValue_max_le {a b : ℤ} {x : ℝ}
    (ha : nodeValue a ≤ x) (hb : nodeValue b ≤ x) :
    nodeValue (max a b) ≤ x := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

private theorem cell_right_eq_next (j : ℕ) : cellRight j=cellLeft (j+1) := by
  simp [cellRight, cellLeft]

/-- The lower actual weighted integral advances H. Only the two delayed
L endpoint enclosures enter; no H target enclosure is a premise. -/
theorem rounded_H_increment (w : WeightedCellRemainders)
    (i : ℕ) (hi : 49153 ≤ i) (old : ℕ → OriginalNode)
    (ha : NodeEncloses (old (delayedIndex i)) (delayedIndex i))
    (hb : NodeEncloses (old (delayedIndex i+1)) (delayedIndex i+1)) :
    nodeValue (nodeChordLo (delayedIndex i)
      (old (delayedIndex i)).Llo (old (delayedIndex i+1)).Llo) ≤
      H (cellLeft i)-H (cellLeft (i-1)) ∧
    H (cellLeft i)-H (cellLeft (i-1)) ≤
      nodeValue (nodeChordHi (delayedIndex i)
        (old (delayedIndex i)).Lhi (old (delayedIndex i+1)).Lhi)+
        nodeValue (nodeError (delayedIndex i)) := by
  have hj : 32768 ≤ delayedIndex i := by unfold delayedIndex; omega
  have hj1 : 1 ≤ delayedIndex i := by omega
  have hb' : nodeValue (old (delayedIndex i+1)).Llo ≤ L (cellRight (delayedIndex i)) ∧
      L (cellRight (delayedIndex i)) ≤ nodeValue (old (delayedIndex i+1)).Lhi := by
    simpa only [cell_right_eq_next] using hb.1
  have ht := node_chord_transport (delayedIndex i) hj1 ha.1 hb'
  change nodeValue (nodeChordLo (delayedIndex i)
      (old (delayedIndex i)).Llo (old (delayedIndex i+1)).Llo) ≤
      originalChord112Lo L (delayedIndex i) ∧
    originalChord112Hi L (delayedIndex i) ≤
      nodeValue (nodeChordHi (delayedIndex i)
        (old (delayedIndex i)).Lhi (old (delayedIndex i+1)).Lhi) at ht
  have hw := (original_actual_chord_112bit_weight_enclosures (delayedIndex i) hj).1
  have he := node_error_rounds_up (delayedIndex i) hj
  have hc := w.lower (delayedIndex i) hj
  rw [(node_coupled_increment i hi).2]
  exact ⟨ht.1.trans (hw.1.trans hc.1), by linarith only [hc.2, hw.2, ht.2, he]⟩

/-- The upper actual weighted integral advances L. Its curvature is subtracted
only from the lower increment, exactly as in the original producer. -/
theorem rounded_L_increment (w : WeightedCellRemainders)
    (i : ℕ) (hi : 65537 ≤ i) (old : ℕ → OriginalNode)
    (ha : NodeEncloses (old (delayedIndex i)) (delayedIndex i))
    (hb : NodeEncloses (old (delayedIndex i+1)) (delayedIndex i+1)) :
    nodeValue (nodeChordLo (delayedIndex i)
      (old (delayedIndex i)).Hlo (old (delayedIndex i+1)).Hlo)-
        nodeValue (nodeError (delayedIndex i)) ≤
      L (cellLeft i)-L (cellLeft (i-1)) ∧
    L (cellLeft i)-L (cellLeft (i-1)) ≤
      nodeValue (nodeChordHi (delayedIndex i)
        (old (delayedIndex i)).Hhi (old (delayedIndex i+1)).Hhi) := by
  have hj : 49152 ≤ delayedIndex i := by unfold delayedIndex; omega
  have hj2 : 32768 ≤ delayedIndex i := by omega
  have hj1 : 1 ≤ delayedIndex i := by omega
  have hb' : nodeValue (old (delayedIndex i+1)).Hlo ≤ H (cellRight (delayedIndex i)) ∧
      H (cellRight (delayedIndex i)) ≤ nodeValue (old (delayedIndex i+1)).Hhi := by
    simpa only [cell_right_eq_next] using hb.2
  have ht := node_chord_transport (delayedIndex i) hj1 ha.2 hb'
  change nodeValue (nodeChordLo (delayedIndex i)
      (old (delayedIndex i)).Hlo (old (delayedIndex i+1)).Hlo) ≤
      originalChord112Lo H (delayedIndex i) ∧
    originalChord112Hi H (delayedIndex i) ≤
      nodeValue (nodeChordHi (delayedIndex i)
        (old (delayedIndex i)).Hhi (old (delayedIndex i+1)).Hhi) at ht
  have hw := (original_actual_chord_112bit_weight_enclosures (delayedIndex i) hj2).2
  have he := node_error_rounds_up (delayedIndex i) hj2
  have hc := w.upper (delayedIndex i) hj
  rw [(node_coupled_increment i (by omega)).1]
  exact ⟨by linarith only [ht.1, hw.1, hc.1, he], hc.2.trans (hw.2.trans ht.2)⟩

/-- Noncircular preservation: the hypothesis quantifies ONLY k<i. The target
node i is computed by the exact original update and is never assumed sound. -/
theorem originalNodeUpdate_preserves (w : WeightedCellRemainders)
    (i : ℕ) (hi : 32768 ≤ i) (old : ℕ → OriginalNode)
    (hprior : ∀ k : ℕ, k < i → 32768 ≤ k → NodeEncloses (old k) k) :
    NodeEncloses (originalNodeUpdate i old) i := by
  by_cases hi0 : i ≤ 32768
  · have he : i=32768 := by omega
    subst i
    simpa only [originalNodeUpdate, if_pos (by omega : 32768 ≤ 32768)]
      using initialNode_encloses
  have hi1 : 32769 ≤ i := by omega
  have hprev := hprior (i-1) (by omega) (by omega)
  have hearlier := delayed_nodes_earlier i hi1
  unfold NodeEncloses
  simp only [originalNodeUpdate, if_neg hi0]
  constructor
  · by_cases hi4 : i ≤ 65536
    · simp only [if_pos hi4, nodeValue_add]
      have hj1 : 1 ≤ delayedIndex i := by unfold delayedIndex; omega
      have hw := (original_weight_112bit_enclosures (delayedIndex i) hj1).2.2
      change nodeValue (originalLogLo (delayedIndex i)) ≤ originalCellLog (delayedIndex i) ∧
        originalCellLog (delayedIndex i) ≤ nodeValue (originalLogHi (delayedIndex i)) at hw
      have he := node_initial_log_increment i hi1 hi4
      constructor <;> linarith only [hprev.1.1, hprev.1.2, hw.1, hw.2, he]
    · simp only [if_neg hi4]
      have hj : 49152 ≤ delayedIndex i := by unfold delayedIndex; omega
      have ha := hprior (delayedIndex i) hearlier.1 (by omega)
      have hb := hprior (delayedIndex i+1) hearlier.2.1 (by omega)
      have hinc := rounded_L_increment w i (by omega) old ha hb
      constructor
      · apply nodeValue_max_le
        · exact hprev.1.1.trans (L_node_monotone i hi1)
        · rw [nodeValue_sub, nodeValue_add]
          linarith only [hprev.1.1, hinc.1]
      · rw [nodeValue_add]
        linarith only [hprev.1.2, hinc.2]
  · by_cases hi3 : i ≤ 49152
    · simp only [if_pos hi3]
      have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
      have hi3R : (i : ℝ) ≤ 49152 := by exact_mod_cast hi3
      have he : H (cellLeft i)=1 := H_eq_one
        (by dsimp [cellLeft]; linarith) (by dsimp [cellLeft]; linarith)
      norm_num [he, nodeValue, originalWeightP]
    · simp only [if_neg hi3, nodeValue_add]
      have hj : 32768 ≤ delayedIndex i := by unfold delayedIndex; omega
      have ha := hprior (delayedIndex i) hearlier.1 hj
      have hb := hprior (delayedIndex i+1) hearlier.2.1 (by omega)
      have hinc := rounded_H_increment w i (by omega) old ha hb
      constructor <;> linarith only [hprev.2.1, hprev.2.2, hinc.1, hinc.2]

/-- Joint strong-prefix invariant for the FOUR literal integer arrays.
Only k<i entries are read by update preservation; no all-node premise occurs. -/
theorem literalNodeState_encloses (w : WeightedCellRemainders) (k : ℕ) :
    ∀ i : ℕ, 32768 ≤ i → i ≤ k → NodeEncloses (literalNodeState k i) i := by
  induction k with
  | zero =>
      intro i hi hik
      omega
  | succ k ih =>
      intro i hi hik
      by_cases he : i=k+1
      · subst i
        simp only [literalNodeState]
        apply originalNodeUpdate_preserves w (k+1) hi
        intro j hj hlow
        exact ih j hlow (by omega)
      · have hik' : i ≤ k := by omega
        simpa only [literalNodeState, if_neg he] using ih i hi hik'

/-- All original [2,12] nodes, with the original n16384/P112 arrays.
The sole analytic parameter has no array or node-enclosure fields. This is
conditional on supplying the actual weighted-curvature theorem, not an
unconditional full query or final U2 certificate. -/
theorem originalFinalNodes_enclose (w : WeightedCellRemainders)
    (i : ℕ) (hi : 32768 ≤ i) (himax : i ≤ 196608) :
    NodeEncloses (originalFinalNodes i) i := by
  exact literalNodeState_encloses w 196608 i hi himax

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Minimal join: actual weighted curvature supplies the record used by the
non-circular literal node induction. The original arrays, n16384, P112,
weighted error denominator12, max update and all branch thresholds are
unchanged. This closes the analytic parameter at source level only.
No rational-query theorem or evaluated numerical certificate is asserted.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section

/-- The actual source L/H weighted integral bounds supply the induction's
analytic record. Its fields contain no node or target enclosure hypotheses. -/
theorem actualWeightedCellRemainders : WeightedCellRemainders := by
  constructor
  · intro j hj
    simpa only [nodeErrorReal, originalWeightedCurvatureAllowance] using
      original_L_weighted_chord_integral_bounds j hj
  · intro j hj
    have hj' : 32768 ≤ j := by omega
    simpa only [nodeErrorReal, originalWeightedCurvatureAllowance] using
      original_H_weighted_chord_integral_bounds j hj'

/-- All four literal original numerator arrays enclose the actual L/H at
EVERY original node in [2,12]. There is no external analytic premise.
This theorem is SOURCEONLY and has not been checked by the Lean kernel. -/
theorem originalFinalNodes_enclose_actual
    (i : ℕ) (hi : 32768 ≤ i) (himax : i ≤ 196608) :
    NodeEncloses (originalFinalNodes i) i := by
  exact originalFinalNodes_enclose actualWeightedCellRemainders i hi himax

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
