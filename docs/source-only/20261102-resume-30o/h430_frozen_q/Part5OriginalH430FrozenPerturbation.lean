import ImbalancedChen.Part5OriginalH430FrozenRootRefinement

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Perturbation identities for the literal physical Program, at the SAME
physical appended coordinates.  Neither a modulus of continuity nor a
source-mass estimate is a premise.  Changed admission sets and changed
table atoms are not identified by these identities.
-/

namespace ImbalancedChen.Part5OriginalH430FrozenPerturbation

noncomputable section
open Set Filter Topology
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorValue)

def meshError (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def levelError (n : ℕ) (tau : ℝ) : ℝ := tau + meshError n

theorem meshError_pos (n : ℕ) : 0 < meshError n := by
  unfold meshError
  positivity

theorem sourceResidual_tau_loss (k : Root) {tau t : ℝ} (htau : 0 ≤ tau) :
    0 ≤ sourceResidual k 0 t - sourceResidual k tau t ∧
      sourceResidual k 0 t - sourceResidual k tau t ≤ tau := by
  cases k with
  | U3 =>
      by_cases ht : t < tailCutoff <;>
        simp [sourceResidual, U3Residual, ht, htau]
  | U4 => simp [sourceResidual, htau]

/-- The total level is perturbed once, at the actual root. -/
def rootLoss (n : ℕ) (k : Root) (tau t : ℝ) : ℝ :=
  (sourceRoot k 0 t).physical.total - (frozenRoot n k tau t).physical.total

theorem rootLoss_bounds {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    0 ≤ rootLoss n k tau t ∧ rootLoss n k tau t ≤ levelError n tau := by
  have hf := frozenLevel_bounds (root_total_bounds htau htauhi ht) n
  have hr := sourceResidual_tau_loss k (t := t) htau
  change frozenLevel n (t + sourceResidual k tau t) ≤ t + sourceResidual k tau t ∧
    t + sourceResidual k tau t - frozenLevel n (t + sourceResidual k tau t) ≤
      1 / ((n : ℝ) + 1) at hf
  change 0 ≤ t + sourceResidual k 0 t - frozenLevel n (t + sourceResidual k tau t) ∧
    t + sourceResidual k 0 t - frozenLevel n (t + sourceResidual k tau t) ≤ _
  unfold levelError meshError
  constructor <;> linarith [hf.1, hf.2, hr.1, hr.2]

/-- Arguments may change. The appended marked word does not. -/
theorem perform_slots_eq {p q : PhysicalNode} (h : p.slots = q.slots)
    (shape : StepShape) (z : P5OriginalActionMassBound.Point) :
    (perform p shape z).slots = (perform q shape z).slots := by
  cases shape <;> simp only [perform, appendOne, appendPair, compareAt, h]

theorem perform_ceiling_eq {p q : PhysicalNode} (h : p.ceiling = q.ceiling)
    (shape : StepShape) (z : P5OriginalActionMassBound.Point) :
    (perform p shape z).ceiling = (perform q shape z).ceiling := by
  cases shape <;> simp only [perform, appendOne, appendPair, compareAt, h]

theorem realize_slots_eq {mesh depth : ℕ} {p q : TypedNode}
    (h : p.physical.slots = q.physical.slots)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth p code z).physical.slots =
      (realize depth q code z).physical.slots := by
  induction depth generalizing p q with
  | zero => exact h
  | succ depth ih =>
      exact ih (perform_slots_eq h (code 0).1 (z 0)) (tail code) (tail z)

theorem realize_ceiling_eq {mesh depth : ℕ} {p q : TypedNode}
    (h : p.physical.ceiling = q.physical.ceiling)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth p code z).physical.ceiling =
      (realize depth q code z).physical.ceiling := by
  induction depth generalizing p q with
  | zero => exact h
  | succ depth ih =>
      exact ih (perform_ceiling_eq h (code 0).1 (z 0)) (tail code) (tail z)

/-- This is an identity, with no membership or regularity assumption. -/
theorem realize_residual_difference {mesh depth : ℕ} {p q : TypedNode}
    (h : p.physical.slots = q.physical.slots)
    (code : Program mesh depth) (z : Coordinates depth) :
    residual (realize depth p code z).physical -
        residual (realize depth q code z).physical =
      p.physical.total - q.physical.total := by
  have hw : word (realize depth p code z).physical =
      word (realize depth q code z).physical :=
    congrArg (List.map Slot.exponent) (realize_slots_eq h code z)
  unfold residual
  rw [hw, realize_total, realize_total]
  ring

theorem actual_descendant_residual_loss (n : ℕ) (k : Root) (tau t : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) :
    residual (realize depth (sourceRoot k 0 t) code z).physical -
        residual (realize depth (frozenRoot n k tau t) code z).physical =
      rootLoss n k tau t :=
  realize_residual_difference rfl code z

/-- Derive the frozen residual floor itself, before dividing by a leaf query. -/
theorem frozen430_residual_floor {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) (hn : meshError n ≤ 11 / 384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    frozenResidualFloor ≤ residual (realize depth (frozenRoot n k tau t) code z).physical := by
  have hp : (101 : ℝ)^depth ≤ (101 : ℝ)^440 :=
    pow_le_pow_right₀ (by norm_num) hd
  have hp0 : 0 < (101 : ℝ)^depth := pow_pos (by norm_num) _
  calc
    frozenResidualFloor ≤ (11 / 384 : ℝ) / (101 : ℝ)^depth :=
      div_le_div_of_nonneg_left (by norm_num) hp0 hp
    _ ≤ residual (frozenRoot n k tau t).physical / (101 : ℝ)^depth :=
      div_le_div_of_nonneg_right (frozenRoot_residual_bounds htau htauhi ht hn).1 hp0.le
    _ ≤ _ := realize_residual_bound hz

theorem frozenResidualFloor_pos : 0 < frozenResidualFloor := by
  unfold frozenResidualFloor
  positivity

/-- The elementary reciprocal estimate is proved from the two positive
denominators. It is not an assumed Lipschitz supplier. -/
theorem reciprocal_difference {b x y e : ℝ} (hb : 0 < b)
    (hx : b ≤ x) (hy : b ≤ y) (he : |x-y| ≤ e) :
    |1/x-1/y| ≤ e/(b*b) := by
  have hx0 := hb.trans_le hx
  have hy0 := hb.trans_le hy
  have hid : 1/x-1/y = (y-x)/(x*y) := by
    field_simp [hx0.ne', hy0.ne']
    <;> ring
  have hp : b*b ≤ x*y := mul_le_mul hx hy hb.le hx0.le
  rw [hid, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact (div_le_div_of_nonneg_right he (mul_pos hx0 hy0).le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans he) (mul_pos hb hb) hp)

theorem quotient_difference {b x y e c : ℝ} (hb : 0 < b)
    (hx : b ≤ x) (hy : b ≤ y) (he : |x-y| ≤ e) :
    |c/x-c/y| ≤ |c|*e/(b*b) := by
  have hi : c/x-c/y = c*(1/x-1/y) := by ring
  rw [hi, abs_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (reciprocal_difference hb hx hy he) (abs_nonneg c)

theorem actual_descendant_reciprocal_error {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) (hn : meshError n ≤ 11 / 384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    |1 / residual (realize depth (sourceRoot k 0 t) code z).physical -
        1 / residual (realize depth (frozenRoot n k tau t) code z).physical| ≤
      levelError n tau / (frozenResidualFloor*frozenResidualFloor) := by
  have hf := frozen430_residual_floor htau htauhi ht hn hd hz
  have he := actual_descendant_residual_loss n k tau t code z
  have hl := rootLoss_bounds htau htauhi ht
  have ho : frozenResidualFloor ≤
      residual (realize depth (sourceRoot k 0 t) code z).physical := by linarith [hl.1]
  apply reciprocal_difference frozenResidualFloor_pos ho hf
  rw [he, abs_of_nonneg hl.1]
  exact hl.2

/-- True alpha retains the complete physical prefix in its numerator. -/
theorem actual_descendant_alpha_error {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) (hn : meshError n ≤ 11 / 384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    |alpha (realize depth (sourceRoot k 0 t) code z).physical -
        alpha (realize depth (frozenRoot n k tau t) code z).physical| ≤
      |1-(word (realize depth (sourceRoot k 0 t) code z).physical).sum| *
        levelError n tau / (frozenResidualFloor*frozenResidualFloor) := by
  have hw : word (realize depth (sourceRoot k 0 t) code z).physical =
      word (realize depth (frozenRoot n k tau t) code z).physical :=
    congrArg (List.map Slot.exponent) (realize_slots_eq rfl code z)
  have hf := frozen430_residual_floor htau htauhi ht hn hd hz
  have he := actual_descendant_residual_loss n k tau t code z
  have hl := rootLoss_bounds htau htauhi ht
  have ho : frozenResidualFloor ≤
      residual (realize depth (sourceRoot k 0 t) code z).physical := by linarith [hl.1]
  unfold alpha
  rw [← hw]
  apply quotient_difference frozenResidualFloor_pos ho hf
  rw [he, abs_of_nonneg hl.1]
  exact hl.2

theorem actual_normalized_coordinate_error {n : ℕ} {k : Root} {tau t lo hi x : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) (hn : meshError n ≤ 11 / 384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    |x / residual (realize depth (sourceRoot k 0 t) code z).physical -
        x / residual (realize depth (frozenRoot n k tau t) code z).physical| ≤
      |x| * levelError n tau / (frozenResidualFloor*frozenResidualFloor) := by
  have he := actual_descendant_reciprocal_error htau htauhi ht hn hd hz
  have hid (L M : ℝ) : x/L-x/M = x*(1/L-1/M) := by ring
  rw [hid, abs_mul]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left he (abs_nonneg x)

/-- The inherited singleton query is evaluated with its original anchor. -/
theorem singleton_query_difference {b L M e x s : ℝ} (hb : 0 < b)
    (hL : b ≤ L) (hM : b ≤ M) (he : |L-M| ≤ e) :
    |P5OriginalFeedbackDomains.singletonProfile s (x/L)-
        P5OriginalFeedbackDomains.singletonProfile s (x/M)| ≤
      |s|*|x|*e/(b*b) := by
  have hi : P5OriginalFeedbackDomains.singletonProfile s (x/L)-
      P5OriginalFeedbackDomains.singletonProfile s (x/M) = -(s*(x/L-x/M)) := by
    unfold P5OriginalFeedbackDomains.singletonProfile
    ring
  rw [hi, abs_neg, abs_mul]
  have h := mul_le_mul_of_nonneg_left
    (quotient_difference (c := x) hb hL hM he) (abs_nonneg s)
  convert h using 1 <;> ring

theorem fixed_pair_query_difference {b L M e x y s : ℝ} (hb : 0 < b)
    (hL : b ≤ L) (hM : b ≤ M) (he : |L-M| ≤ e) :
    |s*(1-x/L-y/L)-s*(1-x/M-y/M)| ≤ |s|*|x+y|*e/(b*b) := by
  have hi : s*(1-x/L-y/L)-s*(1-x/M-y/M) =
      -(s*((x+y)/L-(x+y)/M)) := by ring
  rw [hi, abs_neg, abs_mul]
  have h := mul_le_mul_of_nonneg_left
    (quotient_difference (c := x+y) hb hL hM he) (abs_nonneg s)
  convert h using 1 <;> ring

/-- D7/D8 keep their moving first-prime denominator. They are not max-two
queries. The normalization cancels exactly to a physical quotient. -/
theorem moving_pair_query_physical {L x y : ℝ} (hL : L ≠ 0) :
    (1-x/L-y/L)/(x/L) = (L-x-y)/x := by
  by_cases hx : x = 0
  · simp [hx]
  · field_simp [hL, hx]
    <;> ring

theorem moving_pair_query_difference {L M e x y : ℝ}
    (hL : L ≠ 0) (hM : M ≠ 0) (he : |L-M| ≤ e) :
    |(1-x/L-y/L)/(x/L)-(1-x/M-y/M)/(x/M)| ≤ e/|x| := by
  rw [moving_pair_query_physical hL, moving_pair_query_physical hM, ← sub_div]
  have hi : (L-x-y)-(M-x-y) = L-M := by ring
  rw [hi, abs_div]
  exact div_le_div_of_nonneg_right he (abs_nonneg x)

theorem buchstab_query_difference {L M e x : ℝ} (he : |L-M| ≤ e) :
    |(L/x-1)-(M/x-1)| ≤ e/|x| := by
  have hi : (L/x-1)-(M/x-1) = (L-M)/x := by ring
  rw [hi, abs_div]
  exact div_le_div_of_nonneg_right he (abs_nonneg x)

theorem frozenRoot_alpha_ge_two {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hn : meshError n ≤ 11 / 384) :
    2 ≤ alpha (frozenRoot n k tau t).physical := by
  have ha := sourceRoot_alpha htau htauhi ht
  have hf := frozenRoot_residual_bounds htau htauhi ht hn
  have hfl := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  have ht1 : t ≤ 1 := (rootBand_subset k ht).2.trans (by norm_num)
  have hnum : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hden : residual (frozenRoot n k tau t).physical ≤ sourceResidual k tau t := by
    rw [frozenRoot_residual]
    change frozenLevel n (t+sourceResidual k tau t) ≤ t+sourceResidual k tau t at hfl
    linarith
  have hmon := div_le_div_of_nonneg_left hnum
    ((by norm_num : (0 : ℝ) < 11/384).trans_le hf.1) hden
  apply ha.trans
  simpa [alpha, word, sourceRoot, frozenRoot, residual] using hmon

theorem realize_alpha_ge_two {lo hi : ℝ} {mesh depth : ℕ} {p : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (ha : 2 ≤ alpha p.physical) (hz : Member lo hi depth p code z) :
    2 ≤ alpha (realize depth p code z).physical := by
  induction depth generalizing p with
  | zero => exact ha
  | succ depth ih => exact ih (ha.trans (perform_alpha hz.2.2.1 ha)) hz.2.2.2

/-- The positive-measure ideal clamp stays an EXACT clamp for every
allowed finite tau and every frozen root level. -/
theorem finite_frozen_U3_clamp {n : ℕ} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand .U3) (hc : clampStart ≤ t) :
    (frozenRoot n .U3 tau t).physical.argument = 2 ∧
      H430 ((frozenRoot n .U3 tau t).physical.argument) =
        min (floorValue H430Numerators 49) (floorValue H430Numerators 50) := by
  have hl := sourceResidual_tau_loss .U3 (t := t) htau
  have hid := (actual_U3_clamp hc).1
  have hq : sourceResidual .U3 0 t / a ≤ 2 := (le_max_right _ _).trans_eq hid
  have hq' : sourceResidual .U3 tau t / a ≤ 2 :=
    (div_le_div_of_nonneg_right (by linarith [hl.1]) (by norm_num [a])).trans hq
  have hfinite : (sourceRoot .U3 tau t).physical.argument = 2 := max_eq_left hq'
  have hf := frozenRoot_keeps_clamp htau htauhi ht hfinite
  exact ⟨hf, by rw [hf]; exact H430_two_eq_adjacent_min⟩

theorem root_argument_error {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    |(sourceRoot k 0 t).physical.argument -
        (frozenRoot n k tau t).physical.argument| ≤ levelError n tau / a := by
  have hl := rootLoss_bounds htau htauhi ht
  have ha : 0 < a := by norm_num [a]
  have hd : sourceResidual k 0 t -
      (frozenLevel n (sourceRoot k tau t).physical.total-t) = rootLoss n k tau t := by
    unfold rootLoss
    change sourceResidual k 0 t -
      (frozenLevel n (t+sourceResidual k tau t)-t) =
      t+sourceResidual k 0 t-frozenLevel n (t+sourceResidual k tau t)
    ring
  change |max 2 (sourceResidual k 0 t/a) -
      max 2 ((frozenLevel n (sourceRoot k tau t).physical.total-t)/a)| ≤ _
  calc
    _ ≤ |sourceResidual k 0 t/a-
        (frozenLevel n (sourceRoot k tau t).physical.total-t)/a| := by
      simpa only [max_comm] using abs_max_sub_max_le_abs
        (sourceResidual k 0 t/a)
        ((frozenLevel n (sourceRoot k tau t).physical.total-t)/a) 2
    _ = rootLoss n k tau t/a := by
      rw [← sub_div, abs_div, hd, abs_of_nonneg hl.1, abs_of_pos ha]
    _ ≤ _ := div_le_div_of_nonneg_right hl.2 ha.le

end
end ImbalancedChen.Part5OriginalH430FrozenPerturbation
