import ImbalancedChen.OriginalPairedN48OmegaTrapezoidStep

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Soundness of the literal original positive-divisor interval quotient and of
the Omega(8192) trapezoidal update.  The four signed quotient corners, and
their integer floor/ceil rounding, are retained.  In particular there is no
new finite `StepArithmeticValid` hypothesis or checker call.

The sharp analytic trapezoid error remains explicit.  This file does not
derive that error from the weaker Lipschitz bound, produce the missing U
array, or assert a historical saved-floor check.
-/

namespace ImbalancedChen.OriginalPairedN48OmegaStepArithmetic

noncomputable section

open Set LiLiuPrereqBuchstab
open Certificates.P2DirectedLogRounding
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48OmegaTrapezoidStep

private theorem min_div_pos (x y p : ℚ) (hp : 0 < p) :
    min x y / p = min (x / p) (y / p) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h hp.le)]
  · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h hp.le)]

private theorem max_div_pos (x y p : ℚ) (hp : 0 < p) :
    max x y / p = max (x / p) (y / p) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hp.le)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hp.le)]

/-- The reciprocal interval reverses the positive denominator endpoints. -/
def reciprocal (b : Token) : Enclosure :=
  ⟨P / (b.hi : ℚ), P / (b.lo : ℚ)⟩

private theorem corner_normalization (x y : ℤ) :
    divCorner x y / P = ((x : ℚ) / P) * (P / (y : ℚ)) := by
  by_cases hy : y = 0
  · subst y
    simp [divCorner]
  · have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy
    unfold divCorner
    field_simp [ne_of_gt P_pos, hyQ]
    <;> ring

/-- Exact pre-rounding normalization of the original four corners.
The numerator can have either sign or straddle zero. -/
theorem decoded_division_lower (a b : Token) :
    lowerDivCorner a b / P = ((decode a).mul (reciprocal b)).lower := by
  simp only [lowerDivCorner, min_div_pos _ _ _ P_pos,
    corner_normalization, decode, reciprocal, Enclosure.mul]
  ac_rfl

theorem decoded_division_upper (a b : Token) :
    upperDivCorner a b / P = ((decode a).mul (reciprocal b)).upper := by
  simp only [upperDivCorner, max_div_pos _ _ _ P_pos,
    corner_normalization, decode, reciprocal, Enclosure.mul]
  ac_rfl

/-- `sourceDiv` is literally the existing signed enclosure product followed
by outward 112-bit rounding; this is an identity of arithmetic definitions. -/
theorem decode_sourceDiv (a b : Token) :
    decode (sourceDiv a b) = ((decode a).mul (reciprocal b)).round 112 := by
  apply congrArg₂ Enclosure.mk
  · change (⌊lowerDivCorner a b⌋ : ℚ) / P =
      (⌊((decode a).mul (reciprocal b)).lower * P⌋ : ℚ) / P
    rw [← decoded_division_lower]
    rw [div_mul_cancel₀ _ (ne_of_gt P_pos)]
  · change (⌈upperDivCorner a b⌉ : ℚ) / P =
      (⌈((decode a).mul (reciprocal b)).upper * P⌉ : ℚ) / P
    rw [← decoded_division_upper]
    rw [div_mul_cancel₀ _ (ne_of_gt P_pos)]

theorem reciprocal_contains (b : Token) {y : ℝ}
    (hb : 0 < b.lo) (hy : (decode b).Contains y) :
    (reciprocal b).Contains (1 / y) := by
  have hP : (0 : ℝ) < (P : ℝ) := by exact_mod_cast P_pos
  have hlo : (0 : ℝ) < (b.lo : ℝ) / (P : ℝ) :=
    div_pos (by exact_mod_cast hb) hP
  have hy' : (b.lo : ℝ) / (P : ℝ) ≤ y ∧
      y ≤ (b.hi : ℝ) / (P : ℝ) := by
    simpa only [decode, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast] using hy
  have hy0 : 0 < y := hlo.trans_le hy'.1
  have hu := one_div_le_one_div_of_le hlo hy'.1
  have hl := one_div_le_one_div_of_le hy0 hy'.2
  have hcancel (z : ℝ) : 1 / (z / (P : ℝ)) = (P : ℝ) / z := by
    by_cases hz : z = 0
    · subst z
      simp
    · field_simp [hP.ne', hz]
  rw [hcancel] at hu hl
  simpa only [reciprocal, Enclosure.Contains, Rat.cast_div, Rat.cast_intCast]
    using And.intro hl hu

/-- Soundness of original positive-divisor `J.__truediv__`, with all signed
numerator cases handled by the already proved four-corner product theorem. -/
theorem sourceDiv_contains (a b : Token) {x y : ℝ}
    (hb : 0 < b.lo)
    (hx : (decode a).Contains x) (hy : (decode b).Contains y) :
    (decode (sourceDiv a b)).Contains (x / y) := by
  rw [decode_sourceDiv]
  simpa only [div_eq_mul_inv, one_div] using
    Enclosure.round_contains
      (Enclosure.mul_contains hx (reciprocal_contains b hb hy)) 112

theorem sourceAdd_contains (a b : Token) {x y : ℝ}
    (hx : (decode a).Contains x) (hy : (decode b).Contains y) :
    (decode (sourceAdd a b)).Contains (x + y) := by
  have he : decode (sourceAdd a b) = (decode a).add (decode b) := by
    apply congrArg₂ Enclosure.mk
    <;> simp only [decode, sourceAdd, Enclosure.add, Int.cast_add]
    <;> ring
  rw [he]
  exact Enclosure.add_contains hx hy

/-- Every rational divisor used by the recursive branch is at least one,
so even the outward *lower* integer endpoint is strictly positive. -/
theorem rational_lower_pos {q : ℚ} (hq : 1 ≤ q) : 0 < (rational q).lo := by
  have hP : (1 : ℚ) ≤ P := by norm_num [P, dyadicScale]
  have hp : (1 : ℚ) ≤ q * P := by
    nlinarith only [hq, hP,
      mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hP)]
  have hf := Int.lt_floor_add_one (q * P)
  have hf0 : (0 : ℚ) < (⌊q * P⌋ : ℚ) := by linarith only [hp, hf]
  change 0 < ⌊q * P⌋
  exact_mod_cast hf0

/-- A weighted U-node is divided by its own positive grid coordinate,
not by the lower endpoint of an entire argument query. -/
theorem divided_weighted_node_contains (p : SourceArrays) (k : ℕ)
    (hk : mesh ≤ k)
    (hnode : (decode (Uat p k)).Contains
      (((k : ℝ) / (mesh : ℝ)) * buchstab ((k : ℝ) / (mesh : ℝ)))) :
    (decode (sourceDiv (Uat p k)
      (rational ((k : ℚ) / (mesh : ℚ))))).Contains
        (buchstab ((k : ℝ) / (mesh : ℝ))) := by
  have hmQ : (0 : ℚ) < mesh := by norm_num [mesh]
  have hmR : (0 : ℝ) < mesh := by norm_num [mesh]
  have hq : (1 : ℚ) ≤ (k : ℚ) / (mesh : ℚ) := by
    apply (le_div_iff₀ hmQ).2
    simpa only [one_mul] using (show (mesh : ℚ) ≤ k by exact_mod_cast hk)
  have hdiv := sourceDiv_contains (Uat p k)
    (rational ((k : ℚ) / (mesh : ℚ))) (rational_lower_pos hq)
    hnode (rational_contains ((k : ℚ) / (mesh : ℚ)))
  have hk0 : (0 : ℝ) < (k : ℝ) / (mesh : ℝ) := by
    apply div_pos _ hmR
    have : (mesh : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [hmR, this]
  simp only [Rat.cast_div, Rat.cast_natCast] at hdiv
  have hcancel :
      (((k : ℝ) / (mesh : ℝ)) * buchstab ((k : ℝ) / (mesh : ℝ))) /
        ((k : ℝ) / (mesh : ℝ)) = buchstab ((k : ℝ) / (mesh : ℝ)) := by
    field_simp [ne_of_gt hk0]
  rw [hcancel] at hdiv
  exact hdiv

private theorem errorBand_contains {e : ℝ}
    (he : |e| ≤ (sharpErrorQ : ℝ)) :
    (decode sourceErrorBand).Contains e := by
  have h := abs_le.mp he
  have hu := sharpError_le_sourceError
  simp only [decode, sourceErrorBand, Enclosure.Contains, Rat.cast_div,
    Rat.cast_intCast, Int.cast_neg]
  constructor
  · have hl : -(sourceErrorReal) ≤ e := by linarith only [h.1, hu]
    simpa only [sourceErrorReal, Rat.cast_div, Rat.cast_neg, Rat.cast_intCast,
      neg_div] using hl
  · simpa only [sourceErrorReal, Rat.cast_div, Rat.cast_intCast] using
      h.2.trans hu

/-- The complete literal source update contains the true weighted next
node.  Its inputs are the three earlier true weighted node enclosures and
the explicitly isolated local analytic error.  No arithmetic-check premise
is left, and no global Omega cap or row-saving estimate is assumed. -/
theorem one_original_sourceStep_contains (p : SourceArrays) (i : ℕ)
    (hi : 3 * mesh < i)
    (hprev : (decode (Uat p (i - 1))).Contains
      ((((i - 1 : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))))
    (hleftNode : (decode (Uat p (i - mesh - 1))).Contains
      ((((i - mesh - 1 : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - mesh - 1 : ℕ) : ℝ) / (mesh : ℝ))))
    (hrightNode : (decode (Uat p (i - mesh))).Contains
      ((((i - mesh : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - mesh : ℕ) : ℝ) / (mesh : ℝ))))
    (hsharp : SharpCellError (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))
      ((i : ℝ) / (mesh : ℝ))) :
    (decode (sourceStep p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  let a : ℝ := ((i - 1 : ℕ) : ℝ) / (mesh : ℝ)
  let b : ℝ := (i : ℝ) / (mesh : ℝ)
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hmNat : 0 < mesh := by norm_num [mesh]
  have hkl : mesh ≤ i - mesh - 1 := by omega
  have hkr : mesh ≤ i - mesh := by omega
  have hidxL : (i - mesh - 1 : ℕ) + mesh = i - 1 := by omega
  have hidxR : (i - mesh : ℕ) + mesh = i := by omega
  have hidL : ((i - mesh - 1 : ℕ) : ℝ) / (mesh : ℝ) = a - 1 := by
    have hreal : ((i - mesh - 1 : ℕ) : ℝ) + (mesh : ℝ) =
        ((i - 1 : ℕ) : ℝ) := by exact_mod_cast hidxL
    dsimp [a]
    apply (div_eq_iff hm.ne').2
    field_simp [hm.ne']
    linarith only [hreal]
  have hidR : ((i - mesh : ℕ) : ℝ) / (mesh : ℝ) = b - 1 := by
    have hreal : ((i - mesh : ℕ) : ℝ) + (mesh : ℝ) = (i : ℝ) :=
      by exact_mod_cast hidxR
    dsimp [b]
    apply (div_eq_iff hm.ne').2
    field_simp [hm.ne']
    linarith only [hreal]
  have hl := divided_weighted_node_contains p (i - mesh - 1) hkl hleftNode
  have hr := divided_weighted_node_contains p (i - mesh) hkr hrightNode
  rw [hidL] at hl
  rw [hidR] at hr
  change (decode (sourceDiv (Uat p (i - mesh - 1))
    (rational (((i - mesh - 1 : ℕ) : ℚ) / (mesh : ℚ))))).Contains (delayed a) at hl
  change (decode (sourceDiv (Uat p (i - mesh))
    (rational (((i - mesh : ℕ) : ℚ) / (mesh : ℚ))))).Contains (delayed b) at hr
  have hsum := sourceAdd_contains _ _ hl hr
  have htwo : (1 : ℚ) ≤ 2 * (mesh : ℚ) := by norm_num [mesh]
  have htrap := sourceDiv_contains _ (rational (2 * (mesh : ℚ)))
    (rational_lower_pos htwo) hsum (rational_contains (2 * (mesh : ℚ)))
  have hsucc : (i - 1 : ℕ) + 1 = i := by omega
  have hsuccR : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast hsucc
  have hwidth : b - a = 1 / (mesh : ℝ) := by
    dsimp [a, b]
    apply (eq_div_iff hm.ne').2
    field_simp [hm.ne']
    linarith only [hsuccR]
  have htrapEq : (delayed a + delayed b) / ((2 : ℝ) * (mesh : ℝ)) =
      trapezoid a b := by
    unfold trapezoid
    rw [hwidth]
    ring
  simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at htrap
  rw [htrapEq] at htrap
  have herr := errorBand_contains hsharp
  have hout := sourceAdd_contains _ _
    (sourceAdd_contains _ _ hprev htrap) herr
  have ha : 2 ≤ a := by
    have hidx : 2 * mesh ≤ i - 1 := by omega
    dsimp [a]
    apply (le_div_iff₀ hm).2
    exact_mod_cast hidx
  have hab : a ≤ b := by linarith only [hwidth, inv_nonneg.mpr hm.le]
  have hDDE := buchstab_weighted_sub_eq_integral ha hab
  change b * buchstab b - a * buchstab a = localIntegral a b at hDDE
  have hvalue : a * buchstab a + trapezoid a b +
      (localIntegral a b - trapezoid a b) = b * buchstab b := by
    linarith only [hDDE]
  change (decode (sourceStep p i)).Contains
    (a * buchstab a + trapezoid a b + (localIntegral a b - trapezoid a b)) at hout
  rw [hvalue] at hout
  exact hout

/-- Substitution into the literal source array recurrence.  Producer
validity is arithmetic data, and does not itself assert a real enclosure. -/
theorem recursive_U_contains (p : SourceArrays)
    (hp : SourceProducerValid p) (i : ℕ) (hic : i < uCount)
    (hi : 3 * mesh < i)
    (hprev : (decode (Uat p (i - 1))).Contains
      ((((i - 1 : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))))
    (hl : (decode (Uat p (i - mesh - 1))).Contains
      ((((i - mesh - 1 : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - mesh - 1 : ℕ) : ℝ) / (mesh : ℝ))))
    (hr : (decode (Uat p (i - mesh))).Contains
      ((((i - mesh : ℕ) : ℝ) / (mesh : ℝ)) *
        buchstab (((i - mesh : ℕ) : ℝ) / (mesh : ℝ))))
    (he : SharpCellError (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))
      ((i : ℝ) / (mesh : ℝ))) :
    (decode (Uat p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  rcases hp with ⟨_, _, _, _, _, hrows, _⟩
  have heq := hrows ⟨i, hic⟩
  simp only [Fin.val_mk] at heq
  rw [if_neg (by omega : ¬i ≤ 2 * mesh),
    if_neg (by omega : ¬i ≤ 3 * mesh)] at heq
  rw [heq]
  exact one_original_sourceStep_contains p i hi hprev hl hr he

/-- The physical initial range starts at `i = mesh`.  In particular the
source's unused U[0]=1 slot is not incorrectly asserted to enclose
`0 * buchstab 0`. -/
theorem initial_U_contains (p : SourceArrays)
    (hp : SourceProducerValid p) (i : ℕ) (hic : i < uCount)
    (hil : mesh ≤ i) (hiu : i ≤ 2 * mesh) :
    (decode (Uat p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  rcases hp with ⟨_, _, _, _, _, hrows, _⟩
  have heq := hrows ⟨i, hic⟩
  simp only [Fin.val_mk] at heq
  rw [if_pos hiu] at heq
  rw [heq]
  have hm : (0 : ℝ) < mesh := by norm_num [mesh]
  have hs : (1 : ℝ) ≤ (i : ℝ) / (mesh : ℝ) := by
    apply (le_div_iff₀ hm).2
    simpa only [one_mul] using (show (mesh : ℝ) ≤ i by exact_mod_cast hil)
  have hs2 : (i : ℝ) / (mesh : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hm).2
    exact_mod_cast hiu
  have hs0 : (i : ℝ) / (mesh : ℝ) ≠ 0 := by linarith only [hs]
  have hw : ((i : ℝ) / (mesh : ℝ)) *
      buchstab ((i : ℝ) / (mesh : ℝ)) = 1 := by
    rw [buchstab_eq_one_div hs hs2]
    field_simp [hs0]
  rw [hw]
  simpa only [Rat.cast_one] using rational_contains 1

/-- Strong induction closes *all recursive weighted nodes* once the
separate logarithm range and the genuine per-cell analytic error
have been proved.  The delayed-node enclosures are derived by induction,
not postulated as another whole-array certificate or final omega cap. -/
theorem all_weighted_nodes_of_local_errors (p : SourceArrays)
    (hp : SourceProducerValid p)
    (hlog : ∀ i : ℕ, 2 * mesh < i → i ≤ 3 * mesh → i < uCount →
      (decode (Uat p i)).Contains
        (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))))
    (herror : ∀ i : ℕ, 3 * mesh < i → i < uCount →
      SharpCellError (((i - 1 : ℕ) : ℝ) / (mesh : ℝ))
        ((i : ℝ) / (mesh : ℝ))) :
    ∀ i : ℕ, mesh ≤ i → i < uCount → (decode (Uat p i)).Contains
      (((i : ℝ) / (mesh : ℝ)) * buchstab ((i : ℝ) / (mesh : ℝ))) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hmi hic
    by_cases hb : i ≤ 3 * mesh
    · by_cases hi2 : i ≤ 2 * mesh
      · exact initial_U_contains p hp i hic hmi hi2
      · exact hlog i (by omega) hb hic
    · have hi : 3 * mesh < i := by omega
      have hm : 0 < mesh := by norm_num [mesh]
      apply recursive_U_contains p hp i hic hi
      · exact ih (i - 1) (by omega) (by omega) (by omega)
      · exact ih (i - mesh - 1) (by omega) (by omega) (by omega)
      · exact ih (i - mesh) (by omega) (by omega) (by omega)
      · exact herror i hi hic

end
end ImbalancedChen.OriginalPairedN48OmegaStepArithmetic
