import ImbalancedChen.P2HistoricSieveTableSemantics
import ImbalancedChen.P2HistoricSieveTrapezoidError
import ImbalancedChen.ActualThirdOriginalRationalQuery

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.
The historical Q80 table is proved by its own integer recurrence; no P112
array is substituted. Actual scalar trapezoid increments are isolated in
the small analytic API below, with no integer-node or sf-validity field.
The initial delayed H endpoint at one is the explicit reciprocal-strip
extension. Ordinary's maximum is exactly eight and g=16384 throughout.
-/

namespace ImbalancedChen.P2HistoricSieveStateInduction

noncomputable section
open Set
open OriginalU2CoupledRecurrenceSourceOnly
open P2HistoricSieveTableSemantics
open P2HistoricSieveTrapezoidError
open Certificates.P2HistoricQ80DefectLookup

def endpointLower (s : ℝ) : ℝ := if s ≤ 2 then 0 else lower s
def endpointL (s : ℝ) : ℝ := s * endpointLower s

theorem endpointL_eq_L {s : ℝ} (hs : 2 ≤ s) : endpointL s = L s := by
  by_cases hle : s ≤ 2
  · have he : s = 2 := le_antisymm hle hs
    subst s
    have hl : lower (2 : ℝ) = 0 := by
      rw [lower_eq_log (by norm_num) (by norm_num)]
      norm_num
    simp [endpointL, endpointLower, L, hl]
  · simp [endpointL, endpointLower, hle, L]

def Encloses (z : HistoricNode) (i : ℕ) : Prop :=
  (value z.ll ≤ endpointL (cellLeft i) ∧ endpointL (cellLeft i) ≤ value z.lh) ∧
  (value z.hl ≤ endpointH (cellLeft i) ∧ endpointH (cellLeft i) ≤ value z.hh)

def delayedLTrap (i : ℕ) : ℝ := realTrap 16384 (i - 16384)
  (endpointH (cellLeft ((i - 16384) - 1))) (endpointH (cellLeft (i - 16384)))

def delayedHTrap (i : ℕ) : ℝ := realTrap 16384 (i - 16384)
  (endpointL (cellLeft ((i - 16384) - 1))) (endpointL (cellLeft (i - 16384)))

/-- Mathematical scalar increment API only. No array or target node occurs. -/
structure ActualTrapezoidIncrements : Prop where
  lower : ∀ i : ℕ, 32769 ≤ i →
    delayedLTrap i - 1 / (6 * (16384 : ℝ) ^ 3) ≤ L (cellLeft i) - L (cellLeft (i - 1)) ∧
      L (cellLeft i) - L (cellLeft (i - 1)) ≤ delayedLTrap i
  upper : ∀ i : ℕ, 49153 ≤ i →
    delayedHTrap i ≤ H (cellLeft i) - H (cellLeft (i - 1)) ∧
      H (cellLeft i) - H (cellLeft (i - 1)) ≤ delayedHTrap i + 1 / (12 * (16384 : ℝ) ^ 3)

private theorem realTrap_grid (f : ℝ → ℝ) (j : ℕ) (hj : 0 < j) :
    realTrap 16384 (j + 1) (cellLeft j * f (cellLeft j))
      (cellRight j * f (cellRight j)) = trapezoid f (cellLeft j) (cellRight j) := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  dsimp [realTrap, trapezoid, cellLeft, cellRight]
  push_cast
  field_simp [ne_of_gt hjR, show (j : ℝ) + 1 ≠ 0 by linarith]
  <;> ring

private theorem delayed_grid_dictionary (i : ℕ) (hi : 32769 ≤ i) :
    let j := i - 16385
    cellLeft j + 1 = cellLeft (i - 1) ∧
    cellRight j + 1 = cellLeft i ∧
    delayedLTrap i = trapezoid endpointUpper (cellLeft j) (cellRight j) := by
  let j := i - 16385
  have hj : 16384 ≤ j := by dsimp [j]; omega
  have hind : i - 16384 = j + 1 := by dsimp [j]; omega
  have hprev : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
  have hjcast : (j : ℝ) = (i : ℝ) - 16385 := by
    dsimp [j]
    rw [Nat.cast_sub (by omega : 16385 ≤ i)]
    norm_num
  have hright : cellLeft (j + 1) = cellRight j := by simp [cellLeft, cellRight]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cellLeft]
    rw [hjcast, hprev]
    ring
  · dsimp [cellRight, cellLeft]
    rw [hjcast]
    ring
  · dsimp [delayedLTrap]
    rw [hind, Nat.add_sub_cancel, hright]
    unfold endpointH
    exact realTrap_grid endpointUpper j (by omega)

/-- The analytic API is supplied by genuine actual-factor curvature and
the actual delay integrals, including the first left endpoint at one. -/
theorem actualTrapezoidIncrements : ActualTrapezoidIncrements := by
  constructor
  · intro i hi
    let j := i - 16385
    obtain ⟨hprev, hcur, htrap⟩ := delayed_grid_dictionary i hi
    have hj : 16384 ≤ j := by dsimp [j]; omega
    rw [htrap]
    by_cases hj3 : j < 49152
    · have hb : cellRight j ≤ 3 := by
        have hjR : (j : ℝ) + 1 ≤ 49152 := by exact_mod_cast (show j + 1 ≤ 49152 by omega)
        dsimp [cellRight]
        linarith
      have ha : cellLeft j ≤ 3 := (original_cell_lt j).le.trans hb
      have h := L_initial_cell_increment_trapezoid_error j hj hj3
      rw [hprev, hcur] at h
      simpa only [trapezoid, endpointUpper, if_pos ha, if_pos hb] using h
    · have hj3' : 49152 ≤ j := Nat.le_of_not_gt hj3
      have ha : 1 < cellLeft j := by
        have hjR : (49152 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3'
        dsimp [cellLeft]
        linarith
      have hb : 1 < cellRight j := ha.trans (original_cell_lt j)
      have h := L_tail_cell_increment_trapezoid_error j hj3'
      rw [hprev, hcur] at h
      simpa only [trapezoid, endpointUpper_eq_upper ha, endpointUpper_eq_upper hb] using h
  · intro i hi
    let j := i - 16385
    have hj : 32768 ≤ j := by dsimp [j]; omega
    obtain ⟨hprev, hcur, _htrap⟩ := delayed_grid_dictionary i (by omega)
    have hind : i - 16384 = j + 1 := by dsimp [j]; omega
    have hright : cellLeft (j + 1) = cellRight j := by simp [cellLeft, cellRight]
    have hjR : (32768 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have ha : 2 ≤ cellLeft j := by dsimp [cellLeft]; linarith
    have hb : 2 ≤ cellRight j := ha.trans (original_cell_lt j).le
    have htrap : delayedHTrap i = trapezoid lower (cellLeft j) (cellRight j) := by
      dsimp [delayedHTrap]
      rw [hind, Nat.add_sub_cancel, hright, endpointL_eq_L ha, endpointL_eq_L hb]
      unfold L
      exact realTrap_grid lower j (by omega)
    rw [htrap]
    have h := H_cell_increment_trapezoid_error j hj
    rw [hprev, hcur] at h
    exact h

private theorem coord_prev (i : ℕ) (hi : 1 ≤ i) :
    cellLeft (i - 1) = ((i : ℝ) - 1) / 16384 := by
  dsimp [cellLeft]
  rw [Nat.cast_sub hi]
  norm_num

theorem initial_encloses (i : ℕ) (hi : 16384 ≤ i) (hi2 : i ≤ 32768) :
    Encloses initial i := by
  have hiR : (16384 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hi2R : (i : ℝ) ≤ 32768 := by exact_mod_cast hi2
  have hs1 : 1 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have hs2 : cellLeft i ≤ 2 := by dsimp [cellLeft]; linarith
  have hL : endpointL (cellLeft i) = 0 := by simp [endpointL, endpointLower, hs2]
  have hH : endpointH (cellLeft i) = 1 := endpointH_initial hs1 (by linarith)
  norm_num [Encloses, initial, hL, hH, value, scale]

private theorem value_max_le {a b : ℤ} {x : ℝ}
    (ha : value a ≤ x) (hb : value b ≤ x) : value (max a b) ≤ x := by
  rcases le_total a b with h | h
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left h] using ha

private theorem L_grid_monotone (i : ℕ) (hi : 32769 ≤ i) :
    L (cellLeft (i - 1)) ≤ L (cellLeft i) := by
  have hiR : (32769 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hp := coord_prev i (by omega)
  have ha : 2 ≤ cellLeft (i - 1) := by rw [hp]; linarith
  have hb : 2 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have hab : cellLeft (i - 1) ≤ cellLeft i := by rw [hp]; dsimp [cellLeft]; linarith
  exact mul_le_mul hab (lower_monotone ha hb hab) (lower_nonneg ha) (by linarith)

/-- Exact Q80 max/add/error update preservation, using only strictly
earlier nodes; the target enclosure is never a hypothesis. -/
theorem update_preserves (w : ActualTrapezoidIncrements) (i : ℕ)
    (hi : 16384 ≤ i) (old : ℕ → HistoricNode)
    (hprior : ∀ k : ℕ, k < i → 16384 ≤ k → Encloses (old k) k) :
    Encloses (update 16384 i old) i := by
  by_cases hsmall : i ≤ 32768
  · simpa only [update, show 2 * 16384 = 32768 by norm_num, if_pos hsmall] using
      initial_encloses i hi hsmall
  have hi2 : 32769 ≤ i := by omega
  let j := i - 16384
  have hj : 1 < j := by dsimp [j]; omega
  have hj0 : 16384 ≤ j - 1 := by dsimp [j]; omega
  have hj1 : 16384 ≤ j := by omega
  have hprev := hprior (i - 1) (by omega) (by omega)
  have hdel0 := hprior (j - 1) (by dsimp [j]; omega) hj0
  have hdel1 := hprior j (by dsimp [j]; omega) hj1
  dsimp only [Encloses] at hprev hdel0 hdel1
  have hiR : (32769 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
  have hs2 : 2 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have hsp2 : 2 ≤ cellLeft (i - 1) := by rw [coord_prev i (by omega)]; linarith
  rw [endpointL_eq_L hsp2] at hprev
  have hroundL := trap_roundline_transport 16384 j (by norm_num) hj hdel0.2 hdel1.2
  have hincL := w.lower i hi2
  have herr := original_error_constants 16384 (by norm_num)
  change value (trapLo 16384 j (old (j - 1)).hl (old j).hl) ≤ delayedLTrap i ∧
    delayedLTrap i ≤ value (trapHi 16384 j (old (j - 1)).hh (old j).hh) at hroundL
  simp only [Encloses, update, show 2 * 16384 = 32768 by norm_num, if_neg hsmall,
    show 3 * 16384 = 49152 by norm_num]
  rw [endpointL_eq_L hs2]
  constructor
  · constructor
    · apply value_max_le
      · exact hprev.1.1.trans (L_grid_monotone i hi2)
      · rw [value_sub, value_add]
        linarith only [hprev.1.1, hroundL.1, hincL.1, herr.1]
    · rw [value_add]
      linarith only [hprev.1.2, hroundL.2, hincL.2]
  · by_cases hi3 : i ≤ 49152
    · have hi3R : (i : ℝ) ≤ 49152 := by exact_mod_cast hi3
      have hH : endpointH (cellLeft i) = 1 := endpointH_initial (by linarith) (by
        dsimp [cellLeft]; linarith)
      norm_num [if_pos hi3, hH, value, scale]
    · have hi3' : 49153 ≤ i := by omega
      have hi3R : (49153 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi3'
      have hs1 : 1 < cellLeft i := by dsimp [cellLeft]; linarith
      have hsp1 : 1 < cellLeft (i - 1) := by rw [coord_prev i (by omega)]; linarith
      rw [endpointH_eq_H hsp1] at hprev
      rw [endpointH_eq_H hs1]
      have hroundH := trap_roundline_transport 16384 j (by norm_num) hj hdel0.1 hdel1.1
      change value (trapLo 16384 j (old (j - 1)).ll (old j).ll) ≤ delayedHTrap i ∧
        delayedHTrap i ≤ value (trapHi 16384 j (old (j - 1)).lh (old j).lh) at hroundH
      have hincH := w.upper i hi3'
      simp only [if_neg hi3, value_add]
      constructor <;> linarith only [hprev.2.1, hprev.2.2, hroundH.1, hroundH.2,
        hincH.1, hincH.2, herr.2.1]

theorem state_succ (g k i : ℕ) : state g (k + 1) i =
    if i = k + 1 then update g (k + 1) (state g k) else state g k i := rfl

/-- Joint prefix induction for the actual literal FOUR integer columns. -/
theorem state_encloses (w : ActualTrapezoidIncrements) (k : ℕ) :
    ∀ i : ℕ, 16384 ≤ i → i ≤ k → Encloses (state 16384 k i) i := by
  induction k with
  | zero => intro i hi hik; omega
  | succ k ih =>
      intro i hi hik
      rw [state_succ]
      by_cases he : i = k + 1
      · subst i
        rw [if_pos rfl]
        apply update_preserves w (k + 1) hi
        intro j hj hjlow
        exact ih j hjlow (by omega)
      · rw [if_neg he]
        exact ih i hi (by omega)

theorem table_encloses (w : ActualTrapezoidIncrements) (i : ℕ)
    (hi : 16384 ≤ i) (hmax : i ≤ 131072) : Encloses (table 16384 8 i) i := by
  exact state_encloses w 131072 i hi hmax

theorem table_encloses_actual (i : ℕ) (hi : 16384 ≤ i) (hmax : i ≤ 131072) :
    Encloses (table 16384 8 i) i := table_encloses actualTrapezoidIncrements i hi hmax

/-- Full historical numerator interpolation, with its own Q80 endpoints
and global curvature ceiling. Only integer representation/range is input. -/
theorem numerator_contains_actual_L (a b : ℤ) (hb : 0 < b)
    (ha2 : 2 * b < a) (ha8 : a ≤ 8 * b) :
    let p := numerator 16384 a b (fun i => (table 16384 8 i).ll)
      (fun i => (table 16384 8 i).lh)
    value p.lo ≤ L ((a : ℝ) / (b : ℝ)) ∧
      L ((a : ℝ) / (b : ℝ)) ≤ value p.hi := by
  have ha0 : 0 ≤ a := by omega
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  let q : ℚ := (a : ℚ) / (b : ℚ)
  have hq2 : (2 : ℚ) < q := by
    apply (lt_div_iff₀ hbQ).2
    exact_mod_cast ha2
  have hq8 : q ≤ (8 : ℚ) := by
    apply (div_le_iff₀ hbQ).2
    exact_mod_cast ha8
  let i := queryIndex 16384 a b
  let r := queryResidual 16384 a b
  have hidx : originalQueryIndex q = i := by
    have h := congrArg Int.toNat (original_query_index_literal_divmod a b hb ha0)
    simpa only [Int.toNat_natCast, queryIndex, q, i] using h
  obtain ⟨hilow, _himax, hw0, hw1, hql, hqr⟩ := original_query_cell_geometry hq2.le
    (hq8.trans (by norm_num : (8 : ℚ) ≤ 12))
  rw [hidx] at hilow hw0 hw1 hql hqr
  have hi8 : i ≤ 131072 := by
    have h := Nat.floor_mono (show q * 16384 ≤ (131072 : ℚ) by linarith only [hq8])
    have h' : originalQueryIndex q ≤ 131072 := by
      simpa only [originalQueryIndex, Nat.floor_ofNat] using h
    simpa only [hidx] using h'
  have hw : queryCellWeight i q = (r : ℚ) / (b : ℚ) := by
    simpa only [hidx, queryResidual, q, r] using original_query_weight_literal_divmod a b hb ha0
  have hwR : (queryCellWeight i q : ℝ) = (r : ℝ) / (b : ℝ) := by exact_mod_cast hw
  have hqR : (q : ℝ) = (a : ℝ) / (b : ℝ) := by simp [q]
  have ht : (a : ℝ) / (b : ℝ) ∈ Icc (cellLeft i) (cellRight i) := by
    constructor
    · have h := Rat.cast_mono (K := ℝ) hql
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, hqR, cellLeft] using h
    · have h := Rat.cast_mono (K := ℝ) hqr.le
      simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one,
        Rat.cast_ofNat, hqR, cellRight] using h
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hilow
  have hleft2 : 2 ≤ cellLeft i := by dsimp [cellLeft]; linarith
  have h0 := (table_encloses_actual i (by omega) hi8).1
  rw [endpointL_eq_L hleft2] at h0
  by_cases hr : r = 0
  · have hwz : queryCellWeight i q = 0 := by rw [hw, hr]; simp
    have hnode : (a : ℝ) / (b : ℝ) = cellLeft i := by
      have hz : (queryCellWeight i q : ℝ) = 0 := by exact_mod_cast hwz
      dsimp [queryCellWeight] at hz
      push_cast at hz
      simp only [hqR] at hz
      dsimp [cellLeft]
      linarith only [hz]
    simpa only [numerator, show queryIndex 16384 a b = i from rfl,
      show queryResidual 16384 a b = r from rfl, if_pos hr, hnode] using h0
  · have hnext : i + 1 ≤ 131072 := by
      by_contra hn
      have hieq : i = 131072 := by omega
      have hqge : (8 : ℚ) ≤ q := by
        have h := hql
        norm_num [hieq] at h
        exact h
      have hqe : q = 8 := le_antisymm hq8 hqge
      have hwz : queryCellWeight i q = 0 := by norm_num [hieq, hqe, queryCellWeight]
      have hrz : r = 0 := by
        rw [hw] at hwz
        have hz := (div_eq_zero_iff.mp hwz).resolve_right (ne_of_gt hbQ)
        exact_mod_cast hz
      exact hr hrz
    have hright2 : 2 ≤ cellLeft (i + 1) := by simp only [cellLeft, Nat.cast_add, Nat.cast_one]; linarith
    have h1 := (table_encloses_actual (i + 1) (by omega) hnext).1
    rw [endpointL_eq_L hright2] at h1
    have hright : cellLeft (i + 1) = cellRight i := by simp [cellLeft, cellRight]
    rw [hright] at h1
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hb)
    have hrb : r ≤ b := (Int.emod_lt_of_pos _ hb).le
    have hc := interpolation_roundline_transport b r hb hr0 hrb h0 h1
    have hchord : endpointChord L (cellLeft i) (cellRight i) ((a : ℝ) / (b : ℝ)) =
        (((b - r : ℤ) : ℝ) / (b : ℝ)) * L (cellLeft i) +
          (r : ℝ) / (b : ℝ) * L (cellRight i) := by
      have hwForm : endpointChord L (cellLeft i) (cellRight i) ((q : ℚ) : ℝ) =
          (1 - (queryCellWeight i q : ℝ)) * L (cellLeft i) +
            (queryCellWeight i q : ℝ) * L (cellRight i) := by
        unfold endpointChord
        rw [original_cell_width]
        dsimp [cellLeft, cellRight, queryCellWeight]
        push_cast
        <;> ring
      rw [hqR, hwR] at hwForm
      convert hwForm using 1 <;> push_cast <;> ring
    rw [← hchord] at hc
    have ha := (actual_numerator_interpolation_allowance i hilow ht).1
    have hlow : value (interpolationLo (table 16384 8 i).ll (table 16384 8 (i + 1)).ll b r) ≤
        L ((a : ℝ) / (b : ℝ)) := by linarith only [hc.1, ha.1]
    have hhigh : L ((a : ℝ) / (b : ℝ)) ≤
        value (interpolationHi (table 16384 8 i).lh (table 16384 8 (i + 1)).lh b r +
          interpError 16384) := by
      rw [value_add]
      linarith only [hc.2, ha.2]
    simpa only [numerator, show queryIndex 16384 a b = i from rfl,
      show queryResidual 16384 a b = r from rfl, if_neg hr, Bool.false_eq_true,
      if_false, interpolationLo, interpolationHi] using And.intro hlow hhigh

/-- The exact source point rule, including zero extension and maximum-eight
tail, encloses actual normalized fbar at every integer rational query. -/
theorem point_contains_actual (a b : ℤ) (hb : 0 < b) :
    (point 16384 8 a b).Contains (actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ))) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  by_cases ha2 : a ≤ 2 * b
  · have hs2 : (a : ℝ) / (b : ℝ) ≤ 2 := by
      apply (div_le_iff₀ hbR).2
      exact_mod_cast ha2
    rw [actualExtendedThirdLowerFactor_of_le_two hs2, I80_contains_iff]
    norm_num [point, if_pos ha2, value]
  · have ha2' : 2 * b < a := lt_of_not_ge ha2
    have ha : 0 < a := by omega
    have hs2 : 2 ≤ (a : ℝ) / (b : ℝ) := by
      apply (le_div_iff₀ hbR).2
      exact_mod_cast ha2'.le
    by_cases ha8 : (8 : ℤ) * b < a
    · have hs8 : (8 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
        apply (le_div_iff₀ hbR).2
        exact_mod_cast ha8.le
      have hM := table_encloses_actual 131072 (by norm_num) (by norm_num)
      dsimp only [Encloses] at hM
      have heL : endpointL (cellLeft 131072) = L 8 := by
        norm_num [cellLeft, endpointL_eq_L (s := (8 : ℝ)) (by norm_num)]
      have heH : endpointH (cellLeft 131072) = H 8 := by
        norm_num [cellLeft, endpointH_eq_H (s := (8 : ℝ)) (by norm_num)]
      rw [heL, heH] at hM
      have h := tail_query_transport 8 (by norm_num) hs8 hM.1.1 hM.2.2
      simpa only [point, if_neg ha2, Nat.cast_ofNat, if_pos ha8, show 8 * 16384 = 131072 by norm_num] using h
    · have ha8' : a ≤ 8 * b := le_of_not_gt ha8
      let p := numerator 16384 a b (fun i => (table 16384 8 i).ll)
        (fun i => (table 16384 8 i).lh)
      have hnum := numerator_contains_actual_L a b hb ha2' ha8'
      have h := factor_division_rounds p a b ha hb hnum
      have hqpos : (a : ℝ) / (b : ℝ) ≠ 0 := div_ne_zero (by exact_mod_cast ha.ne') hbR.ne'
      have hactual : L ((a : ℝ) / (b : ℝ)) / ((a : ℝ) / (b : ℝ)) =
          actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ)) := by
        rw [← lower_eq_actual hs2]
        dsimp [L]
        field_simp [hqpos]
        <;> ring
      rw [hactual] at h
      rw [I80_contains_iff]
      simpa only [point, if_neg ha2, Nat.cast_ofNat, if_neg ha8, p] using h

/-- The requested full actual sf licence: no state/node validity, original
floor target, saved loss, or semantic sf hypothesis is passed by callers. -/
theorem sf_contains_actual (q : ℚ) :
    (sf 16384 8 q).Contains (actualExtendedThirdLowerFactor (q : ℝ)) := by
  have hb : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hq : (q.num : ℝ) / ((q.den : ℤ) : ℝ) = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_natCast] using
      congrArg (fun x : ℚ => (x : ℝ)) q.num_div_den
  simpa only [sf, hq] using point_contains_actual q.num (q.den : ℤ) hb

end

end ImbalancedChen.P2HistoricSieveStateInduction
