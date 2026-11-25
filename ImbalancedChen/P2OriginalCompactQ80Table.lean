import ImbalancedChen.P2HistoricSieveStateInduction

/-!
SOURCE ONLY / UNCOMPILED. Actual original compact SieveTable(16384,12).
The universal Q80 prefix induction is reused, with the maximum changed only
from its prior ordinary-pair instantiation (8) to the ORIGINAL compact maximum
(12). The original compact parameters and every recurrence operation remain
unchanged. No P112/P160 table, data acceptance guard, or query licence premise.
-/
namespace ImbalancedChen.P2OriginalCompactQ80TableSourceOnly

noncomputable section
open Set
open OriginalU2CoupledRecurrenceSourceOnly
open P2HistoricSieveTableSemantics P2HistoricSieveStateInduction
open Certificates.P2HistoricQ80DefectLookup

theorem table12_encloses_actual (i : ℕ) (hi : 16384 ≤ i) (hmax : i ≤ 196608) :
    Encloses (table 16384 12 i) i :=
  state_encloses actualTrapezoidIncrements 196608 i hi hmax
/-- Full historical numerator interpolation, with its own Q80 endpoints
and global curvature ceiling. Only integer representation/range is input. -/
theorem numerator12_contains_actual_L (a b : ℤ) (hb : 0 < b)
    (ha2 : 2 * b < a) (ha12 : a ≤ 12 * b) :
    let p := numerator 16384 a b (fun i => (table 16384 12 i).ll)
      (fun i => (table 16384 12 i).lh)
    value p.lo ≤ L ((a : ℝ) / (b : ℝ)) ∧
      L ((a : ℝ) / (b : ℝ)) ≤ value p.hi := by
  have ha0 : 0 ≤ a := by omega
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  let q : ℚ := (a : ℚ) / (b : ℚ)
  have hq2 : (2 : ℚ) < q := by
    apply (lt_div_iff₀ hbQ).2
    exact_mod_cast ha2
  have hq12 : q ≤ (12 : ℚ) := by
    apply (div_le_iff₀ hbQ).2
    exact_mod_cast ha12
  let i := queryIndex 16384 a b
  let r := queryResidual 16384 a b
  have hidx : originalQueryIndex q = i := by
    have h := congrArg Int.toNat (original_query_index_literal_divmod a b hb ha0)
    simpa only [Int.toNat_natCast, queryIndex, q, i] using h
  obtain ⟨hilow, _himax, hw0, hw1, hql, hqr⟩ := original_query_cell_geometry hq2.le
    (hq12.trans (by norm_num : (12 : ℚ) ≤ 12))
  rw [hidx] at hilow hw0 hw1 hql hqr
  have hi12 : i ≤ 196608 := by
    have h := Nat.floor_mono (show q * 16384 ≤ (196608 : ℚ) by linarith only [hq12])
    have h' : originalQueryIndex q ≤ 196608 := by
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
  have h0 := (table12_encloses_actual i (by omega) hi12).1
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
  · have hnext : i + 1 ≤ 196608 := by
      by_contra hn
      have hieq : i = 196608 := by omega
      have hqge : (12 : ℚ) ≤ q := by
        have h := hql
        norm_num [hieq] at h
        exact h
      have hqe : q = 12 := le_antisymm hq12 hqge
      have hwz : queryCellWeight i q = 0 := by norm_num [hieq, hqe, queryCellWeight]
      have hrz : r = 0 := by
        rw [hw] at hwz
        have hz := (div_eq_zero_iff.mp hwz).resolve_right (ne_of_gt hbQ)
        exact_mod_cast hz
      exact hr hrz
    have hright2 : 2 ≤ cellLeft (i + 1) := by simp only [cellLeft, Nat.cast_add, Nat.cast_one]; linarith
    have h1 := (table12_encloses_actual (i + 1) (by omega) hnext).1
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
    have hlow : value (interpolationLo (table 16384 12 i).ll (table 16384 12 (i + 1)).ll b r) ≤
        L ((a : ℝ) / (b : ℝ)) := by linarith only [hc.1, ha.1]
    have hhigh : L ((a : ℝ) / (b : ℝ)) ≤
        value (interpolationHi (table 16384 12 i).lh (table 16384 12 (i + 1)).lh b r +
          interpError 16384) := by
      rw [value_add]
      linarith only [hc.2, ha.2]
    simpa only [numerator, show queryIndex 16384 a b = i from rfl,
      show queryResidual 16384 a b = r from rfl, if_neg hr, Bool.false_eq_true,
      if_false, interpolationLo, interpolationHi] using And.intro hlow hhigh

/-- The exact source point rule, including zero extension and maximum-twelve
tail, encloses actual normalized fbar at every integer rational query. -/
theorem point12_contains_actual (a b : ℤ) (hb : 0 < b) :
    (point 16384 12 a b).Contains (actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ))) := by
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
    by_cases ha12 : (12 : ℤ) * b < a
    · have hs12 : (12 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
        apply (le_div_iff₀ hbR).2
        exact_mod_cast ha12.le
      have hM := table12_encloses_actual 196608 (by norm_num) (by norm_num)
      dsimp only [Encloses] at hM
      have heL : endpointL (cellLeft 196608) = L 12 := by
        norm_num [cellLeft, endpointL_eq_L (s := (12 : ℝ)) (by norm_num)]
      have heH : endpointH (cellLeft 196608) = H 12 := by
        norm_num [cellLeft, endpointH_eq_H (s := (12 : ℝ)) (by norm_num)]
      rw [heL, heH] at hM
      have h := tail_query_transport 12 (by norm_num) hs12 hM.1.1 hM.2.2
      simpa only [point, if_neg ha2, Nat.cast_ofNat, if_pos ha12, show 12 * 16384 = 196608 by norm_num] using h
    · have ha12' : a ≤ 12 * b := le_of_not_gt ha12
      let p := numerator 16384 a b (fun i => (table 16384 12 i).ll)
        (fun i => (table 16384 12 i).lh)
      have hnum := numerator12_contains_actual_L a b hb ha2' ha12'
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
      simpa only [point, if_neg ha2, Nat.cast_ofNat, if_neg ha12, p] using h

/-- The requested full actual sf licence: no state/node validity, original
floor target, saved loss, or semantic sf hypothesis is passed by callers. -/
theorem sf12_contains_actual (q : ℚ) :
    (sf 16384 12 q).Contains (actualExtendedThirdLowerFactor (q : ℝ)) := by
  have hb : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hq : (q.num : ℝ) / ((q.den : ℤ) : ℝ) = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_natCast] using
      congrArg (fun x : ℚ => (x : ℝ)) q.num_div_den
  simpa only [sf, hq] using point12_contains_actual q.num (q.den : ℤ) hb

end
end ImbalancedChen.P2OriginalCompactQ80TableSourceOnly
