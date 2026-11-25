import ImbalancedChen.P2OriginalCompactQ80Encloser
import ImbalancedChen.P4AActualSquaredGapDecay

/-!
SOURCE ONLY / UNCOMPILED.
Actual original Q80 primitives: maximum-12 point queries, original32-term logs,
signed rounding, positive full rectangle mass, and every original integer gap
anchor/minimum. No data guard or desired leaf inequality is assumed.
-/
namespace ImbalancedChen.P2OriginalCompactQ80ArithmeticSourceOnly

noncomputable section
open Set
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80TableSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open P4AActualSquaredGapDecay20261024zSourceOnly

theorem floor_min (a b d : ℤ) (hd : 0 < d) :
    min a b/d = min (a/d) (b/d) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (Int.ediv_le_ediv hd h)]
  · rw [min_eq_right h,min_eq_right (Int.ediv_le_ediv hd h)]

theorem up_mono {a b d : ℤ} (hd : 0 < d) (h : a ≤ b) : up a d ≤ up b d := by
  have hh := Int.ediv_le_ediv hd (neg_le_neg h)
  unfold up
  omega

theorem up_max (a b d : ℤ) (hd : 0 < d) :
    up (max a b) d = max (up a d) (up b d) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (up_mono hd h)]
  · rw [max_eq_left h,max_eq_left (up_mono hd h)]

theorem scale_pos : (0 : ℤ) < scale := by norm_num [scale]
theorem scale_real_pos : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos

/-- Source I(Fraction) has one floor/ceiling at exactly these integers. -/
theorem point_constructor_source (q : ℚ) : I80.point q =
    ⟨q.num*scale/(q.den : ℤ),up (q.num*scale) (q.den : ℤ)⟩ := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have he : q*(Q : ℚ) = ((q.num*scale : ℤ) : ℚ)/(q.den : ℚ) := by
    calc
      q*(Q : ℚ) = ((q.num : ℚ)/(q.den : ℚ))*(Q : ℚ) :=
        congrArg (fun r : ℚ => r*(Q : ℚ)) q.num_div_den.symm
      _ = ((q.num*scale : ℤ) : ℚ)/(q.den : ℚ) := by
        push_cast
        change (q.num : ℚ)/(q.den : ℚ)*(scale : ℚ) =
          (q.num : ℚ)*(scale : ℚ)/(q.den : ℚ)
        ring
  ext <;> simp only [I80.point,I80.ofEnclosure,
    Certificates.P2DirectedLogRounding.Enclosure.point,he]
  · exact Certificates.P2HistoricI80DivisionSoundness.floor_int_div_of_pos _ _ hd
  · exact Certificates.P2HistoricI80DivisionSoundness.ceil_int_div_of_pos _ _ hd

/-- The reused general signed I.mul equals Python's four corner products
followed by precisely one floor/ceil. No extra round is silently inserted. -/
theorem mul_source (x y : I80) : x.mul y =
    ⟨min (min (x.lo*y.lo) (x.lo*y.hi)) (min (x.hi*y.lo) (x.hi*y.hi))/scale,
      up (max (max (x.lo*y.lo) (x.lo*y.hi)) (max (x.hi*y.lo) (x.hi*y.hi))) scale⟩ := by
  have he (m n : ℤ) :
      ((m : ℚ)/Q*((n : ℚ)/Q))*Q = ((m*n : ℤ) : ℚ)/Q := by
    push_cast
    field_simp [Q_ne_zero]
    ring
  ext
  · rw [I80.mul_lo_integer]
    simp only [floor_min _ _ _ scale_pos]
    rfl
  · simp only [I80.mul,I80.ofEnclosure,I80.enclosure,I80.decodeLo,I80.decodeHi,
      Certificates.P2DirectedLogRounding.Enclosure.mul,
      max_mul_of_nonneg _ _ Q_pos.le,
      Certificates.P2HistoricI80DivisionSoundness.ceil_max_rat,he,ceil_div_Q,
      up_max _ _ _ scale_pos]
    rfl

theorem contains_iff (p : I80) (x : ℝ) :
    p.Contains x ↔ val p.lo ≤ x ∧ x ≤ val p.hi :=
  P2HistoricSieveTableSemantics.I80_contains_iff p x

theorem val_mono {a b : ℤ} (h : a ≤ b) : val a ≤ val b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) scale_real_pos.le

theorem val_add (a b : ℤ) : val (a+b) = val a+val b := by
  unfold val
  push_cast
  ring

theorem val_sub (a b : ℤ) : val (a-b) = val a-val b := by
  unfold val
  push_cast
  ring

theorem val_mul_int (a b : ℤ) : val (a*b) = val a*(b : ℝ) := by
  unfold val
  push_cast
  ring

theorem val_max (a b : ℤ) : val (max a b) = max (val a) (val b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (val_mono h)]
  · rw [max_eq_left h,max_eq_left (val_mono h)]

theorem val_zero : val 0 = 0 := by simp [val]

theorem floor_rounds_down (n d : ℤ) (hd : 0 < d) :
    val (n/d) ≤ val n/(d : ℝ) :=
  P2HistoricSieveTableSemantics.value_ediv_le n d hd

theorem ceiling_rounds_up (n d : ℤ) (hd : 0 < d) :
    val n/(d : ℝ) ≤ val (up n d) :=
  P2HistoricSieveTableSemantics.value_ceilDiv_ge n d hd

theorem floor_product (a b : ℤ) : val (a*b/scale) ≤ val a*val b := by
  have h := floor_rounds_down (a*b) scale scale_pos
  convert h using 1 <;> simp only [val,Int.cast_mul] <;> ring

theorem ceiling_product (a b : ℤ) : val a*val b ≤ val (up (a*b) scale) := by
  have h := ceiling_rounds_up (a*b) scale scale_pos
  convert h using 1 <;> simp only [val,Int.cast_mul] <;> ring

theorem point_contains_actual (a b : ℤ) (hb : 0 < b) :
    (point a b).Contains (actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ))) := by
  rw [point_eq_historical]
  exact point12_contains_actual a b hb

theorem point_order (a b : ℤ) (hb : 0 < b) : (point a b).lo ≤ (point a b).hi := by
  have h := (contains_iff _ _).1 (point_contains_actual a b hb)
  have hh := (div_le_div_iff_of_pos_right scale_real_pos).1 (h.1.trans h.2)
  exact_mod_cast hh

theorem logI_contains (q : ℚ) (hq : 1 ≤ q) :
    (logI q).Contains (Real.log (q : ℝ)) := by
  rw [logI_eq_historical]
  exact Certificates.P2HistoricLogPointInterpreter.logI_contains_of_one_le q hq

/-- Specialized mass products need nonnegative computed lower logs, not
merely nonnegative true logarithms. This is proved from the literal loop. -/
theorem logLoop_lower_nonnegative (sq : I80) (ul uh : ℤ) (n : ℕ)
    (hul : 0 ≤ ul) (hsq : 0 ≤ sq.lo) :
    0 ≤ (logLoop sq ul uh n).power.lo ∧ 0 ≤ (logLoop sq ul uh n).total.lo := by
  induction n with
  | zero => exact ⟨hul,le_rfl⟩
  | succ n ih =>
      change 0 ≤ (logLoop sq ul uh n).power.lo*sq.lo/scale ∧
        0 ≤ (logLoop sq ul uh n).total.lo+
          (logLoop sq ul uh n).power.lo/(2*n+1 : ℕ)
      exact ⟨Int.ediv_nonneg (mul_nonneg ih.1 hsq) scale_pos.le,
        add_nonneg ih.2 (Int.ediv_nonneg ih.1 (by positivity))⟩

theorem atanh_lower_nonnegative (ul uh : ℤ) (hul : 0 ≤ ul) :
    0 ≤ (atanhBounds ul uh).lo := by
  have hs : 0 ≤ (logSquare ul uh).lo :=
    Int.ediv_nonneg (mul_nonneg hul hul) scale_pos.le
  exact mul_nonneg (by norm_num)
    (logLoop_lower_nonnegative (logSquare ul uh) ul uh 32 hul hs).2

theorem sourceShift_nonnegative {q : ℤ} (hq : scale ≤ q) :
    0 ≤ Certificates.P2HistoricLogRangeReduction.sourceShift q := by
  have hp : 0 < q := scale_pos.trans_le hq
  have hn : (2 : ℕ)^80 ≤ q.toNat := by
    have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hp.le
    have h : (2 : ℤ)^80 ≤ (q.toNat : ℤ) := by simpa [scale,he] using hq
    exact_mod_cast h
  have hb := (Certificates.P2HistoricLogRangeReduction.binaryExponent_bounds hp).2
  apply (Certificates.P2HistoricLogRangeReduction.sourceShift_nonneg_iff q).2
  by_contra h
  have he : Certificates.P2HistoricLogRangeReduction.binaryExponent q+1 ≤ 80 := by omega
  have hpow : (2 : ℕ)^(Certificates.P2HistoricLogRangeReduction.binaryExponent q+1) ≤ 2^80 := by
    gcongr
  omega

theorem logPoint_lower_nonnegative {q : ℤ} (hq : scale ≤ q) :
    0 ≤ (logPoint q).lo := by
  by_cases he : q = scale
  · simp [logPoint,he,I80.raw]
  have hp : 0 < q := scale_pos.trans_le hq
  have hs := sourceShift_nonnegative hq
  have hg := Certificates.P2HistoricLogRangeReduction.source_endpoint_guards hp
  have hl : scale ≤ Certificates.P2HistoricLogRangeReduction.sourceRL q := hg.1
  have hr : scale ≤ Certificates.P2HistoricLogRangeReduction.sourceRH q := hg.1.trans hg.2.1
  have hu : 0 ≤ (Certificates.P2HistoricLogRangeReduction.sourceRL q-scale)*scale/
      (Certificates.P2HistoricLogRangeReduction.sourceRH q+scale) :=
    Int.ediv_nonneg (mul_nonneg (sub_nonneg.mpr hl) scale_pos.le)
      (by linarith only [hr,scale_pos])
  have htwo : 0 ≤ logTwo.lo :=
    atanh_lower_nonnegative _ _ (Int.ediv_nonneg scale_pos.le (by norm_num))
  simp only [logPoint,if_neg he,if_pos hs,I80.add]
  exact add_nonneg (atanh_lower_nonnegative _ _ hu) (mul_nonneg hs htwo)

theorem logI_lower_nonnegative (q : ℚ) (hq : 1 ≤ q) : 0 ≤ (logI q).lo := by
  apply logPoint_lower_nonnegative
  change scale ≤ ⌊q*(Q : ℚ)⌋
  apply Int.le_floor.mpr
  have h := mul_le_mul_of_nonneg_right hq Q_pos.le
  simpa only [one_mul] using h

theorem logarithmicWidth_contains (lo hi : ℤ) (hl : 0 < lo) (hwidth : lo ≤ hi) :
    (logarithmicWidth lo hi).Contains (Real.log ((hi : ℝ)/(lo : ℝ))) ∧
      0 ≤ (logarithmicWidth lo hi).lo := by
  have hq : (1 : ℚ) ≤ (hi : ℚ)/(lo : ℚ) := by
    apply (le_div_iff₀ (by exact_mod_cast hl : (0 : ℚ)<lo)).2
    simpa only [one_mul] using (show (lo : ℚ)≤hi by exact_mod_cast hwidth)
  exact ⟨by simpa [logarithmicWidth] using logI_contains _ hq,
    logI_lower_nonnegative _ hq⟩

theorem ratio_rounds (p : I80) (n d : ℤ) (hn : 0 ≤ n) (hd : 0 < d)
    {x : ℝ} (hp : p.Contains x) :
    (⟨p.lo*n/d,up (p.hi*n) d⟩ : I80).Contains (x*(n : ℝ)/(d : ℝ)) := by
  obtain ⟨hl,hu⟩ := (contains_iff p x).1 hp
  have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
  apply (contains_iff _ _).2
  constructor
  · exact (floor_rounds_down (p.lo*n) d hd).trans (by
      rw [val_mul_int]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl hnR) hdR)
  · exact (show x*(n : ℝ)/(d : ℝ) ≤ val (p.hi*n)/(d : ℝ) from by
      rw [val_mul_int]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu hnR) hdR).trans
        (ceiling_rounds_up (p.hi*n) d hd)

/-- Actual original mass arithmetic, including the intermediate product
round BEFORE the exact z rational scaling. No mass enclosure is a premise. -/
theorem densityMass_contains (box : RawBox)
    (hpos : ∀ i, 0 < box.1 i) (hwidth : ∀ i, box.1 i ≤ box.2 i) :
    (densityMass box).Contains
      (Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ))*
        Real.log ((box.2 1 : ℝ)/(box.1 1 : ℝ))*
          ((4*denominator*(box.2 2-box.1 2 : ℤ) : ℤ) : ℝ)/
            ((box.1 2*box.2 2 : ℤ) : ℝ)) := by
  obtain ⟨hx,hx0⟩ := logarithmicWidth_contains _ _ (hpos 0) (hwidth 0)
  obtain ⟨hy,hy0⟩ := logarithmicWidth_contains _ _ (hpos 1) (hwidth 1)
  have hprod := Certificates.P2HistoricLogPointInterpreter.positiveMul_contains hx hy hx0 hy0
  have hn : 0 ≤ 4*denominator*(box.2 2-box.1 2) :=
    mul_nonneg (by norm_num [denominator]) (sub_nonneg.mpr (hwidth 2))
  have hd : 0 < box.1 2*box.2 2 := mul_pos (hpos 2) ((hpos 2).trans_le (hwidth 2))
  exact ratio_rounds _ _ _ hn hd hprod

theorem dInteger_bounds_actual_gap (s : ℕ) (hs3 : 3 ≤ s) (hs12 : s ≤ 12) :
    upper (s : ℝ)-lower (s : ℝ) ≤ val (dInteger s) := by
  have hnode := table12_encloses_actual (s*16384) (by omega) (by omega)
  have hg : P2HistoricSieveStateInduction.Encloses (sourceTable (s*16384)) (s*16384) := by
    simpa only [sourceTable_eq_historical] using hnode
  have hs2R : (2 : ℝ) ≤ s := by exact_mod_cast (show 2≤s by omega)
  have hs1R : (1 : ℝ) < s := by exact_mod_cast (show 1<s by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0<s by omega)
  have hsZ : (0 : ℤ) < s := by exact_mod_cast (show 0<s by omega)
  have hgrid : cellLeft (s*16384) = (s : ℝ) := by simp [cellLeft]
  dsimp only [P2HistoricSieveStateInduction.Encloses] at hg
  rw [hgrid,P2HistoricSieveStateInduction.endpointL_eq_L hs2R,
    P2HistoricSieveTableSemantics.endpointH_eq_H hs1R] at hg
  have hraw : upper (s : ℝ)-lower (s : ℝ) ≤
      val ((sourceTable (s*16384)).hh-(sourceTable (s*16384)).ll)/(s : ℝ) := by
    apply (le_div_iff₀ hsR).2
    rw [val_sub]
    have hl := hg.1.1
    have hh := hg.2.2
    change val (sourceTable (s*16384)).ll ≤ (s : ℝ)*lower (s : ℝ) at hl
    change (s : ℝ)*upper (s : ℝ) ≤ val (sourceTable (s*16384)).hh at hh
    nlinarith only [hh,hl]
  exact hraw.trans (ceiling_rounds_up _ (s : ℤ) hsZ)

theorem decayIndices_mem {a b : ℤ} {s : ℕ} (hs : s ∈ decayIndices a b) :
    3 ≤ s ∧ s ≤ 12 ∧ (s : ℤ) ≤ a/b := by
  obtain ⟨hm,hq⟩ := List.mem_filter.mp hs
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
  have hj10 := List.mem_range.mp hj
  exact ⟨by omega,by omega,of_decide_eq_true hq⟩

theorem decayIndices_three (a b : ℤ) (hb : 0 < b) (ha : 3*b ≤ a) :
    3 ∈ decayIndices a b := by
  apply List.mem_filter.mpr
  refine ⟨?_,?_⟩
  · exact List.mem_map.mpr ⟨0,by simp,rfl⟩
  · simpa using (Int.le_ediv_of_mul_le hb ha)

theorem decayTerm_bounds_actual_gap (a b : ℤ) (s : ℕ) (hb : 0 < b)
    (hs : s ∈ decayIndices a b) :
    upper ((a : ℝ)/(b : ℝ))-lower ((a : ℝ)/(b : ℝ)) ≤ val (decayTerm a b s) := by
  obtain ⟨hs3,hs12,hsq⟩ := decayIndices_mem hs
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs3
  have hsqR : (s : ℝ) ≤ ((a/b : ℤ) : ℝ) := by exact_mod_cast hsq
  have hks : (s : ℝ) ≤ (a : ℝ)/(b : ℝ) :=
    hsqR.trans (Certificates.P2HistoricLogPointInterpreter.ediv_le_real a b hb)
  have haR : (0 : ℝ) < a := by
    have hh := (le_div_iff₀ hbR).1 hks
    nlinarith only [hsR,hbR,hh]
  have haZ : 0 < a := by exact_mod_cast haR
  have hgap := normalized_gap_le_anchor_div_sq hsR hks
  have hanc := dInteger_bounds_actual_gap s hs3 hs12
  have hfac : 0 ≤ (s : ℝ)^2/((a : ℝ)/(b : ℝ))^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hanc hfac
  have hup := ceiling_rounds_up (dInteger s*(s : ℤ)*(s : ℤ)*b*b)
    (a*a) (mul_pos haZ haZ)
  calc
    upper ((a : ℝ)/(b : ℝ))-lower ((a : ℝ)/(b : ℝ)) ≤
        (upper (s : ℝ)-lower (s : ℝ))*(s : ℝ)^2/((a : ℝ)/(b : ℝ))^2 := hgap
    _ ≤ val (dInteger s)*(s : ℝ)^2/((a : ℝ)/(b : ℝ))^2 := by
      simpa only [mul_div_assoc] using hmul
    _ = val (dInteger s*(s : ℤ)*(s : ℤ)*b*b)/((a*a : ℤ) : ℝ) := by
      unfold val
      push_cast
      field_simp [haR.ne',hbR.ne']
      ring
    _ ≤ val (decayTerm a b s) := hup

private theorem le_foldl_min (x : ℝ) (ys : List ℤ) (a : ℤ)
    (ha : x ≤ val a) (hy : ∀ y ∈ ys, x ≤ val y) :
    x ≤ val (ys.foldl min a) := by
  induction ys generalizing a with
  | nil => exact ha
  | cons y ys ih =>
      apply ih
      · rcases le_total a y with h | h
        · simpa only [min_eq_left h] using ha
        · simpa only [min_eq_right h] using hy y (by simp)
      · intro z hz
        exact hy z (by simp [hz])

theorem le_minimum (x : ℝ) (xs : List ℤ) (hne : xs ≠ [])
    (hx : ∀ y ∈ xs, x ≤ val y) : x ≤ val (minimum xs) := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a ys =>
      exact le_foldl_min x ys a (hx a (by simp)) (fun y hy => hx y (by simp [hy]))

/-- No cached D_integer value is an input; every admitted original anchor
is paid by the actual max12 table and true squared-gap decay. -/
theorem dUpper_bounds_actual_gap (a b : ℤ) (hb : 0 < b) (ha : 3*b ≤ a) :
    upper ((a : ℝ)/(b : ℝ))-lower ((a : ℝ)/(b : ℝ)) ≤ val (dUpper a b) := by
  apply le_minimum
  · intro hz
    have hm : decayTerm a b 3 ∈ (decayIndices a b).map (decayTerm a b) :=
      List.mem_map.mpr ⟨3,decayIndices_three a b hb ha,rfl⟩
    rw [hz] at hm
    simpa using hm
  · intro y hy
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hy
    exact decayTerm_bounds_actual_gap a b s hb hs

theorem dUpper_nonnegative (a b : ℤ) (hb : 0 < b) (ha : 3*b ≤ a) : 0 ≤ dUpper a b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hs3 : (3 : ℝ) ≤ (a : ℝ)/(b : ℝ) :=
    (le_div_iff₀ hbR).2 (by exact_mod_cast ha)
  have hg := normalized_gap_nonneg (show (2 : ℝ)≤(a : ℝ)/(b : ℝ) by linarith)
  have hn := hg.trans (dUpper_bounds_actual_gap a b hb ha)
  have h := (le_div_iff₀ scale_real_pos).1 hn
  have hi : (0 : ℝ) ≤ (dUpper a b : ℝ) := by simpa only [zero_mul] using h
  exact_mod_cast hi

end
end ImbalancedChen.P2OriginalCompactQ80ArithmeticSourceOnly
