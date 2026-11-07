import ImbalancedChen.P2OriginalCompactQ80Leaf

/-!
SOURCE ONLY / UNCOMPILED / NO FINITE GUARD EVALUATED.

The literal Q80 moment and signed clipped-chord arithmetic of the original
producer. The logarithms are the actual log32 interpreter and every factor
query is the actual max12 table. All signs of the old chord slope are allowed.
Only the original positive-denominator assertions are accepted here; a true
moment or factor bound is never an arithmetic input.
-/
namespace ImbalancedChen.P2OriginalCompactQ80JensenMomentsSourceOnly

noncomputable section
open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open OriginalThirdBoxMomentsSourceOnly

def realXMean (box : RawBox) : ℝ :=
  ((box.2 0 : ℝ)-(box.1 0 : ℝ))/Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ))

def realYMean (box : RawBox) : ℝ :=
  ((box.2 1 : ℝ)-(box.1 1 : ℝ))/Real.log ((box.2 1 : ℝ)/(box.1 1 : ℝ))

def realInvZMean (box : RawBox) : ℝ :=
  ((box.1 2 : ℝ)+(box.2 2 : ℝ))/(2*(box.1 2 : ℝ)*(box.2 2 : ℝ))

def realMaxMean (box : RawBox) : ℝ :=
  2*((box.2 0 : ℝ)*Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ))-
    (box.2 0 : ℝ)+(box.1 0 : ℝ))/
    (Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ))*
      Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ)))

def realNewMean (box : RawBox) : ℝ :=
  ((thetaInteger : ℝ)-realXMean box-realYMean box)*realInvZMean box-1

def realOldMean (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane) : ℝ :=
  if aboveSymmetric box then
    ((57*(denominator : ℝ)/64-realXMean box-realYMean box)-
      (3/2)*realMaxMean box)*realInvZMean box-1
  else
    (((p.a : ℝ)*(denominator : ℝ)/(p.e : ℝ)+
      ((p.b : ℝ)-(p.e : ℝ))/(p.e : ℝ)*realXMean box)+
      ((p.c : ℝ)-(p.e : ℝ))/(p.e : ℝ)*realYMean box)*realInvZMean box+
      ((p.d : ℝ)-(p.e : ℝ))/(p.e : ℝ)

def realChord (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane) : ℝ :=
  let lo := oldLow box p
  let hi := oldHigh box p
  let fl := (point lo.num (lo.den : ℤ)).lo
  let fh := (point hi.num (hi.den : ℤ)).lo
  val fl+(realOldMean box p-(lo : ℝ))/((hi : ℝ)-(lo : ℝ))*(val fh-val fl)

/-- Python's scalar `__rmul__` reverses the interval operand order. The
literal four-corner products give EXACT equality, including both roundings;
this is stronger than an enclosure comparison. -/
theorem mul_comm_exact (x y : I80) : x.mul y=y.mul x := by
  rw [mul_source,mul_source]
  ext <;> simp only [mul_comm,min_assoc,min_left_comm,min_comm,
    max_assoc,max_left_comm,max_comm]

theorem maxMean_python_operand_order (box : RawBox) : maxMean box=
    let lx := logarithmicWidth (box.1 0) (box.2 0)
    let numerator := ((lx.mul (I80.point (box.2 0 : ℚ))).sub
      (I80.point (box.2 0 : ℚ))).add (I80.point (box.1 0 : ℚ))
    historicalDiv (numerator.mul (I80.point 2)) (lx.mul lx) := by
  simp only [maxMean,mul_comm_exact]

theorem oldMean_python_operand_order (box : RawBox)
    (p : P2OriginalCompactQ80EncloserSourceOnly.Plane) : oldMean box p=
    if aboveSymmetric box then
      let base := (((I80.point (((57*denominator : ℤ) : ℚ)/64)).sub (xMean box)).sub
        (yMean box)).sub ((maxMean box).mul (I80.point (3/2)))
      (base.mul (invZMean box)).sub (I80.point 1)
    else
      let base := ((I80.point (((p.a*denominator : ℤ) : ℚ)/(p.e : ℚ))).add
        ((xMean box).mul (I80.point (((p.b-p.e : ℤ) : ℚ)/(p.e : ℚ))))).add
        ((yMean box).mul (I80.point (((p.c-p.e : ℤ) : ℚ)/(p.e : ℚ))))
      (base.mul (invZMean box)).add (I80.point (((p.d-p.e : ℤ) : ℚ)/(p.e : ℚ))) := by
  simp only [oldMean,mul_comm_exact]

theorem xMean_contains (box : RawBox) (g : Geometry box)
    (hlog : 0 < (logarithmicWidth (box.1 0) (box.2 0)).lo) :
    (xMean box).Contains (realXMean box) := by
  have hx := (logarithmicWidth_contains _ _ (g.raw_positive 0) (g.width 0).le).1
  have hn := I80.point_contains (((box.2 0-box.1 0 : ℤ) : ℚ))
  simpa only [xMean,realXMean,Rat.cast_intCast,Int.cast_sub] using
    historicalDiv_contains hn hx hlog

theorem yMean_contains (box : RawBox) (g : Geometry box)
    (hlog : 0 < (logarithmicWidth (box.1 1) (box.2 1)).lo) :
    (yMean box).Contains (realYMean box) := by
  have hy := (logarithmicWidth_contains _ _ (g.raw_positive 1) (g.width 1).le).1
  have hn := I80.point_contains (((box.2 1-box.1 1 : ℤ) : ℚ))
  simpa only [yMean,realYMean,Rat.cast_intCast,Int.cast_sub] using
    historicalDiv_contains hn hy hlog

theorem invZMean_contains (box : RawBox) :
    (invZMean box).Contains (realInvZMean box) := by
  simpa only [invZMean,realInvZMean,Rat.cast_div,Rat.cast_intCast,
    Int.cast_add,Int.cast_mul,Int.cast_ofNat] using
    I80.point_contains (((box.1 2+box.2 2 : ℤ) : ℚ)/
      ((2*box.1 2*box.2 2 : ℤ) : ℚ))

/-- There is a round after each operation in the literal source expression.
In particular the signed multiplication is not replaced by a one-sided one. -/
theorem newMean_contains (box : RawBox) (g : Geometry box)
    (hx : 0 < (logarithmicWidth (box.1 0) (box.2 0)).lo)
    (hy : 0 < (logarithmicWidth (box.1 1) (box.2 1)).lo) :
    (newMean box).Contains (realNewMean box) := by
  have ht := I80.point_contains (thetaInteger : ℚ)
  have h1 := I80.point_contains (1 : ℚ)
  simpa only [newMean,realNewMean,Rat.cast_intCast,Rat.cast_one] using
    I80.sub_contains
      (I80.mul_contains (I80.sub_contains
        (I80.sub_contains ht (xMean_contains box g hx)) (yMean_contains box g hy))
        (invZMean_contains box)) h1

theorem maxMean_contains (box : RawBox) (g : Geometry box)
    (hsq : 0 < ((logarithmicWidth (box.1 0) (box.2 0)).mul
      (logarithmicWidth (box.1 0) (box.2 0))).lo) :
    (maxMean box).Contains (realMaxMean box) := by
  have hl := (logarithmicWidth_contains _ _ (g.raw_positive 0) (g.width 0).le).1
  have hb := I80.point_contains (box.2 0 : ℚ)
  have ha := I80.point_contains (box.1 0 : ℚ)
  have h2 := I80.point_contains (2 : ℚ)
  have hn := I80.mul_contains h2
    (I80.add_contains (I80.sub_contains (I80.mul_contains hb hl) hb) ha)
  simpa only [maxMean,realMaxMean,Rat.cast_intCast,Rat.cast_ofNat] using
    historicalDiv_contains hn (I80.mul_contains hl hl) hsq

theorem oldMean_contains (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane)
    (g : Geometry box)
    (hx : 0 < (logarithmicWidth (box.1 0) (box.2 0)).lo)
    (hy : 0 < (logarithmicWidth (box.1 1) (box.2 1)).lo)
    (hsq : aboveSymmetric box → 0 < ((logarithmicWidth (box.1 0) (box.2 0)).mul
      (logarithmicWidth (box.1 0) (box.2 0))).lo) :
    (oldMean box p).Contains (realOldMean box p) := by
  have ex := xMean_contains box g hx
  have ey := yMean_contains box g hy
  have ez := invZMean_contains box
  by_cases hs : aboveSymmetric box
  · have hc := I80.point_contains (((57*denominator : ℤ) : ℚ)/64)
    have h32 := I80.point_contains (3/2 : ℚ)
    have h1 := I80.point_contains (1 : ℚ)
    have hm := maxMean_contains box g (hsq hs)
    simpa only [oldMean,realOldMean,if_pos hs,Rat.cast_div,Rat.cast_intCast,
      Rat.cast_ofNat,Rat.cast_one,Int.cast_mul,Int.cast_ofNat] using
      I80.sub_contains (I80.mul_contains (I80.sub_contains
        (I80.sub_contains (I80.sub_contains hc ex) ey) (I80.mul_contains h32 hm)) ez) h1
  · have ha := I80.point_contains (((p.a*denominator : ℤ) : ℚ)/(p.e : ℚ))
    have hb := I80.point_contains (((p.b-p.e : ℤ) : ℚ)/(p.e : ℚ))
    have hc := I80.point_contains (((p.c-p.e : ℤ) : ℚ)/(p.e : ℚ))
    have hd := I80.point_contains (((p.d-p.e : ℤ) : ℚ)/(p.e : ℚ))
    simpa only [oldMean,realOldMean,if_neg hs,Rat.cast_div,Rat.cast_intCast,
      Int.cast_mul,Int.cast_sub] using
      I80.add_contains (I80.mul_contains
        (I80.add_contains (I80.add_contains ha (I80.mul_contains hb ex))
          (I80.mul_contains hc ey)) ez) hd

theorem realNewMean_eq_physical (box : RawBox) (g : Geometry box) :
    realNewMean box =
      (thirdPrefixTheta-boxEX (decodeCoordinates box.1) (decodeCoordinates box.2)-
        boxEY (decodeCoordinates box.1) (decodeCoordinates box.2))*
        boxEZInv (decodeCoordinates box.1) (decodeCoordinates box.2)-1 := by
  have hD : (denominator : ℝ) ≠ 0 := by norm_num [denominator]
  have hx : (box.1 0 : ℝ) ≠ 0 := by exact_mod_cast (g.raw_positive 0).ne'
  have hy : (box.1 1 : ℝ) ≠ 0 := by exact_mod_cast (g.raw_positive 1).ne'
  have hz : (box.1 2 : ℝ) ≠ 0 := by exact_mod_cast (g.raw_positive 2).ne'
  have hz' : (box.2 2 : ℝ) ≠ 0 := by exact_mod_cast ((g.raw_positive 2).trans (g.width 2)).ne'
  have htx : (box.2 0 : ℝ)/denominator/((box.1 0 : ℝ)/denominator)=
      (box.2 0 : ℝ)/(box.1 0 : ℝ) := div_div_div_cancel_right₀ hD _ _
  have hty : (box.2 1 : ℝ)/denominator/((box.1 1 : ℝ)/denominator)=
      (box.2 1 : ℝ)/(box.1 1 : ℝ) := div_div_div_cancel_right₀ hD _ _
  have hlx : Real.log ((box.2 0 : ℝ)/(box.1 0 : ℝ)) ≠ 0 :=
    (Real.log_pos ((one_lt_div (by exact_mod_cast g.raw_positive 0)).2
      (by exact_mod_cast g.width 0))).ne'
  have hly : Real.log ((box.2 1 : ℝ)/(box.1 1 : ℝ)) ≠ 0 :=
    (Real.log_pos ((one_lt_div (by exact_mod_cast g.raw_positive 1)).2
      (by exact_mod_cast g.width 1))).ne'
  have ht : (thetaInteger : ℝ)=(denominator : ℝ)*thirdPrefixTheta := by
    norm_num [thetaInteger,denominator,thirdPrefixTheta]
  simp only [realNewMean,realXMean,realYMean,realInvZMean,boxEX,boxEY,boxEZInv,
    decode_binding,htx,hty]
  rw [ht]
  field_simp [hD,hz,hz',hlx,hly]
  ring

theorem new_query_upper (box : RawBox) (g : Geometry box)
    (hx : 0 < (logarithmicWidth (box.1 0) (box.2 0)).lo)
    (hy : 0 < (logarithmicWidth (box.1 1) (box.2 1)).lo) :
    actualExtendedThirdLowerFactor (realNewMean box) ≤
      val (point (newMean box).hi scale).hi := by
  have hm := ((contains_iff _ _).1 (newMean_contains box g hx hy)).2
  exact (monotone_actualExtendedThirdLowerFactor hm).trans
    (((contains_iff _ _).1 (point_contains_actual (newMean box).hi scale scale_pos)).2)

theorem rational_query_lower (q : ℚ) :
    val (point q.num (q.den : ℤ)).lo ≤ actualExtendedThirdLowerFactor (q : ℝ) := by
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have h := ((contains_iff _ _).1 (point_contains_actual q.num (q.den : ℤ) hd)).1
  simpa only [Rat.cast_def,Int.cast_natCast] using h

theorem raw_contains_val (n : ℤ) : (I80.raw n).Contains (val n) := by
  exact (contains_iff _ _).2 ⟨le_rfl,le_rfl⟩

/-- Clipping retains the actual weight; neither endpoint order nor a sign
of fh-fl is needed. -/
theorem clip_contains {w : I80} {r : ℝ} (hw : w.Contains r)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (⟨max 0 w.lo,min scale w.hi⟩ : I80).Contains r := by
  obtain ⟨hl,hh⟩ := (contains_iff _ _).1 hw
  apply (contains_iff _ _).2
  constructor
  · rw [val_max,val_zero]
    exact max_le hr0 hl
  · have hs : val scale=1 := div_self scale_real_pos.ne'
    rcases le_total scale w.hi with h | h
    · simpa only [min_eq_left h,hs] using hr1
    · simpa only [min_eq_right h] using hh

theorem chordWeight_contains (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane)
    (hm : (oldMean box p).Contains (realOldMean box p))
    (hspan : oldLow box p < oldHigh box p)
    (hr : realOldMean box p ∈ Icc (oldLow box p : ℝ) (oldHigh box p : ℝ))
    (hden : 0 < (I80.point (oldHigh box p-oldLow box p)).lo) :
    (chordWeight box p).Contains
      ((realOldMean box p-(oldLow box p : ℝ))/((oldHigh box p : ℝ)-(oldLow box p : ℝ))) := by
  have hd : (0 : ℝ) < (oldHigh box p : ℝ)-(oldLow box p : ℝ) := by
    exact_mod_cast sub_pos.mpr hspan
  have hw := historicalDiv_contains
    (I80.sub_contains hm (I80.point_contains (oldLow box p)))
    (I80.point_contains (oldHigh box p-oldLow box p)) hden
  apply clip_contains (by simpa only [Rat.cast_sub] using hw)
  · exact div_nonneg (sub_nonneg.mpr hr.1) hd.le
  · exact (div_le_one hd).2 (by linarith only [hr.2])

theorem chordLower_le_realChord (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane)
    (hm : (oldMean box p).Contains (realOldMean box p))
    (hspan : oldLow box p < oldHigh box p)
    (hr : realOldMean box p ∈ Icc (oldLow box p : ℝ) (oldHigh box p : ℝ))
    (hden : 0 < (I80.point (oldHigh box p-oldLow box p)).lo) :
    val (chordLower box p) ≤ realChord box p := by
  have hw := chordWeight_contains box p hm hspan hr hden
  let fl := (point (oldLow box p).num ((oldLow box p).den : ℤ)).lo
  let fh := (point (oldHigh box p).num ((oldHigh box p).den : ℤ)).lo
  have hc := I80.add_contains (raw_contains_val fl)
    (I80.mul_contains hw (raw_contains_val (fh-fl)))
  have hh := ((contains_iff _ _).1 hc).1
  simpa only [chordLower,if_neg (ne_of_lt hspan),realChord,val_sub] using hh

theorem rounded_difference_upper (box : RawBox) (p : P2OriginalCompactQ80EncloserSourceOnly.Plane)
    (hnew : actualExtendedThirdLowerFactor (realNewMean box) ≤
      val (point (newMean box).hi scale).hi)
    (hchord : val (chordLower box p) ≤ realChord box p) :
    max 0 (actualExtendedThirdLowerFactor (realNewMean box)-realChord box p) ≤
      val (max 0 ((point (newMean box).hi scale).hi-chordLower box p)) := by
  rw [val_max,val_zero,val_sub]
  exact max_le_max le_rfl (sub_le_sub hnew hchord)

end
end ImbalancedChen.P2OriginalCompactQ80JensenMomentsSourceOnly
