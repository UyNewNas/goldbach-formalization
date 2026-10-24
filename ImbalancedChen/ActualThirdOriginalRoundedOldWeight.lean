import ImbalancedChen.ActualThirdOriginalRoundedNewMean
import ImbalancedChen.ActualThirdOriginalSymmetricClippedMean
import ImbalancedChen.ActualThirdOriginalPositive256Log

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Original above-mu OLD max-moment expression and pre-clipping wt. The original
positive log and squared-log divisor guards remain explicit integer facts. -/
namespace ImbalancedChen.OriginalThirdRoundedOldWeightSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdSymmetricClippedMeanSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly

/-- Literal positive rational division in V.__truediv__, not reciprocal-V division. -/
def divRat (v : IV) (q : ℚ) : IV :=
  ⟨v.lo*(q.den:ℤ)/q.num,up (v.hi*(q.den:ℤ)) q.num⟩

private theorem scaled_floor_div_le {d : ℤ} (hd : 0<d) (n : ℤ) :
    value (n/d)≤(n:ℝ)/(d:ℝ)/(P160:ℝ) := by
  have hf : ⌊(n:ℝ)/(d:ℝ)⌋=n/d := by
    simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) hd.le (n:ℝ)
  have h := Int.floor_le ((n:ℝ)/(d:ℝ))
  rw [hf] at h
  exact (div_le_div_iff_of_pos_right P160_real_pos).2 h

private theorem le_scaled_up_div {d : ℤ} (hd : 0<d) (n : ℤ) :
    (n:ℝ)/(d:ℝ)/(P160:ℝ)≤value (up n d) := by
  have h := neg_le_neg (scaled_floor_div_le hd (-n))
  simpa only [up, value, Int.cast_neg, neg_div, neg_neg] using h

theorem divRat_sound {v : IV} {x : ℝ} {q : ℚ}
    (hv : Encloses v x) (hq : 0<q) : Encloses (divRat v q) (x/(q:ℝ)) := by
  have hn : 0<q.num := Rat.num_pos.mpr hq
  have hqr : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
  have alg (z : ℤ) : ((z*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ)=value z/(q:ℝ) := by
    simp only [value,Rat.cast_def,Int.cast_mul,Int.cast_natCast,div_eq_mul_inv,
      mul_inv_rev,inv_inv]
    ring
  constructor
  · calc
      value (v.lo*(q.den:ℤ)/q.num) ≤ ((v.lo*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ) :=
        scaled_floor_div_le hn _
      _ = value v.lo/(q:ℝ) := alg _
      _ ≤ x/(q:ℝ) := (div_le_div_iff_of_pos_right hqr).2 hv.1
  · calc
      x/(q:ℝ) ≤ value v.hi/(q:ℝ) := (div_le_div_iff_of_pos_right hqr).2 hv.2
      _ = ((v.hi*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ) := (alg _).symm
      _ ≤ value (up (v.hi*(q.den:ℤ)) q.num) := le_scaled_up_div hn _

/-- Python's 2*interval calls __rmul__ with interval self on the left.
The numerator's interval subtraction and both reciprocal roundings are kept. -/
def symmetricMaxMoment (a b : ℝ) (lx : IV) : IV :=
  divide (mul (sub (mul (ofReal b) lx) (ofReal (b-a))) (ofReal 2)) (mul lx lx)

/-- em is the true ordered E[max] under the reciprocal triangle law. -/
theorem symmetricMaxMoment_encloses {a b : ℝ} {lx : IV}
    (hlog : Encloses lx (Real.log (b/a))) (hsquare : 0<(mul lx lx).lo) :
    Encloses (symmetricMaxMoment a b lx) (maxMean a b) := by
  have hnum := mul_sound (sub_sound (mul_sound (ofReal_sound b) hlog)
    (ofReal_sound (b-a))) (ofReal_sound 2)
  have h := divide_sound hnum (mul_sound hlog hlog) hsquare
  have heq : ((b*Real.log (b/a)-(b-a))*2)/(Real.log (b/a)*Real.log (b/a))=
      maxMean a b := by
    unfold maxMean
    simp only [pow_two,div_eq_mul_inv]
    ring
  rw [heq] at h
  exact h

/-- Original old=(V(57/64)-ex-ey-(3/2)*em)*invz-1.
The (3/2)*em operand order follows __rmul__, as in the original producer. -/
def symmetricOld (a b c d : ℝ) (lx : IV) : IV :=
  sub (mul (sub (sub (sub (ofReal (57/64)) (symmetricEx a b lx))
    (symmetricEx a b lx)) (mul (symmetricMaxMoment a b lx) (ofReal (3/2))))
    (ofReal (invZMean c d))) (ofReal 1)

theorem symmetricOld_encloses {a b c d : ℝ} {lx : IV}
    (hlog : Encloses lx (Real.log (b/a))) (hpositive : 0<lx.lo)
    (hsquare : 0<(mul lx lx).lo) :
    Encloses (symmetricOld a b c d lx) (oldMean a b c d) := by
  have hex := divide_sound (ofReal_sound (b-a)) hlog hpositive
  have hem := symmetricMaxMoment_encloses hlog hsquare
  have h := sub_sound (mul_sound
    (sub_sound (sub_sound (sub_sound (ofReal_sound (57/64)) hex) hex)
      (mul_sound hem (ofReal_sound (3/2))))
    (ofReal_sound (invZMean c d))) (ofReal_sound 1)
  have heq : (57/64-(b-a)/Real.log (b/a)-(b-a)/Real.log (b/a)-maxMean a b*(3/2))*
      invZMean c d-1=oldMean a b c d := by
    unfold oldMean sumMean
    ring
  rw [heq] at h
  exact h

/-- Original exact rational low/high from minorant (57,-96,0,0,64),
with a=x0/D,b=x1/D and symmetric x/y endpoints. -/
def oldLowQ (b d : ℚ) : ℚ := (57/64-(7/2)*b)/d-1

def oldHighQ (a c : ℚ) : ℚ := (57/64-(7/2)*a)/c-1

@[simp] theorem cast_oldLowQ (b d : ℚ) : (oldLowQ b d:ℝ)=oldLow (b:ℝ) (d:ℝ) := by
  norm_num [oldLowQ,oldLow]

@[simp] theorem cast_oldHighQ (a c : ℚ) : (oldHighQ a c:ℝ)=oldHigh (a:ℝ) (c:ℝ) := by
  norm_num [oldHighQ,oldHigh]

/-- Literal pre-clipping wt=(old-low)/(high-low), including V.co(low)
and direct positive rational division. -/
def rawWeight (a b c d : ℚ) (lx : IV) : IV :=
  divRat (sub (symmetricOld (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) lx)
    (ofReal (oldLowQ b d:ℝ))) (oldHighQ a c-oldLowQ b d)

theorem rawWeight_encloses (a b c d : ℚ) (lx : IV)
    (hlog : Encloses lx (Real.log ((b:ℝ)/(a:ℝ))))
    (hpositive : 0<lx.lo) (hsquare : 0<(mul lx lx).lo)
    (hspan : oldLow (b:ℝ) (d:ℝ)<oldHigh (a:ℝ) (c:ℝ)) :
    Encloses (rawWeight a b c d lx) (oldWeight (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) := by
  have hq : (0:ℚ)<oldHighQ a c-oldLowQ b d := by
    have hr : (0:ℝ)<((oldHighQ a c-oldLowQ b d:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,cast_oldHighQ,cast_oldLowQ] using sub_pos.mpr hspan
    exact_mod_cast hr
  have h := divRat_sound (sub_sound (symmetricOld_encloses (c := (c : ℝ)) (d := (d : ℝ)) hlog hpositive hsquare)
    (ofReal_sound (oldLowQ b d:ℝ))) hq
  simpa only [rawWeight,oldWeight,Rat.cast_sub,cast_oldHighQ,cast_oldLowQ] using h

/-- Literal original positive256 log supplies the semantic operand. No desired
OLD/weight enclosure or table-node value is an input. These moments contain no
sieve-factor node lookup; the endpoint queries are separate downstream inputs. -/
theorem original_above_mu_rawWeight_encloses (a b c d : ℚ)
    (hab : (a:ℝ)<(b:ℝ)) (ha : (25:ℝ)/128≤(a:ℝ)) (hb : (b:ℝ)≤(19:ℝ)/96)
    (hpositive : 0<(originalLnUnit ((b:ℝ)/(a:ℝ))).lo)
    (hsquare : 0<(mul (originalLnUnit ((b:ℝ)/(a:ℝ)))
      (originalLnUnit ((b:ℝ)/(a:ℝ)))).lo)
    (hspan : oldLow (b:ℝ) (d:ℝ)<oldHigh (a:ℝ) (c:ℝ)) :
    Encloses (rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ))))
      (oldWeight (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) := by
  exact rawWeight_encloses a b c d _ (original_above_mu_log_sound hab ha hb)
    hpositive hsquare hspan

/-- The single original above-mu symmetric Jensen candidate now has its OLD
raw-weight and NEW outward-mean premises supplied by the literal operation
chain and positive256 log. The actual query results remain query premises. -/
theorem original_symmetric_literal_means_candidate
    (a b c d : ℚ) (fl fh out : ℤ)
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu≤(a:ℝ))
    (hpositive : 0<(originalLnUnit ((b:ℝ)/(a:ℝ))).lo)
    (hsquare : 0<(mul (originalLnUnit ((b:ℝ)/(a:ℝ)))
      (originalLnUnit ((b:ℝ)/(a:ℝ)))).lo)
    (hlo : 2≤oldLow (b:ℝ) (d:ℝ))
    (hspan : oldLow (b:ℝ) (d:ℝ)<oldHigh (a:ℝ) (c:ℝ))
    (hfl : value fl≤actualExtendedThirdLowerFactor (oldLow (b:ℝ) (d:ℝ)))
    (hfh : value fh≤actualExtendedThirdLowerFactor (oldHigh (a:ℝ) (c:ℝ)))
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)≤value out) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value (meanHigh
        (rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))).lo
        (rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))).hi fl fh out) := by
  have ha : (25:ℝ)/128≤(a:ℝ) := by simpa only [VariableEnvelope.mu] using hmu
  have hb : (b:ℝ)≤(19:ℝ)/96 := by simpa only [thirdPrefixRho] using hg.upper_rho
  have hlog := original_above_mu_log_sound hg.width_xy ha hb
  have hw := rawWeight_encloses a b c d _ hlog hpositive hsquare hspan
  exact original_symmetric_clipped_mean_candidate hg hmu hlo hspan hw.1 hw.2 hfl hfh
    (actual_newMean_le_original_rounded_query hlog hpositive) hquery

end
end ImbalancedChen.OriginalThirdRoundedOldWeightSourceOnly
