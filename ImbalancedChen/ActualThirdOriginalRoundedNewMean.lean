import ImbalancedChen.ActualThirdOriginalSymmetricJensenLeaf
import ImbalancedChen.ActualThirdOriginalRoundedNewOperations
import ImbalancedChen.Certificates.RationalLogCertificate

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30. One actual original NEW mean
supplier. The OLD/max moment, raw weight, mass ceil and all-min are not claimed. -/
namespace ImbalancedChen.OriginalThirdRoundedNewSourceOnly
noncomputable section
open OriginalThirdClippedChordSourceOnly
open OriginalThirdSymmetricJensenSourceOnly

/-- Normalized coordinates give exactly the producer's rational invz. -/
theorem producer_invz_identity (D z0 z1 : ℝ)
    (hD : D≠0) (hz0 : z0≠0) (hz1 : z1≠0) :
    invZMean (z0/D) (z1/D)=D*(z0+z1)/(2*z0*z1) := by
  unfold invZMean
  field_simp [hD,hz0,hz1]
  <;> ring

theorem producer_log_ratio (D x0 x1 : ℝ) (hD : D≠0) (hx0 : x0≠0) :
    (x1/D)/(x0/D)=x1/x0 := by
  field_simp [hD,hx0]

theorem producer_width_identity (D x0 x1 : ℝ) :
    x1/D-x0/D=(x1-x0)/D := by ring
/-- Literal symmetric ex=ey=V((x1-x0)/D)/ln(x1/x0). -/
def symmetricEx (a b : ℝ) (lx : IV) : IV := divide (ofReal (b-a)) lx

/-- Original new=(V(TH)-ex-ey)*invz-1. Multiplication by rational invz
first applies V.co; the ofReal_int_div_source theorem gives that exact coercion. -/
def symmetricNew (a b c d : ℝ) (lx : IV) : IV :=
  sub (mul (sub (sub (ofReal thirdPrefixTheta) (symmetricEx a b lx))
    (symmetricEx a b lx)) (ofReal (invZMean c d))) (ofReal 1)

/-- Both NEW endpoints are supplied by the real original operation tree.
The only nonexact operand is the existing logarithm interval lx; no enclosure
of ex, NEW mean, OLD mean or raw weight is an input. -/
theorem symmetricNew_encloses {a b c d : ℝ} {lx : IV}
    (hlog : Encloses lx (Real.log (b/a))) (hpositive : 0<lx.lo) :
    Encloses (symmetricNew a b c d lx) (newMean a b c d) := by
  have hex := divide_sound (ofReal_sound (b-a)) hlog hpositive
  have hnew := sub_sound (mul_sound
    (sub_sound (sub_sound (ofReal_sound thirdPrefixTheta) hex) hex)
    (ofReal_sound (invZMean c d))) (ofReal_sound 1)
  have heq : (thirdPrefixTheta-(b-a)/Real.log (b/a)-(b-a)/Real.log (b/a))*
      invZMean c d-1=newMean a b c d := by
    unfold newMean sumMean
    ring
  rw [heq] at hnew
  exact hnew

/-- This is literally sieve.at(new.hi,P)'s rational argument. -/
def symmetricNewQuery (a b c d : ℝ) (lx : IV) : ℚ :=
  ((symmetricNew a b c d lx).hi:ℚ)/(P160:ℚ)

theorem actual_newMean_le_original_rounded_query {a b c d : ℝ} {lx : IV}
    (hlog : Encloses lx (Real.log (b/a))) (hpositive : 0<lx.lo) :
    newMean a b c d≤(symmetricNewQuery a b c d lx:ℝ) := by
  simpa only [symmetricNewQuery,Rat.cast_div,Rat.cast_intCast,value] using
    (symmetricNew_encloses hlog hpositive).2

/-- A finite, independently checked certificate with the SAME original lx
endpoints discharges the logarithm operand. No semantic mean bound is assumed.
This theorem does not assert that such certificates have been collected for
all original leaves or that the original ln routine has been replayed. -/
theorem actual_newMean_le_query_of_checked_log
    (a b c d : ℚ) (lx : IV) (cert : Certificates.RationalLogCertificate)
    (harg : cert.argument=b/a)
    (hlower : cert.lower=(lx.lo:ℚ)/(P160:ℚ))
    (hupper : cert.upper=(lx.hi:ℚ)/(P160:ℚ))
    (hcheck : cert.check=true) (hpositive : 0<lx.lo) :
    newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)≤
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) lx:ℝ) := by
  have hc := Certificates.RationalLogCertificate.check_sound cert hcheck
  have hlog : Encloses lx (Real.log ((b:ℝ)/(a:ℝ))) := by
    simpa only [Encloses,value,harg,hlower,hupper,Rat.cast_div,Rat.cast_intCast] using hc
  exact actual_newMean_le_original_rounded_query hlog hpositive

/-- The existing query's upper result is consequently an actual NEW-factor
upper bound. This removes hnew from the prior clipped-mean candidate interface. -/
theorem actual_new_factor_upper_of_original_query
    {a b c d : ℝ} {lx : IV} {out : ℤ}
    (hlog : Encloses lx (Real.log (b/a))) (hpositive : 0<lx.lo)
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery a b c d lx:ℝ)≤value out) :
    actualExtendedThirdLowerFactor (newMean a b c d)≤value out := by
  exact (monotone_actualExtendedThirdLowerFactor
    (actual_newMean_le_original_rounded_query hlog hpositive)).trans hquery

end
end ImbalancedChen.OriginalThirdRoundedNewSourceOnly
