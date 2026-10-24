import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.Certificates.PairedFibreIntegral

/-!
SOURCE ONLY / UNCOMPILED. No producer, checker, numerical replay, or Lean
elaboration was run for this file.

This is the literal logarithmic payload of manuscript-body.tex (2026-10-24),
equations (current-safe-constants), (current-Z), and (current-extra-fibre).
The coefficient is 8452171/1250000, the inner coefficient is K/80, and
Z is min(u_l, 3(1-t_r-u_r)/13). This independent enclosure evaluates each
logarithm by the historic Q80 `logI` interpreter. All signed products use its
four-corner I80 operation. It does not assert bytewise identity with the
separate P=2^160/W=2^224 paired certificate producer.
The sole geometric premise is the separate exact cell check a <= Z; no
stored gain, saved floor, or target integral inequality is a premise.
-/

namespace ImbalancedChen.Certificates.P2OriginalQ80PairedLogPayload

open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter

def manuscriptK : ℚ := 8452171 / 1250000
def manuscriptA : ℚ := 417 / 5000
def fibreZ (tr ul ur : ℚ) : ℚ := min ul (3 * (1 - tr - ur) / 13)

/-- The old directed Q80 operations applied to the original closed form.
The negated logarithmic bracket is enclosed before the final product. -/
def pairedQ80 (tl tr ul ur : ℚ) : I80 :=
  let Z := fibreZ tr ul ur
  let lt := logI (tr / tl)
  let lu := logI (ur / ul)
  let lz := logI (Z / manuscriptA)
  (((I80.point (manuscriptK / 80)).mul lt).mul lu).mul
    ((I80.point (1 / manuscriptA)).sub
      ((I80.point (1 / Z)).mul ((I80.point 1).add lz)))

theorem manuscriptA_pos : 0 < manuscriptA := by
  norm_num [manuscriptA]

/-- The historical log interpreter proves the three actual log enclosures.
The interval arithmetic then propagates them with the correct sign. -/
theorem pairedQ80_contains_closed_form (tl tr ul ur : ℚ)
    (htl : 0 < tl) (htr : tl ≤ tr) (hul : 0 < ul) (hur : ul ≤ ur)
    (hZ : manuscriptA ≤ fibreZ tr ul ur) :
    (pairedQ80 tl tr ul ur).Contains
      (((manuscriptK : ℝ) / 80) * Real.log (((tr / tl : ℚ) : ℝ)) *
        Real.log (((ur / ul : ℚ) : ℝ)) *
        (1 / (manuscriptA : ℝ) -
          (1 + Real.log ((((fibreZ tr ul ur) / manuscriptA : ℚ) : ℝ))) /
            (fibreZ tr ul ur : ℝ))) := by
  let Z := fibreZ tr ul ur
  have hT : 1 ≤ tr / tl := (le_div_iff₀ htl).2 (by simpa using htr)
  have hU : 1 ≤ ur / ul := (le_div_iff₀ hul).2 (by simpa using hur)
  have hZ' : manuscriptA ≤ Z := hZ
  have hLZ : 1 ≤ Z / manuscriptA :=
    (le_div_iff₀ manuscriptA_pos).2 (by simpa using hZ')
  have htLog := logI_contains_of_one_le (tr / tl) hT
  have huLog := logI_contains_of_one_le (ur / ul) hU
  have hzLog := logI_contains_of_one_le (Z / manuscriptA) hLZ
  have hBracket := I80.sub_contains (I80.point_contains (1 / manuscriptA))
    (I80.mul_contains (I80.point_contains (1 / Z))
      (I80.add_contains (I80.point_contains 1) hzLog))
  have hProduct := I80.mul_contains
    (I80.mul_contains
      (I80.mul_contains (I80.point_contains (manuscriptK / 80)) htLog) huLog)
    hBracket
  unfold pairedQ80
  convert hProduct using 1
  push_cast
  ring

/-- The Q80 enclosure is for the four-variable fibre integral itself.
The only analytic inputs are positive endpoints and the exact Z wall. -/
theorem pairedQ80_contains_integral (tl tr ul ur : ℚ)
    (htl : 0 < tl) (htr : tl ≤ tr) (hul : 0 < ul) (hur : ul ≤ ur)
    (hZ : manuscriptA ≤ fibreZ tr ul ur) :
    (pairedQ80 tl tr ul ur).Contains
      (pairedLocalIntegral (manuscriptK : ℝ) manuscriptA tl tr ul ur
        (fibreZ tr ul ur)) := by
  have haR : (0 : ℝ) < manuscriptA := by exact_mod_cast manuscriptA_pos
  have hZR : (manuscriptA : ℝ) ≤ (fibreZ tr ul ur : ℝ) := by exact_mod_cast hZ
  have htlR : (0 : ℝ) < tl := by exact_mod_cast htl
  have htrR : (0 : ℝ) < tr := by exact_mod_cast htl.trans_le htr
  have hulR : (0 : ℝ) < ul := by exact_mod_cast hul
  have hurR : (0 : ℝ) < ur := by exact_mod_cast hul.trans_le hur
  rw [pairedLocalIntegral_eq (manuscriptK : ℝ) haR hZR htlR htrR hulR hurR]
  simpa only [Rat.cast_div] using
    pairedQ80_contains_closed_form tl tr ul ur htl htr hul hur hZ

end ImbalancedChen.Certificates.P2OriginalQ80PairedLogPayload
