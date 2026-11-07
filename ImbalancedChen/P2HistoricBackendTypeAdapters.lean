import ImbalancedChen.P2HistoricSieveStateInduction
import ImbalancedChen.P2HistoricLogPointInterpreter
import ImbalancedChen.P2HistoricI80DivisionSoundness

/-!
SOURCE_WRITTEN_UNCOMPILED / code only, 2026-10-24.

Both restored historical backends ALREADY return the shared signed I80
carrier from P2HistoricQ80DefectLookup. No new interval carrier or interval
conversion is inserted here. This module pins the actual Ordinary(16384)
delegation to SieveTable(16384,8), the exact log(I(q)) endpoint delegation,
the two normalization scales, and concrete primitive interval licences.

The sf and log licences below are obtained from their source-level proof
modules. Callers do not pass global hsf/hlog semantic hypotheses.
Final cell integrals and parent finite sums are separate composition work.
-/

namespace ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters

noncomputable section

open P2HistoricQ80DefectLookup

/-- Literal Ordinary(16384).f: the source constructor passes maximum=8,
even though the imported SieveTable class has default maximum=12. -/
def sourceSf : ℚ → I80 := ImbalancedChen.P2HistoricSieveTableSemantics.sf 16384 8

/-- Literal source log(I(q)); this retains its initial rational-to-Q80
rounding and then selects opposite log_point endpoint bounds. -/
def sourceLogI : ℚ → I80 := P2HistoricLogPointInterpreter.logI

theorem sieve_scale_eq_Q :
    ImbalancedChen.P2HistoricSieveTableSemantics.scale = (Q:ℤ) := by
  norm_num [ImbalancedChen.P2HistoricSieveTableSemantics.scale,Q]

theorem sieve_value_eq_decode (n : ℤ) :
    ImbalancedChen.P2HistoricSieveTableSemantics.value n = (((n:ℚ)/Q:ℚ):ℝ) := by
  simp [ImbalancedChen.P2HistoricSieveTableSemantics.value,sieve_scale_eq_Q]

theorem log_decode_eq_decode (n : ℤ) :
    P2HistoricLogPointInterpreter.decode n = (((n:ℚ)/Q:ℚ):ℝ) := by
  simp [P2HistoricLogPointInterpreter.decode]

theorem sourceSf_delegation (q : ℚ) : sourceSf q =
    ImbalancedChen.P2HistoricSieveTableSemantics.point 16384 8 q.num (q.den:ℤ) := rfl

theorem sourceSf_lo_exact (q : ℚ) : (sourceSf q).lo =
    (ImbalancedChen.P2HistoricSieveTableSemantics.point 16384 8 q.num (q.den:ℤ)).lo := rfl

theorem sourceSf_hi_exact (q : ℚ) : (sourceSf q).hi =
    (ImbalancedChen.P2HistoricSieveTableSemantics.point 16384 8 q.num (q.den:ℤ)).hi := rfl

theorem sourceSf_decodeLo_eq_value (q : ℚ) :
    ((sourceSf q).decodeLo:ℝ) =
      ImbalancedChen.P2HistoricSieveTableSemantics.value (sourceSf q).lo := by
  rw [sieve_value_eq_decode]
  rfl

theorem sourceSf_decodeHi_eq_value (q : ℚ) :
    ((sourceSf q).decodeHi:ℝ) =
      ImbalancedChen.P2HistoricSieveTableSemantics.value (sourceSf q).hi := by
  rw [sieve_value_eq_decode]
  rfl

theorem sourceLogI_lo_exact (q : ℚ) : (sourceLogI q).lo =
    (P2HistoricLogPointInterpreter.logPoint (I80.point q).lo).lo := rfl

theorem sourceLogI_hi_exact (q : ℚ) : (sourceLogI q).hi =
    (P2HistoricLogPointInterpreter.logPoint (I80.point q).hi).hi := rfl

theorem sourceLogI_decodeLo_eq_value (q : ℚ) :
    ((sourceLogI q).decodeLo:ℝ) =
      P2HistoricLogPointInterpreter.decode (sourceLogI q).lo := by
  rw [log_decode_eq_decode]
  rfl

theorem sourceLogI_decodeHi_eq_value (q : ℚ) :
    ((sourceLogI q).decodeHi:ℝ) =
      P2HistoricLogPointInterpreter.decode (sourceLogI q).hi := by
  rw [log_decode_eq_decode]
  rfl

/-- The whole original sf backend is now instantiated. No arbitrary
backend, node array, accepted checker, or sf-soundness hypothesis remains. -/
theorem sourceSf_contains_actual (q : ℚ) :
    (sourceSf q).Contains (ImbalancedChen.actualExtendedThirdLowerFactor (q:ℝ)) := by
  exact ImbalancedChen.P2HistoricSieveStateInduction.sf_contains_actual q

theorem sourceSf_decodeLo_le_actual (q : ℚ) :
    ((sourceSf q).decodeLo:ℝ) ≤ ImbalancedChen.actualExtendedThirdLowerFactor (q:ℝ) := by
  exact (sourceSf_contains_actual q).1

theorem actual_le_sourceSf_decodeHi (q : ℚ) :
    ImbalancedChen.actualExtendedThirdLowerFactor (q:ℝ) ≤ ((sourceSf q).decodeHi:ℝ) := by
  exact (sourceSf_contains_actual q).2

/-- This is the source's sole rounded query guard, not a logarithm-bound
premise. It is discharged below from physical ratio ordering. -/
theorem sourceLogI_contains (q : ℚ) (hpos : 0 < (I80.point q).lo) :
    (sourceLogI q).Contains (Real.log (q:ℝ)) := by
  exact P2HistoricLogPointInterpreter.logI_contains q hpos

theorem sourceLogI_contains_of_one_le (q : ℚ) (hq : 1 ≤ q) :
    (sourceLogI q).Contains (Real.log (q:ℝ)) := by
  exact P2HistoricLogPointInterpreter.logI_contains_of_one_le q hq

theorem ordered_ratio_one_le (l r : ℚ) (hl : 0 < l) (hlr : l ≤ r) : 1 ≤ r/l := by
  exact (le_div_iff₀ hl).mpr (by simpa using hlr)

theorem sourceLogI_ratio_contains (l r : ℚ) (hl : 0 < l) (hlr : l ≤ r) :
    (sourceLogI (r/l)).Contains (Real.log ((r/l:ℚ):ℝ)) := by
  exact sourceLogI_contains_of_one_le _ (ordered_ratio_one_le l r hl hlr)

theorem sourceLogI_ratio_decodeLo_le (l r : ℚ) (hl : 0 < l) (hlr : l ≤ r) :
    ((sourceLogI (r/l)).decodeLo:ℝ) ≤ Real.log ((r/l:ℚ):ℝ) := by
  exact (sourceLogI_ratio_contains l r hl hlr).1

theorem sourceLogI_ratio_decodeHi_ge (l r : ℚ) (hl : 0 < l) (hlr : l ≤ r) :
    Real.log ((r/l:ℚ):ℝ) ≤ ((sourceLogI (r/l)).decodeHi:ℝ) := by
  exact (sourceLogI_ratio_contains l r hl hlr).2

theorem source_rectangleMass_contains (tl tr ul ur : ℚ)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    (rectangleMass sourceLogI tl tr ul ur).Contains (rectangleMassValue tl tr ul ur) := by
  exact rectangleMass_contains sourceLogI tl tr ul ur
    (sourceLogI_ratio_contains tl tr htl ht) (sourceLogI_ratio_contains ul ur hul hu)

theorem source_rectangleMomentT_contains (tl tr ul ur : ℚ)
    (hul : 0 < ul) (hu : ul ≤ ur) :
    (rectangleMomentT sourceLogI tl tr ul ur).Contains (rectangleMomentTValue tl tr ul ur) := by
  exact rectangleMomentT_contains sourceLogI tl tr ul ur
    (sourceLogI_ratio_contains ul ur hul hu)

theorem source_rectangleMomentU_contains (tl tr ul ur : ℚ)
    (htl : 0 < tl) (ht : tl ≤ tr) :
    (rectangleMomentU sourceLogI tl tr ul ur).Contains (rectangleMomentUValue tl tr ul ur) := by
  exact rectangleMomentU_contains sourceLogI tl tr ul ur
    (sourceLogI_ratio_contains tl tr htl ht)

/-- Concrete original-backend base adapter: there is no hsf or hlog input.
Only physical endpoint ordering remains in this numeric query theorem. -/
theorem source_base_contains (tl tr ul ur rl : ℚ)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    (ordinaryRectangleBase sourceSf sourceLogI tl tr ul ur rl).Contains
      ((ImbalancedChen.actualExtendedThirdLowerFactor ((rl/a:ℚ):ℝ) *
        rectangleMassValue tl tr ul ur * 4)/(a:ℝ)) := by
  exact ordinaryRectangleBase_contains sourceSf sourceLogI tl tr ul ur rl _
    (sourceSf_contains_actual _) (sourceLogI_ratio_contains tl tr htl ht)
    (sourceLogI_ratio_contains ul ur hul hu)

theorem source_base_decodeLo_le (tl tr ul ur rl : ℚ)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    ((ordinaryRectangleBase sourceSf sourceLogI tl tr ul ur rl).decodeLo:ℝ) ≤
      ((ImbalancedChen.actualExtendedThirdLowerFactor ((rl/a:ℚ):ℝ) *
        rectangleMassValue tl tr ul ur * 4)/(a:ℝ)) := by
  exact (source_base_contains tl tr ul ur rl htl hul ht hu).1

theorem source_chord_contains (tl tr ul ur : ℚ) (p : Plane)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hden : 0 < (I80.point ((affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1)).lo) :
    (ordinaryRectangleChord sourceSf sourceLogI tl tr ul ur p).Contains
      (ordinaryRectangleChordValue sourceSf tl tr ul ur p) := by
  exact ordinaryRectangleChord_contains sourceSf sourceLogI tl tr ul ur p
    (sourceLogI_ratio_contains tl tr htl ht) (sourceLogI_ratio_contains ul ur hul hu) hden

theorem source_chord_decodeLo_le (tl tr ul ur : ℚ) (p : Plane)
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hwidth : 1/(Q:ℚ) ≤ (affineRange p tl tr ul ur).2 -
      (affineRange p tl tr ul ur).1) :
    ((ordinaryRectangleChord sourceSf sourceLogI tl tr ul ur p).decodeLo:ℝ) ≤
      ordinaryRectangleChordValue sourceSf tl tr ul ur p := by
  exact (source_chord_contains tl tr ul ur p htl hul ht hu
    (P2HistoricI80DivisionSoundness.chord_denominator_guard _ _ hwidth)).1

end

end ImbalancedChen.Certificates.P2HistoricBackendTypeAdapters
