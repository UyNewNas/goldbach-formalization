import ImbalancedChen.P2HistoricLogWidthPropagation

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The literal historical log_point parameter uses crossed denominators,
not exact evaluation of the Mobius transform at either rounded endpoint.
Here its endpoint caps and width are derived from the actual bit_length
range-reduction theorem. No parameter cap or final log error is assumed.
Every q>0 has parameter endpoints in [0,Q/2], their square upper endpoint
is at most Q/4, and their integer gap is at most two. These are source-state
inputs for the still separate atanh32 power decay and sharp tail estimate.
-/

namespace ImbalancedChen.Certificates.P2HistoricReducedParameterWidth

noncomputable section
open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter
open P2HistoricLogWidthPropagation

def parameterLowerExact (rl rh : ℤ) : ℝ :=
  (decode rl-1)/(decode rh+1)

def parameterUpperExact (rl rh : ℤ) : ℝ :=
  (decode rh-1)/(decode rl+1)

/-- Width of the crossed ratios is at most the normalized input width.
The factor left over after clearing denominators is (H-L)*(L*H+1). -/
theorem crossedRatio_width {L H : ℝ} (hL : 1 ≤ L) (ho : L ≤ H) :
    (H-1)/(L+1) - (L-1)/(H+1) ≤ H-L := by
  have hdL : 0 < L+1 := by linarith
  have hdH : 0 < H+1 := by linarith
  have hden : 0 < (L+1)*(H+1) := mul_pos hdL hdH
  have he : (H-1)/(L+1) - (L-1)/(H+1) =
      (H-L)*(H+L)/((L+1)*(H+1)) := by
    field_simp [hdL.ne',hdH.ne']
    ring
  rw [he]
  apply (div_le_iff₀ hden).2
  have hLH : 0 ≤ L*H+1 := by
    have hL0 : 0 ≤ L := by linarith
    have hH0 : 0 ≤ H := by linarith
    positivity
  have hh := mul_nonneg (sub_nonneg.mpr ho) hLH
  nlinarith only [hh]

theorem parameter_lower_error {rl rh : ℤ}
    (hd : 0 < rh+(Q : ℤ)) :
    0 ≤ parameterLowerExact rl rh - decode (reducedParameter rl rh).lo ∧
      parameterLowerExact rl rh - decode (reducedParameter rl rh).lo < ulp := by
  have hh := ediv_decode_error ((rl-(Q : ℤ))*(Q : ℤ)) (rh+(Q : ℤ)) hd
  have hdiff : (rh : ℝ)+(Q : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((((rl-(Q : ℤ))*(Q : ℤ) : ℤ) : ℝ) /
      ((rh+(Q : ℤ) : ℤ) : ℝ))/(Q : ℝ) = parameterLowerExact rl rh := by
    unfold parameterLowerExact decode
    push_cast
    field_simp [Q_real_pos.ne',hdiff]
    ring
  rw [he] at hh
  exact hh

theorem parameter_upper_error {rl rh : ℤ}
    (hd : 0 < rl+(Q : ℤ)) :
    0 ≤ decode (reducedParameter rl rh).hi - parameterUpperExact rl rh ∧
      decode (reducedParameter rl rh).hi - parameterUpperExact rl rh < ulp := by
  have hh := ceilDiv_decode_error ((rh-(Q : ℤ))*(Q : ℤ)) (rl+(Q : ℤ)) hd
  have hdiff : (rl : ℝ)+(Q : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : ((((rh-(Q : ℤ))*(Q : ℤ) : ℤ) : ℝ) /
      ((rl+(Q : ℤ) : ℤ) : ℝ))/(Q : ℝ) = parameterUpperExact rl rh := by
    unfold parameterUpperExact decode
    push_cast
    field_simp [Q_real_pos.ne',hdiff]
    ring
  rw [he] at hh
  exact hh

/-- Uniform width of the actual crossed-and-rounded parameter. -/
theorem reducedParameter_width_lt {rl rh : ℤ}
    (hrl : (Q : ℤ) ≤ rl) (ho : rl ≤ rh) (hw : rh ≤ rl+1) :
    width (reducedParameter rl rh) < 3*ulp := by
  have hdL : 0 < rl+(Q : ℤ) := by have hh := Q_int_pos; omega
  have hdH : 0 < rh+(Q : ℤ) := by have hh := Q_int_pos; omega
  have hL : 1 ≤ decode rl := by
    apply (le_div_iff₀ Q_real_pos).2
    simpa using (show (Q : ℝ) ≤ (rl : ℝ) by exact_mod_cast hrl)
  have hord : decode rl ≤ decode rh :=
    div_le_div_of_nonneg_right (by exact_mod_cast ho) Q_real_pos.le
  have hwidth : decode rh - decode rl ≤ ulp := by
    have hi : (rh : ℝ)-(rl : ℝ) ≤ 1 := by exact_mod_cast (by omega : rh-rl ≤ 1)
    simpa only [decode, ulp, ← sub_div] using
      (div_le_div_of_nonneg_right hi Q_real_pos.le)
  have hcross := crossedRatio_width hL hord
  have hl := (parameter_lower_error hdH).2
  have hu := (parameter_upper_error hdL).2
  dsimp only [parameterLowerExact, parameterUpperExact] at hl hu
  dsimp only [width]
  linarith

def sourceParameter (q : ℤ) : I80 :=
  reducedParameter (P2HistoricLogRangeReduction.sourceRL q)
    (P2HistoricLogRangeReduction.sourceRH q)

/-- This has no range or cap hypothesis beyond the original q>0 assertion. -/
theorem sourceParameter_width_lt {q : ℤ} (hq : 0 < q) :
    width (sourceParameter q) < 3*ulp := by
  obtain ⟨hl,ho,hu⟩ := P2HistoricLogRangeReduction.source_endpoint_guards hq
  exact reducedParameter_width_lt hl ho
    (P2HistoricLogRangeReduction.source_endpoint_width q)

theorem sourceParameter_contains {q : ℤ} (hq : 0 < q) :
    (sourceParameter q).Contains
      (((P2HistoricLogRangeReduction.exactReduced q : ℝ)-1) /
        ((P2HistoricLogRangeReduction.exactReduced q : ℝ)+1)) := by
  have hr : (I80.mk (P2HistoricLogRangeReduction.sourceRL q)
      (P2HistoricLogRangeReduction.sourceRH q)).Contains
      (P2HistoricLogRangeReduction.exactReduced q : ℝ) := by
    apply (contains_iff _ _).2
    exact P2HistoricLogRangeReduction.source_reduced_contains_real q
  exact reducedParameter_contains hr
    (P2HistoricLogRangeReduction.source_endpoint_guards hq).1

theorem sourceParameter_integer_gap {q : ℤ} (hq : 0 < q) :
    (sourceParameter q).hi - (sourceParameter q).lo ≤ 2 := by
  have hh := sourceParameter_width_lt hq
  have he : width (sourceParameter q) =
      (((sourceParameter q).hi-(sourceParameter q).lo : ℤ) : ℝ)/(Q : ℝ) := by
    simp only [width, decode, Int.cast_sub, sub_div]
  rw [he] at hh
  have hthree : 3*ulp = (3 : ℝ)/(Q : ℝ) := by unfold ulp; ring
  rw [hthree] at hh
  have hg := (div_lt_div_iff_of_pos_right Q_real_pos).1 hh
  have hgI : (sourceParameter q).hi-(sourceParameter q).lo < 3 := by exact_mod_cast hg
  omega

/-- The half/quarter caps are proved directly from the same original
integer endpoint guards, retaining both historical directed roundings. -/
theorem sourceParameter_caps {q : ℤ} (hq : 0 < q) :
    0 ≤ (sourceParameter q).lo ∧
      (sourceParameter q).lo ≤ (sourceParameter q).hi ∧
      (sourceParameter q).hi ≤ (Q : ℤ)/2 ∧
      (oddSquare (sourceParameter q).lo (sourceParameter q).hi).hi ≤ (Q : ℤ)/4 := by
  let rl := P2HistoricLogRangeReduction.sourceRL q
  let rh := P2HistoricLogRangeReduction.sourceRH q
  obtain ⟨hrl,ho,hrh⟩ := P2HistoricLogRangeReduction.source_endpoint_guards hq
  have hd : 0 < rl+(Q : ℤ) := by have hh := Q_int_pos; omega
  have hdh : 0 < rh+(Q : ℤ) := by have hh := Q_int_pos; omega
  let half : ℤ := (Q : ℤ)/2
  let quarter : ℤ := (Q : ℤ)/4
  have hh0 : 0 ≤ half := by norm_num [half,Q]
  have hhQ : 2*half = (Q : ℤ) := by norm_num [half,Q]
  have hqQ : quarter*(Q : ℤ) = half^2 := by norm_num [quarter,half,Q]
  have hpl : 0 ≤ (sourceParameter q).lo := by
    change 0 ≤ (rl-(Q : ℤ))*(Q : ℤ)/(rh+(Q : ℤ))
    exact Int.ediv_nonneg (mul_nonneg (by omega) Q_int_pos.le) hdh.le
  have hph0 : 0 ≤ (sourceParameter q).hi := by
    change 0 ≤ ceilDiv ((rh-(Q : ℤ))*(Q : ℤ)) (rl+(Q : ℤ))
    exact ceilDiv_nonnegative (mul_nonneg (by omega) Q_int_pos.le) hd
  have hph : (sourceParameter q).hi ≤ half := by
    apply ceilDiv_le _ _ _ hd
    have h1 := mul_le_mul_of_nonneg_right
      (show rh-(Q : ℤ) ≤ (Q : ℤ) by omega) Q_int_pos.le
    have h2 := mul_le_mul_of_nonneg_left
      (show 2*(Q : ℤ) ≤ rl+(Q : ℤ) by omega) hh0
    nlinarith
  have hsquare :
      (oddSquare (sourceParameter q).lo (sourceParameter q).hi).hi ≤ quarter := by
    apply ceilDiv_le _ _ _ Q_int_pos
    have hh := mul_nonneg hph0 (sub_nonneg.mpr hph)
    nlinarith
  have hp := (contains_iff _ _).1 (sourceParameter_contains hq)
  have horderR : ((sourceParameter q).lo : ℝ) ≤ ((sourceParameter q).hi : ℝ) :=
    (div_le_div_iff_of_pos_right Q_real_pos).1 (hp.1.trans hp.2)
  have horder : (sourceParameter q).lo ≤ (sourceParameter q).hi := by exact_mod_cast horderR
  exact ⟨hpl,horder,hph,hsquare⟩

end
end ImbalancedChen.Certificates.P2HistoricReducedParameterWidth
