import ImbalancedChen.P2HistoricLogDyadicPowerTail

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

A deliberately coarse uniform bound for the literal Q80 log_point engine.
The rounded odd-power width is at most six ulps, derived from actual state
endpoints, not assumed as a power-state contract. Thirty-two summands then
give total width <=256 ulps; the previously proved literal tail costs at
most 2048 units. Thus atanhBounds width <=2560 ulps. The same proof covers
the actual LOG2 constant, and log_point width is bounded by
2560*(1+abs(sourceShift q)) ulps. This is an operation-width theorem, not a
numerical certificate replay or a claim that this coarse bound closes any
saved-output numerical margin.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogGlobalWidth

noncomputable section
open scoped BigOperators
open P2HistoricQ80DefectLookup P2HistoricLogPointInterpreter
open P2HistoricLogWidthPropagation P2HistoricReducedParameterWidth
open P2HistoricLogDyadicPowerTail

theorem order_of_contains {x : I80} {v : ℝ} (hx : x.Contains v) : x.lo ≤ x.hi := by
  obtain ⟨hl,hu⟩ := (contains_iff _ _).1 hx
  have hr : (x.lo : ℝ) ≤ (x.hi : ℝ) :=
    (div_le_div_iff_of_pos_right Q_real_pos).1 (hl.trans hu)
  exact_mod_cast hr

theorem decode_mono {a b : ℤ} (hab : a ≤ b) : decode a ≤ decode b :=
  div_le_div_of_nonneg_right (by exact_mod_cast hab) Q_real_pos.le

theorem decode_half : decode ((Q : ℤ)/2) = (1/2 : ℝ) := by
  norm_num [decode,Q]

theorem decode_quarter : decode ((Q : ℤ)/4) = (1/4 : ℝ) := by
  norm_num [decode,Q]

theorem parameter_contains_lower {ul uh : ℤ} (ho : ul ≤ uh) :
    (I80.mk ul uh).Contains (decode ul) := by
  apply (contains_iff _ _).2
  exact ⟨le_rfl,decode_mono ho⟩

theorem power_order {ul uh : ℤ} (hl : 0 ≤ ul) (ho : ul ≤ uh) (n : ℕ) :
    (oddLoop (oddSquare ul uh) ul uh n).power.lo ≤
      (oddLoop (oddSquare ul uh) ul uh n).power.hi := by
  obtain ⟨hp,hp0,ht⟩ := oddLoop_invariant (parameter_contains_lower ho) hl n
  exact order_of_contains hp

theorem square_order {ul uh : ℤ} (hl : 0 ≤ ul) (ho : ul ≤ uh) :
    (oddSquare ul uh).lo ≤ (oddSquare ul uh).hi := by
  have hp := parameter_contains_lower ho
  exact order_of_contains (positiveMul_contains hp hp hl hl)

theorem parameter_width_le_two {ul uh : ℤ} (hw : uh-ul ≤ 2) :
    width (I80.mk ul uh) ≤ 2*ulp := by
  have hh : (uh : ℝ)-(ul : ℝ) ≤ 2 := by exact_mod_cast hw
  have hd := div_le_div_of_nonneg_right hh Q_real_pos.le
  simpa only [width,decode,← sub_div,ulp,mul_one_div] using hd

theorem square_width_le_four {ul uh : ℤ}
    (hl : 0 ≤ ul) (ho : ul ≤ uh) (hu : uh ≤ (Q : ℤ)/2) (hw : uh-ul ≤ 2) :
    width (oddSquare ul uh) ≤ 4*ulp := by
  have hcap : decode uh ≤ (1/2 : ℝ) := (decode_mono hu).trans_eq decode_half
  have hcaplo : decode ul ≤ (1/2 : ℝ) := (decode_mono ho).trans hcap
  have hp := positiveMul_width_le (x := I80.mk ul uh) (y := I80.mk ul uh)
    ho ho hcap hcaplo
  have hw' := parameter_width_le_two hw
  change width (oddSquare ul uh) ≤ 4*ulp
  change width (oddSquare ul uh) ≤ (1/2 : ℝ)*width (I80.mk ul uh) +
    (1/2 : ℝ)*width (I80.mk ul uh) + 2*ulp at hp
  linarith

/-- A cap valid for every step, rather than only the first 32 powers. -/
theorem power_hi_half {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) (n : ℕ) :
    (oddLoop (oddSquare ul uh) ul uh n).power.hi ≤ (Q : ℤ)/2 := by
  obtain ⟨hs0,hs⟩ := oddSquare_hi_quarter (ul := ul) hu0 hu
  have hh0 : (0 : ℤ) ≤ (Q : ℤ)/2 := by norm_num [Q]
  have hq : (Q : ℤ)/4 ≤ (Q : ℤ) := by norm_num [Q]
  induction n with
  | zero => exact hu
  | succ n ih =>
      apply ceilDiv_le _ _ _ Q_int_pos
      have hp := mul_le_mul ih hs hs0 hh0
      exact hp.trans (mul_le_mul_of_nonneg_left hq hh0)

/-- The actual rounded power intervals have width <=6 Q80 units.
The square width and both endpoint coefficients are derived above. -/
theorem power_width_le_six {ul uh : ℤ}
    (hl : 0 ≤ ul) (ho : ul ≤ uh) (hu : uh ≤ (Q : ℤ)/2) (hw : uh-ul ≤ 2)
    (n : ℕ) : width (oddLoop (oddSquare ul uh) ul uh n).power ≤ 6*ulp := by
  have hu0 := hl.trans ho
  have hsorder := square_order hl ho
  obtain ⟨hs0,hs⟩ := oddSquare_hi_quarter (ul := ul) hu0 hu
  have hslo : decode (oddSquare ul uh).lo ≤ (1/4 : ℝ) :=
    (decode_mono hsorder).trans ((decode_mono hs).trans_eq decode_quarter)
  have hsw := square_width_le_four hl ho hu hw
  induction n with
  | zero =>
      have hp := parameter_width_le_two hw
      change width (I80.mk ul uh) ≤ 6*ulp
      linarith [ulp_pos]
  | succ n ih =>
      have hporder := power_order hl ho n
      have hphi : decode (oddLoop (oddSquare ul uh) ul uh n).power.hi ≤ (1/2 : ℝ) :=
        (decode_mono (power_hi_half hu0 hu n)).trans_eq decode_half
      have hp := positiveMul_width_le hporder hsorder hphi hslo
      change width (positiveMul (oddLoop (oddSquare ul uh) ul uh n).power
        (oddSquare ul uh)) ≤ 6*ulp
      linarith [ulp_pos]

theorem oddLoop_total_width_le_eight_mul {ul uh : ℤ}
    (hl : 0 ≤ ul) (ho : ul ≤ uh) (hu : uh ≤ (Q : ℤ)/2) (hw : uh-ul ≤ 2)
    (n : ℕ) : width (oddLoop (oddSquare ul uh) ul uh n).total ≤ (n : ℝ)*8*ulp := by
  calc
    width (oddLoop (oddSquare ul uh) ul uh n).total ≤
        ∑ j ∈ Finset.range n,
          (width (oddLoop (oddSquare ul uh) ul uh j).power /
            ((2*j+1 : ℕ) : ℝ) + 2*ulp) := oddLoop_total_width_le _ _ _ _
    _ ≤ ∑ j ∈ Finset.range n, (8*ulp) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp := power_width_le_six hl ho hu hw j
      have hp0 := width_nonneg (power_order hl ho j)
      have hd : (0 : ℝ) < ((2*j+1 : ℕ) : ℝ) := by positivity
      have hd1 : (1 : ℝ) ≤ ((2*j+1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ 2*j+1)
      have hprod := mul_le_mul_of_nonneg_left hd1 hp0
      have hdiv : width (oddLoop (oddSquare ul uh) ul uh j).power /
          ((2*j+1 : ℕ) : ℝ) ≤ width (oddLoop (oddSquare ul uh) ul uh j).power := by
        apply (div_le_iff₀ hd).2
        simpa only [mul_one] using hprod
      linarith
    _ = (n : ℝ)*8*ulp := by simp; ring

theorem tail_decode_le_two_pow_eleven {ul uh : ℤ}
    (hu0 : 0 ≤ uh) (hu : uh ≤ (Q : ℤ)/2) :
    decode (sourceTail ul uh) ≤ 2048*ulp := by
  have hh := sourceTail_le_two_pow_eleven (ul := ul) hu0 hu
  norm_num only [show (2 : ℤ)^11 = 2048 by norm_num] at hh
  have hr : (sourceTail ul uh : ℝ) ≤ (2048 : ℝ) := by exact_mod_cast hh
  have hd := div_le_div_of_nonneg_right hr Q_real_pos.le
  simpa only [decode,ulp,mul_one_div] using hd

/-- Coarse uniform width of the literal rounded atanh32 engine. -/
theorem atanhBounds_width_le {ul uh : ℤ}
    (hl : 0 ≤ ul) (ho : ul ≤ uh) (hu : uh ≤ (Q : ℤ)/2) (hw : uh-ul ≤ 2) :
    width (atanhBounds ul uh) ≤ 2560*ulp := by
  have htotal := oddLoop_total_width_le_eight_mul hl ho hu hw 32
  have htail := tail_decode_le_two_pow_eleven (ul := ul) (hl.trans ho) hu
  rw [atanhBounds_width]
  norm_num only [Nat.cast_ofNat] at htotal
  linarith

theorem actual_reducedLogBounds_width_le {q : ℤ} (hq : 0 < q) :
    width (reducedLogBounds (P2HistoricLogRangeReduction.sourceRL q)
      (P2HistoricLogRangeReduction.sourceRH q)) ≤ 2560*ulp := by
  obtain ⟨hl,ho,hu,hs⟩ := sourceParameter_caps hq
  exact atanhBounds_width_le hl ho hu (sourceParameter_integer_gap hq)

/-- The exact literal LOG2 parameter has the same proven endpoint guards. -/
theorem logTwoBounds_width_le : width logTwoBounds ≤ 2560*ulp := by
  apply atanhBounds_width_le
  all_goals norm_num [Q,ceilDiv]

/-- Uniform for all positive integer queries, with the necessary original
signed-shift amplification retained explicitly. -/
theorem logPoint_width_le {q : ℤ} (hq : 0 < q) :
    width (logPoint q) ≤
      2560*(1+|(P2HistoricLogRangeReduction.sourceShift q : ℝ)|)*ulp := by
  by_cases hqQ : q = (Q : ℤ)
  · rw [logPoint,if_pos hqQ,width_raw]
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) ulp_pos.le
  · rw [logPoint_width_of_ne hqQ]
    have hr := actual_reducedLogBounds_width_le hq
    have htwo := mul_le_mul_of_nonneg_left logTwoBounds_width_le
      (abs_nonneg (P2HistoricLogRangeReduction.sourceShift q : ℝ))
    nlinarith only [hr,htwo]

theorem logPoint_directed_errors_le {q : ℤ} (hq : 0 < q) :
    Real.log ((q : ℝ)/(Q : ℝ)) - decode (logPoint q).lo ≤
      2560*(1+|(P2HistoricLogRangeReduction.sourceShift q : ℝ)|)*ulp ∧
    decode (logPoint q).hi - Real.log ((q : ℝ)/(Q : ℝ)) ≤
      2560*(1+|(P2HistoricLogRangeReduction.sourceShift q : ℝ)|)*ulp := by
  obtain ⟨hl,hu⟩ := logPoint_endpoint_errors hq
  exact ⟨hl.2.trans (logPoint_width_le hq),hu.2.trans (logPoint_width_le hq)⟩

end
end ImbalancedChen.Certificates.P2HistoricLogGlobalWidth
