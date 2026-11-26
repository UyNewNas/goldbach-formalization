import ImbalancedChen.Certificates.P2OriginalLog96

open ImbalancedChen.Certificates.P2OriginalLog96

example (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    ((logInterval q).1 : ℝ) / (2 : ℝ)^160 ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ ((logInterval q).2 : ℝ) / (2 : ℝ)^160 := by
  simpa only [outputScale, Int.cast_pow, Int.cast_ofNat] using
    logInterval_contains q h1 h2

example (q : ℚ) : logInterval q = sourceLogInterval q :=
  logInterval_eq_source q

example : logInterval 1 = (0, 1) := by
  norm_num [logInterval, ImbalancedChen.Certificates.logParameter, workScale,
    outputShift, positiveMul, upperDiv, loop, start, step, divNat, Bounds.add, tail_eq_one]
  decide

#check @logInterval_contains
#check @logInterval_eq_source
#print axioms logInterval_contains
#print axioms logInterval_eq_source
