import ImbalancedChen.VariableEnvelopeConsequences

/-! Exact boundary checks for the literal gated definition. -/

open ImbalancedChen.VariableEnvelope

-- A failed w gate really returns zero, although B is positive.
example : w mu mu mu = 0 ∧ 0 < B mu := by
  norm_num [w, wInner, psi, A, B, mu, cap]

-- Equality passes the original gate, as specified by psi.
example : psi (153 / 256) (153 / 256) = (153 / 256 : ℝ) := by
  norm_num [psi]

-- The added closed-domain face is included in the identity.
example : original mu mu 0 = six mu mu 0 := by
  apply original_eq_six
  norm_num [Ordered, mu]

-- The original, fully expanded formula has the claimed sharp endpoint.
example : original mu mu mu - 3 * mu = (3 / 256 : ℝ) := by
  norm_num [original, w, wInner, psi, v, A, B, C, mu, cap]

-- A winning pair attains the lower bound at a strictly positive ordered point.
example : Ordered mu (mu / 2) (mu / 2) ∧
    v mu ≤ v (mu / 2 + mu / 2) ∧
    v (mu / 2 + mu / 2) - (2 * mu + mu / 2 + mu / 2) = (3 / 256 : ℝ) := by
  norm_num [Ordered, v, A, C, mu]

-- The cutoff is evaluated in exact rational arithmetic.
example : B (7 / 4000) = (597 / 1000 : ℝ) := by
  norm_num [B, cap]

-- The order restriction is substantive: the ungated formula can fail outside it.
example : original 0 1 0 = (1 / 2 : ℝ) ∧ six 0 1 0 = cap ∧
    original 0 1 0 ≠ six 0 1 0 := by
  norm_num [original, six, w, wInner, psi, v, A, B, C, cap]
