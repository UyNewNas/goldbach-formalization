import ImbalancedChen.P5ActualInnerPerLabelGamma
import ImbalancedChen.P5OriginalOrdinaryWholeAtomMonomials

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual fixed common raw beta's NONZERO value supplies its real
endpoint bound. Attaching that same e only to the third factor costs
2*epsilon in the first two original monomials and 39*epsilon/16 in the
third. This exact cost is proved before any capacity licence is claimed.
No final monomial, beta support cardinality or distribution estimate is
assumed. These are numeric interfaces for a fixed SAME group assignment;
the actual marked/common-colour source port remains independent.
-/

namespace ImbalancedChen.P5Z.ActualSmallBetaMonomialCost
noncomputable section
open Classical
open ActualAll16UnrestrictedResidualConvolution

theorem actual_raw_beta_endpoint {N cap r e : ℕ} {w B : ℝ}
    (he : rawBetaWeight N cap r w B e ≠ 0) : 0 < e ∧ (e : ℝ) < B := by
  unfold rawBetaWeight at he
  split_ifs at he with hsign
  · have h := actualSmallRosserPlus_active he
    exact ⟨Nat.pos_of_ne_zero h.2.2.1, h.2.1⟩
  · have h := actualSmallRosserMinus_active he
    exact ⟨Nat.pos_of_ne_zero h.2.2.1, h.2.1⟩

/-- Exact exponent payment for beta in the THIRD original factor.
Every term uses the same A,a,b,c; neither a new factorization nor a
modified local complete scale is introduced. -/
theorem third_factor_beta_cost {x epsilon alpha A a b c e eta1 eta2 eta3 : ℝ}
    (hx : 1 < x) (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (heupper : e ≤ x ^ epsilon)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - eta1))
    (h2 : x ^ (7 * alpha / 32) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - eta2))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - eta3)) :
    A ^ 2 * b * (e * c) ^ 2 ≤ x ^ (1 - eta1 + 2 * epsilon) ∧
      x ^ (7 * alpha / 32) * A * a * b ^ 5 * (e * c) ^ 2 ≤ x ^ (2 - eta2 + 2 * epsilon) ∧
      (A * (e * c) / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * (e * c) ^ 2 ≤
        x ^ (2 - eta3 + (39 / 16 : ℝ) * epsilon) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have he2 : e ^ 2 ≤ x ^ (2 * epsilon) := by
    have h := pow_le_pow_left₀ he.le heupper 2
    simpa only [← Real.rpow_mul_natCast hx0.le, Nat.cast_ofNat, mul_comm epsilon 2] using h
  have he39 : e ^ (39 / 16 : ℝ) ≤ x ^ ((39 / 16 : ℝ) * epsilon) := by
    have h := Real.rpow_le_rpow he.le heupper (by norm_num : (0 : ℝ) ≤ 39 / 16)
    simpa only [← Real.rpow_mul hx0.le, mul_comm epsilon (39 / 16 : ℝ)] using h
  have hsplit : e ^ (39 / 16 : ℝ) = e ^ (7 / 16 : ℝ) * e ^ 2 := by
    rw [show (39 / 16 : ℝ) = 7 / 16 + 2 by norm_num, Real.rpow_add he]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = e ^ 2 * (A ^ 2 * b * c ^ 2) := by ring
      _ ≤ x ^ (2 * epsilon) * x ^ (1 - eta1) :=
        mul_le_mul he2 h1 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1 <;> ring
  · calc
      _ = e ^ 2 * (x ^ (7 * alpha / 32) * A * a * b ^ 5 * c ^ 2) := by ring
      _ ≤ x ^ (2 * epsilon) * x ^ (2 - eta2) :=
        mul_le_mul he2 h2 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1 <;> ring
  · have hfactor :
        (A * (e * c) / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * (e * c) ^ 2 =
        e ^ (39 / 16 : ℝ) * ((A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2) := by
      rw [show A * (e * c) / b = e * (A * c / b) by ring,
        Real.mul_rpow he.le (by positivity), hsplit]
      ring
    rw [hfactor]
    calc
      _ ≤ x ^ ((39 / 16 : ℝ) * epsilon) * x ^ (2 - eta3) :=
        mul_le_mul he39 h3 (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1 <;> ring

/-- Original ordinary15 endpoint margins pay the ACTUAL common beta
when epsilon<=kappa/16. This consumes the same original three monomials,
with their actual spectral alpha=1+3kappa and third-factor assignment. -/
theorem ordinary_beta_margins {x kappa epsilon A a b c e : ℝ}
    (hx : 1 < x) (hk : 0 < kappa) (heps : epsilon ≤ kappa / 16)
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (heupper : e ≤ x ^ epsilon)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 3 * kappa / 2))
    (h2 : x ^ (7 * (1 + 3 * kappa) / 32) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * kappa / 2))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - kappa)) :
    A ^ 2 * b * (e * c) ^ 2 ≤ x ^ (1 - kappa) ∧
      x ^ (7 * (1 + 3 * kappa) / 32) * A * a * b ^ 5 * (e * c) ^ 2 ≤ x ^ (2 - kappa) ∧
      (A * (e * c) / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * (e * c) ^ 2 ≤ x ^ (2 - kappa / 2) := by
  obtain ⟨h1', h2', h3'⟩ := third_factor_beta_cost hx hA ha hb hc he heupper h1 h2 h3
  exact ⟨h1'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
    h2'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
    h3'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))⟩

/-- Genuine W success/overflow margins retain a fixed power after the
same beta attachment. This is a numeric payment, not a W source map. -/
theorem W_beta_margins {x delta epsilon alpha A a b c e : ℝ}
    (hx : 1 < x) (hd : 0 < delta) (heps : epsilon ≤ delta / 4)
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (heupper : e ≤ x ^ epsilon)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 4 * delta))
    (h2 : x ^ (7 * alpha / 32) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 4 * delta))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 39 * delta / 8)) :
    A ^ 2 * b * (e * c) ^ 2 ≤ x ^ (1 - 3 * delta) ∧
      x ^ (7 * alpha / 32) * A * a * b ^ 5 * (e * c) ^ 2 ≤ x ^ (2 - 3 * delta) ∧
      (A * (e * c) / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * (e * c) ^ 2 ≤ x ^ (2 - 4 * delta) := by
  obtain ⟨h1', h2', h3'⟩ := third_factor_beta_cost hx hA ha hb hc he heupper h1 h2 h3
  exact ⟨h1'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
    h2'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
    h3'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))⟩

end
end ImbalancedChen.P5Z.ActualSmallBetaMonomialCost
