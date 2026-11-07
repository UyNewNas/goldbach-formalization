import ImbalancedChen.Part3OriginalMediumPoissonRepeatedQ3H4
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reusable scalar multiindex jets for the literal normalized Poisson
argument Ld*v5/(v1*v2*v3). The nonnegative counts a,b,c record
reciprocal differentiation in q,w1,w2. The count e records signed h
derivatives: e=0 leaves h, e=1 removes it, e>=2 is zero. The n1
coordinate is absent and differentiates to zero. Thus the formula
covers every multiindex of total order at most five, and in fact all
orders, without dividing by h.

This is an inner-map calculus leaf. It does not assert the C5 bound for
psiHat0 or for the complete weight W, nor any Abel variation payment.
-/

namespace ImbalancedChen.Part3.OriginalMediumPoissonMultiindexJet

noncomputable section

def hFactor (e : ℕ) (th : ℝ) : ℝ :=
  if e = 0 then th else if e = 1 then 1 else 0

def jet (a b c e : ℕ) (L tq t1 t2 th : ℝ) : ℝ :=
  (-1 : ℝ) ^ (a + b + c) *
    (a.factorial : ℝ) * (b.factorial : ℝ) *
      (c.factorial : ℝ) * L * hFactor e th *
        tq⁻¹ ^ (a + 1) * t1⁻¹ ^ (b + 1) *
          t2⁻¹ ^ (c + 1)

/-- Zeroth jet is exactly the literal Poisson argument. -/
theorem jet_zero (L tq t1 t2 th : ℝ) :
    jet 0 0 0 0 L tq t1 t2 th =
      L * th / (tq * t1 * t2) := by
  simp only [jet, hFactor, pow_zero, one_mul,
    Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
    pow_one, if_pos rfl]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- h derivatives are linear once and vanish thereafter, at h=0 too. -/
theorem hFactor_step (e : ℕ) (th : ℝ) :
    HasDerivAt (fun u => hFactor e u) (hFactor (e + 1) th) th := by
  by_cases he0 : e = 0
  · subst e
    simpa [hFactor] using (hasDerivAt_id th)
  by_cases he1 : e = 1
  · subst e
    simpa [hFactor] using
      (hasDerivAt_const th (1 : ℝ))
  · have he2 : e + 1 ≠ 0 ∧ e + 1 ≠ 1 := by omega
    simpa [hFactor, he0, he1, he2.1, he2.2] using
      (hasDerivAt_const th (0 : ℝ))

/-- A q derivative advances exactly the q multiindex count. -/
theorem jet_q_step (a b c e : ℕ) (L t1 t2 th : ℝ)
    {tq : ℝ} (htq : tq ≠ 0) :
    HasDerivAt (fun u => jet a b c e L u t1 t2 th)
      (jet (a + 1) b c e L tq t1 t2 th) tq := by
  let C : ℝ := (-1 : ℝ) ^ (a + b + c) *
    (a.factorial : ℝ) * (b.factorial : ℝ) *
      (c.factorial : ℝ) * L * hFactor e th *
        t1⁻¹ ^ (b + 1) * t2⁻¹ ^ (c + 1)
  have hi := ((hasDerivAt_inv htq).pow (a + 1)).const_mul C
  convert! hi using 1
  · funext u
    unfold jet C
    ring
  · unfold jet C
    rw [show (a + 1) + b + c = (a + b + c) + 1 by omega]
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

/-- A w1 derivative advances exactly the w1 multiindex count. -/
theorem jet_w1_step (a b c e : ℕ) (L tq t2 th : ℝ)
    {t1 : ℝ} (ht1 : t1 ≠ 0) :
    HasDerivAt (fun u => jet a b c e L tq u t2 th)
      (jet a (b + 1) c e L tq t1 t2 th) t1 := by
  let C : ℝ := (-1 : ℝ) ^ (a + b + c) *
    (a.factorial : ℝ) * (b.factorial : ℝ) *
      (c.factorial : ℝ) * L * hFactor e th *
        tq⁻¹ ^ (a + 1) * t2⁻¹ ^ (c + 1)
  have hi := ((hasDerivAt_inv ht1).pow (b + 1)).const_mul C
  convert! hi using 1
  · funext u
    unfold jet C
    ring
  · unfold jet C
    rw [show a + (b + 1) + c = (a + b + c) + 1 by omega]
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

/-- A w2 derivative advances exactly the w2 multiindex count. -/
theorem jet_w2_step (a b c e : ℕ) (L tq t1 th : ℝ)
    {t2 : ℝ} (ht2 : t2 ≠ 0) :
    HasDerivAt (fun u => jet a b c e L tq t1 u th)
      (jet a b (c + 1) e L tq t1 t2 th) t2 := by
  let C : ℝ := (-1 : ℝ) ^ (a + b + c) *
    (a.factorial : ℝ) * (b.factorial : ℝ) *
      (c.factorial : ℝ) * L * hFactor e th *
        tq⁻¹ ^ (a + 1) * t1⁻¹ ^ (b + 1)
  have hi := ((hasDerivAt_inv ht2).pow (c + 1)).const_mul C
  convert! hi using 1
  · funext u
    unfold jet C
    ring
  · unfold jet C
    rw [show a + b + (c + 1) = (a + b + c) + 1 by omega]
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

/-- The h step is valid even at h=0 and kills e>=1 jets. -/
theorem jet_h_step (a b c e : ℕ)
    (L tq t1 t2 th : ℝ) :
    HasDerivAt (fun u => jet a b c e L tq t1 t2 u)
      (jet a b c (e + 1) L tq t1 t2 th) th := by
  let C : ℝ := (-1 : ℝ) ^ (a + b + c) *
    (a.factorial : ℝ) * (b.factorial : ℝ) *
      (c.factorial : ℝ) * L *
        tq⁻¹ ^ (a + 1) * t1⁻¹ ^ (b + 1) *
          t2⁻¹ ^ (c + 1)
  have hi := (hFactor_step e th).const_mul C
  convert! hi using 1
  · funext u
    unfold jet C
    ring
  · unfold jet C
    ring

/-- n1 does not occur in the Poisson Fourier argument. -/
theorem jet_n1_zero (a b c e : ℕ)
    (L tq t1 t2 th tn : ℝ) :
    HasDerivAt
      (fun _u : ℝ => jet a b c e L tq t1 t2 th)
      0 tn :=
  hasDerivAt_const tn _

/-- h-factor boundedness on either fixed signed normalized interval. -/
theorem hFactor_bound (e : ℕ) (th : ℝ) (hh : |th| ≤ 1) :
    |hFactor e th| ≤ 1 := by
  by_cases he0 : e = 0
  · simpa [hFactor, he0] using hh
  by_cases he1 : e = 1
  · simp [hFactor, he0, he1]
  · simp [hFactor, he0, he1]

/-- The bound of every inner jet on the physical positive normalized
box; its factorials are absolute constants when a+b+c+e <= 5. -/
theorem jet_box_bound (a b c e : ℕ)
    (L tq t1 t2 th : ℝ)
    (hq : 1 ≤ tq) (h1 : 1 ≤ t1) (h2 : 1 ≤ t2)
    (hh : |th| ≤ 1) :
    |jet a b c e L tq t1 t2 th| ≤
      (a.factorial : ℝ) * (b.factorial : ℝ) *
        (c.factorial : ℝ) * |L| := by
  have hqpos : 0 < tq := lt_of_lt_of_le zero_lt_one hq
  have h1pos : 0 < t1 := lt_of_lt_of_le zero_lt_one h1
  have h2pos : 0 < t2 := lt_of_lt_of_le zero_lt_one h2
  have hqinv : |tq⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_pos hqpos]
    exact (div_le_iff₀ hqpos).2 (by simpa using hq)
  have h1inv : |t1⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_pos h1pos]
    exact (div_le_iff₀ h1pos).2 (by simpa using h1)
  have h2inv : |t2⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_pos h2pos]
    exact (div_le_iff₀ h2pos).2 (by simpa using h2)
  have hhf := hFactor_bound e th hh
  calc
    |jet a b c e L tq t1 t2 th| =
        (a.factorial : ℝ) * (b.factorial : ℝ) *
          (c.factorial : ℝ) * |L| * |hFactor e th| *
            |tq⁻¹| ^ (a + 1) * |t1⁻¹| ^ (b + 1) *
              |t2⁻¹| ^ (c + 1) := by
      simp [jet, abs_mul, abs_pow, Nat.cast_nonneg]
      ring
    _ ≤ (a.factorial : ℝ) * (b.factorial : ℝ) *
          (c.factorial : ℝ) * |L| * 1 *
            1 ^ (a + 1) * 1 ^ (b + 1) *
              1 ^ (c + 1) := by
      gcongr
    _ = (a.factorial : ℝ) * (b.factorial : ℝ) *
          (c.factorial : ℝ) * |L| := by ring

end

end ImbalancedChen.Part3.OriginalMediumPoissonMultiindexJet
