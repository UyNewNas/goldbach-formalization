import ImbalancedChen.Part3MediumPrimitiveShiuFiniteCover
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

-- Reused WindowGate caller; current acceptance is recorded with p31-shiu-windows-20261126.
-- Historical source label: UNCOMPILED_ZERO_CREDIT. Paper section 4, lines 145-153.
-- The sole analytic hypothesis below is a natural-endpoint specialization
-- of primitive Shiu's ORIGINAL x,H,k,b theorem for F=tau^C. It has
-- constants/threshold before all four varying parameters. It is not (10),
-- a translated/nonprimitive progression theorem, or a medium-error bound.

namespace ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumPrimitiveShiuCover20261028

-- Shiu 1980, Theorem 1, as restated in Wright arXiv:2508.17217v1,
-- Theorem 1.1. F(n)=tau(n)^C has F(p)=2^C. The displayed exponential
-- remains intact rather than assuming the desired final log bound.
structure PrimitiveShiuTauBoundary (C : ℕ) (α κ : ℝ) where
  A : ℝ
  X0 : ℝ
  A_pos : 0 < A
  X0_lower : 2 ≤ X0
  alpha_pos : 0 < α
  alpha_half : α < 1 / 2
  kappa_pos : 0 < κ
  kappa_half : κ < 1 / 2
  bound : ∀ X H q b : ℕ, X0 ≤ (X : ℝ) → 0 < H → 0 < q →
      (X : ℝ) ^ κ ≤ (H : ℝ) → H ≤ X →
      (q : ℝ) < (H : ℝ) ^ (1 - α) → q.Coprime b →
      (∑ n ∈ Ico X (X + H),
        if Nat.ModEq q n b then ((n.divisors.card : ℝ) ^ C) else 0) ≤
        A * (H : ℝ) / (q.totient : ℝ) / Real.log X *
          Real.exp ((2 : ℝ) ^ C *
            ∑ p ∈ (range (X + 1)).filter (fun p => p.Prime ∧ ¬p ∣ q),
              (1 : ℝ) / p)

-- A genuine instantiation on one constructed window. The finite cover
-- supplies X=windowStart and H=windowLength; all Shiu inequalities must
-- be proved separately for active windows before this theorem is used.
theorem primitiveShiu_on_window {C : ℕ} {α κ : ℝ}
    (hShiu : PrimitiveShiuTauBoundary C α κ)
    (A T j k q b : ℕ)
    (hX0 : hShiu.X0 ≤ (windowStart A T j k : ℝ))
    (hH : 0 < windowLength T j)
    (hq : 0 < q)
    (hpower : (windowStart A T j k : ℝ) ^ κ ≤ windowLength T j)
    (hshort : windowLength T j ≤ windowStart A T j k)
    (hmod : (q : ℝ) < (windowLength T j : ℝ) ^ (1 - α))
    (hcop : q.Coprime b) :
    (∑ n ∈ window A T j k,
        if Nat.ModEq q n b then ((n.divisors.card : ℝ) ^ C) else 0) ≤
        hShiu.A * (windowLength T j : ℝ) / (q.totient : ℝ) /
          Real.log (windowStart A T j k) *
          Real.exp ((2 : ℝ) ^ C *
            ∑ p ∈ (range (windowStart A T j k + 1)).filter
              (fun p => p.Prime ∧ ¬p ∣ q), (1 : ℝ) / p) := by
  change (∑ n ∈ Ico (windowStart A T j k)
    (windowStart A T j k + windowLength T j),
      if Nat.ModEq q n b then ((n.divisors.card : ℝ) ^ C) else 0) ≤ _
  exact hShiu.bound _ _ q b hX0 hH hq hpower hshort hmod hcop

-- The original condition f<=L*x^-delta and the exact gcd factorization
-- f=g*f' give the quotient length T=L/g >= f'*x^delta.
theorem quotient_length_lower
    {x δ L f g fp : ℝ} (hx : 1 ≤ x) (hg : 0 < g)
    (hfactor : f = g * fp) (hf : f ≤ L * x ^ (-δ)) :
    fp * x ^ δ ≤ L / g := by
  have hxpos : 0 < x := by linarith
  have hxd : 0 < x ^ δ := Real.rpow_pos_of_pos hxpos _
  have hscaled : f * x ^ δ ≤ L := by
    calc
      f * x ^ δ ≤ (L * x ^ (-δ)) * x ^ δ :=
        mul_le_mul_of_nonneg_right hf hxd.le
      _ = L := by
        rw [Real.rpow_neg hxpos.le]
        field_simp [hxd.ne']
  apply (le_div_iff₀ hg).mpr
  rw [hfactor] at hscaled
  nlinarith [hscaled]

theorem ceiling_quotient_length_two_sided {Q : ℝ} (hQ : 1 ≤ Q) :
    Q ≤ (Nat.ceil Q : ℝ) ∧ (Nat.ceil Q : ℝ) ≤ 2 * Q := by
  have hQ0 : 0 ≤ Q := by linarith
  constructor
  · exact Nat.le_ceil Q
  · have h := Nat.ceil_lt_add_one hQ0
    linarith

-- Every finite cover window is polynomially located, including a far
-- translated short branch. Enlarging the fixed exponent from K to K+1
-- absorbs the harmless factor eight without changing the paper's range.
theorem window_polynomial_location
    {x K : ℝ} {A B T j k : ℕ}
    (hx : 8 ≤ x) (_hK : 0 ≤ K)
    (hAB : A ≤ B) (hB0 : B ≠ 0)
    (hj : j < Nat.log 2 B + 1) (hk : k < 8)
    (hB : (B : ℝ) ≤ x ^ K) :
    (windowStart A T j k : ℝ) ≤ x ^ (K + 1) := by
  have hxpos : 0 < x := by linarith
  have hstart : (windowStart A T j k : ℝ) ≤ 8 * B := by
    exact_mod_cast windowStart_le_eight_B A B T j k hAB hB0 hj hk
  calc
    (windowStart A T j k : ℝ) ≤ 8 * B := hstart
    _ ≤ 8 * x ^ K := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ ≤ x * x ^ K :=
      mul_le_mul_of_nonneg_right (by linarith : (8 : ℝ) ≤ x)
        (Real.rpow_nonneg (by linarith : 0 ≤ x) K)
    _ = x ^ (K + 1) := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
      ring

theorem active_window_scale_lower
    {x δ L f g fp : ℝ} {T j n : ℕ}
    (hx : 1 ≤ x) (hδ : 0 ≤ δ) (hg : 0 < g)
    (hfp : 0 < fp) (hfactor : f = g * fp)
    (hf : f ≤ L * x ^ (-δ))
    (hTceil : L / g ≤ (T : ℝ))
    (hpoint : fp * x ^ (δ / 2) ≤ (n : ℝ))
    (hshell : n < 2 * shellBase j) :
    fp * x ^ (δ / 2) / 16 ≤ (windowLength T j : ℝ) := by
  have hquot := quotient_length_lower hx hg hfactor hf
  have hpow : x ^ (δ / 2) ≤ x ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hT : fp * x ^ (δ / 2) / 16 ≤ (T : ℝ) := by
    have hfpow := mul_le_mul_of_nonneg_left hpow hfp.le
    linarith
  exact active_window_length_lower T j n
    (fp * x ^ (δ / 2)) hT hpoint hshell

-- A parameter gate for x above an explicit fixed margin. The hypotheses
-- H>=f'*x^(delta/2)/16 and X<=x^P are established by the finite dyadic
-- cover and f<=L*x^-delta; no analytic estimate enters this calculation.
theorem window_power_and_modulus_gate
    {x δ P fp X H : ℝ}
    (hx : 1 ≤ x) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hP : 1 ≤ P) (hfp : 1 ≤ fp) (hX : 0 < X)
    (hHX : H ≤ X) (hHlower : fp * x ^ (δ / 2) / 16 ≤ H)
    (hXupper : X ≤ x ^ P)
    (hmargin : 16 < x ^ (7 * δ / 16)) :
    let α := δ / (16 * P)
    0 < α ∧ α < 1 / 2 ∧ X ^ α ≤ H ∧ fp < H ^ (1 - α) := by
  let α := δ / (16 * P)
  change 0 < α ∧ α < 1 / 2 ∧ X ^ α ≤ H ∧ fp < H ^ (1 - α)
  have hden : 0 < 16 * P := by positivity
  have hαpos : 0 < α := div_pos hδ hden
  have hαhalf : α < 1 / 2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hXα : X ^ α ≤ x ^ (δ / 16) := by
    have h := Real.rpow_le_rpow hX.le hXupper hαpos.le
    have hpower : P * α = δ / 16 := by
      dsimp [α]
      field_simp
    simpa only [← Real.rpow_mul hx0, hpower] using h
  have hApos : 0 < x ^ (δ / 16) := Real.rpow_pos_of_pos hxpos _
  have hBpos : 0 < x ^ (7 * δ / 16) := Real.rpow_pos_of_pos hxpos _
  have hsplit : x ^ (δ / 2) =
      x ^ (δ / 16) * x ^ (7 * δ / 16) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hHbound : fp *
      (x ^ (δ / 16) * x ^ (7 * δ / 16)) / 16 ≤ H := by
    simpa only [hsplit] using hHlower
  have hfpApos : 0 < fp * x ^ (δ / 16) :=
    mul_pos (by linarith) hApos
  have hlarge : fp * x ^ (δ / 16) <
      fp * (x ^ (δ / 16) * x ^ (7 * δ / 16)) / 16 := by
    have hmul := mul_lt_mul_of_pos_left hmargin hfpApos
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith
  have hHpos : 0 < H := by linarith
  have hHα : H ^ α ≤ x ^ (δ / 16) :=
    (Real.rpow_le_rpow hHpos.le hHX hαpos.le).trans hXα
  have hXH : X ^ α ≤ H := by
    have hAfp : x ^ (δ / 16) ≤ fp * x ^ (δ / 16) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hfp hApos.le
    exact hXα.trans (hAfp.trans (hlarge.le.trans hHbound))
  have hfpH : fp * H ^ α < H := by
    calc
      fp * H ^ α ≤ fp * x ^ (δ / 16) :=
        mul_le_mul_of_nonneg_left hHα (by linarith)
      _ < fp * (x ^ (δ / 16) * x ^ (7 * δ / 16)) / 16 := hlarge
      _ ≤ H := hHbound
  refine ⟨hαpos, hαhalf, hXH, ?_⟩
  have hHαpos : 0 < H ^ α := Real.rpow_pos_of_pos hHpos _
  rw [Real.rpow_sub hHpos, Real.rpow_one]
  exact (lt_div_iff₀ hHαpos).mpr hfpH

-- The combined active-window check. All variable window data come from
-- the finite cover; f=g*f' is the exact Phase4 gcd factorization. The
-- two fixed x margins are eventual conditions, independent of j,k,n.
theorem active_window_shiu_conditions
    {x δ K L f g fp X0 : ℝ} {A B T j k n : ℕ}
    (hx : 8 ≤ x) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hK : 0 ≤ K) (hfp : 1 ≤ fp) (hg : 0 < g)
    (hfactor : f = g * fp) (hf : f ≤ L * x ^ (-δ))
    (hTceil : L / g ≤ (T : ℝ)) (hTpos : 0 < T)
    (hAB : A ≤ B) (hB0 : B ≠ 0)
    (hj : j < Nat.log 2 B + 1) (hk : k < 8)
    (hB : (B : ℝ) ≤ x ^ K)
    (hpoint : fp * x ^ (δ / 2) ≤ (n : ℝ))
    (hshell : n < 2 * shellBase j)
    (hmargin : 16 < x ^ (7 * δ / 16))
    (hthreshold : X0 ≤ fp * x ^ (δ / 2) / 2) :
    let α := δ / (16 * (K + 1))
    0 < α ∧ α < 1 / 2 ∧
      X0 ≤ (windowStart A T j k : ℝ) ∧
      (windowStart A T j k : ℝ) ^ α ≤ windowLength T j ∧
      windowLength T j ≤ windowStart A T j k ∧
      fp < (windowLength T j : ℝ) ^ (1 - α) := by
  let α := δ / (16 * (K + 1))
  change 0 < α ∧ α < 1 / 2 ∧
    X0 ≤ (windowStart A T j k : ℝ) ∧
    (windowStart A T j k : ℝ) ^ α ≤ windowLength T j ∧
    windowLength T j ≤ windowStart A T j k ∧
    fp < (windowLength T j : ℝ) ^ (1 - α)
  have hx1 : 1 ≤ x := by linarith
  have hfp0 : 0 < fp := by linarith
  have hHlower : fp * x ^ (δ / 2) / 16 ≤ (windowLength T j : ℝ) :=
    active_window_scale_lower hx1 hδ.le hg hfp0 hfactor hf hTceil hpoint hshell
  have hXupper : (windowStart A T j k : ℝ) ≤ x ^ (K + 1) :=
    window_polynomial_location hx hK hAB hB0 hj hk hB
  have hHle : windowLength T j ≤ windowStart A T j k :=
    windowLength_le_start A T j k hTpos
  have hHpos : 0 < windowLength T j := windowLength_pos T j hTpos
  have hXpos : (0 : ℝ) < windowStart A T j k := by
    exact_mod_cast hHpos.trans_le hHle
  have hpower := window_power_and_modulus_gate hx1 hδ hδone
    (show 1 ≤ K + 1 by linarith) hfp hXpos
    (by exact_mod_cast hHle) hHlower hXupper hmargin
  have hX0 : X0 ≤ (windowStart A T j k : ℝ) := by
    have hbase : (shellBase j : ℝ) ≤ windowStart A T j k := by
      exact_mod_cast shellBase_le_windowStart A T j k
    have hnX : (n : ℝ) < 2 * shellBase j := by exact_mod_cast hshell
    linarith
  exact ⟨hpower.1, hpower.2.1, hX0, hpower.2.2.1,
    hHle, hpower.2.2.2⟩

-- The reciprocal log in the exact Shiu RHS is no larger than a fixed
-- multiple of 1/log x. The active source point, not the formal shell
-- label alone, gives the needed lower bound on the translated X.
theorem active_window_log_lower
    {x δ fp : ℝ} {A T j k n : ℕ}
    (hx : 1 < x) (_hδ : 0 < δ) (hfp : 1 ≤ fp)
    (hpoint : fp * x ^ (δ / 2) ≤ (n : ℝ))
    (hshell : n < 2 * shellBase j)
    (hmargin : 2 ≤ x ^ (δ / 4)) :
    (δ / 4) * Real.log x ≤ Real.log (windowStart A T j k) := by
  have hxpos : 0 < x := by linarith
  have hpowpos : 0 < x ^ (δ / 4) := Real.rpow_pos_of_pos hxpos _
  have hsplit : x ^ (δ / 2) = x ^ (δ / 4) * x ^ (δ / 4) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hnX : (n : ℝ) < 2 * shellBase j := by exact_mod_cast hshell
  have hbase : (shellBase j : ℝ) ≤ windowStart A T j k := by
    exact_mod_cast shellBase_le_windowStart A T j k
  have hXpow : x ^ (δ / 4) ≤ (windowStart A T j k : ℝ) := by
    rw [hsplit] at hpoint
    have hproduct := mul_le_mul_of_nonneg_left hmargin hpowpos.le
    nlinarith [hproduct]
  have hlog := Real.log_le_log hpowpos hXpow
  rw [Real.log_rpow hxpos] at hlog
  linarith

end
end ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
