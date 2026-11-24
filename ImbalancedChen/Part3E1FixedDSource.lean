import ImbalancedChen.Part3E1FiniteCauchy
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
# The fixed-d retained nonzero S2 source

The finite contract uses the original two `n` unit conditions, the
`(q*d)*r` inverse residue and Fourier scale, the mean denominator
`φ((q*d)*s)`, and the unsplit nonnegative weight at the original q.
The fixed-d q image allows the two square-root factors to reproduce this
weight while retaining the same ordered rough factors and both signs of h.

For the archived `Part3OriginalS2ActualPoissonZeroMode` source, take `Q`
from `OriginalGevreyPoissonPacket20261028.paperPsiNaturalCarrier atom.Q1`,
`R` from `dyadicWindow k.w`, `N` from `atom.alphaCarrier`, and use the
archived `paperQWeight`, `lambdaTrim`, and Fourier transform of `paperPsi`.
The fixed-`d` slice of `MediumGenuinePoissonFibre20261028.fibreCarrier`
then has exactly the order in `retainedS2FixedD_eq_fibreSum`.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators FourierTransform
open OriginalSmoothPoissonTail (inverseResidue)

/-- The physical outer moduli of the fixed small-factor fibre. -/
def fixedDModuli (d : ℕ) (Q : Finset ℕ) : Finset ℕ := Q.image (fun q => d * q)

/-- The square-root factor reproduces the original weight in the two rows.
The q argument is the physical modulus multiplier `d*q`. -/
def fixedDLambda (d : ℕ) (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℂ) (q r : ℕ) : ℂ :=
  (Real.sqrt (qWeight (q / d)) : ℂ) * lambdaTrim r

/-- The exact zero-deleted signed mode of the one-congruence S2 packet. -/
def retainedS2Mode (ψhat : ℝ → ℂ) (V : ℝ) (a : ℤ) (m n : ℕ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else
    (V / (m : ℝ)) • ψhat ((V / (m : ℝ)) * (h : ℝ)) *
      fourier h ((((a * inverseResidue m (n : ℤ) : ℤ) : ℝ) / (m : ℝ)) : UnitAddCircle)

/-- The original S2 nonzero-mode fibre restricted to the retained integer window. -/
def retainedS2Fibre (H d : ℕ) (a : ℤ) (V : ℝ) (ψhat : ℝ → ℂ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ)
    (q r s n n' : ℕ) : ℂ :=
  if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
    ((qWeight q : ℂ) * lambdaTrim r * star (lambdaTrim s) * alpha n * star (alpha n')) *
      (∑ h ∈ Icc (-(H : ℤ)) (H : ℤ), retainedS2Mode ψhat V a (q * d * r) n h) /
        ((q * d * s).totient : ℂ)
  else 0

/-- Retained S2 over independent original rough and alpha carriers at fixed d.
The common signed cutoff is taken on the left physical modulus. -/
def retainedS2FixedD (Q R N : Finset ℕ) (H d : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ R, ∑ n' ∈ N, ∑ r ∈ R,
    retainedS2Fibre H d a V ψhat qWeight lambdaTrim alpha q r s n n'

/-- The original fixed-`d` fibre order, before permuting the finite sums
for the E1 Cauchy square. -/
theorem retainedS2FixedD_eq_fibreSum (Q R N : Finset ℕ) (H d : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) :
    retainedS2FixedD Q R N H d a V ψhat qWeight lambdaTrim alpha =
      ∑ q ∈ primitive a Q, ∑ v ∈ (R ×ˢ N) ×ˢ (R ×ˢ N),
        retainedS2Fibre H d a V ψhat qWeight lambdaTrim alpha q v.1.1 v.2.1 v.1.2 v.2.2 := by
  unfold retainedS2FixedD
  apply sum_congr rfl
  intro q _
  simp only [sum_product]
  let f (r s n n' : ℕ) := retainedS2Fibre H d a V ψhat qWeight lambdaTrim alpha q r s n n'
  calc
    _ = ∑ n ∈ N, ∑ s ∈ R, ∑ r ∈ R, ∑ n' ∈ N, f r s n n' :=
      sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => sum_comm))
    _ = ∑ n ∈ N, ∑ r ∈ R, ∑ s ∈ R, ∑ n' ∈ N, f r s n n' :=
      sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := sum_comm

private theorem retainedS2_character_eq_leftPhase (q r n : ℕ) [NeZero (q * r)]
    (hunit : n.Coprime (q * r)) (a h : ℤ) :
    fourier h ((((a * inverseResidue (q * r) (n : ℤ) : ℤ) : ℝ) /
      ((q * r : ℕ) : ℝ)) : UnitAddCircle) = leftPhase q r n a h := by
  rw [leftPhase_eq_reciprocalPhase, reciprocalPhase_nat_eq_fourier, if_pos hunit]
  simp only [inverseResidue, Int.cast_natCast, Int.cast_mul, fourier_coe_apply]
  congr 1
  push_cast
  ring

private theorem retainedS2Mode_sum_eq_erase_zero (H : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (m n : ℕ) :
    (∑ h ∈ Icc (-(H : ℤ)) (H : ℤ), retainedS2Mode ψhat V a m n h) =
      ∑ h ∈ e1NonzeroFrequencies H, retainedS2Mode ψhat V a m n h := by
  have h0 : (0 : ℤ) ∈ Icc (-(H : ℤ)) (H : ℤ) := mem_Icc.mpr ⟨by omega, by omega⟩
  rw [e1NonzeroFrequencies, ← sum_erase_add _ _ h0]
  simp [retainedS2Mode]

private theorem retainedS2Fibre_eq_sum (H d : ℕ) (a : ℤ) (V : ℝ) (ψhat : ℝ → ℂ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) (q r s n n' : ℕ)
    (hd : 0 < d) (hq : 0 < q) (hr : 0 < r) (hw : 0 ≤ qWeight q) :
    retainedS2Fibre H d a V ψhat qWeight lambdaTrim alpha q r s n n' =
      ∑ h ∈ e1NonzeroFrequencies H, (V : ℂ) *
        (if n'.Coprime (q * d * s) then
          fixedDLambda d qWeight lambdaTrim (q*d) r * star (fixedDLambda d qWeight lambdaTrim (q*d) s) *
            alpha n * star (alpha n') / (((q*d*s).totient : ℂ) * ((q*d*r : ℕ) : ℂ)) *
            ψhat ((h : ℝ) * V / ((q*d*r : ℕ) : ℝ)) * leftPhase (q*d) r n a h
        else 0) := by
  let _ : NeZero (q * d * r) := ⟨(Nat.mul_pos (Nat.mul_pos hq hd) hr).ne'⟩
  by_cases hn : n.Coprime (q * d * r)
  · by_cases hn' : n'.Coprime (q * d * s)
    · have hgate : n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) := ⟨hn, hn'⟩
      simp only [retainedS2Fibre, if_pos hgate, retainedS2Mode_sum_eq_erase_zero, if_pos hn',
        mul_sum, sum_div]
      apply sum_congr rfl
      intro h hh
      have hh0 : h ≠ 0 := (mem_erase.mp hh).1
      have hFourier : V / ((q*d*r : ℕ) : ℝ) * (h : ℝ) = (h : ℝ) * V / ((q*d*r : ℕ) : ℝ) := by ring
      have hweight : (Real.sqrt (qWeight q) : ℂ) * (Real.sqrt (qWeight q) : ℂ) = (qWeight q : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hw
      rw [retainedS2Mode, if_neg hh0, hFourier, retainedS2_character_eq_leftPhase (q*d) r n hn]
      simp only [fixedDLambda, Nat.mul_div_cancel _ hd, star_mul, Complex.star_def,
        Complex.conj_ofReal, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
      simp only [div_eq_mul_inv, mul_inv_rev]
      rw [← hweight]
      ring
    · simp [retainedS2Fibre, hn']
  · simp [retainedS2Fibre, hn, leftPhase_eq_reciprocalPhase, reciprocalPhase_nat_eq_fourier]

/-- Exact retained fixed-d actual S2 equals `V` times the E1 source,
with the q image, two original primitive gates and exact totient preserved.
The only coefficient restriction is primitive support for the physical `d*r`. -/
theorem retainedS2FixedD_eq_source (Q R N : Finset ℕ) (H d : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ)
    (hd : 0 < d) (hQ : ∀ q ∈ Q, 0 < q) (hR : ∀ r ∈ R, 0 < r)
    (hw : ∀ q ∈ Q, 0 ≤ qWeight q)
    (htrim : ∀ r ∈ R, lambdaTrim r ≠ 0 → (d * r).Coprime a.natAbs) :
    retainedS2FixedD Q R N H d a V ψhat qWeight lambdaTrim alpha =
      (V : ℂ) * source (fixedDModuli d Q) R N (e1NonzeroFrequencies H) a V ψhat
        (fixedDLambda d qWeight lambdaTrim) alpha := by
  have htrimZero (r : ℕ) (hr : r ∈ R) (hbad : ¬ (d * r).Coprime a.natAbs) : lambdaTrim r = 0 :=
    by_contra (fun h => hbad (htrim r hr h))
  by_cases hdA : d.Coprime a.natAbs
  · have himage : primitive a (fixedDModuli d Q) = (primitive a Q).image (fun q => d * q) := by
      ext q'
      simp only [primitive_eq_filter, fixedDModuli, mem_filter, mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hqA⟩
        exact ⟨q, ⟨hq, (Nat.coprime_mul_iff_left.mp hqA).2⟩, rfl⟩
      · rintro ⟨q, ⟨hq, hqA⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, hdA.mul_left hqA⟩
    unfold retainedS2FixedD source
    rw [himage, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd h)]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    have hqQ : q ∈ Q := (mem_filter.mp hq).1
    rw [Nat.mul_comm d q]
    apply sum_congr rfl
    intro n _
    rw [primitive_eq_filter, sum_filter]
    apply sum_congr rfl
    intro s hs
    by_cases hsA : s.Coprime a.natAbs
    · simp only [if_pos hsA]
      apply sum_congr rfl
      intro n' _
      rw [sum_filter]
      apply sum_congr rfl
      intro r hr
      by_cases hrA : r.Coprime a.natAbs
      · rw [if_pos hrA]
        exact retainedS2Fibre_eq_sum H d a V ψhat qWeight lambdaTrim alpha q r s n n'
          hd (hQ q hqQ) (hR r hr) (hw q hqQ)
      · have hzero := htrimZero r hr (fun h => hrA (Nat.coprime_mul_iff_left.mp h).2)
        simp [retainedS2Fibre, hzero, hrA]
    · have hzero := htrimZero s hs (fun h => hsA (Nat.coprime_mul_iff_left.mp h).2)
      simp [retainedS2Fibre, hzero, hsA]
  · have hzero : ∀ r ∈ R, lambdaTrim r = 0 := fun r hr =>
      htrimZero r hr (fun h => hdA (Nat.coprime_mul_iff_left.mp h).1)
    have hempty : primitive a (fixedDModuli d Q) = ∅ := by
      ext q'
      constructor
      · intro hq
        obtain ⟨hraw, hcop⟩ := mem_filter.mp hq
        obtain ⟨q, _, rfl⟩ := mem_image.mp hraw
        exact False.elim (hdA (Nat.coprime_mul_iff_left.mp hcop).1)
      · simp
    unfold retainedS2FixedD source
    rw [hempty, sum_empty, mul_zero]
    refine sum_eq_zero (fun _ _ => sum_eq_zero (fun _ _ => sum_eq_zero (fun _ _ =>
      sum_eq_zero (fun _ _ => sum_eq_zero (fun r hr => ?_)))))
    simp [retainedS2Fibre, hzero r hr]

end

end ImbalancedChen.Part3.E1Finite
