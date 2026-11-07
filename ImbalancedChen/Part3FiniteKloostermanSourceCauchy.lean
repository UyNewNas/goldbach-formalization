import ImbalancedChen.Part3FiniteKloostermanSourceCoefficients
import ImbalancedChen.Part3KloostermanCompleteSecondMoment
import ImbalancedChen.Part3ComplexDispersion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Honest complete-second-moment Cauchy for the signed source coefficients.
The one-frequency constant is c*phi(c); if both frequencies vary, the
constant is c^2*phi(c). Residue collisions are retained in the coefficient
energy. In particular an incomplete interval does NOT inherit a pointwise
square-root bound from complete Parseval. The full small-gcd spectral 7/32
bound and passage from finite truncations to an infinite tail remain OPEN.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteSource20261026b

noncomputable section
open Classical Finset
open scoped BigOperators

theorem kloosterman_two_frequency_energy (c : ℕ) [NeZero c] :
    (∑ r : ZMod c × ZMod c,
      ‖kloosterman c (r.1.val : ℤ) (r.2.val : ℤ)‖ ^ 2) =
      (c : ℝ)^2 * (Nat.totient c : ℝ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [CompleteSecondMomentSourceOnly.kloosterman_complete_second_moment]
  simp [ZMod.card, pow_two, mul_assoc]

theorem complete_bilinear_cauchy (c : ℕ) [NeZero c]
    (A : ZMod c × ZMod c → ℂ) :
    ‖∑ r : ZMod c × ZMod c,
      A r * kloosterman c (r.1.val : ℤ) (r.2.val : ℤ)‖ ^ 2 ≤
      ((c : ℝ)^2 * (Nat.totient c : ℝ)) *
        ∑ r : ZMod c × ZMod c, ‖A r‖ ^ 2 := by
  have h := complex_finset_cauchy_norm_sq Finset.univ A
    (fun r => kloosterman c (r.1.val : ℤ) (r.2.val : ℤ))
  rw [kloosterman_two_frequency_energy] at h
  simpa only [mul_comm] using h

theorem complete_fixedRight_cauchy (c : ℕ) [NeZero c]
    (n : ℤ) (A : ZMod c → ℂ) :
    ‖∑ r : ZMod c, A r * kloosterman c (r.val : ℤ) n‖ ^ 2 ≤
      ((c : ℝ) * (Nat.totient c : ℝ)) * ∑ r : ZMod c, ‖A r‖ ^ 2 := by
  have h := complex_finset_cauchy_norm_sq Finset.univ A
    (fun r => kloosterman c (r.val : ℤ) n)
  rw [CompleteSecondMomentSourceOnly.kloosterman_complete_second_moment] at h
  simpa only [mul_comm] using h

variable {ι : Type*}

/-- Genuine finite source bound, with the actual collision energy. No
separability, boundedness or spectral conclusion is assumed. -/
theorem finiteFrequencySource_norm_sq_le (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a : ℤ) (y z m : ι → ℤ) :
    ‖finiteFrequencySource I w B c a y z m‖ ^ 2 ≤
      ((c : ℝ)^2 * (Nat.totient c : ℝ)) *
        ∑ r : ZMod c × ZMod c,
          ‖sourceCoefficient I w B c a y z m r‖ ^ 2 := by
  rw [sourceCoefficient_pairing]
  exact complete_bilinear_cauchy c _

/-- The fixed-y original subfamily has the sharper c*phi(c) fee. The z
labels and their inverse twists may still vary freely on the source. -/
theorem finiteFixedRightSource_norm_sq_le (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a y0 : ℤ) (z m : ι → ℤ) :
    ‖finiteFrequencySource I w B c a (fun _ => y0) z m‖ ^ 2 ≤
      ((c : ℝ) * (Nat.totient c : ℝ)) *
        ∑ r : ZMod c, ‖linearSourceCoefficient I w B c z m r‖ ^ 2 := by
  rw [fixedRightSource_pairing]
  exact complete_fixedRight_cauchy c (a*y0) _

/-- Exact energy for a collision-free finite source. This is an elementary
carrier hypothesis, not a bound on the target sum or spectral data. -/
theorem linearSourceCoefficient_energy_of_injOn (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (z m : ι → ℤ)
    (hinj : Set.InjOn (fun i => ((m i * inverseResidue c (z i) : ℤ) : ZMod c))
      (I : Set ι)) :
    (∑ r : ZMod c, ‖linearSourceCoefficient I w B c z m r‖ ^ 2) =
      ∑ i ∈ I, ‖w i * frequencyAmplitude B c (m i)‖ ^ 2 := by
  classical
  let f : ι → ZMod c := fun i => ((m i * inverseResidue c (z i) : ℤ) : ZMod c)
  have hat (i : ι) (hi : i ∈ I) :
      linearSourceCoefficient I w B c z m (f i) =
        w i * frequencyAmplitude B c (m i) := by
    unfold linearSourceCoefficient
    rw [Finset.sum_eq_single i]
    · simp [f]
    · intro j hj hji
      apply if_neg
      intro heq
      exact hji (hinj hj hi heq)
    · exact fun hnot => (hnot hi).elim
  have hout (r : ZMod c) (hr : r ∉ I.image f) :
      linearSourceCoefficient I w B c z m r = 0 := by
    unfold linearSourceCoefficient
    apply Finset.sum_eq_zero
    intro i hi
    apply if_neg
    intro heq
    exact hr (Finset.mem_image.mpr ⟨i, hi, heq⟩)
  calc
    (∑ r : ZMod c, ‖linearSourceCoefficient I w B c z m r‖ ^ 2) =
        ∑ r ∈ I.image f, ‖linearSourceCoefficient I w B c z m r‖ ^ 2 := by
      symm
      apply Finset.sum_subset (by simp)
      intro r hr hnot
      simp only [hout r hnot, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    _ = ∑ i ∈ I, ‖linearSourceCoefficient I w B c z m (f i)‖ ^ 2 := by
      rw [Finset.sum_image]
      intro i hi j hj heq
      exact hinj hi hj heq
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [hat i hi])

/-- Genuine explicit one-frequency bound on a collision-free subfamily:
the RHS contains only the ORIGINAL finite coefficient/amplitude energy. -/
theorem finiteFixedRightSource_norm_sq_le_of_injOn (I : Finset ι) (w : ι → ℂ)
    (B : ℝ) (c : ℕ) [NeZero c] (a y0 : ℤ) (z m : ι → ℤ)
    (hinj : Set.InjOn (fun i => ((m i * inverseResidue c (z i) : ℤ) : ZMod c))
      (I : Set ι)) :
    ‖finiteFrequencySource I w B c a (fun _ => y0) z m‖ ^ 2 ≤
      ((c : ℝ) * (Nat.totient c : ℝ)) *
        ∑ i ∈ I, ‖w i * frequencyAmplitude B c (m i)‖ ^ 2 := by
  have h := finiteFixedRightSource_norm_sq_le I w B c a y0 z m
  rw [linearSourceCoefficient_energy_of_injOn I w B c z m hinj] at h
  exact h

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.FiniteSource20261026b
