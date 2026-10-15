import ImbalancedChen.Part3TransposedZeroCovariance

/-!
# Reality of the actual primitive zero main term

The actual complex factor coefficients and coprime masses form a Hermitian
pair. The totient density is real and symmetric under exchanging the two
complete physical labels. Finite Fubini therefore makes primitiveZeroMain
self-conjugate without changing any carrier or imposing coefficient bounds.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical
open scoped BigOperators

namespace TransposedZeroCovariance

theorem star_sum_pair_eq_of_hermitian {ι : Type*} (S : Finset ι)
    (f : ι → ι → ℂ)
    (hf : ∀ a ∈ S, ∀ b ∈ S, star (f a b) = f b a) :
    star (∑ a ∈ S, ∑ b ∈ S, f a b) = ∑ a ∈ S, ∑ b ∈ S, f a b := by
  simp only [star_sum]
  calc
    _ = ∑ a ∈ S, ∑ b ∈ S, f b a := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hf a ha b hb
    _ = _ := Finset.sum_comm

theorem primitiveZeroMain_star (d : MediumAtom) :
    star (primitiveZeroMain d) = primitiveZeroMain d := by
  unfold primitiveZeroMain
  rw [star_mul]
  have hs : star ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  rw [hs]
  congr 1
  apply star_sum_pair_eq_of_hermitian
  intro a _ b _
  simp only [star_mul, star_div₀, star_star, star_natCast,
    Nat.mul_comm, mul_comm, mul_left_comm, mul_assoc]

theorem primitiveZeroMain_ofReal_re (d : MediumAtom) :
    ((primitiveZeroMain d).re : ℂ) = primitiveZeroMain d := by
  apply Complex.conj_eq_iff_re.mp
  simpa only [Complex.star_def] using primitiveZeroMain_star d

end TransposedZeroCovariance

end

end ImbalancedChen.Part3
