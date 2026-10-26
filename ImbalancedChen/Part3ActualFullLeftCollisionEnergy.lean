import ImbalancedChen.Part3ActualAmplitudeAliasEnergy

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The ACTUAL complete raw left coefficient retains the original common
scaledDyadicCutoff N q scalar and inverse-z residue fibre. For coprime z,
that fibre is the all-m alias pulled back by the genuine unit permutation;
for noncoprime z the actual scalar gate is zero. Its full energy therefore
has the proved physical-support bound. Finite K/arbitrary eta are NOT
bounded by this identity; their hard-tail bridge belongs to U9.
-/
namespace ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.FiniteSource20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open ActualCompletedPairYFibres20261026b ActualCompletedPairSharpL220261026b
open scoped BigOperators

/-- Native all-m RAW left coefficient. Both the original inverse-z
frequency residue and common target-N scalar are present literally. -/
def actualFullLeftCollision (q z : ℕ) [NeZero q] (M N : ℝ) (u : ZMod q) : ℂ :=
  ∑' m : ℤ,if ((m*inverseResidue q (z : ℤ) : ℤ) : ZMod q)=u then
    actualCommonScalar q z N*frequencyAmplitude M q m else 0

theorem actualFullLeftCollision_summable_norm (q z : ℕ) [NeZero q]
    {M : ℝ} (hM : 0 < M) (N : ℝ) (u : ZMod q) :
    Summable (fun m : ℤ => ‖if ((m*inverseResidue q (z : ℤ) : ℤ) : ZMod q)=u then
      actualCommonScalar q z N*frequencyAmplitude M q m else 0‖) := by
  apply ((amplitude_summable_norm q hM).mul_left ‖actualCommonScalar q z N‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro m
  split_ifs
  · simp only [norm_mul,le_refl]
  · exact (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Exact finite RAW restriction of the same native summand. This is
only a finite identity and carries no finite-window energy estimate. -/
theorem actualLeftCollision_raw_eq_sum (q z : ℕ) [NeZero q] (K : Finset ℤ)
    (M N : ℝ) (u : ZMod q) :
    actualLeftCollision q z K (fun _ => 1) M N u =
      ∑ m ∈ K,if ((m*inverseResidue q (z : ℤ) : ℤ) : ZMod q)=u then
        actualCommonScalar q z N*frequencyAmplitude M q m else 0 := by
  unfold actualLeftCollision packetLeftCoefficient
  simp only [mul_one]

/-- The native singleton summands are absolutely summable. This supplies
the original all-m Fubini consumer without a summability assumption. -/
theorem actualLeftCollision_singleton_summable_norm (q z : ℕ) [NeZero q]
    {M : ℝ} (hM : 0 < M) (N : ℝ) (u : ZMod q) :
    Summable (fun m : ℤ => ‖actualLeftCollision q z {m} (fun _ => 1) M N u‖) := by
  simpa only [actualLeftCollision_raw_eq_sum,Finset.sum_singleton] using
    actualFullLeftCollision_summable_norm q z hM N u

theorem actualFullLeftCollision_eq_tsum_singletons (q z : ℕ) [NeZero q]
    (M N : ℝ) (u : ZMod q) :
    actualFullLeftCollision q z M N u =
      ∑' m : ℤ,actualLeftCollision q z {m} (fun _ => 1) M N u := by
  simp only [actualLeftCollision_raw_eq_sum,Finset.sum_singleton,actualFullLeftCollision]

theorem actualCommonScalar_norm_le_one (q z : ℕ) (N : ℝ) :
    ‖actualCommonScalar q z N‖ ≤ 1 := by
  unfold actualCommonScalar
  split_ifs
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (scaledDyadicCutoff_nonneg N q)]
    exact scaledDyadicCutoff_le_one N q
  · simp

private theorem inverseResidue_natCast (q z : ℕ) [NeZero q] :
    (inverseResidue q (z : ℤ) : ZMod q)=(z : ZMod q)⁻¹ := by
  simp only [inverseResidue,Int.cast_natCast,ZMod.natCast_zmod_val]

/-- Exact inverse-z fibre orientation. For unit z, m*inv(z)=u is the
same residue condition as m=u*z, on ALL residues of composite q. -/
theorem actual_inverse_fibre_iff (q z : ℕ) [NeZero q] (hz : q.Coprime z)
    (m : ℤ) (u : ZMod q) :
    (((m*inverseResidue q (z : ℤ) : ℤ) : ZMod q)=u) ↔ (m : ZMod q)=u*(z : ZMod q) := by
  have hunit : IsUnit (z : ZMod q) := (ZMod.isUnit_iff_coprime z q).mpr hz.symm
  have hbij := (IsUnit.isUnit_iff_mulRight_bijective (a := (z : ZMod q))).mp hunit
  have hcancel : (((m*inverseResidue q (z : ℤ) : ℤ) : ZMod q)*(z : ZMod q))=(m : ZMod q) := by
    rw [Int.cast_mul,inverseResidue_natCast]
    calc
      _ = (m : ZMod q)*((z : ZMod q)⁻¹*(z : ZMod q)) := by ring
      _ = _ := by rw [ZMod.inv_mul_of_unit _ hunit,mul_one]
  constructor
  · intro hm
    have hh := congrArg (fun v : ZMod q => v*(z : ZMod q)) hm
    rwa [hcancel] at hh
  · intro hm
    apply hbij.1
    rw [hcancel]
    exact hm

/-- Native complete raw left coefficient is the common scalar times the
actual all-m alias, with the inverse-z unit permutation derived exactly. -/
theorem actualFullLeftCollision_eq_alias (q z : ℕ) [NeZero q] (M N : ℝ)
    (hz : q.Coprime z) (u : ZMod q) :
    actualFullLeftCollision q z M N u =
      actualCommonScalar q z N*aliasCoefficient q M (u*(z : ZMod q)) := by
  unfold actualFullLeftCollision aliasCoefficient
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [actual_inverse_fibre_iff q z hz m u]
  split_ifs <;> simp

theorem actualFullLeftCollision_eq_zero_of_not_coprime (q z : ℕ) [NeZero q]
    (M N : ℝ) (hz : ¬ q.Coprime z) (u : ZMod q) :
    actualFullLeftCollision q z M N u=0 := by
  simp only [actualFullLeftCollision,actualCommonScalar,if_neg hz,zero_mul,ite_self,tsum_zero]

/-- Exact actual common-scalar energy identity. The inverse-z pullback
is a proved unit permutation; nonunits have not been silently inverted. -/
theorem actualFullLeftCollision_energy_eq (q z : ℕ) [NeZero q] (M N : ℝ) (hz : q.Coprime z) :
    energy q (actualFullLeftCollision q z M N) =
      ‖actualCommonScalar q z N‖^2*energy q (aliasCoefficient q M) := by
  unfold energy
  simp_rw [actualFullLeftCollision_eq_alias q z M N hz,norm_mul,mul_pow]
  rw [← Finset.mul_sum]
  congr 1
  have hunit : IsUnit (z : ZMod q) := (ZMod.isUnit_iff_coprime z q).mpr hz.symm
  apply Fintype.sum_bijective (fun u : ZMod q => u*(z : ZMod q))
    ((IsUnit.isUnit_iff_mulRight_bijective (a := (z : ZMod q))).mp hunit)
  intro u
  rfl

/-- Genuine full actual raw left-energy bound, valid also at noncoprime
levels (where the original scalar gate is exactly zero), every q>0 and
M>0. Finite K and arbitrary completed weights require their own tail proof. -/
theorem actualFullLeftCollision_energy_le (q z : ℕ) [NeZero q] {M : ℝ}
    (hM : 0 < M) (N : ℝ) :
    energy q (actualFullLeftCollision q z M N) ≤ 9*(M/(q : ℝ))*(1+M/(q : ℝ)) := by
  by_cases hz : q.Coprime z
  · rw [actualFullLeftCollision_energy_eq q z M N hz]
    have hscalar : ‖actualCommonScalar q z N‖^2 ≤ 1 := by
      have hh := actualCommonScalar_norm_le_one q z N
      have hn := norm_nonneg (actualCommonScalar q z N)
      nlinarith only [hh,hn]
    have henergy : 0 ≤ energy q (aliasCoefficient q M) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc
      _ ≤ 1*energy q (aliasCoefficient q M) := mul_le_mul_of_nonneg_right hscalar henergy
      _ = energy q (aliasCoefficient q M) := one_mul _
      _ ≤ _ := aliasCoefficient_energy_le q hM
  · have hzero : actualFullLeftCollision q z M N=(fun _ => 0) :=
      funext (actualFullLeftCollision_eq_zero_of_not_coprime q z M N hz)
    rw [hzero]
    simp only [energy,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),Finset.sum_const_zero]
    have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity

end
end ImbalancedChen.Part3.ActualCompletedLeftAlias20261026b
