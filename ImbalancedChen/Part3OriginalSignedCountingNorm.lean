import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity
import ImbalancedChen.Part3ActualReciprocalSquarePoissonCore
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Complex coefficient energy for the physical reciprocal square

The source retains ordered slot labels, both signed frequencies, the two
fixed unit gates, conjugation and the output phase. The auxiliary index
divides the actual nonzero output. The c-unit condition remains in the
completed Poisson kernel, independent of the coefficient.
-/

namespace ImbalancedChen.Part3.OriginalSignedCountingNorm20261028
noncomputable section
open Classical Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (fouvryTau_two)
open scoped BigOperators
open LichtmanSignedDifferenceMultiplicity OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly (Inner fixedUnit atomCoeff level outputY)

abbrev Tuple := (ℕ × ℕ × ℕ) × (ℤ × ℤ)

def squareLeft (t : Tuple) : ℕ × ℤ := (t.1.2.1,t.2.1)
def squareRight (t : Tuple) : ℕ × ℤ := (t.1.1,t.2.2)

/-- The crossed difference in the actual reciprocal-square expansion
is exactly the counting output after this explicit ordered relabeling. -/
theorem output_eq_actual_square_output (t : Tuple) :
    output t =
      (ActualReciprocalSquarePoissonSourceOnly.level (squareLeft t) (squareRight t),
       ActualReciprocalSquarePoissonSourceOnly.outputY (t.1.2.2 : ℤ)
         (squareLeft t) (squareRight t)) := by
  simp only [output,LichtmanSignedDifferenceMultiplicity.difference,
    ActualReciprocalSquarePoissonSourceOnly.level,
    ActualReciprocalSquarePoissonSourceOnly.outputY,
    ActualReciprocalSquarePoissonSourceOnly.difference,squareLeft,squareRight]
  exact Prod.ext (Nat.mul_comm _ _) rfl

def tupleCoefficient (A : ℕ) (a : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (t : Tuple) : ℂ :=
  if fixedUnit A a t.1.1 ∧ fixedUnit A a t.1.2.1 then
    atomCoeff lambda omega (squareLeft t) * star (atomCoeff lambda omega (squareRight t))
  else 0

def countCoefficient (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (zy : ℕ × ℤ) : ℂ :=
  eps zy * ∑ t ∈ (sourceCarrier S H F).filter (fun t => output t = zy),
    tupleCoefficient A a lambda omega t

def countingNorm (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ) : ℝ :=
  ∑ zy ∈ (sourceCarrier S H F).image output,
    if (nu : ℤ) ∣ zy.2 then ‖countCoefficient S H F A a lambda omega eps zy‖^2 else 0

private theorem tupleCoefficient_norm_le_one {S H F : ℝ} (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    {t : Tuple} (ht : t ∈ sourceCarrier S H F) :
    ‖tupleCoefficient A a lambda omega t‖ ≤ 1 := by
  obtain ⟨hprod,hne⟩ := mem_filter.mp ht
  obtain ⟨hs,hh⟩ := mem_product.mp hprod
  obtain ⟨hs1,hs2f⟩ := mem_product.mp hs
  obtain ⟨hs2,hf⟩ := mem_product.mp hs2f
  obtain ⟨hh1,hh2⟩ := mem_product.mp hh
  have hleft : ‖atomCoeff lambda omega (squareLeft t)‖ ≤ 1 := by
    simp only [atomCoeff,squareLeft,norm_mul]
    simpa only [one_mul] using
      mul_le_mul (hlambda _ hs2) (homega _ hh1) (norm_nonneg _) zero_le_one
  have hright : ‖atomCoeff lambda omega (squareRight t)‖ ≤ 1 := by
    simp only [atomCoeff,squareRight,norm_mul]
    simpa only [one_mul] using
      mul_le_mul (hlambda _ hs1) (homega _ hh2) (norm_nonneg _) zero_le_one
  unfold tupleCoefficient
  split_ifs
  · simpa only [norm_mul,norm_star,one_mul] using
      mul_le_mul hleft hright (norm_nonneg _) zero_le_one
  · simp

/-- The COMPLEX coefficient, with its original fixed one-bounded
factors, is bounded by the actual positive fibre cardinality. -/
theorem countCoefficient_norm_le_multiplicity (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (zy : ℕ × ℤ) :
    ‖countCoefficient S H F A a lambda omega eps zy‖ ≤
      (multiplicity S H F zy.1 zy.2 : ℝ) := by
  let T := (sourceCarrier S H F).filter (fun t => output t = zy)
  have hsum : ‖∑ t ∈ T, tupleCoefficient A a lambda omega t‖ ≤ (T.card : ℝ) := by
    calc
      _ ≤ ∑ t ∈ T, ‖tupleCoefficient A a lambda omega t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ T, (1 : ℝ) := sum_le_sum (fun t ht =>
        tupleCoefficient_norm_le_one A a lambda omega hlambda homega (mem_filter.mp ht).1)
      _ = _ := by simp
  unfold countCoefficient
  rw [norm_mul]
  calc
    _ ≤ 1*(T.card : ℝ) := mul_le_mul (heps zy) hsum (norm_nonneg _) zero_le_one
    _ = _ := by simp only [one_mul, LichtmanSignedDifferenceMultiplicity.multiplicity, T]

theorem countingNorm_nonneg (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ) :
    0 ≤ countingNorm S H F A a lambda omega eps nu := by
  unfold countingNorm
  apply sum_nonneg
  intro zy hzy
  split_ifs <;> positivity

/-- The literal real H<1 source is empty. Rounding never creates a
singleton to which the nonempty counting estimate would be applied. -/
theorem sourceCarrier_empty_of_short_H (S H F : ℝ) (hH0 : 0 ≤ H) (hH : H < 1) :
    sourceCarrier S H F = ∅ := by
  have hf : Nat.floor H = 0 := by
    by_contra hn
    have hn1 : 1 ≤ Nat.floor H := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ Nat.floor H := by exact_mod_cast hn1
    have hfloor := Nat.floor_le hH0
    linarith
  simp [sourceCarrier,frequencyCarrier,hf]

theorem countingNorm_zero_of_short_H (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ)
    (hH0 : 0 ≤ H) (hH : H < 1) :
    countingNorm S H F A a lambda omega eps nu = 0 := by
  simp only [countingNorm,sourceCarrier_empty_of_short_H S H F hH0 hH,
    image_empty,sum_empty]

theorem countingNorm_le_native_multiplicity (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) :
    countingNorm S H F A a lambda omega eps nu ≤ multiplicityL2 S H F nu := by
  unfold countingNorm multiplicityL2
  apply sum_le_sum
  intro zy hzy
  split_ifs
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (countCoefficient_norm_le_multiplicity S H F A a lambda omega eps
        hlambda homega heps zy) 2
  · rfl

/-- Original (23), with an explicit finite divisor/harmonic cost and
exact zero beyond nonzero y support. No large-nu +1 is inserted. -/
theorem actual_countingNorm_bound (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) (hnu : 0 < nu) :
    countingNorm S H F A a lambda omega eps nu ≤
      576*(divisorMaximum S H F : ℝ)^5*(harmonic (Nat.floor (2*S)) : ℝ)*
        (1+H/S)*(H*S)^2*F/(nu : ℝ) ∧
      (8*F*H*S ≤ (nu : ℝ) → countingNorm S H F A a lambda omega eps nu = 0) := by
  have hn := countingNorm_le_native_multiplicity S H F A a lambda omega eps
    hlambda homega heps nu
  obtain ⟨hbound,hzero⟩ := signedDifference_multiplicityL2_bound S H F hS hH hF nu hnu
  refine ⟨hn.trans hbound,?_⟩
  intro hlarge
  exact le_antisymm (hn.trans_eq (hzero hlarge))
    (countingNorm_nonneg S H F A a lambda omega eps nu)

/-- Uniform (23), with constants fixed before the dyadic scales and
coefficients. The short-frequency branch uses the literal empty carrier. -/
theorem exists_actual_countingNorm_subpower {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X S H F : ℝ), 1 ≤ X → 1 ≤ S → 0 ≤ H → 1 ≤ F →
      max (4 * S ^ 2) (8 * F * H * S) ≤ X ^ κ →
      ∀ (A : ℕ) (a : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ),
      (∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1) →
      (∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1) →
      (∀ zy, ‖eps zy‖ ≤ 1) → ∀ nu : ℕ, 0 < nu →
        countingNorm S H F A a lambda omega eps nu ≤
          C * X ^ ε * (1 + H / S) * (H * S) ^ 2 * F / (nu : ℝ) := by
  let δ : ℝ := ε / (10 * κ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hhalf : κ * δ * 5 = ε / 2 := by dsimp [δ]; field_simp; ring
  obtain ⟨D, hD, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) hδ
  let K : ℝ := D * 2 ^ δ
  let L : ℝ := 1 + κ / (ε / 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨576 * K ^ 5 * L, by positivity, ?_⟩
  intro X S H F hX hS hH0 hF hcap A a lambda omega eps hlambda homega heps nu hnu
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  by_cases hH : 1 ≤ H
  · let T := max (4 * S ^ 2) (8 * F * H * S)
    have hT : 1 ≤ T := (show (1 : ℝ) ≤ 4 * S ^ 2 by nlinarith [sq_nonneg (S - 1)]).trans
      (le_max_left _ _)
    have hc : 1 ≤ supportCap S H F := by
      exact_mod_cast hT.trans (Nat.le_ceil T)
    obtain ⟨n, hn, hmax⟩ := exists_mem_eq_sup (Icc 1 (supportCap S H F))
      ⟨1, mem_Icc.mpr ⟨le_rfl, hc⟩⟩ (fun n : ℕ => n.divisors.card)
    have hn0 : 0 < n := Nat.succ_le_iff.mp (mem_Icc.mp hn).1
    have hnX : (n : ℝ) ≤ 2 * X ^ κ := by
      calc
        _ ≤ (supportCap S H F : ℝ) := by exact_mod_cast (mem_Icc.mp hn).2
        _ ≤ T + 1 := (Nat.ceil_lt_add_one (zero_le_one.trans hT)).le
        _ ≤ 2 * X ^ κ := by linarith [Real.one_le_rpow hX hκ.le]
    have hdiv : (divisorMaximum S H F : ℝ) ≤ K * X ^ (κ * δ) := by
      rw [divisorMaximum, hmax, ← fouvryTau_two]
      calc
        _ ≤ D * (n : ℝ) ^ δ := htau n hn0
        _ ≤ D * (2 * X ^ κ) ^ δ := by gcongr
        _ = _ := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
            ← Real.rpow_mul hX0.le]
          simp only [K, mul_assoc]
    have hdivpow : (divisorMaximum S H F : ℝ) ^ 5 ≤ K ^ 5 * X ^ (ε / 2) := by
      calc
        _ ≤ (K * X ^ (κ * δ)) ^ 5 := by gcongr
        _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat, hhalf]
    have h2S : 1 ≤ 2 * S := by linarith
    have h2SX : 2 * S ≤ X ^ κ := by
      calc
        _ ≤ 4 * S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
        _ ≤ _ := (le_max_left _ _).trans hcap
    have hJ : (harmonic (Nat.floor (2 * S)) : ℝ) ≤ L * X ^ (ε / 2) := by
      calc
        _ ≤ 1 + Real.log (2 * S) := harmonic_floor_le_one_add_log (2 * S) h2S
        _ ≤ 1 + Real.log (X ^ κ) := by
          exact add_le_add_right (Real.log_le_log (zero_lt_one.trans_le h2S) h2SX) _
        _ ≤ L * X ^ (ε / 2) := by
          rw [Real.log_rpow hX0]
          have hl := Real.log_le_rpow_div hX0.le (show 0 < ε / 2 by positivity)
          have hp := Real.one_le_rpow hX (show 0 ≤ ε / 2 by positivity)
          calc
            _ ≤ X ^ (ε / 2) + κ * (X ^ (ε / 2) / (ε / 2)) :=
              add_le_add hp (mul_le_mul_of_nonneg_left hl hκ.le)
            _ = _ := by dsimp [L]; ring
    have hJ0 : 0 ≤ (harmonic (Nat.floor (2 * S)) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    have hcost : 576 * (divisorMaximum S H F : ℝ) ^ 5 *
        (harmonic (Nat.floor (2 * S)) : ℝ) ≤ 576 * K ^ 5 * L * X ^ ε := by
      calc
        _ ≤ 576 * (K ^ 5 * X ^ (ε / 2)) * (L * X ^ (ε / 2)) := by gcongr
        _ = 576 * K ^ 5 * L * (X ^ (ε / 2) * X ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hX0, add_halves]
    calc
      _ ≤ _ := (actual_countingNorm_bound S H F A a lambda omega eps hS hH hF
        hlambda homega heps nu hnu).1
      _ ≤ _ := by gcongr
  · rw [countingNorm_zero_of_short_H S H F A a lambda omega eps nu hH0 (lt_of_not_ge hH)]
    positivity

/-- The genuine completed physical kernel retains inverse(z), all m
and the c-unit gate. The coefficient is independent of m and c. -/
def physicalKernel (M : ℝ) (c : ℕ) (a : ℤ) (zy : ℕ × ℤ) : ℂ :=
  if c.Coprime zy.1 then
    ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0

/-- Finite source grouping uses the actual Poisson frequency, without
changing its amplitude or interchanging an unjustified infinite sum. -/
theorem physical_count_source_eq_grouped (S H F : ℝ) (A c : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (M : ℝ) :
    (∑ t ∈ sourceCarrier S H F, eps (output t)*tupleCoefficient A a lambda omega t*
      physicalKernel M c a (output t)) =
      ∑ zy ∈ (sourceCarrier S H F).image output,
        countCoefficient S H F A a lambda omega eps zy*physicalKernel M c a zy := by
  have hf := sum_fiberwise_of_maps_to (s := sourceCarrier S H F)
    (t := (sourceCarrier S H F).image output) (g := output)
    (fun t ht => mem_image_of_mem output ht)
    (fun t => eps (output t)*tupleCoefficient A a lambda omega t*
      physicalKernel M c a (output t))
  rw [← hf]
  apply sum_congr rfl
  intro zy hzy
  unfold countCoefficient
  simp only [mul_sum,sum_mul]
  apply sum_congr rfl
  intro t ht
  rw [(mem_filter.mp ht).2]

/-- The fixed-modulus square coefficient times the exact completed kernel. -/
def squarePairTerm (A c : ℕ) (a f : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M : ℝ) (u v : Inner) : ℂ :=
  if fixedUnit A a u.1 ∧ fixedUnit A a v.1 then
    (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
      physicalKernel M c a (level u v, outputY f u v)
  else 0

/-- A single fixed `c,f` weighted physical square, with its original
inverse phases, expands to all ordered completed Poisson pairs. -/
theorem physical_square_eq_completed_pairs {c : ℕ} [NeZero c] {M : ℝ}
    (hM : 0 < M) (B : Finset ℕ) (hB : ∀ b : ℕ, CommonSmoothCutoff.scaledDyadicCutoff M b ≠ 0 → b ∈ B)
    (A : ℕ) (a f : ℤ) (I : Finset Inner) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    (∑ b ∈ B, (CommonSmoothCutoff.scaledDyadicCutoff M b : ℂ) *
      (if b.Coprime c then
        ((‖ActualReciprocalSquarePoissonSourceOnly.reciprocalRow A a f b c I lambda omega‖ ^ 2 : ℝ) : ℂ)
       else 0)) =
      ∑ u ∈ I, ∑ v ∈ I, squarePairTerm A c a f lambda omega M u v := by
  rw [ActualReciprocalSquarePoissonSourceOnly.reciprocal_square_b_poisson hM B hB]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases hfixed : fixedUnit A a u.1 ∧ fixedUnit A a v.1
  · by_cases hc : c.Coprime (level u v)
    · have hgate : fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v) :=
        ⟨hfixed.1, hfixed.2, hc⟩
      rw [if_pos hgate, squarePairTerm, if_pos hfixed, physicalKernel, if_pos hc]
    · have hgate : ¬ (fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v)) :=
        fun h => hc h.2.2
      rw [if_neg hgate, squarePairTerm, if_pos hfixed, physicalKernel, if_neg hc, mul_zero]
  · have hgate : ¬ (fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ c.Coprime (level u v)) :=
      fun h => hfixed ⟨h.1, h.2.1⟩
    simp only [squarePairTerm, if_neg hgate, if_neg hfixed]

private def toSquarePair (t : Tuple) : ℕ × Inner × Inner :=
  (t.1.2.2, squareLeft t, squareRight t)

private def fromSquarePair (p : ℕ × Inner × Inner) : Tuple :=
  ((p.2.2.1, p.2.1.1, p.1), (p.2.1.2, p.2.2.2))

private theorem fromSquarePair_toSquarePair (t : Tuple) :
    fromSquarePair (toSquarePair t) = t := rfl

private theorem toSquarePair_fromSquarePair (p : ℕ × Inner × Inner) :
    toSquarePair (fromSquarePair p) = p := rfl

private theorem toSquarePair_mem_iff (S H F : ℝ) (t : Tuple) :
    toSquarePair t ∈
      (dyadicCarrier F ×ˢ ((dyadicCarrier S ×ˢ frequencyCarrier H) ×ˢ
        (dyadicCarrier S ×ˢ frequencyCarrier H))).filter
        (fun p => ActualReciprocalSquarePoissonSourceOnly.difference p.2.1 p.2.2 ≠ 0) ↔
      t ∈ sourceCarrier S H F := by
  unfold sourceCarrier
  constructor
  · intro ht
    obtain ⟨hp, hdiff⟩ := Finset.mem_filter.mp ht
    obtain ⟨hf, huv⟩ := Finset.mem_product.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨hs₂, hh₁⟩ := Finset.mem_product.mp hu
    obtain ⟨hs₁, hh₂⟩ := Finset.mem_product.mp hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hs₁, Finset.mem_product.mpr ⟨hs₂, hf⟩⟩,
          Finset.mem_product.mpr ⟨hh₁, hh₂⟩⟩,
        hdiff⟩
  · intro ht
    obtain ⟨hp, hdiff⟩ := Finset.mem_filter.mp ht
    obtain ⟨hs, hh⟩ := Finset.mem_product.mp hp
    obtain ⟨hs₁, hs₂f⟩ := Finset.mem_product.mp hs
    obtain ⟨hs₂, hf⟩ := Finset.mem_product.mp hs₂f
    obtain ⟨hh₁, hh₂⟩ := Finset.mem_product.mp hh
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨hf, Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hs₂, hh₁⟩, Finset.mem_product.mpr ⟨hs₁, hh₂⟩⟩⟩,
        hdiff⟩

/-- The actual square's nonzero signed output has exactly the ordered
counting carrier. The output multiplier may vary with `(z,y)`. -/
theorem physical_count_source_eq_nonzero_pairs (S H F : ℝ) (A c : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (M : ℝ) :
    (∑ t ∈ sourceCarrier S H F, eps (output t) * tupleCoefficient A a lambda omega t *
      physicalKernel M c a (output t)) =
      ∑ f ∈ dyadicCarrier F, ∑ u ∈ dyadicCarrier S ×ˢ frequencyCarrier H,
        ∑ v ∈ dyadicCarrier S ×ˢ frequencyCarrier H,
          if ActualReciprocalSquarePoissonSourceOnly.difference u v ≠ 0 then
            eps (level u v, outputY f u v) * squarePairTerm A c a f lambda omega M u v
          else 0 := by
  let I : Finset Inner := dyadicCarrier S ×ˢ frequencyCarrier H
  let P := (dyadicCarrier F ×ˢ (I ×ˢ I)).filter
    (fun p => ActualReciprocalSquarePoissonSourceOnly.difference p.2.1 p.2.2 ≠ 0)
  let term := fun p : ℕ × Inner × Inner =>
    eps (level p.2.1 p.2.2, outputY p.1 p.2.1 p.2.2) *
      squarePairTerm A c a p.1 lambda omega M p.2.1 p.2.2
  change _ = ∑ f ∈ dyadicCarrier F, ∑ u ∈ I, ∑ v ∈ I,
    if ActualReciprocalSquarePoissonSourceOnly.difference u v ≠ 0 then term (f,u,v) else 0
  calc
    _ = ∑ p ∈ P, term p := by
      apply sum_bij' (fun t _ => toSquarePair t) (fun p _ => fromSquarePair p)
      · intro t ht
        exact (toSquarePair_mem_iff S H F t).mpr ht
      · intro p hp
        exact (toSquarePair_mem_iff S H F (fromSquarePair p)).mp
          (by rwa [toSquarePair_fromSquarePair])
      · intro t _
        exact fromSquarePair_toSquarePair t
      · intro p _
        exact toSquarePair_fromSquarePair p
      · intro t _
        rw [output_eq_actual_square_output t]
        have hgate : (fixedUnit A a t.1.1 ∧ fixedUnit A a t.1.2.1) ↔
            (fixedUnit A a (squareLeft t).1 ∧ fixedUnit A a (squareRight t).1) :=
          and_comm
        simp only [term, toSquarePair, squarePairTerm, tupleCoefficient, hgate]
        split_ifs <;> simp only [mul_assoc, mul_zero, zero_mul]
    _ = _ := by
      simp only [P, sum_filter, sum_product]

/-- On the positive dyadic `f` block, the original physical squares split
into a separate zero-difference sum and the grouped complex (23) source. -/
theorem physical_square_sum_eq_zero_add_countCoefficient {c : ℕ} [NeZero c]
    (S H F : ℝ) (A : ℕ) (a : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    {M : ℝ} (hM : 0 < M) (B : Finset ℕ)
    (hB : ∀ b : ℕ, CommonSmoothCutoff.scaledDyadicCutoff M b ≠ 0 → b ∈ B) :
    (∑ f ∈ dyadicCarrier F, ∑ b ∈ B, (CommonSmoothCutoff.scaledDyadicCutoff M b : ℂ) *
      (if b.Coprime c then
        ((‖ActualReciprocalSquarePoissonSourceOnly.reciprocalRow A a f b c
            (dyadicCarrier S ×ˢ frequencyCarrier H) lambda omega‖ ^ 2 : ℝ) : ℂ)
       else 0)) =
      (∑ f ∈ dyadicCarrier F, ∑ u ∈ dyadicCarrier S ×ˢ frequencyCarrier H,
        ∑ v ∈ dyadicCarrier S ×ˢ frequencyCarrier H,
          if ActualReciprocalSquarePoissonSourceOnly.difference u v = 0 then
            squarePairTerm A c a f lambda omega M u v else 0) +
      ∑ zy ∈ (sourceCarrier S H F).image output,
        countCoefficient S H F A a lambda omega (fun _ => 1) zy * physicalKernel M c a zy := by
  let I : Finset Inner := dyadicCarrier S ×ˢ frequencyCarrier H
  rw [← physical_count_source_eq_grouped S H F A c a lambda omega (fun _ => 1) M,
    physical_count_source_eq_nonzero_pairs S H F A c a lambda omega (fun _ => 1) M]
  have hsplit (f : ℕ) (u v : Inner) :
      squarePairTerm A c a f lambda omega M u v =
        (if ActualReciprocalSquarePoissonSourceOnly.difference u v = 0 then
          squarePairTerm A c a f lambda omega M u v else 0) +
        (if ActualReciprocalSquarePoissonSourceOnly.difference u v ≠ 0 then
          squarePairTerm A c a f lambda omega M u v else 0) := by
    by_cases h : ActualReciprocalSquarePoissonSourceOnly.difference u v = 0 <;> simp [h]
  simp only [one_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro f _
  rw [physical_square_eq_completed_pairs hM B hB A a f I lambda omega]
  apply sum_congr rfl
  intro u _
  exact sum_congr rfl (fun v _ => hsplit f u v)

end
end ImbalancedChen.Part3.OriginalSignedCountingNorm20261028
