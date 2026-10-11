import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.FixedEvenRoughCoefficients
import ImbalancedChen.LowerSmallRoughDensityError

/-!
# One actual lower physical coefficient

The even-first-exit rough coefficient is fixed before any integer is tested.
Its nonnegative coefficients select the actual lower small Rosser weight;
its negative coefficients select the actual upper weight. The unique
small/rough factorization defines one physical coefficient, used in both
the pointwise minorant and the density-loss theorem. No lower polynomial
is assumed nonnegative, and integer zero is included.

The policy is still arbitrary: the manuscript's cap/box policy, its support
exponent and its signed distribution theorem remain separate obligations.
-/

namespace ImbalancedChen

noncomputable section

def actualLowerSmallRoughModuli (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w)
    (fixedEvenRoughSupport retainEven N cap w z)

def actualLowerSmallRoughRho (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (fixedEvenRoughSupport retainEven N cap w z)
    (fixedEvenRoughCoefficient retainEven N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)

theorem actualLowerSmallRoughModuli_squarefree
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualLowerSmallRoughModuli retainEven N cap w z) : Squarefree q := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  exact (Nat.squarefree_mul (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hb))).mpr
      ⟨actualSmallRosserSupport_squarefree N cap w ha,
        fixedEvenRoughSupport_squarefree retainEven N cap w z hb⟩

theorem actualLowerSmallRoughModuli_coprime_target
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualLowerSmallRoughModuli retainEven N cap w z) : q.Coprime N := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
  exact (actualSmallRosserSupport_coprime_target N cap w
    (Finset.mem_product.mp hab).1).mul_left
      (fixedEvenRoughSupport_coprime_target retainEven N cap w z
        (Finset.mem_product.mp hab).2)

/-- The same fixed lower coefficient minorizes the actual full prime
indicator at every integer, without a positivity assumption on beta-minus. -/
theorem actualLowerSmallRoughRho_minorant
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    physicalDivisorSum (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualLowerSmallRoughRho retainEven N cap w z L) n.natAbs ≤
      actualSmallRoughIndicator N z n := by
  have hsmall := actualSmallRosser_sandwich N cap w L hL hwL (hwz.trans hzcap) n
  have hrough := fixedEvenRoughDivisorSum_le_roughIndicator
    retainEven N cap w z hzcap n
  have h := physicalDivisorSum_smallRoughRho_lower
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hd)
    (fixedEvenRoughCoefficient retainEven N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) n.natAbs
    (actualSmallRoughIndicator_nonneg N w n) hrough hsmall.1 hsmall.2
  change _ ≤ actualSmallRoughIndicator N w n * actualIntervalRoughIndicator N w z n at h
  rw [actualSmallRoughIndicator_mul_interval N w z hwz n] at h
  exact h

theorem actualLowerSmallRoughRho_abs_le_one
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualLowerSmallRoughRho retainEven N cap w z L q| ≤ 1 := by
  classical
  by_cases hq : q ∈ actualLowerSmallRoughModuli retainEven N cap w z
  · rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    exact abs_smallRoughRho_mul_le_one
      (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hd)
      (fixedEvenRoughCoefficient retainEven N cap w z)
      (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)
      (fun d _ => fixedEvenRoughCoefficient_abs_le_one retainEven N cap w z d)
      (fun d _ => actualSmallRosserPlus_abs_le_one N cap w L d)
      (fun d _ => actualSmallRosserMinus_abs_le_one N cap w L d) ha hb
  · have hz := smallRoughRho_eq_zero_of_not_mem
      (actualSmallRosserSupport N cap w) (fixedEvenRoughSupport retainEven N cap w z)
      (fixedEvenRoughCoefficient retainEven N cap w z)
      (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) hq
    change |smallRoughRho _ _ _ _ _ q| ≤ 1
    rw [hz]
    norm_num

/-- Active physical moduli have an actual small factor strictly below its
level. No support exponent is inferred for the unrestricted rough policy. -/
theorem actualLowerSmallRoughRho_ne_zero_factors
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualLowerSmallRoughRho retainEven N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedEvenRoughSupport retainEven N cap w z,
        q = a * b ∧ (a : ℝ) < L ∧
          fixedEvenRoughCoefficient retainEven N cap w z b ≠ 0 := by
  classical
  have hmem : q ∈ actualLowerSmallRoughModuli retainEven N cap w z := by
    by_contra hnot
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot)
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hprod⟩
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have hvalue := smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hd)
    (fixedEvenRoughCoefficient retainEven N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) ha hb
  have hp : smallRoughPairCoefficient (fixedEvenRoughCoefficient retainEven N cap w z)
      (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) (a, b) ≠ 0 := by
    rw [← hvalue, hprod]
    exact hq
  unfold smallRoughPairCoefficient signAttachedCoefficient at hp
  have hc := (mul_ne_zero_iff.mp hp).1
  have hbeta := (mul_ne_zero_iff.mp hp).2
  refine ⟨a, ha, b, hb, hprod.symm, ?_, hc⟩
  by_cases hsign : 0 ≤ fixedEvenRoughCoefficient retainEven N cap w z b
  · rw [if_pos hsign] at hbeta
    exact (actualSmallRosserMinus_active hbeta).2.1
  · rw [if_neg hsign] at hbeta
    exact (actualSmallRosserPlus_active hbeta).2.1

theorem actualLowerSmallRoughRho_density_eq
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualLowerSmallRoughRho retainEven N cap w z L) =
      signSensitiveReciprocalTotientDensity
        (fixedEvenRoughSupport retainEven N cap w z)
        (fixedEvenRoughCoefficient retainEven N cap w z)
        (actualSmallRosserPlusDensity N cap w L)
        (actualSmallRosserMinusDensity N cap w L) :=
  physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hd)
    (fixedEvenRoughCoefficient retainEven N cap w z)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)

/-- The actual small-weight supplier controls the loss of this same lower
physical coefficient, uniformly in the even target and retention policy. -/
theorem exists_actualLowerSmallRoughRho_density_error :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, Even N → ∀ (retainEven : List ℕ → Bool) (z : ℝ),
            let w := D ^ (epsilon ^ 2)
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let E := actualSmallRosserDensityError C K D epsilon
            let S := fixedEvenRoughSupport retainEven N cap w z
            let c := fixedEvenRoughCoefficient retainEven N cap w z
            let density := physicalDensitySum
              (actualLowerSmallRoughModuli retainEven N cap w z)
              (actualLowerSmallRoughRho retainEven N cap w z L)
            0 ≤ V * reciprocalTotientDensity S c - density ∧
              V * reciprocalTotientDensity S c - density ≤
                (V * E) * reciprocalTotientDensity S (fun d => |c d|) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D₀, hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hN retainEven z
  have h := hsupply D hD N cap hN
  dsimp only at h ⊢
  apply physicalDensitySum_smallRoughRho_lower_error
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    (fun _ hd => fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap _ z hd)
    (fixedEvenRoughCoefficient retainEven N cap _ z)
    (actualSmallRosserMinus N cap _ _) (actualSmallRosserPlus N cap _ _)
  · simpa only [mul_sub, mul_one, actualSmallRosserMinusDensity] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · simpa only [mul_add, mul_one, actualSmallRosserPlusDensity] using h.2.2.2.1

end

end ImbalancedChen
