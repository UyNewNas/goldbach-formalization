import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.SmallRoughMainTerm
import ImbalancedChen.ActualSmallRosserDensity
import ImbalancedChen.SmallRoughDensityError

/-!
# The actual small weights attached to fixed rough coefficients

The resulting physical coefficient is fixed before the integer argument is
evaluated. Its pointwise majorant and one-bound use proved properties of
the literal Rosser weights and odd-first-exit tree; neither property is an
input hypothesis. The retention policy remains a parameter: the current
manuscript's causal caps, density constant, and distribution theorem are
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

/-- Literal indicator for the rough interval, including its lower endpoint. -/
def actualIntervalRoughIndicator (N : ℕ) (w z : ℝ) (n : ℤ) : ℝ := by
  classical
  exact if ∀ p : ℕ, (p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) →
    ¬(p : ℤ) ∣ n then 1 else 0

theorem actualSmallRoughIndicator_nonneg (N : ℕ) (w : ℝ) (n : ℤ) :
    0 ≤ actualSmallRoughIndicator N w n := by
  unfold actualSmallRoughIndicator
  split <;> norm_num

/-- The two half-open prime ranges partition all primes below the upper cutoff. -/
theorem actualSmallRoughIndicator_mul_interval
    (N : ℕ) (w z : ℝ) (hwz : w ≤ z) (n : ℤ) :
    actualSmallRoughIndicator N w n * actualIntervalRoughIndicator N w z n =
      actualSmallRoughIndicator N z n := by
  classical
  have hsplit :
      (∀ p : ℕ, p.Prime ∧ ¬p ∣ N ∧ (p : ℝ) < z → ¬(p : ℤ) ∣ n) ↔
        (∀ p : ℕ, p.Prime ∧ ¬p ∣ N ∧ (p : ℝ) < w → ¬(p : ℤ) ∣ n) ∧
        (∀ p : ℕ, p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z →
          ¬(p : ℤ) ∣ n) := by
    constructor
    · intro h
      exact ⟨fun p hp => h p ⟨hp.1, hp.2.1, hp.2.2.trans_le hwz⟩,
        fun p hp => h p ⟨hp.1, hp.2.1, hp.2.2.2⟩⟩
    · rintro ⟨hs, hr⟩ p hp
      by_cases hw : (p : ℝ) < w
      · exact hs p ⟨hp.1, hp.2.1, hw⟩
      · exact hr p ⟨hp.1, hp.2.1, le_of_not_gt hw, hp.2.2⟩
  unfold actualSmallRoughIndicator actualIntervalRoughIndicator
  rw [hsplit]
  split <;> split <;> simp_all

/-- The displayed physical modulus support for the actual small/rough pair. -/
def actualSmallRoughModuli (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w)
    (fixedRoughSupport retainOdd N cap w z)

/-- One physical coefficient, independent of the integer at which it is tested. -/
def actualSmallRoughRho (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (fixedRoughSupport retainOdd N cap w z)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

theorem actualSmallRoughModuli_squarefree
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallRoughModuli retainOdd N cap w z) : Squarefree q := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  exact (Nat.squarefree_mul (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb))).mpr
    ⟨actualSmallRosserSupport_squarefree N cap w ha,
      fixedRoughSupport_squarefree retainOdd N cap w z hb⟩

theorem actualSmallRoughModuli_coprime_target
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallRoughModuli retainOdd N cap w z) : q.Coprime N := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
  exact (actualSmallRosserSupport_coprime_target N cap w
    (Finset.mem_product.mp hab).1).mul_left
      (fixedRoughSupport_coprime_target retainOdd N cap w z
        (Finset.mem_product.mp hab).2)

/-- The concrete attachment majorizes the full presieving indicator, on all
integers including zero, without abstract lower/upper-weight premises. -/
theorem actualSmallRoughRho_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n.natAbs := by
  have hsmall := actualSmallRosser_sandwich N cap w L hL hwL (hwz.trans hzcap) n
  have hrough := roughIndicator_le_fixedRoughDivisorSum retainOdd N cap w z hzcap n
  have h := productTarget_le_signSensitiveAttachment
    (fixedRoughSupport retainOdd N cap w z)
    (fixedRoughCoefficient retainOdd N cap w z) n.natAbs
    (actualSmallRoughIndicator_nonneg N w n) hrough hsmall.1 hsmall.2
  change actualSmallRoughIndicator N w n * actualIntervalRoughIndicator N w z n ≤ _ at h
  rw [actualSmallRoughIndicator_mul_interval N w z hwz n] at h
  have heq := signSensitiveAttachment_eq_smallRough_physicalDivisorSum
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) n.natAbs
  exact h.trans_eq heq

/-- Nonnegativity also holds at zero and at all composite test arguments. -/
theorem actualSmallRoughRho_divisorSum_nonneg
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    0 ≤ physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L) n.natAbs :=
  (actualSmallRoughIndicator_nonneg N z n).trans
    (actualSmallRoughRho_majorant retainOdd N cap w z L hL hwL hwz hzcap n)

/-- The physical coefficient is one-bounded, with no multiplicity factor. -/
theorem actualSmallRoughRho_abs_le_one
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    |actualSmallRoughRho retainOdd N cap w z L q| ≤ 1 := by
  classical
  by_cases hq : q ∈ actualSmallRoughModuli retainOdd N cap w z
  · rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
    have ha := (Finset.mem_product.mp hab).1
    have hb := (Finset.mem_product.mp hab).2
    exact abs_smallRoughRho_mul_le_one
      (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
      (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
      (fun d _ => fixedRoughCoefficient_abs_le_one retainOdd N cap w z d)
      (fun d _ => actualSmallRosserMinus_abs_le_one N cap w L d)
      (fun d _ => actualSmallRosserPlus_abs_le_one N cap w L d) ha hb
  · have hz := smallRoughRho_eq_zero_of_not_mem
      (actualSmallRosserSupport N cap w) (fixedRoughSupport retainOdd N cap w z)
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) hq
    change |smallRoughRho _ _ _ _ _ q| ≤ 1
    rw [hz]
    norm_num

/-- A nonzero physical coefficient has a unique-type small/rough product
with small factor strictly below its level. The displayed divisor carrier
may contain zero coefficients above the level; no such term is active. -/
theorem actualSmallRoughRho_ne_zero_factors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho retainOdd N cap w z L q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ b ∈ fixedRoughSupport retainOdd N cap w z,
        q = a * b ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient retainOdd N cap w z b ≠ 0 := by
  classical
  have hmem : q ∈ actualSmallRoughModuli retainOdd N cap w z := by
    by_contra hnot
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot)
  rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hprod⟩
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have hvalue := smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) ha hb
  have hp : smallRoughPairCoefficient (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) (a, b) ≠ 0 := by
    rw [← hvalue, hprod]
    exact hq
  unfold smallRoughPairCoefficient signAttachedCoefficient at hp
  have hc := (mul_ne_zero_iff.mp hp).1
  have hbeta := (mul_ne_zero_iff.mp hp).2
  refine ⟨a, ha, b, hb, hprod.symm, ?_, hc⟩
  by_cases hsign : 0 ≤ fixedRoughCoefficient retainOdd N cap w z b
  · rw [if_pos hsign] at hbeta
    exact (actualSmallRosserPlus_active hbeta).2.1
  · rw [if_neg hsign] at hbeta
    exact (actualSmallRosserMinus_active hbeta).2.1

/-- The density of this very same coefficient factors into the actual two
small-weight densities. This is an identity, not yet the sharp K bound. -/
theorem actualSmallRoughRho_density_eq
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) =
      signSensitiveReciprocalTotientDensity
        (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z)
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserMinus N cap w L))
        (reciprocalTotientDensity (actualSmallRosserSupport N cap w)
          (actualSmallRosserPlus N cap w L)) :=
  physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

/-- The genuine small-weight density supplier controls the density error
of the actual physical coefficient, uniformly in the even target and
retention policy. The absolute rough mass remains visible: this does not
claim the sharp complete density constant of the current manuscript. -/
theorem exists_actualSmallRoughRho_density_error :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
          ∀ N cap : ℕ, Even N → ∀ (retainOdd : List ℕ → Bool) (z : ℝ),
            let w := D ^ (epsilon ^ 2)
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let E := actualSmallRosserDensityError C K D epsilon
            let S := fixedRoughSupport retainOdd N cap w z
            let c := fixedRoughCoefficient retainOdd N cap w z
            let density := physicalDensitySum
              (actualSmallRoughModuli retainOdd N cap w z)
              (actualSmallRoughRho retainOdd N cap w z L)
            0 ≤ density - V * reciprocalTotientDensity S c ∧
              density - V * reciprocalTotientDensity S c ≤
                (V * E) * reciprocalTotientDensity S (fun d => |c d|) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D₀, hD₀, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD N cap hN retainOdd z
  have h := hsupply D hD N cap hN
  dsimp only at h ⊢
  apply physicalDensitySum_smallRoughRho_error
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap _ z hd)
    (fixedRoughCoefficient retainOdd N cap _ z)
    (actualSmallRosserMinus N cap _ _) (actualSmallRosserPlus N cap _ _)
  · simpa only [mul_sub, mul_one, actualSmallRosserMinusDensity] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · simpa only [mul_add, mul_one, actualSmallRosserPlusDensity] using h.2.2.2.1

end

end ImbalancedChen
