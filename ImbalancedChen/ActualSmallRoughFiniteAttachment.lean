import ImbalancedChen.FiniteUpperCarrierCore

/-! Uncompiled verbatim finite-attachment extraction candidate; no formal credit. -/
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

end
end ImbalancedChen
