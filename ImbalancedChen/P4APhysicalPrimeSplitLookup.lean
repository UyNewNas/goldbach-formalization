import ImbalancedChen.P4APhysicalMoebiusLookup

/-!
SOURCEONLY / UNCOMPILED. Canonical factors are literal products of q's
prime factors below w and at least w. On the actual physical modulus
support, squarefreeness reconstructs q and separated-support uniqueness
identifies these products with the actual occupied pair. The resulting
lookup uses the provider's original upper/lower admissibility predicates,
selected by the Mobius sign of the canonical rough factor.
-/

namespace ImbalancedChen.P4APhysicalPrimeSplitLookup

noncomputable section
open scoped Classical BigOperators
open P4APhysicalMoebiusLookup P4ARetainedSupportDifferenceMass

def smallPart (w : ℝ) (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => (p : ℝ) < w), p

def roughPart (w : ℝ) (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => w ≤ (p : ℝ)), p

theorem smallPart_primeFactors (w : ℝ) (q : ℕ) :
    (smallPart w q).primeFactors = q.primeFactors.filter (fun p => (p : ℝ) < w) := by
  have hprime : ∀ p ∈ q.primeFactors.filter (fun p => (p : ℝ) < w), Nat.Prime p :=
    fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  simpa only [smallPart, id_eq] using Nat.primeFactors_prod hprime

theorem roughPart_primeFactors (w : ℝ) (q : ℕ) :
    (roughPart w q).primeFactors = q.primeFactors.filter (fun p => w ≤ (p : ℝ)) := by
  have hprime : ∀ p ∈ q.primeFactors.filter (fun p => w ≤ (p : ℝ)), Nat.Prime p :=
    fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  simpa only [roughPart, id_eq] using Nat.primeFactors_prod hprime

theorem smallPart_smallPrimeSupportedAt (w : ℝ) (q : ℕ) :
    SmallPrimeSupportedAt w (smallPart w q) := by
  constructor
  · unfold smallPart
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  · intro p hp
    rw [smallPart_primeFactors] at hp
    exact (Finset.mem_filter.mp hp).2

theorem roughPart_roughPrimeSupportedAt (w : ℝ) (q : ℕ) :
    RoughPrimeSupportedAt w (roughPart w q) := by
  constructor
  · unfold roughPart
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero)
  · intro p hp
    rw [roughPart_primeFactors] at hp
    exact (Finset.mem_filter.mp hp).2

/-- The strict/inclusive cutoff is a literal partition, including p=w. -/
theorem smallPart_mul_roughPart {q : ℕ} (hq : Squarefree q) (w : ℝ) :
    smallPart w q * roughPart w q = q := by
  have hfilter : q.primeFactors.filter (fun p => w ≤ (p : ℝ)) =
      q.primeFactors.filter (fun p => ¬(p : ℝ) < w) := by
    ext p
    simp only [Finset.mem_filter, not_lt]
  unfold smallPart roughPart
  rw [hfilter, Finset.prod_filter_mul_prod_filter_not,
    Nat.prod_primeFactors_of_squarefree hq]

/-- The canonical prime split is the actual occupied small/rough pair. -/
theorem canonical_pair_eq_occupied_pair
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {a b : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    (smallPart w (a * b), roughPart w (a * b)) = (a, b) := by
  have hmem : a * b ∈ actualSmallRoughModuli retainOdd N cap w z := by
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  exact smallRough_factorization_unique
    (smallPart_smallPrimeSupportedAt w (a * b)) (roughPart_roughPrimeSupportedAt w (a * b))
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb)
    (smallPart_mul_roughPart (actualSmallRoughModuli_squarefree retainOdd N cap w z hmem) w)

/-- No existential factor is left in this actual factorization interface. -/
theorem canonical_actual_factorization
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallRoughModuli retainOdd N cap w z) :
    smallPart w q ∈ actualSmallRosserSupport N cap w ∧
      roughPart w q ∈ fixedRoughSupport retainOdd N cap w z ∧
        smallPart w q * roughPart w q = q := by
  rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, hab, rfl⟩
  have ha := (Finset.mem_product.mp hab).1
  have hb := (Finset.mem_product.mp hab).2
  have hpair := canonical_pair_eq_occupied_pair retainOdd N cap w z ha hb
  have hsmall : smallPart w (a * b) = a := congrArg Prod.fst hpair
  have hrough : roughPart w (a * b) = b := congrArg Prod.snd hpair
  rw [hsmall, hrough]
  exact ⟨ha, hb, rfl⟩

/-- The selected original small Rosser admission test, with the original
strict small level. The sign is the literal rough Mobius coefficient. -/
def selectedSmallAdmission (L : ℝ) (a b : ℕ) : Prop :=
  (a : ℝ) < L ∧
    if 0 ≤ (ArithmeticFunction.moebius b : ℝ) then
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L a.primeFactors
    else MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet L a.primeFactors

def canonicalSmallAdmission (w L : ℝ) (q : ℕ) : Prop :=
  selectedSmallAdmission L (smallPart w q) (roughPart w q)

theorem actualMinus_eq_admission_lookup (N cap : ℕ) (w L : ℝ) {a : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w) :
    actualSmallRosserMinus N cap w L a =
      if (a : ℝ) < L ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet L a.primeFactors
      then (ArithmeticFunction.moebius a : ℝ) else 0 := by
  have hraw : actualSmallRosserMinus N cap w L a =
      if (a : ℝ) < L ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet L a.primeFactors
      then (-1 : ℝ) ^ a.primeFactors.card else 0 := by
    change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight
      (actualSmallPrimeProduct N cap w) L a = _
    rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_apply]
    simp only [show a ∈ (actualSmallPrimeProduct N cap w).divisors from ha, true_and]
  by_cases hadm : (a : ℝ) < L ∧
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet L a.primeFactors
  · rw [if_pos hadm]
    apply actualMinus_eq_moebius_of_ne_zero N cap w L
    rw [hraw, if_pos hadm]
    exact pow_ne_zero _ (by norm_num)
  · simp only [hraw, if_neg hadm]

theorem actualPlus_eq_admission_lookup (N cap : ℕ) (w L : ℝ) {a : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w) :
    actualSmallRosserPlus N cap w L a =
      if (a : ℝ) < L ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L a.primeFactors
      then (ArithmeticFunction.moebius a : ℝ) else 0 := by
  have hraw : actualSmallRosserPlus N cap w L a =
      if (a : ℝ) < L ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L a.primeFactors
      then (-1 : ℝ) ^ a.primeFactors.card else 0 := by
    change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N cap w) L a = _
    rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply]
    simp only [show a ∈ (actualSmallPrimeProduct N cap w).divisors from ha, true_and]
  by_cases hadm : (a : ℝ) < L ∧
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L a.primeFactors
  · rw [if_pos hadm]
    apply actualPlus_eq_moebius_of_ne_zero N cap w L
    rw [hraw, if_pos hadm]
    exact pow_ne_zero _ (by norm_num)
  · simp only [hraw, if_neg hadm]

/-- An actual occupied pair has the original selected-admission lookup. -/
theorem actualRho_mul_eq_admission_lookup
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {a b : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    actualSmallRoughRho retainOdd N cap w z L (a * b) =
      if selectedSmallAdmission L a b then (ArithmeticFunction.moebius (a * b) : ℝ) else 0 := by
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb)
  have hmu : (ArithmeticFunction.moebius b : ℝ) * (ArithmeticFunction.moebius a : ℝ) =
      (ArithmeticFunction.moebius (a * b) : ℝ) := by
    have hmul : (ArithmeticFunction.moebius (a * b) : ℝ) =
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
      simpa only [Int.cast_mul] using congrArg (fun n : ℤ => (n : ℝ))
        (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop)
    exact (mul_comm _ _).trans hmul.symm
  rw [actualRho_mul_eq_signSensitive_lookup retainOdd N cap w z L ha hb]
  simp only [coefficient_eq_moebius_indicator, if_pos hb]
  by_cases hsign : 0 ≤ (ArithmeticFunction.moebius b : ℝ)
  · rw [if_pos hsign, actualPlus_eq_admission_lookup N cap w L ha]
    simp only [selectedSmallAdmission, if_pos hsign]
    split_ifs <;> simp only [mul_zero] <;> exact hmu
  · rw [if_neg hsign, actualMinus_eq_admission_lookup N cap w L ha]
    simp only [selectedSmallAdmission, if_neg hsign]
    split_ifs <;> simp only [mul_zero] <;> exact hmu

/-- Complete canonical lookup on the actual physical support. The small
and rough factors are now explicit functions of q, with no pair witness. -/
theorem actualRho_eq_canonical_admission_lookup
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ actualSmallRoughModuli retainOdd N cap w z) :
    actualSmallRoughRho retainOdd N cap w z L q =
      if canonicalSmallAdmission w L q then (ArithmeticFunction.moebius q : ℝ) else 0 := by
  obtain ⟨ha, hb, hprod⟩ := canonical_actual_factorization retainOdd N cap w z hq
  have hlookup := actualRho_mul_eq_admission_lookup retainOdd N cap w z L ha hb
  simpa only [canonicalSmallAdmission, hprod] using hlookup

/-- Total formula, with the exact original displayed-support guard and the
literal canonical prime-split Rosser tests. It is not an abstract mask. -/
theorem actualRho_eq_total_canonical_lookup
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualSmallRoughRho retainOdd N cap w z L q =
      if q ∈ actualSmallRoughModuli retainOdd N cap w z ∧ canonicalSmallAdmission w L q
      then (ArithmeticFunction.moebius q : ℝ) else 0 := by
  by_cases hq : q ∈ actualSmallRoughModuli retainOdd N cap w z
  · simpa only [hq, true_and] using actualRho_eq_canonical_admission_lookup retainOdd N cap w z L hq
  · have hzero : actualSmallRoughRho retainOdd N cap w z L q = 0 :=
      smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq
    simp only [hq, false_and, if_false, hzero]

/-- The same explicit lookup for the actual compact third upper policy. -/
theorem actualCompactThirdRho_eq_total_canonical_lookup
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L q =
      if q ∈ actualSmallRoughModuli (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∧
        canonicalSmallAdmission w L q then (ArithmeticFunction.moebius q : ℝ) else 0 := by
  exact actualRho_eq_total_canonical_lookup (actualExtendedThirdCompactUpperPolicy e h m N false)
    N cap w z L q

end
end ImbalancedChen.P4APhysicalPrimeSplitLookup
