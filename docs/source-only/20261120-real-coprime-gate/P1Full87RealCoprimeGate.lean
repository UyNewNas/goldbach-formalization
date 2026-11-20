import ImbalancedChen.P1Full87RealPrimitiveTail
import ImbalancedChen.RealPhysicalUpperWeightBridge
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
One REAL, strict presieve endpoint for the original RAW/LICENSED
full87 physical delta and the unaltered real half-product source.

The generic natural-cap gate in RealPhysicalUpperWeightBridge asks for
  (Nat.ceil z : ℝ) ≤ T ^ (b/(1+b)).
Here the actual small-prime support is p < z, which is exactly
p < Nat.ceil z for integral p.  Hence the real cutoff inequality
  z ≤ T ^ (b/(1+b))
suffices without a spurious one-unit rounding payment.
The corrected exact-coprime source mass then eliminates the ENTIRE
coprime correction of the SAME signed physical coefficient. Its
primitive distribution error remains unpaid. No upper majorant is
inferred for the signed difference.

The gate is an explicit pending physical-source parameter obligation,
not an assertion that the frozen manuscript already installs it.
No new axiom, analytic input, sorry/admit, native_decide or unsafe.
-/

namespace ImbalancedChen.P1Full87RealCoprimeGate

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaRho)

/-- The real endpoint z (not its integer ceiling) is sufficient:
the original half-product source has no prime factor below or at
the real roughness threshold, while the sieve primes are strictly
below z. The integer ceiling is used only to represent that SAME
strict prime set in a Finset. -/
private theorem source_coprime_of_real_endpoint
    {b T z : ℝ} {N m d : ℕ}
    (hb : 0 < b) (hT : 0 < T)
    (hgate : z ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T)
    (hd : d ∣ sieveProduct N (Nat.ceil z)) :
    Nat.Coprime m d := by
  have hsource : Nat.Coprime m (sieveProduct N (Nat.ceil z)) := by
    classical
    unfold sieveProduct
    apply Nat.coprime_prod_right_iff.mpr
    intro ell hell
    obtain ⟨hellz, hp, _⟩ := mem_sievePrimes.mp hell
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hdiv
    have hrough : T ^ (b / (1 + b)) < (ell : ℝ) :=
      realHalfProductSource_prime_divisor_rough hb hT hm hp hdiv
    have hsmall : (ell : ℝ) < z := Nat.lt_ceil.mp hellz
    exact (not_lt_of_ge (hsmall.le.trans hgate)) hrough
  exact hsource.of_dvd_right hd

/-- Exact equality, not an approximate equidistribution claim:
the original real source is coprime to every supported sieve modulus
under the literal REAL endpoint gate. -/
private theorem real_coprime_mass_eq_card_of_real_endpoint
    {b T z : ℝ} {N d : ℕ}
    (hb : 0 < b) (hT : 0 < T)
    (hgate : z ≤ T ^ (b / (1 + b)))
    (hd : d ∣ sieveProduct N (Nat.ceil z)) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ) := by
  classical
  have hfilter :
      (realHalfProductSource b N T).filter
        (fun m => Nat.Coprime m d) = realHalfProductSource b N T := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact source_coprime_of_real_endpoint hb hT hgate hm hd
  rw [realHalfProductCoprimeMass, hfilter]

/-- A genuine full87 RAW/LICENSED instance. Both policies use the
original small/rough physical supports, with ALL moduli retained.
Each supported d divides the same actual strict-real-cutoff sieve
product; therefore no signed coprime correction survives.
Neither individual policy is replaced by the difference as a
positive upper majorant. -/
theorem actual_full87_delta_real_coprime_correction_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℝ) (N cap : ℕ) (w z L T : ℝ)
    (hb : 0 < b) (hT : 0 < T) (hwz : w ≤ z)
    (hgate : z ≤ T ^ (b / (1 + b))) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    realPhysicalCoprimeCorrection b N T Q rho = 0 := by
  dsimp only
  classical
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let Q := actualSmallRoughModuli (S false) N cap w z ∪
    actualSmallRoughModuli (R false) N cap w z
  let rho := trueDDeltaRho (R false) (S false) N cap w z L
  have hsupport :
      ∀ d ∈ Q, d ∣ sieveProduct N (Nat.ceil z) := by
    intro d hd
    rcases Finset.mem_union.mp hd with hs | hr
    · exact actualSmallRoughModuli_dvd_sieveProduct_ceil
        (S false) N cap w z hwz hs
    · exact actualSmallRoughModuli_dvd_sieveProduct_ceil
        (R false) N cap w z hwz hr
  unfold realPhysicalCoprimeCorrection
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hzero : rho d = 0
  · simp only [hzero, zero_mul]
  · have hmass :
        realHalfProductCoprimeMass b N T d =
          ((realHalfProductSource b N T).card : ℝ) :=
      real_coprime_mass_eq_card_of_real_endpoint hb hT hgate (hsupport d hd)
    rw [hmass]
    simp

/-- Conditional exact single-source assembly, with the genuine
low-physical-d cutoff, the genuine RAW/LICENSED physical difference,
and no coprime correction. The accompanying absolute invoice contains
only the HIGH-d primitive distribution discrepancy, paid ONCE. It
is not asserted to be o(H_N), and this is NOT a final PP license. -/
theorem actual_full87_real_receiver_high_only_primitive
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℝ) (N cap : ℕ) (w z L T : ℝ)
    (hw : 1 ≤ w) (hwz : w ≤ z)
    (hb : 0 < b) (hT : 0 < T)
    (hgate : z ≤ T ^ (b / (1 + b))) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
        ((realHalfProductSource b N T).card : ℝ) *
          physicalDensitySum high rho +
        realPhysicalDistributionError b N T high rho ∧
    |(∑ m ∈ realHalfProductSource b N T,
         physicalDivisorSum Q rho (N - m)) -
       ((realHalfProductSource b N T).card : ℝ) *
         physicalDensitySum high rho| ≤
      ∑ d ∈ high,
        |realHalfProductCongruenceMass b N T d -
          realHalfProductCoprimeMass b N T d /
            (Nat.totient d : ℝ)| := by
  dsimp only
  classical
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let Q := actualSmallRoughModuli (S false) N cap w z ∪
    actualSmallRoughModuli (R false) N cap w z
  let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
  let rho := trueDDeltaRho (R false) (S false) N cap w z L
  have hthree :=
    P1Full87RealPrimitiveTail.actual_full87_real_primitive_three_books_high_only
      delta n e q om b N cap w z L T hw
  have hreceiver :=
    P1Full87RealPrimitiveTail.actual_full87_real_receiver_high_three_books
      delta n e q om b N cap w z L T hw
  have hzero := actual_full87_delta_real_coprime_correction_zero
    delta n e q om b N cap w z L T hb hT hwz hgate
  dsimp only at hthree hreceiver hzero
  rcases hthree with ⟨_, hcop, hdist, hprimitive⟩
  have hhighzero :
      realPhysicalCoprimeCorrection b N T high rho = 0 := by
    rw [← hcop]
    exact hzero
  rw [hhighzero] at hreceiver
  simp only [add_zero] at hreceiver
  constructor
  · exact hreceiver
  · calc
      |(∑ m ∈ realHalfProductSource b N T,
            physicalDivisorSum Q rho (N - m)) -
          ((realHalfProductSource b N T).card : ℝ) *
            physicalDensitySum high rho| =
          |realPhysicalDistributionError b N T high rho| := by
            rw [hreceiver]
            congr 1
            ring
      _ ≤ ∑ d ∈ high,
          |realHalfProductCongruenceMass b N T d -
            realHalfProductCoprimeMass b N T d /
              (Nat.totient d : ℝ)| := by
        rw [← hdist]
        exact hprimitive

end
end ImbalancedChen.P1Full87RealCoprimeGate
