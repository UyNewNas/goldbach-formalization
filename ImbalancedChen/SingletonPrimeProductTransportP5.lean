import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.CurrentChenOriginalLowerFiniteP5

/-! Source-only, uncompiled. Exact b=1 / rank-one dictionary between the
literal Part3 labelled prime-product error and the original prime source.
The label is a prime; the multiplier b=1 is not inserted as a fake prime.
No analytic licence or signed distribution estimate is asserted here. -/

namespace ImbalancedChen.P5S1SingletonPP

noncomputable section

open Filter
open scoped BigOperators
open Part3
open P5S1OriginalLower

/-- A rank-one source weight is fixed before any modulus is summed. -/
def singletonWeight (P : ℕ) (omega : ℕ → ℝ)
    (t : Fin 1 → Fin (P + 1)) : ℝ := omega (t 0).val

theorem labelledProduct_singleton (P : ℕ) (t : Fin 1 → Fin (P + 1)) :
    labelledProduct t = (t 0).val := by
  simp only [labelledProduct, Fin.prod_univ_one]

/-- Exact singleton label transport, including the inclusive prime cap. -/
theorem sum_labelledSingleton (P : ℕ) (f : ℕ → ℝ) :
    (∑ t ∈ labelledPrimeTuples 1 P, f (t 0).val) =
      ∑ p ∈ chenPrimePrefix P, f p := by
  classical
  refine Finset.sum_bij (fun t _ => (t 0).val) ?_ ?_ ?_ ?_
  · intro t ht
    exact mem_chenPrimePrefix.mpr
      ⟨Nat.le_of_lt_succ (t 0).isLt, (Finset.mem_filter.mp ht).2 0⟩
  · intro t _ht s _hs heq
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact Fin.ext heq
  · intro p hp
    obtain ⟨hpP, hprime⟩ := mem_chenPrimePrefix.mp hp
    let t : Fin 1 → Fin (P + 1) := fun _ => ⟨p, Nat.lt_succ_of_le hpP⟩
    refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    intro i
    exact hprime
  · intro t _ht
    rfl

/-- The literal PP mean is the exact primitive-coprime mean, with all
signs inside the one final signed sum. No total-mass substitution occurs. -/
theorem primeProductSignedError_singleton_eq
    (P N : ℕ) (Q : Finset ℕ) (rho omega : ℕ → ℝ) :
    primeProductSignedError 1 P N Q rho (singletonWeight P omega) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix P) omega N q := by
  classical
  unfold primeProductSignedError
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun x : ℝ => rho q * x)
  simp only [singletonWeight, labelledProduct_singleton]
  rw [sum_labelledSingleton P (fun p => omega p *
    ((if Nat.ModEq q p N then 1 else 0) -
      (if Nat.Coprime p q then 1 else 0) / (q.totient : ℝ))),
    finitePrimitiveDiscrepancy_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

def primeIntervalSource (P : ℕ) (lo hi : ℝ) : Finset ℕ := by
  classical
  exact (chenPrimePrefix P).filter (fun p => lo < (p : ℝ) ∧ (p : ℝ) ≤ hi)

def primeIntervalWeight (lo hi : ℝ) (omega : ℕ → ℝ) (p : ℕ) : ℝ := by
  classical
  exact if lo < (p : ℝ) ∧ (p : ℝ) ≤ hi then omega p else 0

/-- The interval endpoints are the same for every modulus, and keep their
literal left-open/right-closed conventions. Signed weights are allowed. -/
theorem interval_discrepancy_eq (P N q : ℕ) (lo hi : ℝ) (omega : ℕ → ℝ) :
    finitePrimitiveDiscrepancy (chenPrimePrefix P) (primeIntervalWeight lo hi omega) N q =
      finitePrimitiveDiscrepancy (primeIntervalSource P lo hi) omega N q := by
  classical
  rw [finitePrimitiveDiscrepancy_eq_sum, finitePrimitiveDiscrepancy_eq_sum]
  unfold primeIntervalSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : lo < (p : ℝ) ∧ (p : ℝ) ≤ hi <;>
    simp [primeIntervalWeight, hp]

theorem primeProductSignedError_singleton_interval_eq
    (P N : ℕ) (Q : Finset ℕ) (rho omega : ℕ → ℝ) (lo hi : ℝ) :
    primeProductSignedError 1 P N Q rho
      (singletonWeight P (primeIntervalWeight lo hi omega)) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (primeIntervalSource P lo hi) omega N q := by
  rw [primeProductSignedError_singleton_eq]
  apply Finset.sum_congr rfl
  intro q _
  rw [interval_discrepancy_eq]

/-- A labelled family has exactly the dependent weight type expected by
UniformPrimeProductTarget. Its interval belongs to the member, not q. -/
def singletonIntervalFamily {ι : Type*} (cap : ℕ → ℕ)
    (lo hi : ℕ → ι → ℝ) (omega : ℕ → ι → ℕ → ℝ)
    (N : ℕ) (i : ι) : (Fin 1 → Fin (cap N + 1)) → ℝ :=
  singletonWeight (cap N) (primeIntervalWeight (lo N i) (hi N i) (omega N i))

theorem singletonIntervalFamily_error_eq {ι : Type*} (cap : ℕ → ℕ)
    (lo hi : ℕ → ι → ℝ) (omega : ℕ → ι → ℕ → ℝ)
    (N : ℕ) (i : ι) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    primeProductSignedError 1 (cap N) N Q rho (singletonIntervalFamily cap lo hi omega N i) =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy
        (primeIntervalSource (cap N) (lo N i) (hi N i)) (omega N i) N q := by
  exact primeProductSignedError_singleton_interval_eq (cap N) N Q rho
    (omega N i) (lo N i) (hi N i)

/-- A low-prime trim is an exact prefix restriction, not a silent removal
of source labels or a change in the primitive mean. -/
theorem prefix_truncation_discrepancy_eq (P Y N q : ℕ) (hYP : Y ≤ P) :
    finitePrimitiveDiscrepancy (chenPrimePrefix P)
      (fun p => if p ≤ Y then (1 : ℝ) else 0) N q =
        finitePrimitiveDiscrepancy (chenPrimePrefix Y) (fun _ => 1) N q := by
  classical
  have hsub : chenPrimePrefix Y ⊆ chenPrimePrefix P := by
    intro p hp
    obtain ⟨hpY, hprime⟩ := mem_chenPrimePrefix.mp hp
    exact mem_chenPrimePrefix.mpr ⟨hpY.trans hYP, hprime⟩
  rw [← finitePrimitiveDiscrepancy_indicator_of_subset
    (chenPrimePrefix Y) (chenPrimePrefix P) N q hsub]
  apply finitePrimitiveDiscrepancy_congr
  intro p hp
  have hpPrime := (mem_chenPrimePrefix.mp hp).2
  have hmem : p ∈ chenPrimePrefix Y ↔ p ≤ Y := by
    rw [mem_chenPrimePrefix]
    exact and_iff_left hpPrime
  simp only [hmem]

/-- Full singleton error equals the retained high-prime error plus the
explicit low-prime correction. The source sign and both gcd masks survive. -/
theorem primeProductSignedError_singleton_cutoff_split
    (P Y N : ℕ) (hYP : Y ≤ P) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    primeProductSignedError 1 P N Q rho (singletonWeight P (fun _ => 1)) =
      (∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (chenPrimePrefix Y) (fun _ => 1) N q) +
      primeProductSignedError 1 P N Q rho
        (singletonWeight P (fun p => if Y < p then 1 else 0)) := by
  classical
  rw [primeProductSignedError_singleton_eq, primeProductSignedError_singleton_eq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hsplit : finitePrimitiveDiscrepancy (chenPrimePrefix P) (fun _ => 1) N q =
      finitePrimitiveDiscrepancy (chenPrimePrefix P)
        (fun p => if p ≤ Y then 1 else 0) N q +
      finitePrimitiveDiscrepancy (chenPrimePrefix P)
        (fun p => if Y < p then 1 else 0) N q := by
    rw [← finitePrimitiveDiscrepancy_add]
    apply finitePrimitiveDiscrepancy_congr
    intro p _
    by_cases hp : p ≤ Y
    · simp [hp, Nat.not_lt.mpr hp]
    · simp [hp, Nat.lt_of_not_ge hp]
  rw [hsplit, prefix_truncation_discrepancy_eq P Y N q hYP]
  ring

/-- Actual scalar coefficient bounds transport to labelled family members,
without adding any modulus argument to their weight. -/
theorem singleton_interval_weight_abs_le_one
    (P : ℕ) (lo hi : ℝ) (omega : ℕ → ℝ)
    (homega : ∀ p ∈ chenPrimePrefix P, |omega p| ≤ 1)
    (t : Fin 1 → Fin (P + 1)) (ht : t ∈ labelledPrimeTuples 1 P) :
    |singletonWeight P (primeIntervalWeight lo hi omega) t| ≤ 1 := by
  classical
  have hp : (t 0).val ∈ chenPrimePrefix P := mem_chenPrimePrefix.mpr
    ⟨Nat.le_of_lt_succ (t 0).isLt, (Finset.mem_filter.mp ht).2 0⟩
  unfold singletonWeight primeIntervalWeight
  split
  · exact homega _ hp
  · norm_num

/-- The actual lower coefficient supplies every algebraic physical gate.
The independent numerical level/factorization licence is not inferred. -/
theorem active_physical_data
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ active retainEven N cap w z L) :
    0 < q ∧ Squarefree q ∧ Nat.Coprime q N ∧
      |actualLowerSmallRoughRho retainEven N cap w z L q| ≤ 1 := by
  classical
  have hm := (Finset.mem_filter.mp hq).1
  have hsf := actualLowerSmallRoughModuli_squarefree retainEven N cap w z hm
  exact ⟨Nat.pos_of_ne_zero hsf.ne_zero, hsf,
    actualLowerSmallRoughModuli_coprime_target retainEven N cap w z hm,
    actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q⟩

/-- On every active modulus, the original residue is primitive. The
congruence fibre has no prime dividing its modulus, including at q=1. -/
theorem active_singleton_fibre_not_dvd_modulus
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ active retainEven N cap w z L)
    (t : Fin 1 → Fin (N + 1)) (ht : t ∈ labelledPrimeTuples 1 N)
    (hAP : Nat.ModEq q (labelledProduct t) N) : ¬(t 0).val ∣ q := by
  have hp : Nat.Prime (t 0).val := (Finset.mem_filter.mp ht).2 0
  have hcop := (active_physical_data retainEven N cap w z L hq).2.2.1
  exact chenPrimeAP_not_dvd_modulus hp
    (by simpa only [labelledProduct_singleton] using hAP) hcop.symm

/-- The precise remaining scalar support condition is displayed as a
physical modulus inequality. It is not a distribution-estimate assumption. -/
def CausalSingletonPhysicalLevel (theta : ℝ) (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : Prop :=
  ∀ q ∈ active retainEven N cap w z L, (q : ℝ) ≤ (N : ℝ) ^ theta

theorem active_physical_data_of_level
    (theta : ℝ) (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hlevel : CausalSingletonPhysicalLevel theta retainEven N cap w z L)
    {q : ℕ} (hq : q ∈ active retainEven N cap w z L) :
    0 < q ∧ Squarefree q ∧ Nat.Coprime q N ∧
      |actualLowerSmallRoughRho retainEven N cap w z L q| ≤ 1 ∧
        (q : ℝ) ≤ (N : ℝ) ^ theta := by
  obtain ⟨hp, hsf, hcop, habs⟩ := active_physical_data retainEven N cap w z L hq
  exact ⟨hp, hsf, hcop, habs, hlevel q hq⟩

/-- Exact source-mask transport for the original additive-prime carrier;
the zero extension removes only centre prime divisors. -/
theorem additive_source_discrepancy_eq_mask (N q : ℕ) (omega : ℕ → ℝ) :
    finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) omega N q =
      finitePrimitiveDiscrepancy (chenPrimePrefix N)
        (fun p => if ¬p ∣ N then omega p else 0) N q := by
  classical
  rw [chenAdditivePrimeCarrier_eq_prefix_filter,
    finitePrimitiveDiscrepancy_eq_sum, finitePrimitiveDiscrepancy_eq_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ¬p ∣ N <;> simp [hp]

/-- Explicit centre-prime correction between the two primitive means.
The modulus-prime atom cancels here only because it appears on BOTH sides. -/
theorem additive_discrepancy_eq_prefix_add_centre
    (N : ℕ) (hEven : Even N) {q : ℕ} (hqN : Nat.Coprime q N) :
    finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N q =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q +
        chenPrimeDivisorCount N N / (Nat.totient q : ℝ) - chenCentrePrimeAPCount N N q := by
  have hsrc := chenInitialBoundingSieve_rem_eq_source_discrepancy N 0 hEven hqN
  have hpre := chenInitialBoundingSieve_rem_sub_primitive_error N 0 hEven q
  have hcorr : chenInitialPrimitiveCorrection N q =
      chenPrimeDivisorCount N N / (Nat.totient q : ℝ) -
        chenPrimeDivisorCount N q / (Nat.totient q : ℝ) - chenCentrePrimeAPCount N N q := by
    unfold chenInitialPrimitiveCorrection
    ring
  rw [hcorr] at hpre
  linarith only [hsrc, hpre]

/-- The PP target's unit singleton is centred at the actual coprime prime
mass. Replacing it by the total prime count costs the modulus-prime term. -/
theorem primeProductSignedError_singleton_unit_eq_AP
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    primeProductSignedError 1 N N Q rho (singletonWeight N (fun _ => 1)) =
      (∑ q ∈ Q, rho q * (chenPrimeAPCount N N q -
        ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ))) +
      ∑ q ∈ Q, rho q * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
  classical
  rw [primeProductSignedError_singleton_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N q =
      chenPrimeAPCount N N q := by
    simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [finitePrimitiveDiscrepancy, hAP, chenPrimePrefix_coprime_mass]
  ring

/-- Full original-prime AP mass in terms of the exact PP target, with
centre and modulus prime corrections separately visible and signed. -/
theorem original_signed_AP_mass_eq_PP
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ q ∈ Q, rho q * (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) =
      ((chenPrimePrefix N).card : ℝ) * physicalDensitySum Q rho +
        primeProductSignedError 1 N N Q rho (singletonWeight N (fun _ => 1)) -
        (∑ q ∈ Q, rho q * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))) -
        ∑ q ∈ Q, rho q * chenCentrePrimeAPCount N N q := by
  rw [primeProductSignedError_singleton_unit_eq_AP]
  simp only [physicalDensitySum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The original first-exit rho is unchanged in the density and exact PP
term. This is a finite lower inequality, leaving its analytic PP estimate
and adopted raw L1 density evaluation unasserted. -/
theorem causal_PP_lower
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hEven : Even N)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
      primeProductSignedError 1 N N (active retainEven N cap w z L)
        (actualLowerSmallRoughRho retainEven N cap w z L) (singletonWeight N (fun _ => 1)) -
      chenInitialCorrectionCost N (active retainEven N cap w z L) ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  rw [primeProductSignedError_singleton_eq]
  exact causal_primitive_lower retainEven N cap w z L hEven hL hwL hwz hzcap

/-- The actual current first row receives the exact Part3 singleton PP
error, with all finite correction costs already paid below N^theta, theta<1.
No greater-than-sqrt ordinary BV estimate has been assumed or produced. -/
theorem eventually_currentUpsilon1_PP_lower_paid
    (theta eta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap Q : ℕ) (w L : ℝ),
      Even N → 1 < L → w ≤ L → w ≤ (N : ℝ) ^ (417 / 5000 : ℝ) →
      (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (cap : ℝ) →
      (Q : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ q ∈ active retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L, q ≤ Q) →
      ((chenAdditivePrimeCarrier N).card : ℝ) *
          physicalDensitySum
            (actualLowerSmallRoughModuli retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)))
            (actualLowerSmallRoughRho retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L) +
        primeProductSignedError 1 N N
          (active retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L)
          (actualLowerSmallRoughRho retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L)
          (singletonWeight N (fun _ => 1)) -
        eta * singularNormalization N ≤ currentChenUpsilon1 N := by
  filter_upwards [eventually_currentUpsilon1_causal_primitive_lower_paid
    theta eta htheta0 htheta1 heta] with N hN
  intro retainEven cap Q w L hEven hL hwL hwz hzcap hQ hsupport
  rw [primeProductSignedError_singleton_eq]
  exact hN retainEven cap Q w L hEven hL hwL hwz hzcap hQ hsupport

end

end ImbalancedChen.P5S1SingletonPP
