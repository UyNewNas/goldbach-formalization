import ImbalancedChen.P2FrozenReceiverCountActions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite mean for the actual frozen receiver is its coprime prime
population.  The li/phi model differs from that mean by a second, explicit
term.  These identities retain the nonprimitive residue count and all
receiver restrictions.  No distribution estimate is asserted for arbitrary E.
-/
namespace ImbalancedChen.P2SameQSeedCoprimeMean

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

def receiverPrimes (N : ℕ) (E : ℕ → Prop) : Finset ℕ :=
  (range (N+1)).filter (fun ell => ell.Prime ∧ E ell)

def coprimePopulation (N : ℕ) (E : ℕ → Prop) (m : ℕ) : ℕ :=
  ((receiverPrimes N E).filter (fun ell => ell.Coprime m)).card

def noncoprimePopulation (N : ℕ) (E : ℕ → Prop) (m : ℕ) : ℕ :=
  ((receiverPrimes N E).filter (fun ell => ¬ell.Coprime m)).card

/-- The exact finite population in the mean; its complement is retained. -/
theorem coprimePopulation_add_noncoprime (N : ℕ) (E : ℕ → Prop) (m : ℕ) :
    coprimePopulation N E m + noncoprimePopulation N E m =
      (receiverPrimes N E).card := by
  exact card_filter_add_card_filter_not (s := receiverPrimes N E) (fun ell => ell.Coprime m)

/-- Multiplication of the complete prefix and residual modulus is justified
by their coprimality, with the original prime label and receiver unchanged. -/
theorem frozenSequenceCount_eq_complete_source (N : ℕ) {d r : ℕ}
    (hcop : d.Coprime r) (E : ℕ → Prop) :
    frozenSequenceCount N d E r = ((goldbachDivisible N (d*r)).filter E).card := by
  unfold frozenSequenceCount
  congr 1
  ext ell
  simp only [goldbachDivisible,mem_filter]
  constructor
  · rintro ⟨⟨⟨hell,hprime,hd⟩,hE⟩,hr⟩
    exact ⟨⟨hell,hprime,hcop.mul_dvd_of_dvd_of_dvd hd hr⟩,hE⟩
  · rintro ⟨⟨hell,hprime,hm⟩,hE⟩
    exact ⟨⟨⟨hell,hprime,(dvd_mul_right d r).trans hm⟩,hE⟩,
      (dvd_mul_left r d).trans hm⟩

/-- The residue N is primitive when the original prefix is target-coprime;
the residual coprimality follows from the actual sifted prime product. -/
theorem complete_modulus_coprime {N d r : ℕ} {z : ℝ}
    (hd : d.Coprime N) (hr : r∈(ordinarySievePrimeProduct (d*N) z).divisors) :
    (d*r).Coprime N := by
  have hmask := (ordinarySievePrimeProduct_coprime (d*N) z).of_dvd_left
    (Nat.mem_divisors.mp hr).1
  exact hd.mul_left (hmask.of_dvd_right (dvd_mul_left N d))

def finiteAPDiscrepancy (N : ℕ) (E : ℕ → Prop) (m : ℕ) : ℝ :=
  (((goldbachDivisible N m).filter E).card:ℝ) -
    (coprimePopulation N E m:ℝ)/(Nat.totient m:ℝ)

def finiteMeanShift (N : ℕ) (E : ℕ → Prop) (m : ℕ) : ℝ :=
  ((coprimePopulation N E m:ℝ)-logarithmicIntegral N)/(Nat.totient m:ℝ)

def signedAPDiscrepancy (side : Bool) (N d D : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ :=
  ∑ r∈(ordinarySievePrimeProduct (d*N) z).divisors,
    ordinaryRosserWeight side N d D z r*finiteAPDiscrepancy N E (d*r)

def signedMeanShift (side : Bool) (N d D : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ :=
  ∑ r∈(ordinarySievePrimeProduct (d*N) z).divisors,
    ordinaryRosserWeight side N d D z r*finiteMeanShift N E (d*r)

/-- An exact same-coefficient decomposition. The second term cannot be
discarded merely because a primitive AP discrepancy has been paid. -/
theorem frozenRemainder_eq_coprime_split (side : Bool) (N d D : ℕ)
    (E : ℕ → Prop) (z : ℝ) :
    frozenRemainder side N d D E z =
      signedAPDiscrepancy side N d D E z + signedMeanShift side N d D E z := by
  unfold frozenRemainder signedAPDiscrepancy signedMeanShift
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  have hc : d.Coprime r :=
    ((ordinarySievePrimeProduct_coprime (d*N) z).of_dvd_left
      (Nat.mem_divisors.mp hr).1 |>.of_dvd_right (dvd_mul_right d N)).symm
  rw [frozenSequenceCount_eq_complete_source N hc E]
  unfold finiteAPDiscrepancy finiteMeanShift
  ring

theorem frozenPolynomial_eq_coprime_split (side : Bool) (N d D : ℕ)
    (E : ℕ → Prop) (z : ℝ) :
    frozenPolynomial side N d D E z =
      (logarithmicIntegral N/(Nat.totient d:ℝ))*ordinaryRosserMainSum side N d D z +
        signedAPDiscrepancy side N d D E z + signedMeanShift side N d D E z := by
  rw [frozenPolynomial_eq_model_add_remainder,frozenRemainder_eq_coprime_split]
  ring

/-- Arbitrary frozen receivers do not carry an uncorrected positive lower
baseline: the empty receiver is already an exact obstruction. -/
theorem empty_receiver_not_positive_lower {N d : ℕ} {z c : ℝ} (hc : 0<c) :
    ¬c≤(frozenCount N d (fun _ => False) z:ℝ) := by
  have hz : (frozenCount N d (fun _ => False) z:ℝ)=0 := by
    simp [frozenCount,frozenCarrier]
  rw [hz]
  exact not_le.mpr hc

end
end ImbalancedChen.P2SameQSeedCoprimeMean
