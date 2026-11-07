import ImbalancedChen.Part3OriginalPrimaryPacketRows
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The arithmetic prerequisites for ABL Lemma 3.1 are derived from the actual
computed primary block, not added to CoprimePacket as assumptions.  Its
integer K at q_ABL=1, r_ABL=z, s_ABL=1 is the supported part of
z/gcd(v*q_f,z) on the primes of |a|*nu.  It is one for every actual row and
every dilation label.  In particular it is one for every legal oldform.

This proves no Hecke identity, oldform norm, automorphic realization,
spectral gap, Kuznetsov formula, A/J estimate, or Eq. (24)/(25).
-/

namespace ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102

noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalCompletedReciprocalSource20261102
open OriginalPrimaryPacketRows20261102
open ActualCompletedSquarePushforwardSourceOnly
open FixedRhoPrimarySignedFiniteSourceOnly CanonicalReciprocalData
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

/-- The multiplier's prime support is recovered from a real source member
of the computed block.  No coprimality of the Poisson modulus is used. -/
theorem outputCarrier_multiplier_prime_support (D : OriginalData) (k : BlockKey)
    {zy : Output} (hzy : zy ∈ outputCarrier D k) :
    ∀ p : ℕ, p.Prime → p ∣ k.1 → p ∣ D.block.atom.residue.natAbs := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hzy
  change s ∈ block D.block.atom.residue (originalSource D) k at hs
  have hkey := congrArg Prod.fst (mem_filter.mp hs).2
  change rhoPrimaryNu D.block.atom.residue (output s).2 = k.1 at hkey
  intro p hp hpk
  exact rhoPrimaryNu_prime_support D.block.atom.residue (output s).2 hp
    (by simpa only [hkey] using hpk)

/-- An occupied original row supplies the prime-support condition uniformly
in the earlier completion frequency and in all future spectral labels. -/
theorem row_multiplier_prime_support (D : OriginalData) (k : BlockKey)
    (z : Row D k) :
    ∀ p : ℕ, p.Prime → p ∣ k.1 → p ∣ D.block.atom.residue.natAbs := by
  obtain ⟨n, hn⟩ := levelCarrier_has_n D k z.property
  exact outputCarrier_multiplier_prime_support D k (nCarrier_decode D k z.val hn)

/-- This is the (n,m)=1 premise of ABL Lemma 3.1 after its substitution
(n,m)=(|a|*nu,n0).  Coprimality only to |a| would not by itself be its type. -/
theorem original_index_coprime_abl_argument (D : OriginalData) (k : BlockKey)
    (z : Row D k) {n : ℕ} (hn : n ∈ nCarrier D k z.val) :
    n.Coprime (D.block.atom.residue.natAbs * k.1) := by
  have hna := (nCarrier_positive_coprime D k z.val hn).2.2
  exact hna.mul_right (coprime_of_prime_support hna
    (row_multiplier_prime_support D k z))

/-- Every factor removed by ABL is coprime to the ACTUAL level. -/
theorem original_abl_argument_coprime_level (D : OriginalData) (k : BlockKey)
    (z : Row D k) :
    (D.block.atom.residue.natAbs * k.1).Coprime z.val := by
  have haz := (levelCarrier_licensed D k z.property).2
  have hnuz : k.1.Coprime z.val :=
    (coprime_of_prime_support haz.symm (row_multiplier_prime_support D k z)).symm
  exact haz.mul_left hnuz

/-- The literal s_ABL=1 cofactor in Lemma 3.1.  No newform level or
dilation has been selected, and no spectral object is defined here. -/
def oldformCofactor (z qf v : ℕ) : ℕ := z / Nat.gcd (v * qf) z

def oldformExceptionalInteger (D : OriginalData) (k : BlockKey)
    (z : Row D k) (qf v : ℕ) : ℕ :=
  supportedPart (oldformCofactor z.val qf v)
    (D.block.atom.residue.natAbs * k.1)

private theorem oldformCofactor_dvd (z qf v : ℕ) : oldformCofactor z qf v ∣ z := by
  refine ⟨Nat.gcd (v * qf) z, ?_⟩
  simpa only [oldformCofactor, Nat.mul_comm] using
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right (v * qf) z)).symm

private theorem supportedPart_eq_one_of_coprime {b a : ℕ}
    (hba : b.Coprime a) : supportedPart b a = 1 := by
  unfold supportedPart
  apply Finset.prod_eq_one
  intro p hp
  obtain ⟨hpb, hpa⟩ := mem_filter.mp hp
  have hbad : ¬b.Coprime a := Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, Nat.prime_of_mem_primeFactors hpb, Nat.dvd_of_mem_primeFactors hpb, hpa⟩
  exact False.elim (hbad hba)

/-- Uniform K=1, including every q_f|z and v|z/q_f allowed in the actual
oldclass.  The stronger quantification is legitimate for this integer
formula; it asserts no existence or identity of an illegal oldform. -/
theorem original_oldformExceptionalInteger_eq_one (D : OriginalData)
    (k : BlockKey) (z : Row D k) (qf v : ℕ) :
    oldformExceptionalInteger D k z qf v = 1 := by
  apply supportedPart_eq_one_of_coprime
  exact ((original_abl_argument_coprime_level D k z).of_dvd_right
    (oldformCofactor_dvd z.val qf v)).symm

end
end ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102
