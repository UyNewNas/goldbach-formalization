import ImbalancedChen.Part3FixedRhoPrimaryFiniteCore

/-! # ABL arithmetic on the literal primary fibres -/

namespace ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102

noncomputable section
open Finset CanonicalReciprocalData

/-- The literal s_ABL=1 cofactor in Lemma 3.1.  No newform level or
dilation has been selected, and no spectral object is defined here. -/
def oldformCofactor (z qf v : ℕ) : ℕ := z / Nat.gcd (v * qf) z

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

end
end ImbalancedChen.Part3.OriginalRowOldformArithmetic20261102

namespace ImbalancedChen.Part3.LiteralPrimaryOldformArithmetic

open Finset CanonicalReciprocalData ActualCompletedSquarePushforwardSourceOnly
open FixedRhoPrimarySignedFiniteSourceOnly OriginalRowOldformArithmetic20261102

/-- The signed output in a computed primary fibre supplies both ABL coprimalities
and the supported cofactor integer for every dilation label. -/
theorem literal_primaryFibre_abl_licenses
    {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {nu : ℕ} {s : Source}
    (hs : s ∈ primaryFibre a (nonzeroSource (carrier A a T H F)) nu) :
    let z := (output s).1
    let y := (output s).2
    let n := (y / (nu : ℤ)).natAbs
    0 < nu ∧ y ≠ 0 ∧ (nu : ℤ) ∣ y ∧
      (nu : ℤ) * (y / (nu : ℤ)) = y ∧ 0 < n ∧
      n.Coprime (a.natAbs * nu) ∧
      (a.natAbs * nu).Coprime z ∧
      ∀ qf v : ℕ,
        supportedPart (oldformCofactor z qf v) (a.natAbs * nu) = 1 := by
  obtain ⟨hsource, rfl⟩ := mem_primaryFibre_iff.mp hs
  obtain ⟨hcarrier, hy⟩ := mem_filter.mp hsource
  have hgate := primaryFibre_gate (fun _ ht => (mem_filter.mp ht).2) hs
  have hsupport := fun (p : ℕ) (hp : p.Prime) =>
    rhoPrimaryNu_prime_support a (output s).2 hp
  have haz := output_residue_coprime hcarrier
  have hlevel := haz.mul_left (coprime_of_prime_support haz.symm hsupport).symm
  refine ⟨rhoPrimaryNu_pos a _, hy, hgate.1, rhoPrimary_reconstruct a hy,
    Int.natAbs_pos.mpr (rhoPrimaryQuotient_ne_zero a hy),
    hgate.2.mul_right (coprime_of_prime_support hgate.2 hsupport), hlevel, ?_⟩
  intro qf v
  exact supportedPart_eq_one_of_coprime
    (hlevel.of_dvd_right (oldformCofactor_dvd _ qf v)).symm

/-- A nonzero grouped coefficient has an original source witness with this output. -/
theorem literal_primaryBeta_abl_licenses
    {A : ℕ} {a : ℤ} {T : Finset ℕ} {H : ℕ} {F : Finset ℤ}
    {nu : ℕ} {lambda : ℕ → ℂ} {omega : ℤ → ℂ} {zy : Output}
    (hb : beta (primaryFibre a (nonzeroSource (carrier A a T H F)) nu)
      lambda omega zy ≠ 0) :
    let n := (zy.2 / (nu : ℤ)).natAbs
    0 < nu ∧ zy.2 ≠ 0 ∧ (nu : ℤ) ∣ zy.2 ∧
      (nu : ℤ) * (zy.2 / (nu : ℤ)) = zy.2 ∧ 0 < n ∧
      n.Coprime (a.natAbs * nu) ∧
      (a.natAbs * nu).Coprime zy.1 ∧
      ∀ qf v : ℕ,
        supportedPart (oldformCofactor zy.1 qf v) (a.natAbs * nu) = 1 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  exact literal_primaryFibre_abl_licenses hs

end ImbalancedChen.Part3.LiteralPrimaryOldformArithmetic
