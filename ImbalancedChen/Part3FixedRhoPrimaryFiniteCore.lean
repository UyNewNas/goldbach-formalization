import ImbalancedChen.Part3PrimaryPrimeSupport
import ImbalancedChen.Part3LiteralReciprocalSource

/-! # The fixed-residue primary decomposition of the signed output -/

namespace ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly

noncomputable section
open Classical Finset CanonicalReciprocalData ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Full powers in |y| of the primes dividing the fixed |rho|. -/
def rhoPrimaryNu (rho y : ℤ) : ℕ := supportedPart y.natAbs rho.natAbs

/-- Signed exact quotient; negative y is never replaced by |y|. -/
def rhoPrimaryQuotient (rho y : ℤ) : ℤ := y / (rhoPrimaryNu rho y : ℤ)

theorem rhoPrimaryNu_pos (rho y : ℤ) : 0 < rhoPrimaryNu rho y := by
  exact supportedPart_pos _ _

theorem rhoPrimaryNu_dvd_natAbs (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    rhoPrimaryNu rho y ∣ y.natAbs := by
  exact supportedPart_dvd (Int.natAbs_pos.mpr hy) _

theorem rhoPrimaryNu_dvd (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    (rhoPrimaryNu rho y : ℤ) ∣ y := by
  exact Int.natCast_dvd.mpr (rhoPrimaryNu_dvd_natAbs rho hy)

theorem rhoPrimary_reconstruct (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    (rhoPrimaryNu rho y : ℤ) * rhoPrimaryQuotient rho y = y := by
  exact Int.mul_ediv_cancel' (rhoPrimaryNu_dvd rho hy)

theorem rhoPrimaryQuotient_natAbs (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    (rhoPrimaryQuotient rho y).natAbs = coprimePart y.natAbs rho.natAbs := by
  unfold rhoPrimaryQuotient
  rw [Int.natAbs_ediv_of_dvd (rhoPrimaryNu_dvd rho hy), Int.natAbs_natCast]
  have hprod : rhoPrimaryNu rho y * coprimePart y.natAbs rho.natAbs = y.natAbs :=
    supportedPart_mul_coprimePart (Int.natAbs_pos.mpr hy) _
  calc
    y.natAbs / rhoPrimaryNu rho y =
        (rhoPrimaryNu rho y * coprimePart y.natAbs rho.natAbs) /
          rhoPrimaryNu rho y :=
      congrArg (fun m : ℕ => m / rhoPrimaryNu rho y) hprod.symm
    _ = coprimePart y.natAbs rho.natAbs :=
      Nat.mul_div_cancel_left _ (rhoPrimaryNu_pos rho y)

theorem rhoPrimaryQuotient_coprime (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    (rhoPrimaryQuotient rho y).natAbs.Coprime rho.natAbs := by
  rw [rhoPrimaryQuotient_natAbs rho hy]
  exact coprimePart_coprime _ _

theorem rhoPrimaryQuotient_ne_zero (rho : ℤ) {y : ℤ} (hy : y ≠ 0) :
    rhoPrimaryQuotient rho y ≠ 0 := by
  intro hn
  have hrec := rhoPrimary_reconstruct rho hy
  rw [hn, mul_zero] at hrec
  exact hy hrec.symm

/-- Prime-support version of nu|rho^infinity; no claim nu|c is made. -/
theorem rhoPrimaryNu_prime_support (rho y : ℤ) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ rhoPrimaryNu rho y) : p ∣ rho.natAbs := by
  exact prime_dvd_supportedPart hp hpn

/-- The complete signed arithmetic interface, with the actual nonzero rho
requirement exposed. The arithmetic helpers even handle rho=0, but no such
extension of the spectral packet is claimed here. -/
theorem rhoPrimary_spec {rho y : ℤ} (_hrho : rho ≠ 0) (hy : y ≠ 0) :
    0 < rhoPrimaryNu rho y ∧
      (rhoPrimaryNu rho y : ℤ) ∣ y ∧
      (rhoPrimaryNu rho y : ℤ) * rhoPrimaryQuotient rho y = y ∧
      rhoPrimaryQuotient rho y ≠ 0 ∧
      (rhoPrimaryQuotient rho y).natAbs.Coprime rho.natAbs ∧
      ∀ p : ℕ, p.Prime → p ∣ rhoPrimaryNu rho y → p ∣ rho.natAbs := by
  exact ⟨rhoPrimaryNu_pos rho y, rhoPrimaryNu_dvd rho hy,
    rhoPrimary_reconstruct rho hy, rhoPrimaryQuotient_ne_zero rho hy,
    rhoPrimaryQuotient_coprime rho hy,
    fun _ hp hpn => rhoPrimaryNu_prime_support rho y hp hpn⟩

/-- The finite support is the IMAGE of the actual output-dependent key. -/
def primaryKeys (rho : ℤ) (U : Finset Source) : Finset ℕ :=
  U.image (fun s => rhoPrimaryNu rho (output s).2)

def primaryFibre (rho : ℤ) (U : Finset Source) (nu : ℕ) : Finset Source :=
  U.filter (fun s => rhoPrimaryNu rho (output s).2 = nu)

theorem mem_primaryFibre_iff {rho : ℤ} {U : Finset Source} {nu : ℕ} {s : Source} :
    s ∈ primaryFibre rho U nu ↔ s ∈ U ∧ rhoPrimaryNu rho (output s).2 = nu := by
  exact mem_filter

theorem source_mem_own_primaryFibre {rho : ℤ} {U : Finset Source} {s : Source}
    (hs : s ∈ U) :
    rhoPrimaryNu rho (output s).2 ∈ primaryKeys rho U ∧
      s ∈ primaryFibre rho U (rhoPrimaryNu rho (output s).2) := by
  exact ⟨mem_image_of_mem _ hs, mem_filter.mpr ⟨hs, rfl⟩⟩

theorem primaryFibre_key_unique {rho : ℤ} {U : Finset Source} {nu eta : ℕ}
    {s : Source} (hn : s ∈ primaryFibre rho U nu)
    (he : s ∈ primaryFibre rho U eta) : nu = eta := by
  exact (mem_filter.mp hn).2.symm.trans (mem_filter.mp he).2

theorem primaryKeys_pos {rho : ℤ} {U : Finset Source} {nu : ℕ}
    (hn : nu ∈ primaryKeys rho U) : 0 < nu := by
  obtain ⟨s, _, rfl⟩ := mem_image.mp hn
  exact rhoPrimaryNu_pos _ _

theorem primaryKeys_prime_support {rho : ℤ} {U : Finset Source} {nu p : ℕ}
    (hn : nu ∈ primaryKeys rho U) (hp : p.Prime) (hpn : p ∣ nu) :
    p ∣ rho.natAbs := by
  obtain ⟨s, _, rfl⟩ := mem_image.mp hn
  exact rhoPrimaryNu_prime_support _ _ hp hpn

/-- Every source in a computed fibre has the OLD fixed-rho coprime gate,
without assuming that gate in the fibre definition. -/
theorem primaryFibre_gate {rho : ℤ} {U : Finset Source}
    (hU : ∀ s ∈ U, (output s).2 ≠ 0) {nu : ℕ} {s : Source}
    (hs : s ∈ primaryFibre rho U nu) :
    (nu : ℤ) ∣ (output s).2 ∧
      ((output s).2 / (nu : ℤ)).natAbs.Coprime rho.natAbs := by
  obtain ⟨hsU, hkey⟩ := mem_filter.mp hs
  have hy := hU s hsU
  constructor
  · simpa only [hkey] using rhoPrimaryNu_dvd rho hy
  · simpa only [rhoPrimaryQuotient, hkey] using rhoPrimaryQuotient_coprime rho hy

/-- Exact finite partition for any original complex payload, including an
entire already-completed kernel. No summability interchange is performed. -/
theorem finite_primary_decomposition (rho : ℤ) (U : Finset Source)
    (F : Source → ℂ) :
    (∑ s ∈ U, F s) =
      ∑ nu ∈ primaryKeys rho U, ∑ s ∈ primaryFibre rho U nu, F s := by
  exact (sum_fiberwise_of_maps_to (s := U) (t := primaryKeys rho U)
    (g := fun s => rhoPrimaryNu rho (output s).2)
    (fun s hs => mem_image_of_mem _ hs) F).symm

/-- At each fixed original physical c, the only changed kernel coordinate
is the reconstructed signed numerator y=nu*n. c and rho are unchanged. -/
theorem finite_primary_original_modulus (rho : ℤ) (U : Finset Source)
    (hU : ∀ s ∈ U, (output s).2 ≠ 0)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (c : ℕ)
    (K : ℕ → ℤ → ℕ → ℤ → ℂ) :
    (∑ s ∈ U, weight lambda omega s * K c rho (output s).1 (output s).2) =
      ∑ nu ∈ primaryKeys rho U, ∑ s ∈ primaryFibre rho U nu,
        weight lambda omega s * K c rho (output s).1
          ((nu : ℤ) * ((output s).2 / (nu : ℤ))) := by
  rw [finite_primary_decomposition rho U]
  apply sum_congr rfl
  intro nu hnu
  apply sum_congr rfl
  intro s hs
  rw [Int.mul_ediv_cancel' (primaryFibre_gate hU hs).1]

end
end ImbalancedChen.Part3.FixedRhoPrimarySignedFiniteSourceOnly
