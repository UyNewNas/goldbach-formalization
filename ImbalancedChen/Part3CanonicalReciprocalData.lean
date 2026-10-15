import ImbalancedChen.Part3ComplexCRTConsumer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Canonical finite arithmetic licenses for the actual reciprocal phase

Namespace-isolated source extraction from fixed goldbach commit
09b97db5764ade1246bfb77206baa1b124760958:
* PrimeSupport.lean:16-81, source SHA256
  1ea4d63da2028c7dd7ea169c9c9547ee1e4f3f88f760ed7ba104e706452acf04;
* WGCD.lean:16-145,184-232, source SHA256
  d92fa9b50de42b01d91e8d66b2d76dad09ae0d8b9800b71640c84f50e8d9a033.
Both original blobs were compared byte-for-byte with the exact fixed commit.
Only the finite prime-support split and canonical gcd arithmetic are copied;
the original unbuilt WGCD/phase/Poisson modules are not imported.

Original full physical moduli and both original beta integers determine all
nine canonical coordinates. Actual row membership pays their positivity.
On the existing CRT-compatible branch, arithmetic proves all coprimality
licenses of the three-phase identity, including the D and D' factors.
The caller supplies neither a factor dictionary nor replacement hypotheses.

This file proves finite arithmetic licenses. It does not yet prove an actual
Poisson phase identity, discard a slow phase, cancel primitive V/U, estimate
an exponential sum, or change the residue bound to a fixed multiple of scale.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators

namespace CanonicalReciprocalData

/-- The factor of `n` containing the full powers of primes dividing `d`. -/
def supportedPart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∣ d), p ^ n.factorization p

/-- The complementary factor of `n`, containing primes not dividing `d`. -/
def coprimePart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬p ∣ d), p ^ n.factorization p

theorem supportedPart_pos (n d : ℕ) : 0 < supportedPart n d := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem coprimePart_pos (n d : ℕ) : 0 < coprimePart n d := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem supportedPart_mul_coprimePart {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d * coprimePart n d = n := by
  rw [supportedPart, coprimePart, Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn)).symm

theorem supportedPart_dvd {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d ∣ n :=
  ⟨coprimePart n d, (supportedPart_mul_coprimePart hn d).symm⟩

theorem coprimePart_dvd {n : ℕ} (hn : 0 < n) (d : ℕ) :
    coprimePart n d ∣ n := by
  refine ⟨supportedPart n d, ?_⟩
  rw [Nat.mul_comm]
  exact (supportedPart_mul_coprimePart hn d).symm

/-- Every prime divisor of the supported part divides the reference integer. -/
theorem prime_dvd_supportedPart {n d p : ℕ} (hp : p.Prime)
    (hps : p ∣ supportedPart n d) : p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hps
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

/-- Every prime divisor of the complementary part avoids the reference integer. -/
theorem prime_dvd_coprimePart_not_dvd {n d p : ℕ} (hp : p.Prime)
    (hpt : p ∣ coprimePart n d) : ¬p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpt
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

theorem coprimePart_coprime (n d : ℕ) : (coprimePart n d).Coprime d := by
  by_contra h
  obtain ⟨p, hp, hpt, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact prime_dvd_coprimePart_not_dvd hp hpt hpd

/-- Coprimality transfers from `d` to every integer supported on primes dividing `d`. -/
theorem coprime_of_prime_support {u d s : ℕ} (hu : u.Coprime d)
    (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) : u.Coprime s := by
  by_contra h
  obtain ⟨p, hp, hpu, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpu, hs p hp hps⟩) hu

@[ext] structure WGCDData where
  d : ℕ
  d₁ : ℕ
  δ : ℕ
  δ₁ : ℕ
  δ₂ : ℕ
  k₁ : ℕ
  k₂ : ℕ
  n₁ : ℕ
  n₂ : ℕ
  deriving DecidableEq

def wGCDData (q r N₁ N₂ : ℕ) : WGCDData :=
  let d := N₁.gcd N₂
  let δ := q.gcd r
  { d := d, d₁ := supportedPart (N₁ / d) d
    δ := δ, δ₁ := supportedPart (q / δ) δ, δ₂ := supportedPart (r / δ) δ
    k₁ := coprimePart (q / δ) δ, k₂ := coprimePart (r / δ) δ
    n₁ := coprimePart (N₁ / d) d, n₂ := N₂ / d }

def WGCDData.D (v : WGCDData) : ℕ := v.δ * v.δ₁ * v.δ₂

def WGCDData.D' (v : WGCDData) : ℕ := v.d * v.d₁ * v.D

/-- Arithmetic facts, not distribution or phase estimates. -/
structure WGCDData.Valid (v : WGCDData) (q r N₁ N₂ : ℕ) : Prop where
  d_pos : 0 < v.d
  d₁_pos : 0 < v.d₁
  δ_pos : 0 < v.δ
  δ₁_pos : 0 < v.δ₁
  δ₂_pos : 0 < v.δ₂
  k₁_pos : 0 < v.k₁
  k₂_pos : 0 < v.k₂
  n₁_pos : 0 < v.n₁
  n₂_pos : 0 < v.n₂
  q_eq : q = v.δ * v.δ₁ * v.k₁
  r_eq : r = v.δ * v.δ₂ * v.k₂
  N₁_eq : N₁ = v.d * v.d₁ * v.n₁
  N₂_eq : N₂ = v.d * v.n₂
  d_eq : v.d = N₁.gcd N₂
  δ_eq : v.δ = q.gcd r
  d₁_support : ∀ p : ℕ, p.Prime → p ∣ v.d₁ → p ∣ v.d
  δ₁_support : ∀ p : ℕ, p.Prime → p ∣ v.δ₁ → p ∣ v.δ
  δ₂_support : ∀ p : ℕ, p.Prime → p ∣ v.δ₂ → p ∣ v.δ
  n₁_d : v.n₁.Coprime v.d
  k₁_δ : v.k₁.Coprime v.δ
  k₂_δ : v.k₂.Coprime v.δ
  n_primitive : (v.d₁ * v.n₁).Coprime v.n₂
  k_primitive : (v.δ₁ * v.k₁).Coprime (v.δ₂ * v.k₂)

private theorem gcd_quotients_coprime {u v : ℕ} (hu : 0 < u) :
    (u / u.gcd v).Coprime (v / u.gcd v) := by
  have hg := Nat.gcd_pos_of_pos_left v hu
  change (u / u.gcd v).gcd (v / u.gcd v) = 1
  apply Nat.mul_left_cancel hg
  rw [← Nat.gcd_mul_left, Nat.mul_div_cancel' (Nat.gcd_dvd_left u v),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right u v), mul_one]

/-- The data are constructed for every positive original tuple, with no
compatibility, size cutoff, or analytic premise. -/
theorem wGCDData_valid {q r N₁ N₂ : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    (wGCDData q r N₁ N₂).Valid q r N₁ N₂ := by
  have hd := Nat.gcd_pos_of_pos_left N₂ hN₁
  have hδ := Nat.gcd_pos_of_pos_left r hq
  have hu := Nat.div_pos (Nat.le_of_dvd hN₁ (Nat.gcd_dvd_left N₁ N₂)) hd
  have hv := Nat.div_pos (Nat.le_of_dvd hN₂ (Nat.gcd_dvd_right N₁ N₂)) hd
  have hk := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hδ
  have hl := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hδ
  refine ⟨hd, supportedPart_pos _ _, hδ, supportedPart_pos _ _,
    supportedPart_pos _ _, coprimePart_pos _ _, coprimePart_pos _ _,
    coprimePart_pos _ _, hv, ?_, ?_, ?_, ?_, rfl, rfl,
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    coprimePart_coprime _ _, coprimePart_coprime _ _, coprimePart_coprime _ _,
    ?_, ?_⟩
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hk,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)]
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hl,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)]
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hu,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left N₁ N₂)]
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right N₁ N₂)).symm
  · dsimp [wGCDData]
    rw [supportedPart_mul_coprimePart hu]
    exact gcd_quotients_coprime hN₁
  · dsimp [wGCDData]
    rw [supportedPart_mul_coprimePart hk, supportedPart_mul_coprimePart hl]
    exact gcd_quotients_coprime hq

namespace WGCDData.Valid

variable {v : WGCDData} {q r N₁ N₂ : ℕ} (hv : v.Valid q r N₁ N₂)

include hv

theorem D_pos : 0 < v.D := Nat.mul_pos (Nat.mul_pos hv.δ_pos hv.δ₁_pos) hv.δ₂_pos

theorem D'_pos : 0 < v.D' := Nat.mul_pos (Nat.mul_pos hv.d_pos hv.d₁_pos) hv.D_pos

theorem k₁_dvd : v.k₁ ∣ q := by rw [hv.q_eq]; exact dvd_mul_left _ _

theorem k₂_dvd : v.k₂ ∣ r := by rw [hv.r_eq]; exact dvd_mul_left _ _

theorem k_coprime : v.k₁.Coprime v.k₂ :=
  hv.k_primitive.of_dvd (dvd_mul_left _ _) (dvd_mul_left _ _)

theorem δ_coprime : v.δ₁.Coprime v.δ₂ :=
  hv.k_primitive.of_dvd (dvd_mul_right _ _) (dvd_mul_right _ _)

theorem lcm_eq : q.lcm r = v.D * v.k₁ * v.k₂ := by
  apply Nat.mul_left_cancel hv.δ_pos
  calc
    v.δ * q.lcm r = q * r := by rw [hv.δ_eq, Nat.gcd_mul_lcm]
    _ = v.δ * (v.D * v.k₁ * v.k₂) := by rw [hv.q_eq, hv.r_eq]; unfold D; ring

theorem k_D : (v.k₁ * v.k₂).Coprime v.D := by
  have hkδ := hv.k₁_δ.mul_left hv.k₂_δ
  exact (hkδ.mul_right (coprime_of_prime_support hkδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hkδ hv.δ₂_support)

theorem n₁_d₁ : v.n₁.Coprime v.d₁ :=
  coprime_of_prime_support hv.n₁_d hv.d₁_support

theorem n₁_n₂ : v.n₁.Coprime v.n₂ :=
  hv.n_primitive.of_dvd_left (dvd_mul_left _ _)

/-- Original compatibility gives the two cross-coprimalities through the
common modulus, even when the original moduli are not coprime. -/
theorem N₁_D (hc : ComplexCRT.Compatible q r N₁ N₂) : N₁.Coprime v.D := by
  have hNδ : N₁.Coprime v.δ := by
    rw [hv.δ_eq]
    exact hc.1.of_dvd_right (Nat.gcd_dvd_left q r)
  exact (hNδ.mul_right (coprime_of_prime_support hNδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hNδ hv.δ₂_support)

theorem N₂_D (hc : ComplexCRT.Compatible q r N₁ N₂) : N₂.Coprime v.D := by
  have hNδ : N₂.Coprime v.δ := by
    rw [hv.δ_eq]
    exact hc.2.1.of_dvd_right (Nat.gcd_dvd_right q r)
  exact (hNδ.mul_right (coprime_of_prime_support hNδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hNδ hv.δ₂_support)

theorem n_congruence (hc : ComplexCRT.Compatible q r N₁ N₂) :
    Nat.ModEq v.δ (v.d₁ * v.n₁) v.n₂ := by
  have hdδ : v.d.Coprime v.δ := by
    apply (hv.N₁_D hc).of_dvd
    · rw [hv.N₁_eq]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  apply Nat.ModEq.cancel_left_of_coprime hdδ.symm.gcd_eq_one
  simpa only [← hv.δ_eq, hv.N₁_eq, hv.N₂_eq, mul_assoc] using hc.2.2

/-- All the arithmetic hypotheses of the existing three-factor phase follow
from the canonical decomposition and the original W compatibility. -/
theorem phase_coprime (hc : ComplexCRT.Compatible q r N₁ N₂) :
    (v.n₁ * v.k₁ * v.k₂).Coprime v.D' ∧
      v.k₁.Coprime (v.n₁ * v.k₂) ∧ v.n₂.Coprime (v.n₁ * v.k₂) := by
  have hN₁ : (v.d * v.d₁ * v.n₁).Coprime q := hv.N₁_eq ▸ hc.1
  have hN₂ : (v.d * v.n₂).Coprime r := hv.N₂_eq ▸ hc.2.1
  have hnq := hN₁.of_dvd_right hv.k₁_dvd
  have hnr := hN₂.of_dvd_right hv.k₂_dvd
  have hk₁d : v.k₁.Coprime v.d :=
    (hnq.of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).symm
  have hk₂d : v.k₂.Coprime v.d :=
    (hnr.of_dvd_left (dvd_mul_right _ _)).symm
  have hn₁D : v.n₁.Coprime v.D := by
    apply (hv.N₁_D hc).of_dvd_left
    rw [hv.N₁_eq]; exact dvd_mul_left _ _
  have hnd : (v.n₁ * v.k₁ * v.k₂).Coprime v.d :=
    (hv.n₁_d.mul_left hk₁d).mul_left hk₂d
  have hnd₁ := coprime_of_prime_support hnd hv.d₁_support
  have hnD : (v.n₁ * v.k₁ * v.k₂).Coprime v.D := by
    simpa only [mul_assoc] using hn₁D.mul_left hv.k_D
  refine ⟨(hnd.mul_right hnd₁).mul_right hnD, ?_, ?_⟩
  · exact (hnq.of_dvd_left (dvd_mul_left _ _)).symm.mul_right hv.k_coprime
  · exact hv.n₁_n₂.symm.mul_right (hnr.of_dvd_left (dvd_mul_left _ _))

end WGCDData.Valid

end CanonicalReciprocalData

/-- The actual original full-modulus and beta labels determine the data once. -/
def MediumAtom.canonicalReciprocalData (d : MediumAtom)
    (l l' : (ℕ × ℕ × ℕ) × ℕ) : CanonicalReciprocalData.WGCDData :=
  CanonicalReciprocalData.wGCDData
    (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2

private theorem positive_carrier {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))) : 0 < n := by
  have hlo := (Finset.mem_Icc.mp hn).1
  have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
  omega

private theorem actual_row_positive
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l : (ℕ × ℕ × ℕ) × ℕ} (hl : l ∈ d.complexRowLabels) :
    0 < complexFactorModulus l.1 ∧ 0 < l.2 := by
  obtain ⟨_, hV, hQ1, hQ2, hQ3, _⟩ := hd
  obtain ⟨hf, hb⟩ := Finset.mem_product.mp hl
  obtain ⟨h1, h23⟩ := Finset.mem_product.mp hf
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
  exact ⟨Nat.mul_pos (Nat.mul_pos (positive_carrier hQ1 h1)
    (positive_carrier hQ2 h2)) (positive_carrier hQ3 h3), positive_carrier hV hb⟩

/-- All reconstruction and prime-support facts are obtained from actual labels. -/
theorem MediumAtom.canonicalReciprocalData_valid
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels) :
    (d.canonicalReciprocalData l l').Valid
      (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 := by
  obtain ⟨hq, hn⟩ := actual_row_positive hd hl
  obtain ⟨hr, hn'⟩ := actual_row_positive hd hl'
  exact CanonicalReciprocalData.wGCDData_valid hq hr hn hn'

/-- The complete lcm and the two original beta integers are reconstructed. -/
theorem MediumAtom.canonicalReciprocalData_reconstruct
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels) :
    let v := d.canonicalReciprocalData l l'
    (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) = v.D * v.k₁ * v.k₂ ∧
      l.2 = v.d * v.d₁ * v.n₁ ∧ l'.2 = v.d * v.n₂ := by
  have hv := d.canonicalReciprocalData_valid hd hl hl'
  exact ⟨hv.lcm_eq, hv.N₁_eq, hv.N₂_eq⟩

/-- Every core unit gate follows on the actual pre-existing compatible branch. -/
theorem MediumAtom.canonicalReciprocalData_phase_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {l l' : (ℕ × ℕ × ℕ) × ℕ}
    (hl : l ∈ d.complexRowLabels) (hl' : l' ∈ d.complexRowLabels)
    (hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2) :
    let v := d.canonicalReciprocalData l l'
    (v.k₁ * v.k₂).Coprime v.D ∧
      (v.n₁ * v.k₁ * v.k₂).Coprime v.D' ∧
        v.k₁.Coprime (v.n₁ * v.k₂) ∧ v.n₂.Coprime (v.n₁ * v.k₂) := by
  have hv := d.canonicalReciprocalData_valid hd hl hl'
  exact ⟨hv.k_D, hv.phase_coprime hc⟩

end

end ImbalancedChen.Part3
