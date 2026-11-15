import ImbalancedChen.Part3OriginalMediumDoubleLambdaColorWindows
import ImbalancedChen.Part3MediumDeletedIndicatorShiftBridge
import ImbalancedChen.Part3MediumSingleZeroFiberCost
import ImbalancedChen.Part3MediumOriginalLambdaDivisorBound
import Mathlib.Tactic

-- UNCOMPILED_ZERO_CREDIT. Paper medium module lines 156-160, 169-189.
-- A pre-restoration finite S3' two-deleted kernel. Its q,d,r,s,n1,n2,m
-- support is supplied as the original finite carrier. No equality to an
-- installed S3' square owner or weighted estimate is claimed here.

namespace ImbalancedChen.Part3.MediumLiteralS3Deleted20261028

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.MediumOriginalLambdaDivisor20261028

structure Index where
  q d r s n1 n2 m : ℕ
  deriving DecidableEq

def firstDeleted (a : ℤ) (t : Index) : ℂ :=
  deletedIndicator a ((t.q * t.d) * t.r) t.n1 t.m

def secondDeleted (a : ℤ) (t : Index) : ℂ :=
  deletedIndicator a ((t.q * t.d) * t.s) t.n2 t.m

def fullIndicator (a : ℤ) (q n m : ℕ) : ℂ :=
  if ((n * m : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ) then 1 else 0

def zeroIndicator (a : ℤ) (n m : ℕ) : ℂ :=
  if ((n * m : ℕ) : ℤ) = a then 1 else 0

theorem fullIndicator_eq_deleted_add_zero
    (a : ℤ) (q n m : ℕ) :
    fullIndicator a q n m =
      deletedIndicator a q n m + zeroIndicator a n m := by
  by_cases hzero : ((n * m : ℕ) : ℤ) = a
  · simp [fullIndicator, deletedIndicator, zeroIndicator, hzero]
  · by_cases hmod : ((n * m : ℕ) : ℤ) % (q : ℤ) = a % (q : ℤ)
    · simp [fullIndicator, deletedIndicator, zeroIndicator, hzero, hmod]
    · simp [fullIndicator, deletedIndicator, zeroIndicator, hzero, hmod]

theorem zeroIndicator_norm_le_one (a : ℤ) (n m : ℕ) :
    ‖zeroIndicator a n m‖ ≤ (1 : ℝ) := by
  unfold zeroIndicator
  split_ifs <;> simp

theorem deletedIndicator_norm_le_one (a : ℤ) (q n m : ℕ) :
    ‖deletedIndicator a q n m‖ ≤ (1 : ℝ) := by
  unfold deletedIndicator
  split_ifs <;> simp

theorem double_zero_impossible
    {a : ℤ} {t : Index}
    (hm : 0 < t.m) (h12 : t.n1 ≠ t.n2)
    (h1 : ((t.n1 * t.m : ℕ) : ℤ) = a)
    (h2 : ((t.n2 * t.m : ℕ) : ℤ) = a) : False := by
  have hprod : t.n1 * t.m = t.n2 * t.m := by
    exact_mod_cast h1.trans h2.symm
  exact h12 (Nat.eq_of_mul_eq_mul_right hm hprod)

theorem zeroIndicator_product_eq_zero
    {a : ℤ} {t : Index}
    (hm : 0 < t.m) (h12 : t.n1 ≠ t.n2) :
    zeroIndicator a t.n1 t.m *
      Complex.conj (zeroIndicator a t.n2 t.m) = 0 := by
  by_cases h1 : ((t.n1 * t.m : ℕ) : ℤ) = a
  · have h2 : ((t.n2 * t.m : ℕ) : ℤ) ≠ a := by
      intro h2
      exact double_zero_impossible hm h12 h1 h2
    simp [zeroIndicator, h2]
  · simp [zeroIndicator, h1]

theorem full_two_indicators_restore_single_zeros
    (a : ℤ) (t : Index)
    (hm : 0 < t.m) (h12 : t.n1 ≠ t.n2) :
    fullIndicator a ((t.q * t.d) * t.r) t.n1 t.m *
        Complex.conj (fullIndicator a ((t.q * t.d) * t.s) t.n2 t.m) =
      firstDeleted a t * Complex.conj (secondDeleted a t) +
      zeroIndicator a t.n1 t.m * Complex.conj (secondDeleted a t) +
      firstDeleted a t * Complex.conj (zeroIndicator a t.n2 t.m) := by
  simp only [fullIndicator_eq_deleted_add_zero]
  change (firstDeleted a t + zeroIndicator a t.n1 t.m) *
      Complex.conj (secondDeleted a t + zeroIndicator a t.n2 t.m) = _
  rw [map_add]
  have hzz := zeroIndicator_product_eq_zero (a := a) hm h12
  calc
    _ = firstDeleted a t * Complex.conj (secondDeleted a t) +
          zeroIndicator a t.n1 t.m * Complex.conj (secondDeleted a t) +
          firstDeleted a t * Complex.conj (zeroIndicator a t.n2 t.m) +
          zeroIndicator a t.n1 t.m *
            Complex.conj (zeroIndicator a t.n2 t.m) := by ring
    _ = _ := by rw [hzz]; ring

def twoDeletedCarrier (a : ℤ) (U : Finset Index) : Finset Index :=
  U.filter (fun t => firstDeleted a t ≠ 0 ∧ secondDeleted a t ≠ 0)

-- F.lambdaAt is the Charts literal st=d, u*v=w convolution. The same
-- m appears in both deleted indicators; the two Lambda factors remain
-- independent and the original alpha pair and outer weights are visible.
def twoDeletedTerm
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) : ℂ :=
  qWeight t.q * F.lambdaAt t.d t.r *
    Complex.conj (F.lambdaAt t.d t.s) *
    alpha t.n1 * Complex.conj (alpha t.n2) * mWeight t.m *
    firstDeleted a t * Complex.conj (secondDeleted a t)

def commonCoefficient
    (F : FactorData) (qWeight mWeight : ℕ → ℂ)
    (alpha : ℕ → ℂ) (t : Index) : ℂ :=
  qWeight t.q * F.lambdaAt t.d t.r *
    Complex.conj (F.lambdaAt t.d t.s) *
    alpha t.n1 * Complex.conj (alpha t.n2) * mWeight t.m

theorem commonCoefficient_norm_le_original_divisors
    (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index)
    (hd : 0 < t.d) (hr : 0 < t.r) (hs : 0 < t.s)
    (hsmall : ∀ s ∈ F.smoothS, SmallPrimeSupportedAt z s)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1) :
    ‖commonCoefficient F qWeight mWeight alpha t‖ ≤
      ‖qWeight t.q‖ * ((t.d * t.r).divisors.card : ℝ) *
        ((t.d * t.s).divisors.card : ℝ) *
        ‖alpha t.n1‖ * ‖alpha t.n2‖ * ‖mWeight t.m‖ := by
  have hrBound := lambdaAt_norm_le_divisors F z t.d t.r
    hd hr hsmall hrough hgamma2 hgamma3
  have hsBound := lambdaAt_norm_le_divisors F z t.d t.s
    hd hs hsmall hrough hgamma2 hgamma3
  calc
    ‖commonCoefficient F qWeight mWeight alpha t‖ =
      ‖qWeight t.q‖ * ‖F.lambdaAt t.d t.r‖ *
        ‖F.lambdaAt t.d t.s‖ * ‖alpha t.n1‖ *
        ‖alpha t.n2‖ * ‖mWeight t.m‖ := by
      simp only [commonCoefficient, norm_mul, norm_conj]
    _ ≤ _ := by
      gcongr
      all_goals assumption

def twoFullTerm
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) : ℂ :=
  commonCoefficient F qWeight mWeight alpha t *
    fullIndicator a ((t.q * t.d) * t.r) t.n1 t.m *
    Complex.conj (fullIndicator a ((t.q * t.d) * t.s) t.n2 t.m)

def firstSingleZeroTerm
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) : ℂ :=
  commonCoefficient F qWeight mWeight alpha t *
    zeroIndicator a t.n1 t.m * Complex.conj (secondDeleted a t)

def secondSingleZeroTerm
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) : ℂ :=
  commonCoefficient F qWeight mWeight alpha t *
    firstDeleted a t * Complex.conj (zeroIndicator a t.n2 t.m)

theorem firstSingleZeroTerm_norm_le_original_divisors
    (a : ℤ) (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index)
    (hd : 0 < t.d) (hr : 0 < t.r) (hs : 0 < t.s)
    (hsmall : ∀ s ∈ F.smoothS, SmallPrimeSupportedAt z s)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1) :
    ‖firstSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      ‖qWeight t.q‖ * ((t.d * t.r).divisors.card : ℝ) *
        ((t.d * t.s).divisors.card : ℝ) *
        ‖alpha t.n1‖ * ‖alpha t.n2‖ * ‖mWeight t.m‖ := by
  have hzero := zeroIndicator_norm_le_one a t.n1 t.m
  have hdel := deletedIndicator_norm_le_one a
    ((t.q * t.d) * t.s) t.n2 t.m
  have hcoeff := commonCoefficient_norm_le_original_divisors F z
    qWeight mWeight alpha t hd hr hs hsmall hrough hgamma2 hgamma3
  have hdrop : ‖firstSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      ‖commonCoefficient F qWeight mWeight alpha t‖ := by
    have h1 : ‖commonCoefficient F qWeight mWeight alpha t‖ *
        ‖zeroIndicator a t.n1 t.m‖ ≤
        ‖commonCoefficient F qWeight mWeight alpha t‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hzero
    have h2 :
        (‖commonCoefficient F qWeight mWeight alpha t‖ *
          ‖zeroIndicator a t.n1 t.m‖) *
          ‖secondDeleted a t‖ ≤
        ‖commonCoefficient F qWeight mWeight alpha t‖ *
          ‖zeroIndicator a t.n1 t.m‖ :=
      mul_le_of_le_one_right (by positivity) hdel
    simpa only [firstSingleZeroTerm, norm_mul, norm_conj,
      secondDeleted] using h2.trans h1
  exact hdrop.trans hcoeff

theorem secondSingleZeroTerm_norm_le_original_divisors
    (a : ℤ) (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index)
    (hd : 0 < t.d) (hr : 0 < t.r) (hs : 0 < t.s)
    (hsmall : ∀ s ∈ F.smoothS, SmallPrimeSupportedAt z s)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1) :
    ‖secondSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      ‖qWeight t.q‖ * ((t.d * t.r).divisors.card : ℝ) *
        ((t.d * t.s).divisors.card : ℝ) *
        ‖alpha t.n1‖ * ‖alpha t.n2‖ * ‖mWeight t.m‖ := by
  have hdel := deletedIndicator_norm_le_one a
    ((t.q * t.d) * t.r) t.n1 t.m
  have hzero := zeroIndicator_norm_le_one a t.n2 t.m
  have hcoeff := commonCoefficient_norm_le_original_divisors F z
    qWeight mWeight alpha t hd hr hs hsmall hrough hgamma2 hgamma3
  have hdrop : ‖secondSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      ‖commonCoefficient F qWeight mWeight alpha t‖ := by
    have h1 : ‖commonCoefficient F qWeight mWeight alpha t‖ *
        ‖firstDeleted a t‖ ≤
        ‖commonCoefficient F qWeight mWeight alpha t‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hdel
    have h2 :
        (‖commonCoefficient F qWeight mWeight alpha t‖ *
          ‖firstDeleted a t‖) *
          ‖zeroIndicator a t.n2 t.m‖ ≤
        ‖commonCoefficient F qWeight mWeight alpha t‖ *
          ‖firstDeleted a t‖ :=
      mul_le_of_le_one_right (by positivity) hzero
    simpa only [secondSingleZeroTerm, norm_mul, norm_conj,
      firstDeleted] using h2.trans h1
  exact hdrop.trans hcoeff

theorem twoFullTerm_eq_deleted_add_single_zeros
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) (hm : 0 < t.m) (h12 : t.n1 ≠ t.n2) :
    twoFullTerm a F qWeight mWeight alpha t =
      twoDeletedTerm a F qWeight mWeight alpha t +
      firstSingleZeroTerm a F qWeight mWeight alpha t +
      secondSingleZeroTerm a F qWeight mWeight alpha t := by
  have h := full_two_indicators_restore_single_zeros a t hm h12
  calc
    twoFullTerm a F qWeight mWeight alpha t =
        commonCoefficient F qWeight mWeight alpha t *
          (fullIndicator a ((t.q * t.d) * t.r) t.n1 t.m *
            Complex.conj
              (fullIndicator a ((t.q * t.d) * t.s) t.n2 t.m)) := by
      unfold twoFullTerm
      ring
    _ = commonCoefficient F qWeight mWeight alpha t *
          (firstDeleted a t * Complex.conj (secondDeleted a t) +
           zeroIndicator a t.n1 t.m * Complex.conj (secondDeleted a t) +
           firstDeleted a t *
             Complex.conj (zeroIndicator a t.n2 t.m)) := by rw [h]
    _ = _ := by
      unfold twoDeletedTerm firstSingleZeroTerm secondSingleZeroTerm
        commonCoefficient
      ring

theorem twoFull_sum_eq_deleted_add_single_zeros
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (U : Finset Index)
    (hm : ∀ t ∈ U, 0 < t.m)
    (h12 : ∀ t ∈ U, t.n1 ≠ t.n2) :
    (∑ t ∈ U, twoFullTerm a F qWeight mWeight alpha t) =
      (∑ t ∈ U, twoDeletedTerm a F qWeight mWeight alpha t) +
      (∑ t ∈ U, firstSingleZeroTerm a F qWeight mWeight alpha t) +
      (∑ t ∈ U, secondSingleZeroTerm a F qWeight mWeight alpha t) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact twoFullTerm_eq_deleted_add_single_zeros a F qWeight mWeight
    alpha t (hm t ht) (h12 t ht)

def firstSingleZeroCarrier (a : ℤ) (U : Finset Index) : Finset Index :=
  U.filter (fun t => zeroIndicator a t.n1 t.m ≠ 0 ∧
    secondDeleted a t ≠ 0)

def secondSingleZeroCarrier (a : ℤ) (U : Finset Index) : Finset Index :=
  U.filter (fun t => firstDeleted a t ≠ 0 ∧
    zeroIndicator a t.n2 t.m ≠ 0)

theorem firstSingleZeroCarrier_data
    {a : ℤ} {U : Finset Index} {t : Index}
    (ht : t ∈ firstSingleZeroCarrier a U) :
    ((t.n1 * t.m : ℕ) : ℤ) = a ∧
    ((t.n2 * t.m : ℕ) : ℤ) - a ≠ 0 ∧
    (((t.q * t.d) * t.s : ℕ) : ℤ) ∣
      ((t.n2 * t.m : ℕ) : ℤ) - a := by
  obtain ⟨_, hzero, hdel⟩ := Finset.mem_filter.mp ht
  have heq : ((t.n1 * t.m : ℕ) : ℤ) = a := by
    by_contra hne
    exact hzero (by simp [zeroIndicator, hne])
  obtain ⟨hnz, hdiv⟩ := deletedIndicator_nonzero_data hdel
  exact ⟨heq, hnz, hdiv⟩

theorem secondSingleZeroCarrier_data
    {a : ℤ} {U : Finset Index} {t : Index}
    (ht : t ∈ secondSingleZeroCarrier a U) :
    ((t.n2 * t.m : ℕ) : ℤ) = a ∧
    ((t.n1 * t.m : ℕ) : ℤ) - a ≠ 0 ∧
    (((t.q * t.d) * t.r : ℕ) : ℤ) ∣
      ((t.n1 * t.m : ℕ) : ℤ) - a := by
  obtain ⟨_, hdel, hzero⟩ := Finset.mem_filter.mp ht
  have heq : ((t.n2 * t.m : ℕ) : ℤ) = a := by
    by_contra hne
    exact hzero (by simp [zeroIndicator, hne])
  obtain ⟨hnz, hdiv⟩ := deletedIndicator_nonzero_data hdel
  exact ⟨heq, hnz, hdiv⟩

theorem firstSingleZero_to_existing_fiber
    {a : ℤ} {A L U : ℕ} {S : Finset ℕ}
    {V : Finset Index} {t : Index}
    (ha : a = (A : ℤ))
    (ht : t ∈ firstSingleZeroCarrier a V)
    (hn2 : t.n2 ∈ Ico L U) (hs : t.s ∈ S)
    (hne : t.n2 ≠ t.n1) :
    (t.n2, t.s) ∈
      firstZeroFiber L U t.m t.n1 t.q t.d A S := by
  obtain ⟨_, _, hdiv⟩ := firstSingleZeroCarrier_data ht
  have hmodDiv : ((t.q * t.d : ℕ) : ℤ) ∣
      ((t.n2 * t.m : ℕ) : ℤ) - (A : ℤ) := by
    have hfactor : ((t.q * t.d : ℕ) : ℤ) ∣
        (((t.q * t.d) * t.s : ℕ) : ℤ) := by
      exact_mod_cast dvd_mul_right (t.q * t.d) t.s
    exact hfactor.trans (ha ▸ hdiv)
  have hmod : Nat.ModEq (t.q * t.d) (t.m * t.n2) A := by
    apply Nat.modEq_iff_dvd.mpr
    have hrev := dvd_neg.mpr hmodDiv
    simpa only [Nat.cast_mul, Nat.mul_comm, neg_sub] using hrev
  have hsDiv : t.s ∣ otherShiftAbs t.m t.n2 A := by
    have hfactor : ((t.s : ℕ) : ℤ) ∣
        (((t.q * t.d) * t.s : ℕ) : ℤ) := by
      exact_mod_cast dvd_mul_left t.s (t.q * t.d)
    have hInt : (t.s : ℤ) ∣
        ((t.n2 * t.m : ℕ) : ℤ) - (A : ℤ) :=
      hfactor.trans (ha ▸ hdiv)
    have hNat := Int.natAbs_dvd_natAbs.mpr hInt
    simpa only [Int.natAbs_natCast, otherShiftAbs, Nat.mul_comm]
      using hNat
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hn2, hs⟩, hne, hmod, hsDiv⟩

theorem firstSingleZero_existing_fiber_count
    {a : ℤ} {A L U : ℕ} {S : Finset ℕ}
    {V : Finset Index} {t : Index}
    (ha : a = (A : ℤ))
    (ht : t ∈ firstSingleZeroCarrier a V)
    (hm : 0 < t.m) (hcop : t.m.Coprime (t.q * t.d))
    (hell : 0 < t.q * t.d) :
    (firstZeroFiber L U t.m t.n1 t.q t.d A S).card ≤
      (U / (t.q * t.d) + 1) *
        secondDivisorEnvelope L U t.m t.n1 t.q t.d A := by
  have hfirstZ := (firstSingleZeroCarrier_data ht).1
  have hfirstN : t.m * t.n1 = A := by
    have hcast : t.n1 * t.m = A := by
      exact_mod_cast hfirstZ.trans ha
    simpa only [Nat.mul_comm] using hcast
  exact firstZeroFiber_card_le_progression_times_divisors
    L U t.m t.n1 t.q t.d A S hm hfirstN hcop hell

theorem secondSingleZero_to_existing_fiber
    {a : ℤ} {A L U : ℕ} {R : Finset ℕ}
    {V : Finset Index} {t : Index}
    (ha : a = (A : ℤ))
    (ht : t ∈ secondSingleZeroCarrier a V)
    (hn1 : t.n1 ∈ Ico L U) (hr : t.r ∈ R)
    (hne : t.n1 ≠ t.n2) :
    (t.n1, t.r) ∈
      firstZeroFiber L U t.m t.n2 t.q t.d A R := by
  obtain ⟨_, _, hdiv⟩ := secondSingleZeroCarrier_data ht
  have hmodDiv : ((t.q * t.d : ℕ) : ℤ) ∣
      ((t.n1 * t.m : ℕ) : ℤ) - (A : ℤ) := by
    have hfactor : ((t.q * t.d : ℕ) : ℤ) ∣
        (((t.q * t.d) * t.r : ℕ) : ℤ) := by
      exact_mod_cast dvd_mul_right (t.q * t.d) t.r
    exact hfactor.trans (ha ▸ hdiv)
  have hmod : Nat.ModEq (t.q * t.d) (t.m * t.n1) A := by
    apply Nat.modEq_iff_dvd.mpr
    have hrev := dvd_neg.mpr hmodDiv
    simpa only [Nat.cast_mul, Nat.mul_comm, neg_sub] using hrev
  have hrDiv : t.r ∣ otherShiftAbs t.m t.n1 A := by
    have hfactor : ((t.r : ℕ) : ℤ) ∣
        (((t.q * t.d) * t.r : ℕ) : ℤ) := by
      exact_mod_cast dvd_mul_left t.r (t.q * t.d)
    have hInt : (t.r : ℤ) ∣
        ((t.n1 * t.m : ℕ) : ℤ) - (A : ℤ) :=
      hfactor.trans (ha ▸ hdiv)
    have hNat := Int.natAbs_dvd_natAbs.mpr hInt
    simpa only [Int.natAbs_natCast, otherShiftAbs, Nat.mul_comm]
      using hNat
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hn1, hr⟩, hne, hmod, hrDiv⟩

theorem secondSingleZero_existing_fiber_count
    {a : ℤ} {A L U : ℕ} {R : Finset ℕ}
    {V : Finset Index} {t : Index}
    (ha : a = (A : ℤ))
    (ht : t ∈ secondSingleZeroCarrier a V)
    (hm : 0 < t.m) (hcop : t.m.Coprime (t.q * t.d))
    (hell : 0 < t.q * t.d) :
    (firstZeroFiber L U t.m t.n2 t.q t.d A R).card ≤
      (U / (t.q * t.d) + 1) *
        secondDivisorEnvelope L U t.m t.n2 t.q t.d A := by
  have hfirstZ := (secondSingleZeroCarrier_data ht).1
  have hfirstN : t.m * t.n2 = A := by
    have hcast : t.n2 * t.m = A := by
      exact_mod_cast hfirstZ.trans ha
    simpa only [Nat.mul_comm] using hcast
  exact firstZeroFiber_card_le_progression_times_divisors
    L U t.m t.n2 t.q t.d A R hm hfirstN hcop hell

def firstFixedSingleZeroRow
    (a : ℤ) (V : Finset Index)
    (q d r m n1 L U : ℕ) (S : Finset ℕ) : Finset Index :=
  (firstSingleZeroCarrier a V).filter (fun t =>
    t.q = q ∧ t.d = d ∧ t.r = r ∧ t.m = m ∧ t.n1 = n1 ∧
      t.n2 ∈ Ico L U ∧ t.s ∈ S ∧ t.n2 ≠ n1)

theorem firstFixedSingleZeroRow_card_le_fiber
    (a : ℤ) (A q d r m n1 L U : ℕ)
    (V : Finset Index) (S : Finset ℕ)
    (ha : a = (A : ℤ)) :
    (firstFixedSingleZeroRow a V q d r m n1 L U S).card ≤
      (firstZeroFiber L U m n1 q d A S).card := by
  apply Finset.card_le_card_of_injOn
    (fun t : Index => (t.n2, t.s))
  · intro t ht
    obtain ⟨hfirst, hq, hd, hr, hm, hn1, hn2, hs, hne⟩ :=
      Finset.mem_filter.mp ht
    have hmem := firstSingleZero_to_existing_fiber ha hfirst hn2 hs hne
    simpa only [hq, hd, hm, hn1] using hmem
  · intro t ht u hu heq
    obtain ⟨_, htq, htd, htr, htm, htn1, _, _, _⟩ :=
      Finset.mem_filter.mp ht
    obtain ⟨_, huq, hud, hur, hum, hun1, _, _, _⟩ :=
      Finset.mem_filter.mp hu
    have htn2 : t.n2 = u.n2 := congrArg Prod.fst heq
    have hts : t.s = u.s := congrArg Prod.snd heq
    exact Index.ext (htq.trans huq.symm) (htd.trans hud.symm)
      (htr.trans hur.symm) hts (htn1.trans hun1.symm) htn2
      (htm.trans hum.symm)

theorem firstFixedSingleZeroRow_card_le_progression_envelope
    (a : ℤ) (A q d r m n1 L U : ℕ)
    (V : Finset Index) (S : Finset ℕ)
    (ha : a = (A : ℤ))
    (hm : 0 < m) (hfirst : m * n1 = A)
    (hcop : m.Coprime (q * d)) (hell : 0 < q * d) :
    (firstFixedSingleZeroRow a V q d r m n1 L U S).card ≤
      (U / (q * d) + 1) *
        secondDivisorEnvelope L U m n1 q d A := by
  exact (firstFixedSingleZeroRow_card_le_fiber a A q d r m n1 L U
    V S ha).trans
      (firstZeroFiber_card_le_progression_times_divisors
        L U m n1 q d A S hm hfirst hcop hell)

theorem firstFixedSingleZeroRow_weighted_divisor_bound
    (a : ℤ) (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (q d r m n1 L U : ℕ) (V : Finset Index) (S : Finset ℕ)
    (hd : 0 < d) (hr : 0 < r) (hS : ∀ s ∈ S, 0 < s)
    (hsmall : ∀ s ∈ F.smoothS, SmallPrimeSupportedAt z s)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1) :
    ‖∑ t ∈ firstFixedSingleZeroRow a V q d r m n1 L U S,
      firstSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖) *
      ∑ t ∈ firstFixedSingleZeroRow a V q d r m n1 L U S,
        ((d * t.s).divisors.card : ℝ) * ‖alpha t.n2‖ := by
  let R := firstFixedSingleZeroRow a V q d r m n1 L U S
  calc
    ‖∑ t ∈ R, firstSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
        ∑ t ∈ R, ‖firstSingleZeroTerm a F qWeight mWeight alpha t‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ t ∈ R,
        (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
          ‖alpha n1‖ * ‖mWeight m‖) *
          (((d * t.s).divisors.card : ℝ) * ‖alpha t.n2‖) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨_, hq, hdEq, hrEq, hmEq, hn1Eq, _, hs, _⟩ :=
        Finset.mem_filter.mp ht
      have hterm := firstSingleZeroTerm_norm_le_original_divisors
        a F z qWeight mWeight alpha t
        (by simpa [hdEq] using hd)
        (by simpa [hrEq] using hr)
        (hS t.s hs) hsmall hrough hgamma2 hgamma3
      calc
        _ ≤ ‖qWeight t.q‖ * ((t.d * t.r).divisors.card : ℝ) *
            ((t.d * t.s).divisors.card : ℝ) *
            ‖alpha t.n1‖ * ‖alpha t.n2‖ *
            ‖mWeight t.m‖ := hterm
        _ = _ := by rw [hq, hdEq, hrEq, hmEq, hn1Eq]; ring
    _ = _ := by rw [Finset.mul_sum]

theorem firstFixedSingleZeroRow_weighted_envelope
    (a : ℤ) (A q d r m n1 L U : ℕ)
    (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (V : Finset Index) (S : Finset ℕ) (T A2 : ℝ)
    (ha : a = (A : ℤ))
    (hm : 0 < m) (hfirst : m * n1 = A)
    (hcop : m.Coprime (q * d)) (hell : 0 < q * d)
    (hd : 0 < d) (hr : 0 < r) (hS : ∀ s ∈ S, 0 < s)
    (hsmall : ∀ s ∈ F.smoothS, SmallPrimeSupportedAt z s)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1)
    (hT : 0 ≤ T) (hA2 : 0 ≤ A2)
    (hTauS : ∀ s ∈ S, ((d * s).divisors.card : ℝ) ≤ T)
    (hAlpha2 : ∀ n ∈ Ico L U, ‖alpha n‖ ≤ A2) :
    ‖∑ t ∈ firstFixedSingleZeroRow a V q d r m n1 L U S,
      firstSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖) *
      (((U / (q * d) + 1) *
        secondDivisorEnvelope L U m n1 q d A : ℕ) : ℝ) * T * A2 := by
  let R := firstFixedSingleZeroRow a V q d r m n1 L U S
  have hweight := firstFixedSingleZeroRow_weighted_divisor_bound
    a F z qWeight mWeight alpha q d r m n1 L U V S
    hd hr hS hsmall hrough hgamma2 hgamma3
  have hcount := firstFixedSingleZeroRow_card_le_progression_envelope
    a A q d r m n1 L U V S ha hm hfirst hcop hell
  have hpoint :
      (∑ t ∈ R, ((d * t.s).divisors.card : ℝ) * ‖alpha t.n2‖) ≤
      (R.card : ℝ) * (T * A2) := by
    calc
      _ ≤ ∑ _t ∈ R, T * A2 := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨_, _, _, _, _, _, hn2, hs, _⟩ :=
          Finset.mem_filter.mp ht
        exact mul_le_mul (hTauS t.s hs) (hAlpha2 t.n2 hn2)
          (norm_nonneg _) hT
      _ = (R.card : ℝ) * (T * A2) := by simp
  have hcap :
      (R.card : ℝ) * (T * A2) ≤
      (((U / (q * d) + 1) *
        secondDivisorEnvelope L U m n1 q d A : ℕ) : ℝ) *
        (T * A2) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hT hA2)
    exact_mod_cast hcount
  have hfactor : 0 ≤
      ‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖ := by positivity
  calc
    _ ≤ (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖) *
      (∑ t ∈ R, ((d * t.s).divisors.card : ℝ) * ‖alpha t.n2‖) := hweight
    _ ≤ (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖) *
        ((((U / (q * d) + 1) *
          secondDivisorEnvelope L U m n1 q d A : ℕ) : ℝ) *
          (T * A2)) :=
      mul_le_mul_of_nonneg_left (hpoint.trans hcap) hfactor
    _ = (‖qWeight q‖ * ((d * r).divisors.card : ℝ) *
        ‖alpha n1‖ * ‖mWeight m‖) *
        (((U / (q * d) + 1) *
          secondDivisorEnvelope L U m n1 q d A : ℕ) : ℝ) * T * A2 := by
      ring

def secondFixedSingleZeroRow
    (a : ℤ) (V : Finset Index)
    (q d s m n2 L U : ℕ) (R : Finset ℕ) : Finset Index :=
  (secondSingleZeroCarrier a V).filter (fun t =>
    t.q = q ∧ t.d = d ∧ t.s = s ∧ t.m = m ∧ t.n2 = n2 ∧
      t.n1 ∈ Ico L U ∧ t.r ∈ R ∧ t.n1 ≠ n2)

theorem secondFixedSingleZeroRow_card_le_fiber
    (a : ℤ) (A q d s m n2 L U : ℕ)
    (V : Finset Index) (R : Finset ℕ)
    (ha : a = (A : ℤ)) :
    (secondFixedSingleZeroRow a V q d s m n2 L U R).card ≤
      (firstZeroFiber L U m n2 q d A R).card := by
  apply Finset.card_le_card_of_injOn
    (fun t : Index => (t.n1, t.r))
  · intro t ht
    obtain ⟨hsecond, hq, hd, hs, hm, hn2, hn1, hr, hne⟩ :=
      Finset.mem_filter.mp ht
    have hmem := secondSingleZero_to_existing_fiber ha hsecond hn1 hr hne
    simpa only [hq, hd, hm, hn2] using hmem
  · intro t ht u hu heq
    obtain ⟨_, htq, htd, hts, htm, htn2, _, _, _⟩ :=
      Finset.mem_filter.mp ht
    obtain ⟨_, huq, hud, hus, hum, hun2, _, _, _⟩ :=
      Finset.mem_filter.mp hu
    have htn1 : t.n1 = u.n1 := congrArg Prod.fst heq
    have htr : t.r = u.r := congrArg Prod.snd heq
    exact Index.ext (htq.trans huq.symm) (htd.trans hud.symm)
      htr (hts.trans hus.symm) htn1 (htn2.trans hun2.symm)
      (htm.trans hum.symm)

theorem secondFixedSingleZeroRow_card_le_progression_envelope
    (a : ℤ) (A q d s m n2 L U : ℕ)
    (V : Finset Index) (R : Finset ℕ)
    (ha : a = (A : ℤ))
    (hm : 0 < m) (hfirst : m * n2 = A)
    (hcop : m.Coprime (q * d)) (hell : 0 < q * d) :
    (secondFixedSingleZeroRow a V q d s m n2 L U R).card ≤
      (U / (q * d) + 1) *
        secondDivisorEnvelope L U m n2 q d A := by
  exact (secondFixedSingleZeroRow_card_le_fiber a A q d s m n2 L U
    V R ha).trans
      (firstZeroFiber_card_le_progression_times_divisors
        L U m n2 q d A R hm hfirst hcop hell)

theorem secondFixedSingleZeroRow_weighted_divisor_bound
    (a : ℤ) (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (q d s m n2 L U : ℕ) (V : Finset Index) (Rough : Finset ℕ)
    (hd : 0 < d) (hs : 0 < s)
    (hRough : ∀ r ∈ Rough, 0 < r)
    (hsmall : ∀ u ∈ F.smoothS, SmallPrimeSupportedAt z u)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1) :
    ‖∑ t ∈ secondFixedSingleZeroRow a V q d s m n2 L U Rough,
      secondSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖) *
      ∑ t ∈ secondFixedSingleZeroRow a V q d s m n2 L U Rough,
        ((d * t.r).divisors.card : ℝ) * ‖alpha t.n1‖ := by
  let R := secondFixedSingleZeroRow a V q d s m n2 L U Rough
  calc
    ‖∑ t ∈ R, secondSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
        ∑ t ∈ R, ‖secondSingleZeroTerm a F qWeight mWeight alpha t‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ t ∈ R,
        (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
          ‖alpha n2‖ * ‖mWeight m‖) *
          (((d * t.r).divisors.card : ℝ) * ‖alpha t.n1‖) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨_, hq, hdEq, hsEq, hmEq, hn2Eq, _, hr, _⟩ :=
        Finset.mem_filter.mp ht
      have hterm := secondSingleZeroTerm_norm_le_original_divisors
        a F z qWeight mWeight alpha t
        (by simpa [hdEq] using hd)
        (hRough t.r hr)
        (by simpa [hsEq] using hs)
        hsmall hrough hgamma2 hgamma3
      calc
        _ ≤ ‖qWeight t.q‖ * ((t.d * t.r).divisors.card : ℝ) *
            ((t.d * t.s).divisors.card : ℝ) *
            ‖alpha t.n1‖ * ‖alpha t.n2‖ *
            ‖mWeight t.m‖ := hterm
        _ = _ := by rw [hq, hdEq, hsEq, hmEq, hn2Eq]; ring
    _ = _ := by rw [Finset.mul_sum]

theorem secondFixedSingleZeroRow_weighted_envelope
    (a : ℤ) (A q d s m n2 L U : ℕ)
    (F : FactorData) (z : ℝ)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (V : Finset Index) (Rough : Finset ℕ) (T A1 : ℝ)
    (ha : a = (A : ℤ))
    (hm : 0 < m) (hfirst : m * n2 = A)
    (hcop : m.Coprime (q * d)) (hell : 0 < q * d)
    (hd : 0 < d) (hs : 0 < s)
    (hRough : ∀ r ∈ Rough, 0 < r)
    (hsmall : ∀ u ∈ F.smoothS, SmallPrimeSupportedAt z u)
    (hrough : ∀ u ∈ F.roughU, RoughPrimeSupportedAt z u)
    (hgamma2 : ∀ k, ‖F.lambdaCoeff k‖ ≤ 1)
    (hgamma3 : ∀ k, ‖F.nuCoeff k‖ ≤ 1)
    (hT : 0 ≤ T) (hA1 : 0 ≤ A1)
    (hTauR : ∀ r ∈ Rough, ((d * r).divisors.card : ℝ) ≤ T)
    (hAlpha1 : ∀ n ∈ Ico L U, ‖alpha n‖ ≤ A1) :
    ‖∑ t ∈ secondFixedSingleZeroRow a V q d s m n2 L U Rough,
      secondSingleZeroTerm a F qWeight mWeight alpha t‖ ≤
      (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖) *
      (((U / (q * d) + 1) *
        secondDivisorEnvelope L U m n2 q d A : ℕ) : ℝ) * T * A1 := by
  let R := secondFixedSingleZeroRow a V q d s m n2 L U Rough
  have hweight := secondFixedSingleZeroRow_weighted_divisor_bound
    a F z qWeight mWeight alpha q d s m n2 L U V Rough
    hd hs hRough hsmall hrough hgamma2 hgamma3
  have hcount := secondFixedSingleZeroRow_card_le_progression_envelope
    a A q d s m n2 L U V Rough ha hm hfirst hcop hell
  have hpoint :
      (∑ t ∈ R, ((d * t.r).divisors.card : ℝ) * ‖alpha t.n1‖) ≤
      (R.card : ℝ) * (T * A1) := by
    calc
      _ ≤ ∑ _t ∈ R, T * A1 := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨_, _, _, _, _, _, hn1, hr, _⟩ :=
          Finset.mem_filter.mp ht
        exact mul_le_mul (hTauR t.r hr) (hAlpha1 t.n1 hn1)
          (norm_nonneg _) hT
      _ = (R.card : ℝ) * (T * A1) := by simp
  have hcap :
      (R.card : ℝ) * (T * A1) ≤
      (((U / (q * d) + 1) *
        secondDivisorEnvelope L U m n2 q d A : ℕ) : ℝ) *
        (T * A1) := by
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hT hA1)
    exact_mod_cast hcount
  have hfactor : 0 ≤
      ‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖ := by positivity
  calc
    _ ≤ (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖) *
      (∑ t ∈ R, ((d * t.r).divisors.card : ℝ) * ‖alpha t.n1‖) := hweight
    _ ≤ (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖) *
        ((((U / (q * d) + 1) *
          secondDivisorEnvelope L U m n2 q d A : ℕ) : ℝ) *
          (T * A1)) :=
      mul_le_mul_of_nonneg_left (hpoint.trans hcap) hfactor
    _ = (‖qWeight q‖ * ((d * s).divisors.card : ℝ) *
        ‖alpha n2‖ * ‖mWeight m‖) *
        (((U / (q * d) + 1) *
          secondDivisorEnvelope L U m n2 q d A : ℕ) : ℝ) * T * A1 := by
      ring

theorem twoDeletedTerm_eq_zero_of_first_zero
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) (h : firstDeleted a t = 0) :
    twoDeletedTerm a F qWeight mWeight alpha t = 0 := by
  simp [twoDeletedTerm, h]

theorem twoDeletedTerm_eq_zero_of_second_zero
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (t : Index) (h : secondDeleted a t = 0) :
    twoDeletedTerm a F qWeight mWeight alpha t = 0 := by
  simp [twoDeletedTerm, h]

theorem twoDeleted_sum_eq_retained
    (a : ℤ) (F : FactorData)
    (qWeight mWeight : ℕ → ℂ) (alpha : ℕ → ℂ)
    (U : Finset Index) :
    (∑ t ∈ U, twoDeletedTerm a F qWeight mWeight alpha t) =
    (∑ t ∈ twoDeletedCarrier a U,
      twoDeletedTerm a F qWeight mWeight alpha t) := by
  rw [twoDeletedCarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h1 : firstDeleted a t = 0
  · simp [h1, twoDeletedTerm_eq_zero_of_first_zero a F qWeight mWeight alpha t h1]
  · by_cases h2 : secondDeleted a t = 0
    · simp [h2, twoDeletedTerm_eq_zero_of_second_zero a F qWeight mWeight alpha t h2]
    · simp [h1, h2]

theorem retained_two_nonzero_shifts
    {a : ℤ} {U : Finset Index} {t : Index}
    (ht : t ∈ twoDeletedCarrier a U) :
    ((t.n1 * t.m : ℕ) : ℤ) - a ≠ 0 ∧
    ((t.n2 * t.m : ℕ) : ℤ) - a ≠ 0 ∧
    (((t.q * t.d) * t.r : ℕ) : ℤ) ∣
      ((t.n1 * t.m : ℕ) : ℤ) - a ∧
    (((t.q * t.d) * t.s : ℕ) : ℤ) ∣
      ((t.n2 * t.m : ℕ) : ℤ) - a := by
  obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp ht
  exact two_congruence_shift_data h1 h2

end
end ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
