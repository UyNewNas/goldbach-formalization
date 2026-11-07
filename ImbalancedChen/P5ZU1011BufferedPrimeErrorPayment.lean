import ImbalancedChen.P5ZU1011BufferedActualSixteenError

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual four-prime weights pay true physical positive errors before ANY
moving keep mask or tuple-dependent physical buffer maps. The original
domain/eligibility are tested at the actual tuple, never at a mesh snap.
-/

namespace ImbalancedChen.P5Z.BufferedPrimeErrorPayment

noncomputable section

open Set
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenKnotPayment
open U1011AdaptivePrimeError BufferedOrdinaryClamp BufferedActualSixteenError

abbrev Tuple := Fin 4 → ℕ
abbrev BufferMap := Policy → Tuple → ℝ

def tuples (N : ℕ) : Finset Tuple := actualPrimeBoxTuples N
  (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
def weight (t : Tuple) : ℝ := ∏ i, 1 / ((t i : ℝ) - 1)

def SmallOn (N : ℕ) (δ e : ℝ) (τ ξ ρ : BufferMap) : Prop :=
  ∀ t ∈ tuples N, Small δ e (fun p => τ p t) (fun p => ξ p t) (fun p => ρ p t)

def policyError (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
    (τ ξ ρ : BufferMap) (p : Policy) : ℝ := ∑ t ∈ tuples N,
  if keep t ∧ actualPrimeTupleLog N t ∈ originalDomain mask ∧ TypedEligible p (actualPrimeTupleLog N t)
  then weight t * max 0 (physicalCost (typedResidual p (actualPrimeTupleLog N t))
    (actualPrimeTupleLog N t 3) (τ p t) (ξ p t) (ρ p t) -
      originalCost (typedResidual p (actualPrimeTupleLog N t)) (actualPrimeTupleLog N t 3)) else 0

def envelopeError (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
    (τ ξ ρ : BufferMap) : ℝ := ∑ t ∈ tuples N,
  if keep t ∧ actualPrimeTupleLog N t ∈ originalDomain mask then
    weight t * max 0 (bufferedEnvelope (fun p => τ p t) (fun p => ξ p t) (fun p => ρ p t)
      (actualPrimeTupleLog N t) - targetEnvelope (actualPrimeTupleLog N t)) else 0

def totalError (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop) (τ ξ ρ : BufferMap) : ℝ :=
  (∑ p : Policy, policyError N mask keep τ ξ ρ p) + envelopeError N mask keep τ ξ ρ

def payment (N : ℕ) (keep : Tuple → Prop) (δ e : ℝ) : ℝ :=
  e * actualPrimeBoxMass N (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) +
    badCostBound * maskedStripMass N keep δ

private theorem finite_weight_payment (N : ℕ) (keep active : Tuple → Prop) (f : Tuple → ℝ)
    {δ e : ℝ} (he : 0 ≤ e) (hkeep : ∀ t, active t → keep t)
    (hpaid : ∀ t ∈ tuples N, active t → f t ≤ pointError δ e (actualPrimeTupleLog N t)) :
    (∑ t ∈ tuples N, if active t then weight t * f t else 0) ≤ payment N keep δ e := by
  unfold payment actualPrimeBoxMass maskedStripMass
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hweight : 0 ≤ weight t := actualPrimeBoxWeight_nonneg ht
  have heWeight : 0 ≤ e * weight t := mul_nonneg he hweight
  by_cases hact : active t
  · have hk := hkeep t hact
    have hh := mul_le_mul_of_nonneg_left (hpaid t ht hact) hweight
    simp only [if_pos hact]
    by_cases hbad : actualPrimeTupleLog N t ∈ knotStrip δ
    · simp only [pointError, if_pos hbad] at hh
      simp only [hk, hbad, and_self, if_true]
      change weight t * f t ≤ e * weight t + badCostBound * weight t
      nlinarith only [hh, heWeight]
    · simp only [pointError, if_neg hbad] at hh
      simp only [hbad, and_false, if_false, mul_zero, add_zero]
      simpa only [mul_comm, weight] using hh
  · simp only [if_neg hact]
    by_cases hb : keep t ∧ actualPrimeTupleLog N t ∈ knotStrip δ
    · rw [if_pos hb]
      exact add_nonneg heWeight (mul_nonneg badCostBound_pos.le hweight)
    · rw [if_neg hb, mul_zero, add_zero]
      exact heWeight

theorem policyError_le_payment (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) (τ ξ ρ : BufferMap)
    (hsmall : SmallOn N δ e τ ξ ρ) (p : Policy) :
    policyError N mask keep τ ξ ρ p ≤ payment N keep δ e := by
  apply finite_weight_payment N keep _ _ he.le (fun t ht => ht.1)
  intro t ht hact
  have hUpper := ordinary_upper mask p hact.2.1 hact.2.2 hd he (hsmall t ht)
  apply max_le (pointError_nonneg he.le _)
  linarith only [hUpper]

theorem envelopeError_le_payment (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) (τ ξ ρ : BufferMap)
    (hsmall : SmallOn N δ e τ ξ ρ) :
    envelopeError N mask keep τ ξ ρ ≤ payment N keep δ e := by
  apply finite_weight_payment N keep _ _ he.le (fun t ht => ht.1)
  intro t ht hact
  have hUpper := envelope_upper mask hact.2 hd he (hsmall t ht)
  apply max_le (pointError_nonneg he.le _)
  linarith only [hUpper]

/-- All sixteen policies PLUS the true nonlinear guarded minimum are
paid together. This seventeen is solely an optional reporting sum; the
minimum itself still incurs ONE error, independently of bank size. -/
theorem totalError_le_payment (N : ℕ) (mask : Set (ℝ × ℝ)) (keep : Tuple → Prop)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) (τ ξ ρ : BufferMap)
    (hsmall : SmallOn N δ e τ ξ ρ) :
    totalError N mask keep τ ξ ρ ≤ 17 * payment N keep δ e := by
  have hp : (∑ p : Policy, policyError N mask keep τ ξ ρ p) ≤ 16 * payment N keep δ e := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Policy))
      (fun p _ => policyError_le_payment N mask keep hd he τ ξ ρ hsmall p)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have he' := envelopeError_le_payment N mask keep hd he τ ξ ρ hsmall
  dsimp only [totalError]
  linarith only [hp, he']

end

end ImbalancedChen.P5Z.BufferedPrimeErrorPayment
