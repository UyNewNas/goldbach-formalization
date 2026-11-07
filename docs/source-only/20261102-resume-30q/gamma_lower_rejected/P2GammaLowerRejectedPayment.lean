import ImbalancedChen.P2GammaCompleteProductTrimPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay only the lower complete-product part of P's ACTUAL rejectedWeight.
The rejection is split first at m < H * exp(4 delta); all rejection at
or above that boundary remains in the second summand, unpaid here.
The literal smoothTrim is retained in this discarded summand.

The finite low-product estimate is imported, not reproved.  A fixed
upper comparison H <= C0*N^(1-kappa) and a fixed mesh ceiling delta0
are essential: H >= 2*N^(1-kappa) alone does not make this tail small.
No modulus, residue, conductor, or signed rho enters the grid weights.
-/

namespace ImbalancedChen.P2GammaLowerRejectedPayment
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaCompleteProductTrimPayment P2OriginalGammaUpperLowRankConsumer
open P5OriginalU5CausalFinite (pairSupport)

/-- This is the real, nonnegative representative of the existing complex
rejectedWeight, with precisely the same two finite grid index sums. -/
def rejectedRealWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
    weight δ j (labelHead x) *
      (if Retain N H δ j l (labelComplement x) then 0 else
        weight δ l (product (t.1*t.2) (labelComplement x)))

theorem rejectedRealWeight_cast (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ)
    (K : ℕ) (x : Label) :
    (rejectedRealWeight N t H δ K x : ℂ) = rejectedWeight N t H δ K x := by
  simp only [rejectedRealWeight,rejectedWeight,Complex.ofReal_sum,
    Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : Retain N H δ j l (labelComplement x) <;>
    simp [rejectedLabel,complexWeight,h]

/-- Positivity and the PARTIAL hat partition give norm one without
charging K^2 and without requiring a cover or any residual estimate. -/
theorem rejectedRealWeight_range (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ)
    (K : ℕ) (x : Label) :
    0 ≤ rejectedRealWeight N t H δ K x ∧
      rejectedRealWeight N t H δ K x ≤ 1 := by
  have hb (j l : ℕ) :
      0 ≤ (if Retain N H δ j l (labelComplement x) then (0 : ℝ) else
        weight δ l (product (t.1*t.2) (labelComplement x))) ∧
      (if Retain N H δ j l (labelComplement x) then (0 : ℝ) else
        weight δ l (product (t.1*t.2) (labelComplement x))) ≤
          weight δ l (product (t.1*t.2) (labelComplement x)) := by
    by_cases h : Retain N H δ j l (labelComplement x)
    · simp only [if_pos h]
      exact ⟨le_rfl,weight_nonneg _ _ _⟩
    · simp only [if_neg h]
      exact ⟨weight_nonneg _ _ _,le_rfl⟩
  constructor
  · exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ =>
      mul_nonneg (weight_nonneg _ _ _) (hb j l).1))
  · calc
      _ ≤ ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
          weight δ j (labelHead x) *
            weight δ l (product (t.1*t.2) (labelComplement x)) := by
        exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left (hb j l).2 (weight_nonneg _ _ _)))
      _ = (∑ j ∈ Finset.range K, weight δ j (labelHead x)) *
          (∑ l ∈ Finset.range K,
            weight δ l (product (t.1*t.2) (labelComplement x))) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
      _ ≤ 1 := by
        have h0 : 0 ≤ ∑ l ∈ Finset.range K,
            weight δ l (product (t.1*t.2) (labelComplement x)) :=
          Finset.sum_nonneg (fun _ _ => weight_nonneg _ _ _)
        exact (mul_le_mul (weight_sum_le_one _ _ _)
          (weight_sum_le_one _ _ _) h0 zero_le_one).trans_eq (by norm_num)

/-- First-priority lower split: the boundary itself is assigned to the
remaining upper/order part.  The product is the COMPLETE original m. -/
def rawLowerRejectedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℝ :=
  if (product (t.1*t.2) x : ℝ) < H*Real.exp (4*δ) then
    rejectedRealWeight N t H δ K x else 0

def rawRemainingRejectedWeight (N : ℕ) (t : ℕ × ℕ) (H δ : ℝ) (K : ℕ)
    (x : Label) : ℝ :=
  if (product (t.1*t.2) x : ℝ) < H*Real.exp (4*δ) then 0 else
    rejectedRealWeight N t H δ K x

theorem rejectedWeight_eq_lower_add_remaining (N : ℕ) (t : ℕ × ℕ)
    (H δ : ℝ) (K : ℕ) (x : Label) :
    rejectedWeight N t H δ K x =
      (rawLowerRejectedWeight N t H δ K x : ℂ) +
        (rawRemainingRejectedWeight N t H δ K x : ℂ) := by
  rw [← rejectedRealWeight_cast]
  by_cases h : (product (t.1*t.2) x : ℝ) < H*Real.exp (4*δ) <;>
    simp [rawLowerRejectedWeight,rawRemainingRejectedWeight,h]

theorem rawLowerRejectedWeight_range (N : ℕ) (t : ℕ × ℕ)
    (H δ : ℝ) (K : ℕ) (x : Label) :
    0 ≤ rawLowerRejectedWeight N t H δ K x ∧
      rawLowerRejectedWeight N t H δ K x ≤ 1 := by
  by_cases h : (product (t.1*t.2) x : ℝ) < H*Real.exp (4*δ)
  · simpa only [rawLowerRejectedWeight,if_pos h] using
      rejectedRealWeight_range N t H δ K x
  · simp [rawLowerRejectedWeight,h]

/-- The actual trimmed rejected term.  The empty word has no head row
and is left entirely in the original source, not charged to this split. -/
def wordLowerRejectedWeight (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K : ℕ) (x : Label) : ℝ :=
  if cs=[] then 0 else smoothTrim T (product (t.1*t.2) x) *
    rawLowerRejectedWeight N t H δ K x

theorem wordLowerRejectedWeight_abs_le_one (N : ℕ) (t : ℕ × ℕ)
    (cs : List ℕ) (T H δ : ℝ) (K : ℕ) (x : Label) :
    |wordLowerRejectedWeight N t cs T H δ K x| ≤ 1 := by
  by_cases hcs : cs=[]
  · simp [wordLowerRejectedWeight,hcs]
  · have hr := rawLowerRejectedWeight_range N t H δ K x
    have h0 : 0 ≤ smoothTrim T (product (t.1*t.2) x) :=
      Real.smoothTransition.nonneg _
    have h1 : smoothTrim T (product (t.1*t.2) x) ≤ 1 :=
      Real.smoothTransition.le_one _
    simp only [wordLowerRejectedWeight,if_neg hcs,
      abs_of_nonneg (mul_nonneg h0 hr.1)]
    exact (mul_le_mul h1 hr.2 hr.1 zero_le_one).trans_eq (by norm_num)

/-- The existing rejected sum splits exactly, with the literal trim and
same test F.  No estimate for the remaining summand is asserted. -/
theorem original_rejected_trim_split (N : ℕ) (t : ℕ × ℕ)
    (c : ℕ) (cs : List ℕ) (T H δ : ℝ) (K : ℕ) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs), rejectedWeight N t H δ K x *
      (smoothTrim T (product (t.1*t.2) x) : ℂ) * F (product (t.1*t.2) x)) =
    (∑ x ∈ rootLabels N t (c::cs),
      (wordLowerRejectedWeight N t (c::cs) T H δ K x : ℂ) *
        F (product (t.1*t.2) x)) +
    ∑ x ∈ rootLabels N t (c::cs),
      (rawRemainingRejectedWeight N t H δ K x : ℂ) *
        (smoothTrim T (product (t.1*t.2) x) : ℂ) * F (product (t.1*t.2) x) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [rejectedWeight_eq_lower_add_remaining]
  simp only [wordLowerRejectedWeight,List.cons_ne_nil,if_false,
    Complex.ofReal_mul]
  ring

/-- Compose the existing exact reconstruction and proved trim plateau
with the new split.  All rows are fixed before the arbitrary test F.
The last summand is the unchanged, UNPAID upper/order remainder. -/
theorem original_trimmed_word_eq_retained_add_lower_add_remaining
    {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (c : ℕ) (cs : List ℕ)
    {T H δ : ℝ} (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ)
    {K : ℕ} (hK : Real.log (N : ℝ)/δ+1 ≤ K) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (smoothTrim T (product (t.1*t.2) x) : ℂ)*F (product (t.1*t.2) x)) =
    (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
      ∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::cs),
        (complexWeight δ j p*betaLabel N t H δ j l y)*
          F (product (t.1*t.2) y*p)) +
    (∑ x ∈ rootLabels N t (c::cs),
      (wordLowerRejectedWeight N t (c::cs) T H δ K x : ℂ)*
        F (product (t.1*t.2) x)) +
    ∑ x ∈ rootLabels N t (c::cs),
      (rawRemainingRejectedWeight N t H δ K x : ℂ)*
        (smoothTrim T (product (t.1*t.2) x) : ℂ)*F (product (t.1*t.2) x) := by
  have hrow (j l : ℕ) :
      (∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::cs),
        (complexWeight δ j p*betaLabel N t H δ j l y)*
          ((smoothTrim T (product (t.1*t.2) y*p) : ℂ)*
            F (product (t.1*t.2) y*p))) =
      ∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::cs),
        (complexWeight δ j p*betaLabel N t H δ j l y)*
          F (product (t.1*t.2) y*p) := by
    rw [← original_retained_row_eq_cartesian ht c cs hδ j l
      (fun m => (smoothTrim T m : ℂ)*F m)]
    calc
      _ = ∑ x ∈ rootLabels N t (c::cs),
          (complexWeight δ j (labelHead x)*
            betaLabel N t H δ j l (labelComplement x))*
              (smoothTrim T (product (t.1*t.2) x) : ℂ)*F (product (t.1*t.2) x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := original_retained_trimmed_row_eq_cartesian ht c cs hT hH hδ j l F
  have hbase := original_word_eq_retained_rows_add_rejected ht c cs hδ hK
    (fun m => (smoothTrim T m : ℂ)*F m)
  simp only [hrow] at hbase
  have hsplit := original_rejected_trim_split N t c cs T H δ K F
  simp only [mul_assoc] at hbase hsplit ⊢
  rw [hbase,hsplit]
  ring

/-- The enlarged INTEGER cutoff, not the old cutoff ceil(2T). -/
def enlargedCut (H δ : ℝ) : ℕ := ⌈H*Real.exp (4*δ)⌉₊

theorem wordLowerRejectedWeight_eq_zero_above (N : ℕ) (t : ℕ × ℕ)
    (cs : List ℕ) (T H δ : ℝ) (K : ℕ) (x : Label)
    (hx : enlargedCut H δ < product (t.1*t.2) x) :
    wordLowerRejectedWeight N t cs T H δ K x = 0 := by
  have hcut : H*Real.exp (4*δ) ≤ (product (t.1*t.2) x : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hx.le)
  simp [wordLowerRejectedWeight,rawLowerRejectedWeight,not_lt.mpr hcut]

/-- Fixed constants precede N; H and delta may vary at every later N.
No small-mesh limit or selection depending on rho is required here. -/
theorem eventually_enlargedCut_bounds (kappa C0 delta0 : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (hC0 : 0 < C0) :
    ∀ᶠ N : ℕ in atTop, ∀ H δ : ℝ,
      0 ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → δ ≤ delta0 →
      enlargedCut H δ < N ∧ (enlargedCut H δ : ℝ) ≤
        (C0*Real.exp (4*delta0)+1)*(N : ℝ)^(1-kappa) := by
  let E : ℝ := C0*Real.exp (4*delta0)+1
  filter_upwards [eventually_powerLog_le_logAccuracy E (1-kappa) 0 0
    (by linarith) (1/2) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  intro H δ hH hHC hδ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT1 : 1 ≤ (N : ℝ)^(1-kappa) :=
    Real.one_le_rpow hN1 (by linarith)
  have hprod : H*Real.exp (4*δ) ≤
      C0*Real.exp (4*delta0)*(N : ℝ)^(1-kappa) := by
    have he : Real.exp (4*δ) ≤ Real.exp (4*delta0) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ (C0*(N : ℝ)^(1-kappa))*Real.exp (4*delta0) :=
        mul_le_mul hHC he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hY : (enlargedCut H δ : ℝ) ≤ E*(N : ℝ)^(1-kappa) := by
    have hc := (Nat.ceil_lt_add_one (mul_nonneg hH (Real.exp_pos _).le)).le
    dsimp [enlargedCut]
    dsimp [E]
    nlinarith
  have hhalf : E*(N : ℝ)^(1-kappa) ≤ (1/2)*(N : ℝ) := by
    simpa only [pow_zero,mul_one,div_one] using hsmall
  refine ⟨?_,hY⟩
  have hlt : (enlargedCut H δ : ℝ) < N := by linarith
  exact_mod_cast hlt

def wordLowerRejectedError (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  wordError N t cs Q rho (wordLowerRejectedWeight N t cs T H δ K)

/-- Invoke P's finite ACTUAL low-label/modulus budget at the enlarged
cut.  Its two divisor constants and exact coprime mean are unchanged.
The only new estimate is the fixed-cutoff inflation conversion. -/
theorem eventually_word_lowerRejected_logAccuracy (cs : List ℕ)
    (kappa C0 delta0 : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (hC0 : 0 < C0) (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (T H δ : ℝ) (K M : ℕ)
      (Q : Finset ℕ) (rho : ℕ → ℝ),
      0 ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → δ ≤ delta0 →
      M ≤ N → Q ⊆ Finset.Icc 1 M → (∀ q ∈ Q, |rho q| ≤ 1) →
      |wordLowerRejectedError N t cs Q rho T H δ K| ≤
        eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,D,hC,hD,hbudget⟩ := exists_word_low_product_budget cs
    (show 0 < kappa/4 by positivity)
  let E : ℝ := C0*Real.exp (4*delta0)+1
  have hE : 0 < E := by dsimp [E]; positivity
  filter_upwards
    [eventually_enlargedCut_bounds kappa C0 delta0 hkappa hkappa1 hC0,
      eventually_powerLog_le_logAccuracy (E*C*D) (1-kappa/2) 0 A
        (by linarith) (eta/3) (by positivity),
      eventually_powerLog_le_logAccuracy (4*E*C) (1-3*kappa/4) 0 A
        (by linarith) (eta/3) (by positivity),
      eventually_powerLog_le_logAccuracy (4*E*C) (1-3*kappa/4) 1 A
        (by linarith) (eta/3) (by positivity),
      eventually_ge_atTop (2 : ℕ)] with N hcut hAP hM0 hM1 hN
  intro t ht T H δ K M Q rho hH hHC hδ hMN hQ hrho
  obtain ⟨hYN,hY⟩ := hcut H δ hH hHC hδ
  have hbound := hbudget N (enlargedCut H δ) M t ht Q rho
    (wordLowerRejectedWeight N t cs T H δ K) hYN hQ hrho
    (fun x _ => wordLowerRejectedWeight_abs_le_one N t cs T H δ K x)
    (fun x _ hx => wordLowerRejectedWeight_eq_zero_above N t cs T H δ K x hx)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : Real.log (max 1 (M : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hN1 (by exact_mod_cast hMN))
  have hB0 : 0 ≤ D*(N : ℝ)^(kappa/4)+4*(1+Real.log (max 1 (M : ℝ))) := by
    have hl := Real.log_nonneg (le_max_left (1 : ℝ) (M : ℝ))
    positivity
  have hp1 : (N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4) =
      (N : ℝ)^(1-3*kappa/4) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hp2 : (N : ℝ)^(1-3*kappa/4)*(N : ℝ)^(kappa/4) =
      (N : ℝ)^(1-kappa/2) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    _ ≤ (E*(N : ℝ)^(1-kappa))*(C*(N : ℝ)^(kappa/4))*
        (D*(N : ℝ)^(kappa/4)+4*(1+Real.log (N : ℝ))) := by
      apply hbound.trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hY (by positivity))
        (by linarith) hB0 (by positivity)
    _ = E*C*D*(N : ℝ)^(1-kappa/2)+4*E*C*(N : ℝ)^(1-3*kappa/4)+
        4*E*C*(N : ℝ)^(1-3*kappa/4)*Real.log (N : ℝ) := by
      calc
        _ = E*C*D*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))*(N : ℝ)^(kappa/4)+
            4*E*C*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))+
            4*E*C*((N : ℝ)^(1-kappa)*(N : ℝ)^(kappa/4))*Real.log (N : ℝ) := by ring
        _ = _ := by rw [hp1]; rw [mul_assoc (E*C*D),hp2]
    _ ≤ _ := by
      simp only [pow_zero,pow_one,mul_one] at hAP hM0 hM1
      linarith

def listLowerRejectedError (L : List (List ℕ)) (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (L.map (fun cs => wordLowerRejectedError N t cs Q rho T H δ K)).sum

/-- Induction is on occurrences, with one threshold before every later
t,T,H,delta,K,Q,rho.  No finite occurrence count is evaluated. -/
theorem eventually_list_lowerRejected_logAccuracy (L : List (List ℕ))
    (kappa C0 delta0 : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (hC0 : 0 < C0) (A : ℕ) :
    ∀ eta : ℝ, 0 < eta →
      ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (T H δ : ℝ) (K M : ℕ)
        (Q : Finset ℕ) (rho : ℕ → ℝ),
        0 ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) → δ ≤ delta0 →
        M ≤ N → Q ⊆ Finset.Icc 1 M → (∀ q ∈ Q, |rho q| ≤ 1) →
        |listLowerRejectedError L N t Q rho T H δ K| ≤
          eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  induction L with
  | nil =>
      intro eta heta
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      intro t ht T H δ K M Q rho hH hHC hδ hMN hQ hrho
      have hlog : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
      simp only [listLowerRejectedError,List.map_nil,List.sum_nil,abs_zero]
      positivity
  | cons cs L ih =>
      intro eta heta
      filter_upwards
        [eventually_word_lowerRejected_logAccuracy cs kappa C0 delta0
          hkappa hkappa1 hC0 A (eta/2) (by positivity),
          ih (eta/2) (by positivity)] with N hword htail
      intro t ht T H δ K M Q rho hH hHC hδ hMN hQ hrho
      have hw := hword t ht T H δ K M Q rho hH hHC hδ hMN hQ hrho
      have hl := htail t ht T H δ K M Q rho hH hHC hδ hMN hQ hrho
      change |wordLowerRejectedError N t cs Q rho T H δ K+
        listLowerRejectedError L N t Q rho T H δ K| ≤ _
      exact (abs_add _ _).trans ((add_le_add hw hl).trans_eq (by ring))

/-- Literal nested mother lists and original root labels, including
every repeated word/representation and the original unit quotient. -/
def originalLowerRejectedKernel (N : ℕ) (t : ℕ × ℕ)
    (T H δ : ℝ) (K q : ℕ) : ℝ :=
  (Wu2008DoubleSieve.secondFunctionalMotherPrefixIndices.map fun i =>
    ((Wu2008DoubleSieve.secondFunctionalMotherGammaWords i).map fun cs =>
      ∑ x ∈ rootLabels N t cs,
        wordLowerRejectedWeight N t cs T H δ K x *
          gammaKernel N q (product (t.1*t.2) x)).sum).sum

theorem originalLowerRejected_sum_eq_literal_list (N : ℕ) (t : ℕ × ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) :
    (∑ q ∈ Q, rho q * originalLowerRejectedKernel N t T H δ K q) =
      listLowerRejectedError originalMotherOccurrences N t Q rho T H δ K := by
  have hflat (I : List ℕ) (f : List ℕ → ℝ) :
      ((I.flatMap Wu2008DoubleSieve.secondFunctionalMotherGammaWords).map f).sum =
        (I.map fun i =>
          ((Wu2008DoubleSieve.secondFunctionalMotherGammaWords i).map f).sum).sum := by
    induction I with
    | nil => simp
    | cons i I ih =>
        simp only [List.flatMap_cons,List.map_append,List.sum_append,
          List.map_cons,List.sum_cons,ih]
  have hsource (q : ℕ) : rho q*originalLowerRejectedKernel N t T H δ K q =
      (originalMotherOccurrences.map fun cs => rho q*
        ∑ x ∈ rootLabels N t cs,
          wordLowerRejectedWeight N t cs T H δ K x *
            gammaKernel N q (product (t.1*t.2) x)).sum := by
    unfold originalLowerRejectedKernel originalMotherOccurrences
    rw [hflat]
    simp only [List.sum_map_mul_left]
  simp_rw [hsource]
  have hcomm (L : List (List ℕ)) :
      (∑ q ∈ Q, (L.map fun cs => rho q*
        ∑ x ∈ rootLabels N t cs,
          wordLowerRejectedWeight N t cs T H δ K x *
            gammaKernel N q (product (t.1*t.2) x)).sum) =
        listLowerRejectedError L N t Q rho T H δ K := by
    induction L with
    | nil => simp [listLowerRejectedError]
    | cons cs L ih =>
        simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih,
          listLowerRejectedError,wordLowerRejectedError,wordError]
  exact hcomm originalMotherOccurrences

/-- One original-N threshold pays the enlarged lower rejected part on
the retained-row smoothTrim plateau.  Grid cover is still needed for
P's reconstruction, but not for this payment; no K or mesh cost is lost.
This is not an estimate for the remaining upper/order rejected term. -/
theorem eventually_original_Gamma_lowerRejected_logAccuracy
    (kappa C0 delta0 : ℝ) (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (hC0 : 0 < C0) (A : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ pairSupport N, ∀ (H δ : ℝ) (K M : ℕ)
      (Q : Finset ℕ) (rho : ℕ → ℝ),
      2*(N : ℝ)^(1-kappa) ≤ H → H ≤ C0*(N : ℝ)^(1-kappa) →
      0 < δ → δ ≤ delta0 → M ≤ N → Q ⊆ Finset.Icc 1 M →
      (∀ q ∈ Q, |rho q| ≤ 1) →
      |∑ q ∈ Q, rho q * originalLowerRejectedKernel N t
        ((N : ℝ)^(1-kappa)) H δ K q| ≤
          eta*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_list_lowerRejected_logAccuracy originalMotherOccurrences
    kappa C0 delta0 hkappa hkappa1 hC0 A eta heta] with N hN
  intro t ht H δ K M Q rho hH hHC hδ0 hδ hMN hQ hrho
  rw [originalLowerRejected_sum_eq_literal_list]
  exact hN t ht ((N : ℝ)^(1-kappa)) H δ K M Q rho
    ((by positivity : 0 ≤ 2*(N : ℝ)^(1-kappa)).trans hH)
    hHC hδ hMN hQ hrho

end
end ImbalancedChen.P2GammaLowerRejectedPayment
