import ImbalancedChen.P2GammaJointDiscardedPayment

/-!
Source-only / UNCOMPILED / KERNEL-UNVERIFIED.
Exact original Gamma -> retained Cartesian rows + paid joint remainder.
The retained object is a direct finite sum, never defined by subtraction.
A possible empty mother word is explicitly preserved as an unchanged
trimmed lane; no nonempty-word assertion is assumed or silently inferred.
This is a reduction to retained PP, NOT the retained PP estimate itself.
-/

namespace ImbalancedChen.P2GammaJointRetainedReduction
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2OriginalGammaUpperLowRankConsumer
open P2OriginalU5ExactNormalizedSource
open P2GammaOriginalCartesianMask P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaCompleteProductTrimPayment P2GammaLowerRejectedPayment
open P2GammaOrderingStripPayment P2GammaJointLabels P2GammaJointUpperPayment
open P2GammaJointRemainingPayment P2GammaJointDiscardedPayment
open P5OriginalU5CausalFinite (pairSupport)

/-- Explicit retained rows with the unchanged head carrier, complement
labels and beta mask. The nil branch is kept rather than pretending a
head-prime extraction exists for an empty word. -/
def retainedWordKernel (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (T H δ : ℝ) (K q : ℕ) : ℝ :=
  match cs with
  | [] => ∑ x ∈ rootLabels N t [],
      smoothTrim T (product (t.1*t.2) x)*gammaKernel N q (product (t.1*t.2) x)
  | c::ds =>
      (∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K,
        ∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::ds),
          (complexWeight δ j p*betaLabel N t H δ j l y)*
            (gammaKernel N q (product (t.1*t.2) y*p) : ℂ)).re

/-- Q16's exact complex reconstruction, at the actual real AP-minus-
coprime-mean kernel, including its proved trim plateau on retained rows. -/
theorem trimmed_word_split {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (cs : List ℕ) {T H δ : ℝ} (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ)
    {K : ℕ} (hK : Real.log (N : ℝ)/δ+1 ≤ K) (q : ℕ) :
    (∑ x ∈ rootLabels N t cs,
      smoothTrim T (product (t.1*t.2) x)*gammaKernel N q (product (t.1*t.2) x)) =
      retainedWordKernel N t cs T H δ K q+
      (∑ x ∈ rootLabels N t cs,
        wordLowerRejectedWeight N t cs T H δ K x*gammaKernel N q (product (t.1*t.2) x))+
      ∑ x ∈ rootLabels N t cs,
        wordRemainingRejectedWeight N t cs T H δ K x*gammaKernel N q (product (t.1*t.2) x) := by
  cases cs with
  | nil => simp [retainedWordKernel,wordLowerRejectedWeight,wordRemainingRejectedWeight]
  | cons c cs =>
      have h := original_trimmed_word_eq_retained_add_lower_add_remaining ht c cs
        hT hH hδ hK (fun m => (gammaKernel N q m : ℂ))
      have hr := congrArg Complex.re h
      simp only [← Complex.ofReal_mul,← Complex.ofReal_sum,Complex.add_re,Complex.ofReal_re] at hr
      have hrem :
          (∑ x ∈ rootLabels N t (c::cs),rawRemainingRejectedWeight N t H δ K x*
            smoothTrim T (product (t.1*t.2) x)*gammaKernel N q (product (t.1*t.2) x)) =
          ∑ x ∈ rootLabels N t (c::cs),wordRemainingRejectedWeight N t (c::cs) T H δ K x*
            gammaKernel N q (product (t.1*t.2) x) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [wordRemainingRejectedWeight,List.cons_ne_nil,if_false]
        ring
      rw [hrem] at hr
      exact hr

/-- Pointwise algebra of the original trim, followed by the actual row
reconstruction; no analytic estimate is a premise. -/
theorem untrimmed_word_split {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (cs : List ℕ) {T H δ : ℝ} (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ)
    {K : ℕ} (hK : Real.log (N : ℝ)/δ+1 ≤ K) (q : ℕ) :
    (∑ x ∈ rootLabels N t cs,gammaKernel N q (product (t.1*t.2) x)) =
      retainedWordKernel N t cs T H δ K q+
      (∑ x ∈ rootLabels N t cs,
        trimRemainder T (product (t.1*t.2) x)*gammaKernel N q (product (t.1*t.2) x))+
      (∑ x ∈ rootLabels N t cs,
        wordLowerRejectedWeight N t cs T H δ K x*gammaKernel N q (product (t.1*t.2) x))+
      ∑ x ∈ rootLabels N t cs,
        wordRemainingRejectedWeight N t cs T H δ K x*gammaKernel N q (product (t.1*t.2) x) := by
  have htrim := trimmed_word_split ht cs hT hH hδ hK q
  have hsplit :
      (∑ x ∈ rootLabels N t cs,gammaKernel N q (product (t.1*t.2) x)) =
      (∑ x ∈ rootLabels N t cs,smoothTrim T (product (t.1*t.2) x)*
        gammaKernel N q (product (t.1*t.2) x))+
      ∑ x ∈ rootLabels N t cs,trimRemainder T (product (t.1*t.2) x)*
        gammaKernel N q (product (t.1*t.2) x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [trimRemainder]
    ring
  linarith

private theorem list_flatMap_sum {α β : Type*} (I : List α)
    (J : α → List β) (f : β → ℝ) :
    ((I.flatMap J).map f).sum =
      (I.map (fun i => ((J i).map f).sum)).sum := by
  induction I with
  | nil => simp
  | cons i I ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,
        List.map_cons,List.sum_cons,ih]

/-- Pure literal-list flattening of the existing sourceTest. -/
theorem sourceTest_eq_occurrences (N : ℕ) (t : ℕ × ℕ) (F : ℕ → ℝ) :
    sourceTest N t F =
      (originalMotherOccurrences.map (fun cs =>
        ∑ x ∈ rootLabels N t cs,F (product (t.1*t.2) x))).sum := by
  unfold sourceTest originalMotherOccurrences
  exact (list_flatMap_sum _ _ _).symm

private theorem sum_map_scale_comm (L : List (List ℕ)) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (F : ℕ → List ℕ → ℝ) :
    (∑ q ∈ Q,rho q*(L.map (F q)).sum) =
      (L.map (fun cs => ∑ q ∈ Q,rho q*F q cs)).sum := by
  induction L with
  | nil => simp
  | cons cs L ih =>
      simp only [List.map_cons,List.sum_cons,mul_add,Finset.sum_add_distrib,ih]

def retainedPairError (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  (originalMotherOccurrences.map
    (fun cs => ∑ q ∈ Q,rho q*retainedWordKernel N t cs T H δ K q)).sum

theorem original_pair_split {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (Q : Finset ℕ) (rho : ℕ → ℝ) {T H δ : ℝ}
    (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ)
    {K : ℕ} (hK : Real.log (N : ℝ)/δ+1 ≤ K) :
    (∑ q ∈ Q,rho q*gammaDiscrepancy N t q) =
      retainedPairError N t Q rho T H δ K+
      listTrimError originalMotherOccurrences N t Q rho T+
      listLowerRejectedError originalMotherOccurrences N t Q rho T H δ K+
      originalRemainingRejectedError N t Q rho T H δ K := by
  have hraw : (∑ q ∈ Q,rho q*gammaDiscrepancy N t q) =
      (originalMotherOccurrences.map (fun cs => wordError N t cs Q rho (fun _ => 1))).sum := by
    simp only [gammaDiscrepancy,sourceTest_eq_occurrences,wordError,one_mul]
    exact sum_map_scale_comm _ Q rho _
  have hword (cs : List ℕ) : wordError N t cs Q rho (fun _ => 1) =
      (∑ q ∈ Q,rho q*retainedWordKernel N t cs T H δ K q)+
      wordError N t cs Q rho (fun x => trimRemainder T (product (t.1*t.2) x))+
      wordLowerRejectedError N t cs Q rho T H δ K+
      wordError N t cs Q rho (wordRemainingRejectedWeight N t cs T H δ K) := by
    simp only [wordError,one_mul]
    simp_rw [untrimmed_word_split ht cs hT hH hδ hK]
    simp only [mul_add,Finset.sum_add_distrib,wordLowerRejectedError,wordError]
  have hlist (L : List (List ℕ)) :
      (L.map (fun cs => wordError N t cs Q rho (fun _ => 1))).sum =
      (L.map (fun cs => ∑ q ∈ Q,rho q*retainedWordKernel N t cs T H δ K q)).sum+
      listTrimError L N t Q rho T+listLowerRejectedError L N t Q rho T H δ K+
      (L.map (fun cs => wordError N t cs Q rho
        (wordRemainingRejectedWeight N t cs T H δ K))).sum := by
    induction L with
    | nil => simp [listTrimError,listLowerRejectedError]
    | cons cs L ih =>
        rw [List.map_cons,List.sum_cons,hword,ih]
        simp only [listTrimError,listLowerRejectedError,List.map_cons,List.sum_cons]
        ring
  rw [hraw]
  exact hlist originalMotherOccurrences

def originalJointGammaError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*∑ q ∈ Q,rho q*gammaDiscrepancy N t q

def originalJointRetainedError (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*retainedPairError N t Q rho T H δ K

/-- All original labels, occurrence multiplicities and the same rho
survive the exact outer-sum reconstruction. No injective product fiction. -/
theorem originalJointGammaError_eq_retained_add_discarded
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ)
    {T H δ : ℝ} (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ)
    {K : ℕ} (hK : Real.log (N : ℝ)/δ+1 ≤ K) :
    originalJointGammaError N Q rho sigma =
      originalJointRetainedError N Q rho sigma T H δ K+
        originalJointDiscardedError N Q rho sigma T H δ K := by
  rw [originalJointDiscardedError,originalJointLowError_eq_outer]
  unfold originalJointGammaError originalJointRetainedError originalJointRemainingError
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [original_pair_split ht Q rho hT hH hδ hK]
  ring

/-- Concrete choices of trim, lower endpoint and grid. They are analysis
parameters, not an identification of the causal physical rootQ. -/
def chosenWidth (A N : ℕ) : ℝ :=
  boundaryLogMesh (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) N

def chosenGrid (A N : ℕ) : ℕ := ⌈Real.log (N : ℝ)/chosenWidth A N+1⌉₊

theorem chosenWidth_range {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) (A : ℕ) :
    0 < chosenWidth A N ∧ chosenWidth A N ≤ 1 := by
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hp : 1 ≤ (Real.log (N : ℝ))^
      (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A) := by
    simpa only [pow_zero] using pow_le_pow_right₀ hlog
      (Nat.zero_le (orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A))
  dsimp [chosenWidth,boundaryLogMesh]
  refine ⟨one_div_pos.mpr (pow_pos hl _),?_⟩
  apply (div_le_iff₀ (pow_pos hl _)).mpr
  simpa only [one_mul] using hp

/-- Fully instantiated discarded-side reduction. In particular no Y,
cutoff-size, grid-cover, thin-count or energy licence is an input.
The retained side is still an explicit nontrivial arithmetic sum. -/
theorem eventually_originalJointGamma_retained_reduction
    (C : ℝ) (hC : 0 < C) (A : ℕ) (kappa : ℝ)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ),
      Q ⊆ Finset.Icc 1 N → (∀ q ∈ Q,|rho q| ≤ 1) →
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ C) →
      |originalJointGammaError N Q rho sigma-
        originalJointRetainedError N Q rho sigma ((N : ℝ)^(1-kappa))
          (2*(N : ℝ)^(1-kappa)) (chosenWidth A N) (chosenGrid A N)| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_originalJointDiscardedError_height C hC A kappa 2 1
      hkappa hkappa1 (by norm_num) eta heta,
    eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)] with N hpay hlog hN
  intro Q rho sigma hQ hrho hsigma
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hT : 0 < (N : ℝ)^(1-kappa) := Real.rpow_pos_of_pos hNp _
  have hd := chosenWidth_range hlog A
  have hK : Real.log (N : ℝ)/chosenWidth A N+1 ≤ (chosenGrid A N : ℝ) := Nat.le_ceil _
  have hsplit := originalJointGammaError_eq_retained_add_discarded N Q rho sigma
    hT (le_refl _) hd.1 hK
  rw [hsplit,add_sub_cancel_left]
  exact hpay Q rho sigma _ _ _ _ hQ hrho hsigma hT (le_refl _) (le_refl _)
    hd.1 hd.2 (le_refl _)

end
end ImbalancedChen.P2GammaJointRetainedReduction
