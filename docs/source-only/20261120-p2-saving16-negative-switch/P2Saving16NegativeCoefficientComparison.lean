import ImbalancedChen.P2Saving16OriginalPhysicalEightSource
import ImbalancedChen.P2Saving16NegativeOriginalFibreSum

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Exact negative-Mobius coefficient comparison on the same actual full
modulus. The two original support decisions are computed predicates, not
an assumed equality with the compiler correction. -/
namespace ImbalancedChen.P2Saving16NegativeCoefficientComparison
noncomputable section
open scoped Classical BigOperators
open Set
open P5OriginalCommonRefinedConstructor
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16NegativeOriginalFibreSum P2Saving16OriginalPhysicalEightSource
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P4AOriginalOrderedThirdActualCoefficient (keep)

/-- Signed original new-minus-parent coefficient in units of beta-minus.
The original policy support decisions are kept distinct. -/
def originalSwitch (old fresh : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (d : ℕ) : ℝ :=
  (if d ∈ rawSupport old N cap w z then 1 else 0) -
    (if d ∈ rawSupport fresh N cap w z then 1 else 0)

/-- An actual rough modulus is squarefree; negative Möbius is therefore
exactly -1. -/
theorem negative_mu_eq_neg_one (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z) (hneg : (ArithmeticFunction.moebius d : ℝ) < 0) :
    (ArithmeticFunction.moebius d : ℝ) = -1 := by
  have hunit : |(ArithmeticFunction.moebius d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (P2LowerFiniteCellRounding.universe_squarefree N cap w z hd)
  rw [abs_of_neg hneg] at hunit
  linarith

/-- For the literal old or fresh policy, the negative word's raw
attachment reads the signed beta-minus coefficient at the full product. -/
theorem negative_raw_at_product (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) {s d : ℕ} (hs : s ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ universe N cap w z) (hneg : (ArithmeticFunction.moebius d : ℝ) < 0) :
    actualSmallRoughRho ret N cap w z L (s*d) =
      -(if d ∈ rawSupport ret N cap w z then actualSmallRosserMinus N cap w L s else 0) := by
  have hmu := negative_mu_eq_neg_one N cap w z hd hneg
  have h := smallRoughRho_mul
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
    (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
    (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L) hs hd
  rw [raw_attachment_eq_actual ret N cap w z L] at h
  change actualSmallRoughRho ret N cap w z L (s*d) =
    signAttachedCoefficient (raw ret N cap w z d)
      (actualSmallRosserMinus N cap w L s) (actualSmallRosserPlus N cap w L s) at h
  rw [h, raw_value]
  by_cases hr : d ∈ rawSupport ret N cap w z <;>
    simp [hr, hmu, signAttachedCoefficient]

/-- The full-q original new-minus-parent coefficient is the exact old/new
support switch times the same beta-minus. -/
theorem negative_original_difference_at_product
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {s d : ℕ}
    (hs : s ∈ actualSmallRosserSupport N cap w) (hd : d ∈ universe N cap w z)
    (hneg : (ArithmeticFunction.moebius d : ℝ) < 0) :
    actualSmallRoughRho fresh N cap w z L (s*d) -
      actualSmallRoughRho old N cap w z L (s*d) =
      originalSwitch old fresh N cap w z d * actualSmallRosserMinus N cap w L s := by
  rw [negative_raw_at_product fresh N cap w z L hs hd hneg,
    negative_raw_at_product old N cap w z L hs hd hneg]
  unfold originalSwitch
  by_cases ho : d ∈ rawSupport old N cap w z <;>
    by_cases hf : d ∈ rawSupport fresh N cap w z <;> simp [ho, hf] <;> ring

/-- The exact switch equals one precisely for an original old-retained,
new-unretained word; this is a support test, not a target equality premise. -/
theorem switch_eq_one_iff_original_delete
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    originalSwitch old fresh N cap w z d = 1 ↔
      d ∈ rawSupport old N cap w z ∧ d ∉ rawSupport fresh N cap w z := by
  classical
  unfold originalSwitch
  by_cases ho : d ∈ rawSupport old N cap w z <;>
    by_cases hf : d ∈ rawSupport fresh N cap w z <;> norm_num [ho, hf]


/-- Exact original switch values: deletion +1, addition -1, and zero
when the two original policies make the same support decision. -/
theorem original_switch_three_cases
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    originalSwitch old fresh N cap w z d =
      if d ∈ rawSupport old N cap w z ∧ d ∉ rawSupport fresh N cap w z then 1
      else if d ∈ rawSupport fresh N cap w z ∧ d ∉ rawSupport old N cap w z then -1
      else 0 := by
  classical
  unfold originalSwitch
  by_cases ho : d ∈ rawSupport old N cap w z <;>
    by_cases hf : d ∈ rawSupport fresh N cap w z <;> norm_num [ho, hf]

/-- Pointwise comparison for one actual negative-inner compiler occurrence.
Both source coefficients and the compiler correction use the same s*d and G. -/
theorem selected_original_and_compiler_coefficients
    (old fresh ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ)
    {x : ℕ × ℕ} (hx : x ∈ selected ret tag N cap w z tau delta i) :
    x.1*x.2 ∈ support N cap w z ∧
    (actualSmallRoughRho fresh N cap w z L (x.1*x.2) -
      actualSmallRoughRho old N cap w z L (x.1*x.2)) * G (x.1*x.2) =
        originalSwitch old fresh N cap w z x.2 *
          actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) ∧
    (rho ret tag N cap w z tau L (x.1*x.2) -
      actualSmallRoughRho ret N cap w z L (x.1*x.2)) * G (x.1*x.2) =
        actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) := by
  have hp := Finset.mem_filter.mp hx
  have hc : x.1 ∈ actualSmallRosserSupport N cap w ∧ x.2 ∈ universe N cap w z :=
    Finset.mem_product.mp hp.1
  have hneg : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := hp.2.2.2.1
  have hQ : x.1*x.2 ∈ support N cap w z :=
    selected_moduli_subset_Q ret tag N cap w z tau delta i
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hsource := negative_original_difference_at_product old fresh N cap w z L hc.1 hc.2 hneg
  refine ⟨hQ, ?_, selected_term_is_actual_compiler_difference ret tag N cap w z tau delta L i G hx⟩
  rw [hsource]


/-- If the actual beta/discrepancy product is nonzero, the original
source and compiler correction agree exactly when the original old tree
retains d and the original new tree does not. No such deletion is assumed. -/
theorem selected_match_iff_original_delete
    (old fresh ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ)
    {x : ℕ × ℕ} (hx : x ∈ selected ret tag N cap w z tau delta i)
    (hnonzero : actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) ≠ 0) :
    ((actualSmallRoughRho fresh N cap w z L (x.1*x.2) -
      actualSmallRoughRho old N cap w z L (x.1*x.2)) * G (x.1*x.2) =
      (rho ret tag N cap w z tau L (x.1*x.2) -
        actualSmallRoughRho ret N cap w z L (x.1*x.2)) * G (x.1*x.2)) ↔
      x.2 ∈ rawSupport old N cap w z ∧ x.2 ∉ rawSupport fresh N cap w z := by
  have h := selected_original_and_compiler_coefficients old fresh ret tag N cap w z tau delta L i G hx
  rw [h.2.1, h.2.2]
  constructor
  · intro heq
    have hm : (originalSwitch old fresh N cap w z x.2 - 1) *
        (actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2)) = 0 := by
      calc
        _ = originalSwitch old fresh N cap w z x.2 *
              actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) -
              actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) := by ring
        _ = 0 := sub_eq_zero.mpr heq
    have hs : originalSwitch old fresh N cap w z x.2 = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hnonzero)
    exact (switch_eq_one_iff_original_delete old fresh N cap w z x.2).mp hs
  · intro hdelete
    rw [(switch_eq_one_iff_original_delete old fresh N cap w z x.2).mpr hdelete]
    ring

/-- All three possible original signs and the compiler correction are
kept in the exact discrepancy on the selected pair family. -/
theorem selected_original_minus_compiler_gap
    (old fresh ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) :
    (∑ x ∈ selected ret tag N cap w z tau delta i,
      (actualSmallRoughRho fresh N cap w z L (x.1*x.2) -
        actualSmallRoughRho old N cap w z L (x.1*x.2)) * G (x.1*x.2)) -
      selectedSum ret tag N cap w z tau delta L i G =
    ∑ x ∈ selected ret tag N cap w z tau delta i,
      (originalSwitch old fresh N cap w z x.2 - 1) *
        actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) := by
  unfold selectedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have h := selected_original_and_compiler_coefficients old fresh ret tag N cap w z tau delta L i G hx
  rw [h.2.1]
  ring

/-- The actual union bank, original old/fresh policies and signed compiler
have the above exact coefficient gap at the same physical scales. -/
theorem actual_bank_selected_negative_gap
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ) (N : ℕ) (i : Fin 14)
    (b T : ℝ) :
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    let old := policy6 bank (N : ℝ) false
    let fresh := originalPolicy bank N false
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ)^(nu*beta)
    let ret := keep r n e q a omega N
    let G := P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T
    (∑ x ∈ selected ret (fun _ => []) N N w z tau (width r) i,
      (actualSmallRoughRho fresh N N w z L (x.1*x.2) -
        actualSmallRoughRho old N N w z L (x.1*x.2)) * G (x.1*x.2)) -
      selectedSum ret (fun _ => []) N N w z tau (width r) L i G =
    ∑ x ∈ selected ret (fun _ => []) N N w z tau (width r) i,
      (originalSwitch old fresh N N w z x.2 - 1) *
        actualSmallRosserMinus N N w L x.1 * G (x.1*x.2) := by
  exact selected_original_minus_compiler_gap
    (policy6 (P4AOriginalFull87UnionHistory.bank e q a) (N : ℝ) false)
    (originalPolicy (P4AOriginalFull87UnionHistory.bank e q a) N false)
    (keep r n e q a (nu*beta^2) N) (fun _ => []) N N
    ((N : ℝ)^(nu*beta^2)) (P4AOriginalFull87RawChronology.cutoff N)
    tau (width r) ((N : ℝ)^(nu*beta)) i
    (P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T)


/-- The precise coefficient comparison on the same scheduled original
ordered eight-prefix and its admitted fourth ancestor. All quantities use
the actual bank, the same positive-w carrier, beta and full modulus. -/
theorem scheduled_actual_negative_coefficient
    (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        q0 ≤ q → a ≤ 1 / 100 → nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) (b T : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        let old := policy6 bank (N : ℝ) false
        let fresh := originalPolicy bank N false
        let omega := nu*beta^2
        let w := (N : ℝ)^omega
        let z := P4AOriginalFull87RawChronology.cutoff N
        let L := (N : ℝ)^(nu*beta)
        let ret := keep r n e q a omega N
        let G := P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T
        ∀ x ∈ selected ret (fun _ => []) N N w z tau (width r) i,
          let p := canonicalPrefix 8 x.2
          p ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z) ∧
          primeHistoryTuple 4 (rosserAncestor 4
            (P2OriginalFourteenRetainedTupleOwnership.history p)) ∈
              firstExitAdmittedTuples 4 (oddFirstExitPolicy ret)
                (roughPrimeUniverse N N w z) ∧
          x.1*x.2 ∈ support N N w z ∧
          (actualSmallRoughRho fresh N N w z L (x.1*x.2) -
            actualSmallRoughRho old N N w z L (x.1*x.2)) * G (x.1*x.2) =
            originalSwitch old fresh N N w z x.2 *
              actualSmallRosserMinus N N w L x.1 * G (x.1*x.2) ∧
          (rho ret (fun _ => []) N N w z tau L (x.1*x.2) -
            actualSmallRoughRho ret N N w z L (x.1*x.2)) * G (x.1*x.2) =
              actualSmallRosserMinus N N w L x.1 * G (x.1*x.2) := by
  obtain ⟨e0, he0, h⟩ := tuples_are_scheduled_original_fourths r
  refine ⟨e0, he0, ?_⟩
  intro e he he0e
  obtain ⟨q0, hq0⟩ := h e he he0e
  refine ⟨q0, ?_⟩
  intro n q a nu beta tau hq ha hcut hh N hN i b T
  dsimp only
  intro x hx
  let w := (N : ℝ)^(nu*beta^2)
  let z := P4AOriginalFull87RawChronology.cutoff N
  let ret := keep r n e q a (nu*beta^2) N
  let G := P2Saving16SameRhoDistributionFrontier.realHalfProductDiscrepancy b N T
  have hkey : canonicalPrefix 8 x.2 ∈ tuples ret (fun _ => []) N N w z tau (width r) i :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hanc := hq0 n q a nu beta tau hq ha hcut hh N hN i (canonicalPrefix 8 x.2) hkey
  have hcoeff := selected_original_and_compiler_coefficients
    (policy6 (P4AOriginalFull87UnionHistory.bank e q a) (N : ℝ) false)
    (originalPolicy (P4AOriginalFull87UnionHistory.bank e q a) N false)
    ret (fun _ => []) N N w z tau (width r) ((N : ℝ)^(nu*beta)) i G hx
  exact ⟨hanc.1, hanc.2, hcoeff.1, hcoeff.2.1, hcoeff.2.2⟩

end
end ImbalancedChen.P2Saving16NegativeCoefficientComparison
