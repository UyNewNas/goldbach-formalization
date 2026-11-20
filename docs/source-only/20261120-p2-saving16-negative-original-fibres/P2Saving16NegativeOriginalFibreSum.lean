import ImbalancedChen.P2Saving16CommonTrimNegativeFibre
import ImbalancedChen.P2Saving16SignedCorrectionFamilies
import ImbalancedChen.P2Saving16ActualCompilerDifference

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The actual negative-inner pair occurrences on one original trimmed cell
are grouped by their ordered eight-prefix, keeping each full product and
its signed beta-minus test. The untouched complement stays in the same
negative-inner sum; no new bound or reserve is asserted. -/
namespace ImbalancedChen.P2Saving16NegativeOriginalFibreSum
noncomputable section
open scoped Classical BigOperators
open Set
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P2Saving16CommonTrimNegativeFibre P2Saving16FirstRowCompilerFibre
open P2Saving16SameRhoDistributionFrontier P2Saving16ActualFourthFrontier P2Saving16ActualFourthTuples
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87CompiledCounting (moduli)

/-- The precise negative-inner test used by the existing correction sum. -/
def negativeTest (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  (ArithmeticFunction.moebius d : ℝ) < 0 ∧
    d ∈ rawSupport ret N cap w z ∧ ¬inner ret tag N cap w z tau d

/-- A single original cell, with its actual full rough word and rank. -/
def selected (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (i : Fin 14) : Finset (ℕ × ℕ) :=
  (smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z)).filter
    (fun x => 8 ≤ x.2.primeFactorsList.length ∧
      firstEightCoordinates N x.2 ∈ trim (sourceCell i) delta ∧
      negativeTest ret tag N cap w z tau x.2)

def tuples (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (i : Fin 14) : Finset (Fin 8 → ℕ) :=
  (selected ret tag N cap w z tau delta i).image (fun x => canonicalPrefix 8 x.2)

def negativeTerm (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) (x : ℕ × ℕ) : ℝ :=
  (if negativeTest ret tag N cap w z tau x.2 then
    actualSmallRosserMinus N cap w L x.1 else 0) * G (x.1 * x.2)

def selectedSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ selected ret tag N cap w z tau delta i,
    actualSmallRosserMinus N cap w L x.1 * G (x.1 * x.2)

def complementSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ (smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z)).filter
      (fun x => ¬ (8 ≤ x.2.primeFactorsList.length ∧
        firstEightCoordinates N x.2 ∈ trim (sourceCell i) delta ∧
        negativeTest ret tag N cap w z tau x.2)),
    negativeTerm ret tag N cap w z tau L G x

def fibreSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14)
    (G : ℕ → ℝ) (p : Fin 8 → ℕ) : ℝ :=
  ∑ x ∈ (selected ret tag N cap w z tau delta i).filter
      (fun x => canonicalPrefix 8 x.2 = p),
    actualSmallRosserMinus N cap w L x.1 * G (x.1 * x.2)

/-- Literal splitting of the existing negative-inner sum. The complement
continues to contain its original indicator and signed full-q weight. -/
theorem negativeInner_exact_split (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) :
    negativeInnerSum ret tag N cap w z tau L G =
      selectedSum ret tag N cap w z tau delta L i G +
        complementSum ret tag N cap w z tau delta L i G := by
  classical
  let C := smallRoughPairs (actualSmallRosserSupport N cap w) (universe N cap w z)
  let P : ℕ × ℕ → Prop := fun x => 8 ≤ x.2.primeFactorsList.length ∧
    firstEightCoordinates N x.2 ∈ trim (sourceCell i) delta ∧
    negativeTest ret tag N cap w z tau x.2
  let F := negativeTerm ret tag N cap w z tau L G
  have hs : (∑ x ∈ C.filter P, F x) = selectedSum ret tag N cap w z tau delta L i G := by
    change (∑ x ∈ selected ret tag N cap w z tau delta i, F x) = _
    unfold selectedSum
    apply Finset.sum_congr rfl
    intro x hx
    have htest : negativeTest ret tag N cap w z tau x.2 := (Finset.mem_filter.mp hx).2.2.2
    simp only [F, negativeTerm, if_pos htest]
  have hsplit := Finset.sum_filter_add_sum_filter_not C P F
  symm
  change selectedSum ret tag N cap w z tau delta L i G +
      complementSum ret tag N cap w z tau delta L i G =
    negativeInnerSum ret tag N cap w z tau L G
  change selectedSum ret tag N cap w z tau delta L i G +
      (∑ x ∈ C.filter (fun x => ¬ P x), F x) = ∑ x ∈ C, F x
  rw [← hs]
  exact hsplit

/-- Fibres preserve every selected (s,d) occurrence and its literal
beta-minus times G(s*d). Equal eight-prefixes are not collapsed to one term. -/
theorem selectedSum_eq_ordered_eight_fibres
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) :
    selectedSum ret tag N cap w z tau delta L i G =
      ∑ p ∈ tuples ret tag N cap w z tau delta i,
        fibreSum ret tag N cap w z tau delta L i G p := by
  classical
  unfold selectedSum tuples fibreSum
  exact (Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem (fun y : ℕ × ℕ => canonicalPrefix 8 y.2) hx)
    (fun x : ℕ × ℕ => actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2))).symm

/-- A physical modulus has at most one selected small/rough pair. This
does not claim that different d with the same eight-prefix are equal. -/
theorem selected_full_modulus_injective
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (i : Fin 14)
    {x y : ℕ × ℕ} (hx : x ∈ selected ret tag N cap w z tau delta i)
    (hy : y ∈ selected ret tag N cap w z tau delta i)
    (hxy : x.1*x.2 = y.1*y.2) : x = y := by
  have hx' : x.1 ∈ actualSmallRosserSupport N cap w ∧ x.2 ∈ universe N cap w z := by
    exact Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy' : y.1 ∈ actualSmallRosserSupport N cap w ∧ y.2 ∈ universe N cap w z := by
    exact Finset.mem_product.mp (Finset.mem_filter.mp hy).1
  have h := product_unique N cap w z hx'.1 hx'.2 hy'.1 hy'.2 hxy
  exact Prod.ext h.1 h.2

/-- Each selected signed weight is exactly the compiler-minus-raw
correction at its own full modulus, with no independent sieve bound. -/
theorem selected_term_is_actual_compiler_difference
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ)
    {x : ℕ × ℕ} (hx : x ∈ selected ret tag N cap w z tau delta i) :
    (rho ret tag N cap w z tau L (x.1*x.2) -
      actualSmallRoughRho ret N cap w z L (x.1*x.2)) * G (x.1*x.2) =
      actualSmallRosserMinus N cap w L x.1 * G (x.1*x.2) := by
  have hp := Finset.mem_filter.mp hx
  have hcarrier : x.1 ∈ actualSmallRosserSupport N cap w ∧ x.2 ∈ universe N cap w z :=
    Finset.mem_product.mp hp.1
  have hn := hp.2.2.2
  have hneg : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := hn.1
  have hc : changed ret tag N cap w z tau x.2 := by
    simpa only [changed, if_neg (not_le_of_gt hneg)] using hn.2
  have h := actual_weighted_product_correction ret tag N cap w z tau L hcarrier.1 hcarrier.2 G
  simpa only [if_pos hc, if_neg (not_le_of_gt hneg)] using h



/-- Every selected full modulus belongs to the actual compiler Q. -/
theorem selected_moduli_subset_Q
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (i : Fin 14) :
    (selected ret tag N cap w z tau delta i).image (fun x => x.1*x.2) ⊆
      support N cap w z := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
  change x.1*x.2 ∈ smallRoughModuli (actualSmallRosserSupport N cap w) (universe N cap w z)
  exact Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩

/-- The selected pair sum equals the actual compiler-minus-raw weighted
sum over its full-q image. Injectivity prevents a repeated full modulus. -/
theorem selectedSum_eq_full_Q_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (i : Fin 14) (G : ℕ → ℝ) :
    (∑ m ∈ (selected ret tag N cap w z tau delta i).image (fun x => x.1*x.2),
      (rho ret tag N cap w z tau L m - actualSmallRoughRho ret N cap w z L m) * G m) =
      selectedSum ret tag N cap w z tau delta L i G := by
  classical
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1*x.2)
      (selected ret tag N cap w z tau delta i) := by
    intro x hx y hy hxy
    exact selected_full_modulus_injective ret tag N cap w z tau delta i hx hy hxy
  rw [Finset.sum_image hinj]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro x hx
  exact selected_term_is_actual_compiler_difference ret tag N cap w z tau delta L i G hx

/-- Every grouped key is an original-policy admitted eight-tuple and its
own compiler-policy fourth ancestor. The retained fibre still contains all
separate full moduli that gave this key. -/
theorem tuples_are_scheduled_original_fourths (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        q0 ≤ q → a ≤ 1 / 100 → nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) (p : Fin 8 → ℕ),
          let w := (N : ℝ)^(nu*beta^2)
          let z := P4AOriginalFull87RawChronology.cutoff N
          let f := keep r n e q a (nu*beta^2) N
          p ∈ tuples f (fun _ => []) N N w z tau (width r) i →
          p ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z) ∧
          primeHistoryTuple 4 (rosserAncestor 4
            (P2OriginalFourteenRetainedTupleOwnership.history p)) ∈
            firstExitAdmittedTuples 4 (oddFirstExitPolicy f)
              (roughPrimeUniverse N N w z) := by
  obtain ⟨e0, he0, h⟩ := scheduled_negative_inner_one_trim r
  refine ⟨e0, he0, ?_⟩
  intro e he he0e
  obtain ⟨q0, hq0⟩ := h e he he0e
  refine ⟨q0, ?_⟩
  intro n q a nu beta tau
  dsimp only
  intro hq ha hcut hh N hN i p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  have hsel := Finset.mem_filter.mp hx
  have hpair : x.1 ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu*beta^2)) ∧
      x.2 ∈ universe N N ((N : ℝ)^(nu*beta^2))
        (P4AOriginalFull87RawChronology.cutoff N) := Finset.mem_product.mp hsel.1
  have hrank := hsel.2.1
  have ht := hsel.2.2.1
  have hn := hsel.2.2.2
  have hneg : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := hn.1
  have hc : changed (keep r n e q a (nu*beta^2) N) (fun _ => []) N N
      ((N : ℝ)^(nu*beta^2)) (P4AOriginalFull87RawChronology.cutoff N) tau x.2 := by
    simpa only [changed, if_neg (not_le_of_gt hneg)] using hn.2
  have hs := hq0 n q a nu beta tau hq ha hcut hh N hN i hrank ht hpair.1 hneg hc 0 0
  exact ⟨hs.1, hs.2.1⟩

/-- The existing same-Q, same-rho signed distribution error now exposes
one original-cell negative-inner family by ordered eight-prefix, with the
remaining negative-inner terms preserved once in their exact complement. -/
theorem r17_distribution_error_with_original_eight_fibres
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (N : ℕ) (i : Fin 14) (b T : ℝ) :
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let rho := coefficient r n e q a omega N tau L
    let f := keep r n e q a omega N
    let G := realHalfProductDiscrepancy b N T
    realPhysicalDistributionError b N T Q rho =
      stoppedBeforeFour f N N w z L G +
        (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f)
            (roughPrimeUniverse N N w z), fourthTupleTerm f N N w z L G p) +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          ((∑ p ∈ tuples f (fun _ => []) N N w z tau (width r) i,
              fibreSum f (fun _ => []) N N w z tau (width r) L i G p) +
            complementSum f (fun _ => []) N N w z tau (width r) L i G)) := by
  have h := r17_distribution_error_on_actual_fourths r n e q a nu beta tau N b T
  rw [negativeInner_exact_split _ _ _ _ _ _ _ (width r) _ i _,
    selectedSum_eq_ordered_eight_fibres] at h
  exact h

end
end ImbalancedChen.P2Saving16NegativeOriginalFibreSum
