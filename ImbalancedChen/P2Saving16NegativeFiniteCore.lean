import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P4AOriginalFull87HistoryCore
import ImbalancedChen.P4AOriginalFull87Ownership
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding

/-! SOURCE_ONLY / NOT COMPILED / UNEVALUATED.

Mechanical relocation of 31 existing finite declarations, with their
original namespaces and public names. The identity ledger records the
two permitted lexical compatibility edits and the private helper move.
Scheduled and analytic theorems remain with their original heavy owners.
See docs/source-only/20261125-p2-5-fourteen-family/README.md.
-/

namespace ImbalancedChen.P2CanonicalWallFullResidualPayment
noncomputable section
open scoped Classical BigOperators

abbrev Prefix (j : ℕ) := Fin j → ℕ

/-- The prefix is the first j primes in the actual canonical decreasing
word. The construction is total, but its data theorems retain j<=rank. -/
def canonicalPrefix (j r : ℕ) : Prefix j :=
  primeHistoryTuple j ((r.primeFactorsList.reverse.take j).reverse)

end
end ImbalancedChen.P2CanonicalWallFullResidualPayment

namespace ImbalancedChen.P2Saving16FirstRowCompilerFibre
noncomputable section
open scoped Classical BigOperators

def firstEightCoordinates (N d : ℕ) : Fin 8 → ℝ :=
  primeHistoryLogCoordinates (N : ℝ) 8 (rosserAncestor 8 d.primeFactorsList)

end
end ImbalancedChen.P2Saving16FirstRowCompilerFibre

namespace ImbalancedChen.P4AOriginalFull87StrictActionTrim
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope P4AOriginalFull87SourceDictionary

theorem source_iff_rows (c : Cell) (t : Point) :
    Source c t ↔ ∀ r : Fin (rowCount c), 0 < rowValue c r t := by
  cases c <;> rfl

inductive Margin where
  | positive
  | improvement
  | full (j : Fin 8)
  | complement (j : Fin 8)
  deriving DecidableEq, Fintype

/-- Selected slots impose no new complementary-square requirement. -/
def actionSlack (c : Cell) (t : Point) : Margin → ℝ
  | .positive => newCap c t
  | .improvement => newCap c t - comparison c t
  | .full j => newCap c t - prefixSquareExpr t j
  | .complement j =>
      if j ∈ selected c then newCap c t
      else newCap c t - selectedSquareExpr (selected c) t j

/-- Unlike Source intersect the old history core, this entire set is
closed and compact.  Every strict source row has the same positive floor. -/
def trim (c : Cell) (delta : ℝ) : Set Point :=
  P4AOriginalFull87HistoryCore.core delta ∩
    (⋂ r : Fin (rowCount c), {t | delta ≤ rowValue c r t}) ∩
    (⋂ j : Margin, {t | delta ≤ actionSlack c t j})

theorem mem_trim (c : Cell) (delta : ℝ) (t : Point) :
    t ∈ trim c delta ↔
      t ∈ P4AOriginalFull87HistoryCore.core delta ∧
      (∀ r : Fin (rowCount c), delta ≤ rowValue c r t) ∧
      (∀ j : Margin, delta ≤ actionSlack c t j) := by
  simp only [trim, mem_inter_iff, mem_iInter, mem_ofPred_eq, and_assoc]

theorem trim_subset_source (c : Cell) {delta : ℝ} (hd : 0 < delta) :
    trim c delta ⊆ sourceSet c := by
  intro t ht
  apply (source_iff_rows c t).mpr
  exact fun r => hd.trans_le (((mem_trim c delta t).mp ht).2.1 r)

end
end ImbalancedChen.P4AOriginalFull87StrictActionTrim

namespace ImbalancedChen.P4AFull87TaggedAtomValue
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler

abbrev CellKey := List Bool × List ℤ

def fibre (tag : ℕ → List Bool) (N cap : ℕ) (w z tau : ℝ) (j : CellKey) :=
  («universe» N cap w z).filter fun m => label tag N tau m=j

def admit (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (w z tau : ℝ) (j : CellKey) : Prop :=
  if 0≤(-1:ℝ)^j.2.length then
    (fibre tag N cap w z tau j ∩ rawSupport ret N cap w z).Nonempty
  else fibre tag N cap w z tau j ⊆ rawSupport ret N cap w z

def occupied (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (w z tau : ℝ) (d : ℕ) : ℝ :=
  if d ∈ «universe» N cap w z ∧ admit ret tag N cap w z tau (label tag N tau d) then 1 else 0

theorem literal_value (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (w z tau : ℝ) (d : ℕ) :
    coefficient ret tag N cap w z tau d =
      (ArithmeticFunction.moebius d:ℝ) * occupied ret tag N cap w z tau d := by
  by_cases hd : d ∈ «universe» N cap w z
  · have hs := P2LowerFiniteCellRounding.universe_squarefree N cap w z hd
    have hm : (ArithmeticFunction.moebius d:ℝ) =
        (-1:ℝ)^(label tag N tau d).2.length := by
      simp only [label,primeWordLabel,P2LowerFiniteCellRounding.label,List.length_map,List.length_reverse]
      rw [ArithmeticFunction.moebius_apply_of_squarefree hs,ArithmeticFunction.cardFactors_apply]
      push_cast <;> rfl
    change coefficient ret tag N cap w z tau d = _
    simp only [coefficient,if_pos hd,occupied,hd,true_and,admit,fibre,← hm]
    unfold outer inner cell
    split_ifs <;> simp
  · simp [coefficient,occupied,hd]

end
end ImbalancedChen.P4AFull87TaggedAtomValue

namespace ImbalancedChen.P2Saving16ActualCompilerDifference
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment

private theorem attach_indicator (p : Prop) (mu bminus bplus : ℝ) :
    signAttachedCoefficient (if p then mu else 0) bminus bplus =
      (if p then mu else 0) * (if 0 ≤ mu then bplus else bminus) := by
  classical
  by_cases hp : p <;> simp [hp, signAttachedCoefficient]

/-- At an occupied product, the compiler correction is the signed beta
value when the rough word changed, and zero otherwise. The value can be
negative or zero even in a changed cell. -/
theorem actual_product_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) {a d : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ «universe» N cap w z) :
    rho ret tag N cap w z tau L (a * d) -
      actualSmallRoughRho ret N cap w z L (a * d) =
    if changed ret tag N cap w z tau d then
      (if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a)
    else 0 := by
  let P := d ∈ «universe» N cap w z ∧
    P4AFull87TaggedAtomValue.admit ret tag N cap w z tau
      (label tag N tau d)
  let R := d ∈ rawSupport ret N cap w z
  let mu : ℝ := ArithmeticFunction.moebius d
  let bm := actualSmallRosserMinus N cap w L a
  let bp := actualSmallRosserPlus N cap w L a
  have hc : coefficient ret tag N cap w z tau d = if P then mu else 0 := by
    rw [P4AFull87TaggedAtomValue.literal_value]
    dsimp only [P4AFull87TaggedAtomValue.occupied, P, mu]
    split_ifs <;> simp
  have hr : raw ret N cap w z d = if R then mu else 0 := by
    simpa only [R, mu] using raw_value ret N cap w z d
  have hdelta : coefficient ret tag N cap w z tau d - raw ret N cap w z d =
      if changed ret tag N cap w z tau d then 1 else 0 := by
    have h := abs_coefficient_sub_raw ret tag N cap w z tau hd
    rw [abs_of_nonneg (sub_nonneg.mpr (raw_le_coefficient ret tag N cap w z tau d))] at h
    exact h
  have hcompiled : rho ret tag N cap w z tau L (a * d) =
      signAttachedCoefficient (coefficient ret tag N cap w z tau d) bm bp := by
    rw [rho_at_product ret tag N cap w z tau L ha hd]
    rfl
  have hraw : actualSmallRoughRho ret N cap w z L (a * d) =
      signAttachedCoefficient (raw ret N cap w z d) bm bp := by
    have h := smallRoughRho_mul
      (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
      (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) ha hd
    rw [raw_attachment_eq_actual ret N cap w z L] at h
    exact h
  rw [hcompiled, hraw]
  calc
    _ = (coefficient ret tag N cap w z tau d - raw ret N cap w z d) *
        (if 0 ≤ mu then bp else bm) := by
          rw [hc, hr, attach_indicator, attach_indicator]
          ring
    _ = _ := by
      rw [hdelta]
      dsimp only [mu, bm, bp]
      split_ifs <;> simp

/-- The same actual occurrence test stays attached to its full modulus;
there is no extra enumeration, sign replacement, or factorial. -/
theorem actual_weighted_product_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) {a d : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ «universe» N cap w z) (G : ℕ → ℝ) :
    (rho ret tag N cap w z tau L (a * d) -
      actualSmallRoughRho ret N cap w z L (a * d)) * G (a * d) =
    (if changed ret tag N cap w z tau d then
      (if 0 ≤ (ArithmeticFunction.moebius d : ℝ) then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a)
     else 0) * G (a * d) :=
  congrArg (fun x : ℝ => x * G (a * d))
    (actual_product_correction ret tag N cap w z tau L ha hd)

end
end ImbalancedChen.P2Saving16ActualCompilerDifference

namespace ImbalancedChen.P2Saving16SignedCorrectionFamilies
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment

def negativeInnerSum (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z),
    (if (ArithmeticFunction.moebius x.2 : ℝ) < 0 ∧
        x.2 ∈ rawSupport ret N cap w z ∧ ¬inner ret tag N cap w z tau x.2 then
      actualSmallRosserMinus N cap w L x.1 else 0) * G (x.1*x.2)

end
end ImbalancedChen.P2Saving16SignedCorrectionFamilies

namespace ImbalancedChen.P2Saving16NegativeOriginalFibreSum
noncomputable section
open scoped Classical BigOperators
open Set
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2CanonicalWallFullResidualPayment P2Saving16FirstRowCompilerFibre
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P4AOriginalFull87StrictActionTrim (trim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)

/-- The precise negative-inner test used by the existing correction sum. -/
def negativeTest (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau : ℝ) (d : ℕ) : Prop :=
  (ArithmeticFunction.moebius d : ℝ) < 0 ∧
    d ∈ rawSupport ret N cap w z ∧ ¬inner ret tag N cap w z tau d

/-- A single original cell, with its actual full rough word and rank. -/
def selected (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (i : Fin 14) : Finset (ℕ × ℕ) :=
  (smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z)).filter
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
  ∑ x ∈ (smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z)).filter
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
  let C := smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z)
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
  have hx' : x.1 ∈ actualSmallRosserSupport N cap w ∧ x.2 ∈ «universe» N cap w z := by
    exact Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have hy' : y.1 ∈ actualSmallRosserSupport N cap w ∧ y.2 ∈ «universe» N cap w z := by
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
  have hcarrier : x.1 ∈ actualSmallRosserSupport N cap w ∧ x.2 ∈ «universe» N cap w z :=
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
  change x.1*x.2 ∈ smallRoughModuli (actualSmallRosserSupport N cap w) («universe» N cap w z)
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

end
end ImbalancedChen.P2Saving16NegativeOriginalFibreSum

