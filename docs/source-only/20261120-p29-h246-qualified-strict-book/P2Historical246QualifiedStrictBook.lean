import ImbalancedChen.P2Historical246ActualRectangleDebit

/-! SOURCE ONLY / UNEVALUATED. The actual same-Q theta contribution of
qualifying marked successor tuples is pushed forward without merging path
occurrences, then bounded by the original H246 j=0 strict book with its
four pair occurrences and its one /5. Qualification is not assumed to
hold for any tuple; no count, endpoint, reserve or nonemptiness follows. -/
namespace ImbalancedChen.P2Historical246QualifiedStrictBook
noncomputable section
open Set Finset Filter
open scoped Classical BigOperators Topology
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2EnhancedSwitchedTrueNormalization P2EnhancedTwentyOneSameQWeighted
open P2EnhancedMarkedBoxExceptionSupply P2EnhancedNonunitMarkedMass
open P2Historical246ActualRectangleDebit P2Historical246StrictRectangleIntegral
open P2Historical246StrictDebit P2Historical246StrictCeilingChildUpper
open P2OriginalChildPhysicalNormalization

/-- Filter tuple occurrences in each original successor path. Both the
compact L condition and the strict physical ceiling retain their values
from that very tuple. -/
def qualifyingSource (m : Mark) (choice : SuccessorChoice) (N : ℕ) (nu Lmin Lmax : ℝ) :
    Finset (Fin (advance m choice).rank → Fin (N+1)) :=
  ((advance m choice).source N nu).filter fun t =>
    let L := residualExponent N (parentProduct (oldWord t)) nu
    L ∈ Icc Lmin Lmax ∧
      (advance m choice).history.ceiling (advance m choice).ceiling t < L*(2999/10000:ℝ)

def qualifyingSupport {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu Lmin Lmax : ℝ) : Finset ℕ :=
  mixtureSupport A (fun a => (advance (marks a) (choices a)).rank)
    (fun a => qualifyingSource (marks a) (choices a) N nu Lmin Lmax)

def qualifyingSigma {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu Lmin Lmax : ℝ) (d : ℕ) : ℝ :=
  mixtureSigma A (fun a => (advance (marks a) (choices a)).rank)
    (fun a => qualifyingSource (marks a) (choices a) N nu Lmin Lmax)
    (fun a _ => (advance (marks a) (choices a)).weight) d

/-- Exact product-fibre identity for the FILTERED actual source. A tuple
appears once for each external path even when products or tuples coincide. -/
theorem qualifyingSigma_test {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu Lmin Lmax : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ qualifyingSupport A marks choices N nu Lmin Lmax,
      qualifyingSigma A marks choices N nu Lmin Lmax d * G d) =
      ∑ a ∈ A, ∑ t ∈ qualifyingSource (marks a) (choices a) N nu Lmin Lmax,
        (advance (marks a) (choices a)).weight * G (Part3.labelledProduct t) := by
  unfold qualifyingSigma mixtureSigma
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  have hsub : markSupport (qualifyingSource (marks a) (choices a) N nu Lmin Lmax) ⊆
      qualifyingSupport A marks choices N nu Lmin Lmax := by
    intro d hd
    exact mem_biUnion.mpr ⟨a,ha,hd⟩
  rw [← marked_support_test]
  symm
  apply sum_subset hsub
  intro d hd hnot
  rw [marked_weight_zero_off_support _ _ hnot,zero_mul]

/-- Same literal li, singular factor C(dN), phi(d), Q and path weights
as the original book, restricted only by qualifyingSource. -/
theorem qualifying_Theta_exact {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu Lmin Lmax : ℝ) :
    Theta N ((N:ℝ)^nu) (qualifyingSupport A marks choices N nu Lmin Lmax)
      (qualifyingSigma A marks choices N nu Lmin Lmax) =
      ∑ a ∈ A, ∑ t ∈ qualifyingSource (marks a) (choices a) N nu Lmin Lmax,
        (advance (marks a) (choices a)).weight *
          thetaAtom N ((N:ℝ)^nu) (parentProduct (oldWord t)) := by
  rw [Theta_eq_sum_atoms,qualifyingSigma_test]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro t ht
  rw [oldWord_product]

/-- A qualifying subset, not all of the source, contributes a positive
same-Q theta term to the original strict debit. The coefficient includes
the one original /5 for this one of the four ordered pair occurrences.
No positivity or nonemptiness of the selected theta is asserted. -/
theorem qualifying_Theta_le_original_strictBook {Lmin Lmax eta : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < eta) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      (h52/2000000000) *
        Theta N ((N:ℝ)^nu) (qualifyingSupport A marks choices N nu Lmin Lmax)
          (qualifyingSigma A marks choices N nu Lmin Lmax) ≤
      strictBook A marks choices N nu 0 := by
  obtain ⟨T,hT,hpoint⟩ := actual_rectangle_strictLane_lower hmin hmax he horizon
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm
  have hN4 : 4 ≤ N := hT.trans hN
  rw [qualifying_Theta_exact,Finset.mul_sum]
  unfold strictBook
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  let next := advance (marks a) (choices a)
  have hw : 0 ≤ next.weight := by
    exact mul_nonneg (advance_boxRows (marks a) (choices a) (hm a ha)).2.2.2.2
      next.history.scalar_nonneg
  have hnonneg (t : Fin next.rank → Fin (N+1)) (ht : t ∈ next.source N nu)
      (k : Fin 4) : 0 ≤ strictLane N nu (marks a) (choices a) t 0 k := by
    exact successor_strict_ceiling_nonnegative hN4 he (marks a) (choices a) (hm a ha) ht 0 k
  have hterm (t : Fin next.rank → Fin (N+1)) (ht : t ∈ next.source N nu) :
      0 ≤ next.weight * ((∑ k : Fin 4, strictLane N nu (marks a) (choices a) t 0 k)/5) := by
    exact mul_nonneg hw (div_nonneg (Finset.sum_nonneg (fun k _ => hnonneg t ht k)) (by norm_num))
  calc
    _ ≤ ∑ t ∈ qualifyingSource (marks a) (choices a) N nu Lmin Lmax,
          next.weight * ((∑ k : Fin 4, strictLane N nu (marks a) (choices a) t 0 k)/5) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htsrc,hqual⟩ := Finset.mem_filter.mp ht
      obtain ⟨hL,hcap⟩ := hqual
      have hlane := hpoint N hN nu hnu (marks a) (choices a) (hm a ha) t htsrc hL hcap
      have hsum : strictLane N nu (marks a) (choices a) t 0 0 ≤
          ∑ k : Fin 4, strictLane N nu (marks a) (choices a) t 0 k := by
        exact Finset.single_le_sum (fun k _ => hnonneg t htsrc k) (Finset.mem_univ 0)
      have hscaled := mul_le_mul_of_nonneg_left (hlane.trans hsum) hw
      dsimp [next] at hscaled ⊢
      nlinarith only [hscaled]
    _ ≤ ∑ t ∈ next.source N nu,
          next.weight * ((∑ k : Fin 4, strictLane N nu (marks a) (choices a) t 0 k)/5) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro t ht _
        exact hterm t ht

end
end ImbalancedChen.P2Historical246QualifiedStrictBook
