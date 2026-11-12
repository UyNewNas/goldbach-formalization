import ImbalancedChen.P2GammaRetainedSameRhoMother

/-! The Wu prefix dictionary used by the retained Gamma source.
Source candidate. The finite identities use the existing occurrence list,
marked quotient labels, signed coefficient and exact coprime mean.
-/

namespace ImbalancedChen.P2GammaActualEmptyMotherSource
noncomputable section

open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2TwentyOneUnsiftedArithmeticSource (product)
open P2OriginalU5WholeGroupCapacity (rootLabels root_word_length)
open P2OriginalGammaUpperLowRankConsumer (gammaKernel)
open P2GammaCompleteProductTrimPayment (originalMotherOccurrences smoothTrim)
open P2GammaJointRetainedReduction (originalJointRetainedError)
open P2GammaRetainedSameRhoMother
open P2EnhancedTwentyOneSameQWeighted (Phi cutoff)

/-- Each occurrence comes with its original Gamma index and its word in
that index's list. The native producer proves at least two positions. -/
theorem original_occurrence_length {cs : List ℕ}
    (hcs : cs ∈ originalMotherOccurrences) : 2 ≤ cs.length := by
  obtain ⟨i, hi, hword⟩ := List.mem_flatMap.mp hcs
  exact secondFunctionalMother_prefix_lengths i hi cs hword

theorem original_nil_not_mem : ([] : List ℕ) ∉ originalMotherOccurrences := by
  intro h
  exact Nat.not_succ_le_zero 1 (original_occurrence_length h)

/-- The coefficient counts list occurrences, including repeated words. -/
theorem original_nil_count : originalMotherOccurrences.count [] = 0 :=
  List.count_eq_zero.mpr original_nil_not_mem

/-- A colour block can have multiplicity zero. At least one actual colour
has a positive count, including when the first colour is the label 0. -/
theorem original_occurrence_has_live_colour {cs : List ℕ}
    (hcs : cs ∈ originalMotherOccurrences) : ∃ c ∈ cs, 0 < cs.count c := by
  cases cs with
  | nil => exact (original_nil_not_mem hcs).elim
  | cons c cs =>
    have hc : c ∈ c :: cs := List.mem_cons_self
    exact ⟨c, hc, Nat.pos_of_ne_zero (fun hz => (List.count_eq_zero.mp hz) hc)⟩

/-- This holds after the actual marked-pair cutoffs, the half-open colour
test and the quotient restrictions have selected the integer tuple. -/
theorem original_root_label_length {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hcs : cs ∈ originalMotherOccurrences) {x : List ℕ × ℕ}
    (hx : x ∈ rootLabels N t cs) : 2 ≤ x.1.length := by
  rw [root_word_length hx]
  exact original_occurrence_length hcs

/-- The word-level function is defined even on a formal nil argument.
Its marked multiplier is the old pair product and its residual is x.2.
Both terms below use the identical physical q and rho(q). -/
theorem literal_nil_marked_kernel (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (T : ℝ) :
    emptyWordError N t [] Q rho T =
      ∑ q ∈ Q, rho q * ∑ x ∈ rootLabels N t [],
        smoothTrim T ((t.1*t.2)*x.2) *
          ((if Nat.ModEq q ((t.1*t.2)*x.2) N then 1 else 0) -
           (if Nat.Coprime ((t.1*t.2)*x.2) q then 1 else 0) / (Nat.totient q : ℝ)) := by
  simp only [emptyWordError, if_pos rfl]
  apply Finset.sum_congr rfl
  intro q _
  apply congrArg (fun v : ℝ => rho q * v)
  apply Finset.sum_congr rfl
  intro x hx
  have hnil : x.1 = [] := List.length_eq_zero_iff.mp (root_word_length hx)
  have hm : product (t.1*t.2) x = (t.1*t.2)*x.2 := by simp [product, hnil]
  simp only [hm, gammaKernel]

/-- Every producer occurrence has zero projection onto the nil branch. -/
theorem original_empty_word_error_zero {cs : List ℕ} (hcs : cs ∈ originalMotherOccurrences)
    (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) (T : ℝ) :
    emptyWordError N t cs Q rho T = 0 :=
  if_neg (fun h => original_nil_not_mem (h ▸ hcs))

/-- Pay the exact original pair sum before any arithmetic estimate or
outer-family cancellation. The term on a formal nil argument stays intact. -/
theorem original_empty_pair_zero (N : ℕ) (t : ℕ × ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (T : ℝ) : emptyPairError N t Q rho T = 0 := by
  have h (L : List (List ℕ)) : ([] : List ℕ) ∉ L →
      (L.map (fun cs => emptyWordError N t cs Q rho T)).sum = 0 := by
    induction L with
    | nil => intro _; rfl
    | cons cs L ih =>
      intro hL
      have hcs : cs ≠ [] := by
        rintro rfl
        exact hL List.mem_cons_self
      have htail : ([] : List ℕ) ∉ L := fun hx => hL (List.mem_cons_of_mem cs hx)
      have hw : emptyWordError N t cs Q rho T = 0 := if_neg hcs
      rw [List.map_cons, List.sum_cons, hw, ih htail, zero_add]
  exact h originalMotherOccurrences original_nil_not_mem

theorem original_empty_joint_zero (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T : ℝ) : emptyJointError N Q rho sigma T = 0 := by
  simp only [emptyJointError, original_empty_pair_zero, mul_zero, Finset.sum_const_zero]

theorem original_retained_eq_head (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointRetainedError N Q rho sigma T H δ K = headJointError N Q rho sigma H δ K := by
  rw [jointRetained_eq_head_add_empty, original_empty_joint_zero, add_zero]

/-- Gamma 1 has two ordinary queries on the unchanged marked prefix,
with the two original cutoffs of the same Q/d. They occur outside the
prefix-word dictionary. This equality retains both source counts. -/
theorem gamma_one_weighted_same_prefix (N M : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s0 phi1 phi2 phi3 s : ℝ) :
    (∑ d ∈ D, sigma d * secondFunctionalMotherGamma N d M
      (cutoff Q d s0) (cutoff Q d phi1) (cutoff Q d phi2)
      (cutoff Q d phi3) (cutoff Q d s) 1) =
      4 * Phi N Q D sigma s0 + Phi N Q D sigma phi1 := by
  unfold Phi
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [secondFunctionalMotherGamma]
  ring

end
end ImbalancedChen.P2GammaActualEmptyMotherSource
