import ImbalancedChen.Part5OriginalH430ActualReadEdgeDefect
import ImbalancedChen.Part5OriginalH430RequestedSignedStep

/-!
P5.6 / h34: actual Buchstab read-to-integral residual.

This source-only bridge separates the two UNLIKE objects which were still
lumped into the literal Buchstab read/edge defect:
  (1) the ACTUAL rounded integer suffix read minus the old ideal integral;
  (2) the ACTUAL strict-prime child sum minus that same old integral.

Only (2) receives the existing coefficientwise absolute-error payment.
The integer suffix (1) is retained as a signed, unpaid arithmetic residual.
No sign or equality is assumed for it. Both polarities, both read modes,
the original parent Q, actual ceiling, list-position multiplicities and
positive original history marks remain unchanged. This is NOT a closed-cell
arithmetic-count induction. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabDefectIntegralBridge

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedNonbankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430RequestedSignedStep

/-- The exact signed amount left to pay when an actual, chosen
Buchstab INTEGER suffix is compared with the original PREDECESSOR
integral profile. It reads the new table at the actual chosen request:
neither the scalar owner nor a specified cell is substituted. -/
def buchstabReadIntegralResidual (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l *
      (readTerm N n root tau p g l -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          idealProfile (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical
            (precedingH g) (precedingh g))

/-- Each summand really contains the original integer suffix selected
at generation g+1, for the correct resolved index i. No equality to
the strict-prime sum or to the integral is claimed. -/
theorem buchstab_actual_suffix_residual (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hl : l ∈ buchstabLevel N n root tau p g) :
    ∃ i : Fin 200,
      Selected g.val (levelOccurrence l).current i .buchstab ∧
      readTerm N n root tau p g l -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          idealProfile (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical
            (precedingH g) (precedingh g) =
      thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
        (((buchstabValue (iterate g.val)
             (levelOccurrence l).current.node.upper i : ℝ)/(2:ℝ)^80) -
          idealProfile (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical
            (precedingH g) (precedingh g)) := by
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  refine ⟨i,hi,?_⟩
  unfold readTerm
  rw [requested_buchstab_value hi]
  ring

/-- Exact arithmetic decomposition; the second term is the original
strict-prime physical child sum compared with the same integral.
This equality keeps SIGN and does not charge a replacement error twice. -/
theorem buchstab_defect_ideal_split (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelDefect N n root tau p g l) =
      buchstabReadIntegralResidual N n root tau p g +
      (buchstabIdeal N n root tau p g -
        buchstabActual N n root tau p g) := by
  unfold buchstabReadIntegralResidual buchstabIdeal buchstabActual
  change (∑ l ∈ buchstabLevel N n root tau p g,
      levelDefect N n root tau p g l) =
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelMark l *
        (readTerm N n root tau p g l -
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
            idealProfile (levelOccurrence l).current.node.upper
              (levelOccurrence l).current.node.physical
              (precedingH g) (precedingh g))) +
    ((∑ l ∈ buchstabLevel N n root tau p g,
       levelMark l *
         (thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
            idealProfile (levelOccurrence l).current.node.upper
              (levelOccurrence l).current.node.physical
              (precedingH g) (precedingh g))) -
     (∑ l ∈ buchstabLevel N n root tau p g,
       levelMark l * childTerm N n root tau p g l))
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold levelDefect
  ring

/-- Pay ONLY strict-prime versus integral error with the established
absolute Buchstab row certificate. The suffix-to-integral amount is NOT
silently declared small or nonpositive. -/
theorem buchstab_defect_le_integral_residual (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelDefect N n root tau p g l) ≤
      buchstabReadIntegralResidual N n root tau p g +
        buchstabLevelError N n root tau p g := by
  have habs := (buchstab_abs_le_applied N n root tau p g).trans
    (buchstab_applied_le_rowError N n root tau p g
      hN ht ht' hn hp hband)
  have hneg := neg_le_abs
    (buchstabActual N n root tau p g -
      buchstabIdeal N n root tau p g)
  have hpaid : buchstabIdeal N n root tau p g -
      buchstabActual N n root tau p g ≤
        buchstabLevelError N n root tau p g := by
    linarith only [habs,hneg]
  rw [buchstab_defect_ideal_split]
  exact add_le_add_left hpaid _

/-- Genuine all-action one-generation read/edge comparison. Retention
vanishes exactly, the 106 bank winners keep their real candidate upper,
and only the correctly signed Buchstab integer suffix-to-integral
residual survives as an UNPAID term. -/
theorem actual_one_generation_integral_residual_upper (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g ≤
      (buchstabReadIntegralResidual N n root tau p g +
        buchstabLevelError N n root tau p g) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          bankCandidateGap N n root tau p g a l) := by
  rw [level_defect_nonretained]
  exact add_le_add
    (buchstab_defect_le_integral_residual N n root tau p g
      (by omega : 1 < N) ht ht' hn hp hband)
    (bank_defect_sum_le N n root tau p g hN ht ht' hn hp hband)

/-- ONE uniform pre-N threshold from the existing quantitative strict
Buchstab supplier, with no new prime-distribution input or per-level
epsilon chosen after the actual request. This is still NOT a bound on
the integer suffix residual, and is not a closed-count induction. -/
theorem uniform_actual_one_generation_integral_residual_upper
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        levelReadMass N n root tau p g -
            levelChildMass N n root tau p g ≤
        (buchstabReadIntegralResidual N n root tau p g +
          epsilon * buchstabLevelTheta N n root tau p g) +
        (∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a,
            bankCandidateGap N n root tau p g a l) := by
  obtain ⟨T,hT,hbuch⟩ := uniform_level_buchstab_supply he
  refine ⟨T,hT,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hstep := actual_one_generation_integral_residual_upper
    N n root tau p g (hT.trans hN) ht ht' hn hp hband
  have herror := (hbuch N hN n root tau ht ht' hn p hp hband g).1
  linarith only [hstep,herror]

end
end ImbalancedChen.Part5OriginalH430BuchstabDefectIntegralBridge
