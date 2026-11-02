import ImbalancedChen.Part5OriginalH430ArithmeticAtomRows
import ImbalancedChen.P2Selected430CausalOccurrenceExporter

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact seed-only430 predecessor arrays are read from the existing literal
source interpreter. No saved248/312/430 table is an input. A single
arithmetic threshold is proved for every bank profile query against all
430 actual old arrays, before the parent family and its action assignment.

This is a SIGNED profile error. It is deliberately not called the
coefficientwise absolute localBudget, and does not supply the moving
full-Member nested smooth refinement or the extra eleven physical levels.
-/

namespace ImbalancedChen.Part5OriginalH430ImmutableBankProfiles

noncomputable section
open Set Filter
open scoped Classical BigOperators Topology
open P5OriginalActionMassBound
open P2OriginalChildPhysicalNormalization
open Part5OriginalH430ArithmeticParentMass
open Part5OriginalH430ArithmeticAtomRows

abbrev precedingH (g : Fin 430) : Fin 200 → ℤ :=
  P2Selected430CausalOccurrenceExporter.iterate g.val true

abbrev precedingh (g : Fin 430) : Fin 200 → ℤ :=
  P2Selected430CausalOccurrenceExporter.iterate g.val false

/-- This identity pins the previous-state convention; it does not execute
the interpreter or authenticate its saved endpoint integers. -/
theorem preceding_state_used (g : Fin 430) (upper : Bool) (i : Fin 200) :
    P2Selected430CausalOccurrenceExporter.iterate (g.val+1) upper i =
      (P2Selected430CausalOccurrenceExporter.roundDecision
        (P2Selected430CausalOccurrenceExporter.iterate g.val) upper i).numerator := rfl

theorem immutable_bank_point_errors {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ g : Fin 430, ∀ Q L : ℝ, ∀ d : ℕ,
      L ∈ Icc Lmin Lmax → 0 < d → Q = (d:ℝ)*(N:ℝ)^L →
      2 ≤ alpha (Real.log (d:ℝ)/Real.log (N:ℝ)) L →
      ∀ a : Original106Action,
        |arithmeticProfile N Q L d (precedingH g) (precedingh g) a -
          thetaAtom N Q d*idealProfile (precedingH g) (precedingh g) a| ≤
            epsilon*thetaAtom N Q d := by
  have hfixed (g : Fin 430) : ∀ᶠ N : ℕ in atTop,
      ∀ Q L : ℝ, ∀ d : ℕ,
        L ∈ Icc Lmin Lmax → 0 < d → Q = (d:ℝ)*(N:ℝ)^L →
        2 ≤ alpha (Real.log (d:ℝ)/Real.log (N:ℝ)) L →
        ∀ a : Original106Action,
          |arithmeticProfile N Q L d (precedingH g) (precedingh g) a -
            thetaAtom N Q d*idealProfile (precedingH g) (precedingh g) a| ≤
              epsilon*thetaAtom N Q d := by
    obtain ⟨T,hT⟩ := all106_arithmetic_profile_error hmin hmax he (precedingH g) (precedingh g)
    exact (eventually_ge_atTop T).mono (fun N hN => hT N hN)
  exact eventually_atTop.mp (eventually_all.mpr hfixed)

/-- Generation labels, physical prefixes and action labels all remain
distinct. In particular equal products from different histories are not
collapsed without adding their original positive weights. -/
theorem immutable_bank_marked_absolute_errors {Lmin Lmax epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ {ι : Type*} (S : Finset ι)
      (g : ι → Fin 430) (L : ι → ℝ) (d : ι → ℕ) (sigma : ι → ℝ)
      (a : ι → Original106Action),
      (∀ i ∈ S, L i ∈ Icc Lmin Lmax) → (∀ i ∈ S, 0 < d i) →
      (∀ i ∈ S, Q = (d i:ℝ)*(N:ℝ)^(L i)) → (∀ i ∈ S, 0 ≤ sigma i) →
      (∀ i ∈ S, 2 ≤ alpha (Real.log (d i:ℝ)/Real.log (N:ℝ)) (L i)) →
      |(∑ i ∈ S, sigma i*arithmeticProfile N Q (L i) (d i)
          (precedingH (g i)) (precedingh (g i)) (a i)) -
        (∑ i ∈ S, sigma i*thetaAtom N Q (d i)*idealProfile
          (precedingH (g i)) (precedingh (g i)) (a i))| ≤
            epsilon*parentTheta N Q S d sigma := by
  obtain ⟨T,hT⟩ := immutable_bank_point_errors hmin hmax he
  refine ⟨T, ?_⟩
  intro N hN Q ι S g L d sigma a hL hd hQ hsigma halpha
  rw [← Finset.sum_sub_distrib, parentTheta, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have heq : sigma i*arithmeticProfile N Q (L i) (d i)
      (precedingH (g i)) (precedingh (g i)) (a i) -
      sigma i*thetaAtom N Q (d i)*idealProfile (precedingH (g i)) (precedingh (g i)) (a i) =
      sigma i*(arithmeticProfile N Q (L i) (d i) (precedingH (g i)) (precedingh (g i)) (a i) -
        thetaAtom N Q (d i)*idealProfile (precedingH (g i)) (precedingh (g i)) (a i)) := by ring
  rw [heq, abs_mul, abs_of_nonneg (hsigma i hi)]
  have h := mul_le_mul_of_nonneg_left (hT N hN (g i) Q (L i) (d i)
    (hL i hi) (hd i hi) (hQ i hi) (halpha i hi) (a i)) (hsigma i hi)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end
end ImbalancedChen.Part5OriginalH430ImmutableBankProfiles
