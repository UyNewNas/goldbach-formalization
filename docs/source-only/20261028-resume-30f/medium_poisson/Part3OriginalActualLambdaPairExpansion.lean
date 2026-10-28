import ImbalancedChen.Part3OriginalNoncleanGeneralDPackets
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
Both actual lambdaTrim copies are expanded independently, including
their separate s*t=d choices and original individual windows/trims.
The physical q*d*w moduli are proved equal to the original q*q2*q3
products for each choice. No diagonal polarization or coloring bound
is assumed, and this is not a square of an untrimmed or common choice.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumInstalledFactorChoiceMap20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028

namespace ImbalancedChen.Part3.OriginalActualLambdaPairExpansion20261028

/-- Original gamma2(us)*gamma3(vt), with the source numerical rough
cutoff translated only in its integer support convention. -/
def choiceCoefficient (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (p : Factor) : ℂ :=
  ((fixedBlock k small).factorData atom (strictReceiverCutoff z)).term p

@[simp] theorem choiceCoefficient_eq_gamma (atom : MediumAtom) (z : ℝ)
    (k : Key) (small : ℕ) (p : Factor) :
    choiceCoefficient atom z k small p =
      atom.gamma2 (p.u * p.s) * atom.gamma3 (p.v * p.t) := rfl

/-- All individual factor windows and both smooth trims remain in the
two actual trimmedChoices; the two witnesses need not coincide. -/
theorem actual_lambda_pair_eq_independent_choices
    (atom : MediumAtom) (z y : ℝ) (k : Key) (small r s : ℕ) :
    lambdaTrim atom (strictReceiverCutoff z) y k small r *
      star (lambdaTrim atom (strictReceiverCutoff z) y k small s) =
      ∑ p ∈ trimmedChoices atom (strictReceiverCutoff z) y k small r,
        ∑ p' ∈ trimmedChoices atom (strictReceiverCutoff z) y k small s,
          choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') := by
  unfold lambdaTrim choiceCoefficient
  rw [star_sum, Finset.sum_mul_sum]

/-- Each independent choice retains exactly its own original product
labels and trim. Neither s*t=d identity is inferred from the other. -/
theorem actual_choice_original_data
    {atom : MediumAtom} {z y : ℝ} {k : Key} {small w : ℕ} {p : Factor}
    (hp : p ∈ trimmedChoices atom (strictReceiverCutoff z) y k small w) :
    p.s * p.t = small ∧ p.u * p.v = w ∧
      p.u * p.s ∈ factorCarrier atom.Q2 ∧ p.v * p.t ∈ factorCarrier atom.Q3 ∧
      (p.s : ℝ) ≤ y ∧ (p.t : ℝ) ≤ y := by
  have hchoice := (Finset.mem_filter.mp hp).1
  obtain ⟨hd, hw, h2, h3, hprod⟩ := choice_products hchoice
  exact ⟨hd, hw, h2, h3, (Finset.mem_filter.mp hp).2⟩

/-- Each physical modulus is the original complete q*q2*q3 product,
not q with d silently absorbed into a new first-factor variable. -/
theorem choice_complete_modulus
    {atom : MediumAtom} {z y : ℝ} {k : Key} {small w : ℕ} {p : Factor}
    (hp : p ∈ trimmedChoices atom (strictReceiverCutoff z) y k small w) (q : ℕ) :
    q * (p.u * p.s) * (p.v * p.t) = (q * small) * w := by
  obtain ⟨hd, hw, h2, h3, hsy, hty⟩ := actual_choice_original_data hp
  rw [← hd, ← hw]
  ring

/-- The genuine constructed block's clean coefficient now has the
two ORIGINAL independent factor expansions. Its inverse phase and
q*w1*w2 denominator remain the existing physical typed definitions. -/
theorem actual_block_coeff_eq_independent_choices
    {b : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ OriginalSamePsiS1OwnedAtlas.activeD atom k)
    (negative : Bool) (t : Index) :
    (poissonAtlasBlock atom z y k hA Csep j small hd negative).coeff t =
      ∑ p ∈ trimmedChoices atom (strictReceiverCutoff z) y k small t.w1,
        ∑ p' ∈ trimmedChoices atom (strictReceiverCutoff z) y k small t.w2,
          (choiceCoefficient atom z k small p * star (choiceCoefficient atom z k small p') *
            atom.alpha t.n1 * star (atom.alpha t.n2) /
              ((t.q * t.w1 * t.w2 : ℕ) : ℂ)) *
                (poissonAtlasBlock atom z y k hA Csep j small hd negative).firstPhase t := by
  unfold FixedBlock.coeff
  simp only [poissonAtlasBlock_atom, poissonAtlasBlock_lambda, Complex.star_def]
  rw [← Complex.star_def,
    actual_lambda_pair_eq_independent_choices atom z y k small t.w1 t.w2]
  simp only [Finset.sum_mul, Finset.sum_div, Complex.star_def]

end ImbalancedChen.Part3.OriginalActualLambdaPairExpansion20261028
