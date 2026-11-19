import ImbalancedChen.P2CausalSuccessorOccurrence

/-!
SOURCE ONLY. Exact finite marked-Theta semantics for one constructed
W1/W2 action, at its original common Q=(N:ℝ)^nu. This is not a count
estimate, a numerical table licence, or an all-roots admission theorem.
Each successor mark keeps the existing child carrier and edge scalar.
-/
namespace ImbalancedChen.P2CausalSuccessorTheta

noncomputable section
open Finset
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalBankOccurrenceBinding
open P2CausalSuccessorOccurrence P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2OriginalLiteralW1OldProfile P2OriginalBankOldProfilePassage
open Part5OriginalH430NativeQueryPaths
open scoped Classical BigOperators

/-- The actual labelled source with a single external path label. -/
def singletonTheta (m : Mark) (N : ℕ) (nu : ℝ) : ℝ :=
  Theta N ((N : ℝ)^nu) (sourceSupport ({()} : Finset Unit) (fun _ => m) N nu)
    (sourceSigma ({()} : Finset Unit) (fun _ => m) N nu)

/-- The existing product-fibre pushforward is exact, including empty
carriers and repeated products. No division by total marked mass occurs. -/
theorem singletonTheta_eq_parentTest (m : Mark) (N : ℕ) (nu : ℝ) :
    singletonTheta m N nu = parentTest m N nu (thetaAtom N ((N : ℝ)^nu)) := by
  have h := source_Theta_exact ({()} : Finset Unit) (fun _ => m) N nu
  simpa [singletonTheta, parentTest] using h

/-- The actual W1 component evaluated with the same Theta atom. -/
theorem w1_successors_theta (m : Mark) (N : ℕ) (nu : ℝ)
    (i : Fin 7) (j : Fin 10) :
    componentSum (.inl (i,j))
      (componentTest m N nu (fun _ => thetaAtom N ((N : ℝ)^nu))) =
      singletonTheta m N nu +
        singletonTheta (singleSuccessor m (.w1 i j)) N nu := by
  rw [w1_components_are_successors]
  simp only [← singletonTheta_eq_parentTest]

/-- The W2 parent contributions retain 4:1 before their common /5.
Each singleton and good pair has its own marked support and original
1/5 edge, even if two supports contain the same product. -/
theorem w2_successors_theta (m : Mark) (N : ℕ) (nu : ℝ) (bank : Fin 36) :
    componentSum (.inr bank)
      (componentTest m N nu (fun _ => thetaAtom N ((N : ℝ)^nu))) =
      singletonTheta m N nu +
        (∑ piece : Fin 3, singletonTheta (singleSuccessor m (.w2 bank piece)) N nu) +
        (∑ piece : Fin 4, singletonTheta (pairSuccessor m bank piece) N nu) := by
  rw [w2_components_are_successors]
  simp only [← singletonTheta_eq_parentTest]
  ring


/-- An occurrence selects one genuine singleton or one genuine good pair.
The external index of the marked book is never quotiented by this tag. -/
def SuccessorChoice := SingleRule ⊕ (Fin 36 × Fin 4)

def advance (m : Mark) : SuccessorChoice → Mark
  | .inl rule => singleSuccessor m rule
  | .inr (bank, piece) => pairSuccessor m bank piece

/-- Root-box geometric rows and the original incoming coefficient survive
one actual history edge; only the finite depth budget grows by one. -/
theorem advance_boxRows (m : Mark) (choice : SuccessorChoice)
    {nu eta : ℝ} {horizon : ℕ} (hm : m.BoxRows nu eta horizon) :
    (advance m choice).BoxRows nu eta (horizon+1) := by
  rcases hm with ⟨hbox,hres,halpha,hdepth,hcoef⟩
  cases choice with
  | inl rule =>
      refine ⟨hbox,hres,halpha,?_,hcoef⟩
      change m.history.depth + 1 ≤ horizon + 1
      omega
  | inr p =>
      rcases p with ⟨bank,piece⟩
      refine ⟨hbox,hres,halpha,?_,hcoef⟩
      change m.history.depth + 1 ≤ horizon + 1
      omega

/-- The existing literal half-open W1 old-profile passage now acts on
the actual successor book, with one threshold chosen before N, mark
labels and successor choices. This supplies only profile/integral
semantics for arbitrary supplied old arrays: it does not license those
arrays as bounds for actual H/h. -/
theorem advance_book_W1_old_profile {eta epsilon : ℝ} (he : 0 < eta)
    (heps : 0 < epsilon) (horizon : ℕ) (oldH oldh : Fin 200 → ℤ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ i : Fin 7, ∀ j : Fin 10,
      let next := fun a => advance (marks a) (choices a)
      let D := sourceSupport A next N nu
      let sigma := sourceSigma A next N nu
      |(∑ d ∈ D, sigma d * literalW1ThetaOldProfile N ((N : ℝ)^nu) d i j oldH oldh) -
        Theta N ((N : ℝ)^nu) D sigma * W1OldIntegral i j oldH oldh| ≤
        epsilon * Theta N ((N : ℝ)^nu) D sigma := by
  obtain ⟨T,hT,hprofile⟩ := actual_source_W1_profile he heps (horizon+1) oldH oldh
  refine ⟨T,hT,?_⟩
  intro N hN nu hnu I A marks choices hm i j
  apply hprofile N hN nu hnu I A (fun a => advance (marks a) (choices a)) ?_ i j
  intro a ha
  exact advance_boxRows (marks a) (choices a) (hm a ha)

end
end ImbalancedChen.P2CausalSuccessorTheta
