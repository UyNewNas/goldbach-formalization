import ImbalancedChen.ActualPrimeFineLabelSortedSelector

/-!
P3.6: original fine-prime MARKED and residual words, complete-product diagonal.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Manuscript: 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1, 3 (T), 4 (F).

This file imports an EXISTING production source directly. Both the marked
prime word and the residual prime word use the literal fine-prime alphabet
excluding divisors of the SAME physical target N; their fine scales may
differ. For N != 1 their combined complete product cannot equal N.
The previous singleton residual exception r=N is therefore absent once
r is actually a product of marked primes from this alphabet. The marked
compiler's membership in these boxes is NOT established by this lemma,
and this conclusion is NOT asserted for HB integer variables.
-/

namespace ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen

private theorem nil_mem_box_iff {ι : Type*}
    (B : ι → Finset ℕ) (word : List ι) :
    ([] : List ℕ) ∈ actualPrimeSlotBox B word ↔ word = [] := by
  cases word with
  | nil => simp [actualPrimeSlotBox]
  | cons i rest => simp [actualPrimeSlotBox]

/-- A NONEMPTY original fine-prime slot word cannot have a product
dividing N: every prime in the literal original box satisfies p ∤ N.
This does not assume the tuple is sorted or squarefree. -/
theorem original_prime_box_product_not_dvd
    (N : ℕ) (τ : ℝ) (word ps : List ℕ)
    (hps : ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) word)
    (hword : word ≠ []) : ¬ ps.prod ∣ N := by
  have hall : ∀ p ∈ ps, ¬ p ∣ N :=
    actualPrimeSlotBox_forall
      (actualPrimeFineLabelFinset N τ) word
      (fun p : ℕ => ¬ p ∣ N)
      (by
        intro i hi p hp
        exact (mem_actualPrimeFineLabelFinset.mp hp).2.1)
      ps hps
  cases ps with
  | nil =>
      have hw : word = [] :=
        (nil_mem_box_iff (actualPrimeFineLabelFinset N τ) word).mp hps
      exact (hword hw).elim
  | cons p tail =>
      have hnot : ¬ p ∣ N := hall p (by simp)
      intro hdiv
      apply hnot
      have hpdiv : p ∣ (p :: tail).prod :=
        ⟨tail.prod, by simp [List.prod_cons]⟩
      exact dvd_trans hpdiv hdiv

/-- Two genuine original fine-prime words (marked and residual) may have
different smooth label scales. If either word is nonempty, their entire
physical integer product cannot equal the same target N. -/
theorem marked_residual_full_product_ne_target
    (N : ℕ) (τm τr : ℝ) (markedWord residualWord : List ℕ)
    (marked residual : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hr : residual ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τr) residualWord)
    (hwords : markedWord ≠ [] ∨ residualWord ≠ []) :
    marked.prod * residual.prod ≠ N := by
  intro hfull
  rcases hwords with hmarked | hresidual
  · have hnot := original_prime_box_product_not_dvd
      N τm markedWord marked hm hmarked
    apply hnot
    exact ⟨residual.prod, hfull.symm⟩
  · have hnot := original_prime_box_product_not_dvd
      N τr residualWord residual hr hresidual
    apply hnot
    refine ⟨marked.prod, ?_⟩
    exact hfull.symm.trans (Nat.mul_comm _ _)

/-- The literal Cartesian marked/residual source has no full-product=N
exception if any original prime slot is present. -/
theorem marked_residual_target_fibre_empty_of_nonempty
    (N : ℕ) (τm τr : ℝ) (markedWord residualWord : List ℕ)
    (hwords : markedWord ≠ [] ∨ residualWord ≠ []) :
    ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τm) markedWord).product
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N τr) residualWord)).filter
      (fun ps => ps.1.prod * ps.2.prod = N) = ∅ := by
  classical
  ext ps
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hp, hfull⟩
  obtain ⟨hm, hr⟩ := Finset.mem_product.mp hp
  exact (marked_residual_full_product_ne_target
    N τm τr markedWord residualWord ps.1 ps.2 hm hr hwords) hfull

/-- If the original physical target N differs from 1, even the BOTH-empty
marked/residual word has full product 1 != N. This pays the complete
prime-only diagonal on its literal box, independently of rho. -/
theorem marked_residual_target_fibre_empty_of_target_ne_one
    (N : ℕ) (τm τr : ℝ) (markedWord residualWord : List ℕ)
    (hN : N ≠ 1) :
    ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τm) markedWord).product
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N τr) residualWord)).filter
      (fun ps => ps.1.prod * ps.2.prod = N) = ∅ := by
  classical
  by_cases hwords : markedWord ≠ [] ∨ residualWord ≠ []
  · exact marked_residual_target_fibre_empty_of_nonempty
      N τm τr markedWord residualWord hwords
  · have hm : markedWord = [] := by
      by_contra hh
      exact hwords (Or.inl hh)
    have hr : residualWord = [] := by
      by_contra hh
      exact hwords (Or.inr hh)
    subst markedWord
    subst residualWord
    have hnot : (1 : ℕ) ≠ N := Ne.symm hN
    simp [actualPrimeSlotBox, hnot]

/-- The original literal marked-prime and residual-prime source has zero
exact diagonal AFTER the entire SAME signed physical q/rho sum. Count and
coprime mean both test the complete product, not the residual product.
No bound on rho, W or the Fourier coefficients is assumed. -/
theorem marked_residual_same_rho_exact_diagonal_zero
    (N : ℕ) (τm τr : ℝ) (markedWord residualWord : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (c : ℂ)
    (W : List ℕ × List ℕ → ℂ) (hN : N ≠ 1) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ ps ∈
        ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τm) markedWord).product
          (actualPrimeSlotBox (actualPrimeFineLabelFinset N τr) residualWord)).filter
          (fun t => t.1.prod * t.2.prod = N),
        c * W ps *
          (((ArithmeticFunction.moebius (ps.1.prod * ps.2.prod) : ℝ) *
            ((if (ps.1.prod * ps.2.prod) % q = N % q
                then (1 : ℝ) else 0) -
             (if Nat.Coprime (ps.1.prod * ps.2.prod) q
                then (Nat.totient q : ℝ)⁻¹ else 0))) : ℂ)) = 0 := by
  rw [marked_residual_target_fibre_empty_of_target_ne_one
    N τm τr markedWord residualWord hN]
  simp

end
end ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
