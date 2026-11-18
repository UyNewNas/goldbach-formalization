import ImbalancedChen.P3ActualSortedMarkedSameRhoNoDiagonal
import ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre

/-!

IMPORTANT COEFFICIENT SCOPE AUDIT (2026-11-18): the mu of the COMPLETE
product below is a specialized arithmetic model, NOT the literal HB
coefficient of the frozen manuscript. The real HB expansion uses products
of mu_Z on INDIVIDUAL truncated variables, signed binomial constants,
and a separate log slot. In general mu(3)*mu(3)=1 but mu(9)=0.
Therefore the five finite identities below must NOT be cited as actual
full-HB coefficient/exception payment. See the arbitrary occurrence-
coefficient repair in P3ActualHybridCoefficientFaithfulDiagonal.lean.
P3.6 — actual fine-prime slots interleaved with ARBITRARY HB integer slots.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b
manuscript-body.tex eq:current-PP; prime-product completion §§2–4.

The preceding no-diagonal result covered two PRIME-only words. This file
permits any third list of HB INTEGER factors (composites, units, repeated
factors, and zero are not silently declared prime). It proves that the
complete physical product cannot be N if EITHER literal original
fine-prime word is nonempty: a prime p not dividing N divides that
complete product. This statement remains true with an arbitrary HB
integer word inserted between the original marked and residual primes.

For the BOTH-prime-words-empty case, the complete product=N exceptional
contribution is calculated explicitly as a weighted HB-product=N fibre.
The exact coprime mean and one common signed rho are retained. This
is a finite source calculation; it does not assert any particular full
HB compiler output or bound its exceptional mass.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualHybridHBPrimeDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre
open ImbalancedChen.P3ActualMarkedOffShiftDivisors

/-- An arbitrary HB integer word cannot create a complete-product=N
diagonal when at least one original fine-prime slot is present.
No primality, roughness, coprimality or positivity assumption is
imposed on the HB factors; all original prime factors use the SAME N
but the marked/residual fine scales may differ. -/
theorem hybrid_full_product_ne_target
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked hb ps : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τr blocks)
    (hprime : markedWord ≠ [] ∨
      actualPrimeLabelBlocksWord blocks ≠ []) :
    (marked.prod * hb.prod) * ps.prod ≠ N := by
  rcases hprime with hmarked | hresidual
  · have hnot : ¬ marked.prod ∣ N :=
      original_prime_box_product_not_dvd
        N τm markedWord marked hm hmarked
    intro heq
    apply hnot
    refine ⟨hb.prod * ps.prod, ?_⟩
    calc
      N = (marked.prod * hb.prod) * ps.prod := heq.symm
      _ = marked.prod * (hb.prod * ps.prod) := by ac_rfl
  · have hrbox : ps ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τr)
        (actualPrimeLabelBlocksWord blocks) :=
      (Finset.mem_filter.mp hps).1
    have hnot : ¬ ps.prod ∣ N :=
      original_prime_box_product_not_dvd
        N τr (actualPrimeLabelBlocksWord blocks)
        ps hrbox hresidual
    intro heq
    apply hnot
    refine ⟨marked.prod * hb.prod, ?_⟩
    calc
      N = (marked.prod * hb.prod) * ps.prod := heq.symm
      _ = ps.prod * (marked.prod * hb.prod) := by ac_rfl

/-- Exact complete-product=N fibre is empty in a mixed prime/HB source
as soon as either original prime word has a slot. This does not use
the much stronger (and generally false) claim that all HB factors
are themselves fine primes. -/
theorem hybrid_full_target_fibre_empty
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked hb : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hprime : markedWord ≠ [] ∨
      actualPrimeLabelBlocksWord blocks ≠ []) :
    (actualPrimeFineLabelSortedTuples N τr blocks).filter
      (fun ps => (marked.prod * hb.prod) * ps.prod = N) = ∅ := by
  classical
  ext ps
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hps, heq⟩
  exact (hybrid_full_product_ne_target
    N τm τr markedWord blocks marked hb ps hm hps hprime) heq

/-- The actual weighted SORTED residual PP with arbitrary HB integer
factors is exactly its NONZERO complete-shift divisor expression on
the prime-present subfamily. The very same signed rho, original q,
mu of the entire integer product and exact coprime mean occur on
both sides. There is no bound on the shifted divisor sum here. -/
theorem hybrid_weightedSortedPP_off_divisors
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked hb : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hprime : markedWord ≠ [] ∨
      actualPrimeLabelBlocksWord blocks ≠ [])
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (c : ℝ) (W : List ℕ → ℝ) :
    weightedSortedPP N τr blocks Q rho N
      (marked.prod * hb.prod) c W =
      ∑ q ∈ Q, rho q *
        ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
            (fun ps => (marked.prod * hb.prod) * ps.prod ≠ N),
          (c *
            (ArithmeticFunction.moebius
              ((marked.prod * hb.prod) * ps.prod) : ℝ)) *
            W ps *
            ((if q ∈
                  (markedShiftAbs (marked.prod * hb.prod) N ps.prod).divisors
                then (1 : ℝ) else 0) -
             (if Nat.Coprime ((marked.prod * hb.prod) * ps.prod) q
                then (Nat.totient q : ℝ)⁻¹ else 0)) := by
  rw [weightedSortedPP_split_full_product]
  rw [hybrid_full_target_fibre_empty
    N τm τr markedWord blocks marked hb hm hprime]
  simpa using
    (weightedSortedPP_off_divisors N τr blocks Q rho N
      (marked.prod * hb.prod) c W)

/-- The previous identity is valid after the WHOLE original finite
marked-box/HB-word sum, retaining every labelled occurrence and
arbitrary three-word geometric W. No interchange of tuple weights
through a product-only fibre is used. -/
theorem hybrid_whole_box_same_rho_off_divisors
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (hprime : markedWord ≠ [] ∨
      actualPrimeLabelBlocksWord blocks ≠ [])
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (c : List ℕ → List ℕ → ℝ)
    (W : List ℕ → List ℕ → List ℕ → ℝ) :
    (∑ marked ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord,
      ∑ hb ∈ H,
        weightedSortedPP N τr blocks Q rho N
          (marked.prod * hb.prod) (c marked hb) (W marked hb)) =
    (∑ marked ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord,
      ∑ hb ∈ H,
        ∑ q ∈ Q, rho q *
          ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
              (fun ps => (marked.prod * hb.prod) * ps.prod ≠ N),
            ((c marked hb) *
              (ArithmeticFunction.moebius
                ((marked.prod * hb.prod) * ps.prod) : ℝ)) *
              (W marked hb ps) *
              ((if q ∈
                    (markedShiftAbs (marked.prod * hb.prod) N ps.prod).divisors
                  then (1 : ℝ) else 0) -
               (if Nat.Coprime ((marked.prod * hb.prod) * ps.prod) q
                  then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  apply Finset.sum_congr rfl
  intro marked hm
  apply Finset.sum_congr rfl
  intro hb hhb
  exact hybrid_weightedSortedPP_off_divisors
    N τm τr markedWord blocks marked hb hm hprime Q rho
    (c marked hb) (W marked hb)

/-- When BOTH original prime slot words are empty, the only remaining
diagonal is the HB-only product=N fibre. Its signed value is computed,
not bounded. This is deliberately NOT the empty Gamma mother-word
payment or a claim that the full HB compiler emits this exact H. -/
theorem hybrid_prime_free_hb_exact_diagonal
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (H : Finset (List ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (c : List ℕ → List ℕ → ℝ)
    (W : List ℕ → List ℕ → List ℕ → ℝ)
    (hmarked : markedWord = [])
    (hresidual : actualPrimeLabelBlocksWord blocks = [])
    (hcop : ∀ q ∈ Q, Nat.Coprime N q) :
    (∑ marked ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord,
      ∑ hb ∈ H,
        ∑ q ∈ Q, rho q *
          ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
              (fun ps => (marked.prod * hb.prod) * ps.prod = N),
            ((c marked hb) *
              (ArithmeticFunction.moebius
                ((marked.prod * hb.prod) * ps.prod) : ℝ)) *
              (W marked hb ps) *
              fineKernel N q ((marked.prod * hb.prod) * ps.prod)) =
    (∑ hb ∈ H.filter (fun hb => hb.prod = N),
      (((c [] hb) * (ArithmeticFunction.moebius N : ℝ)) *
        W [] hb []) *
        (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹))) := by
  subst markedWord
  have hbox : actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) ([] : List ℕ) =
      {([] : List ℕ)} := by
    simp [actualPrimeSlotBox]
  rw [hbox]
  simp only [Finset.sum_singleton, List.prod_nil, one_mul]
  calc
    (∑ hb ∈ H,
      ∑ q ∈ Q, rho q *
        ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
            (fun ps => hb.prod * ps.prod = N),
          ((c [] hb) *
            (ArithmeticFunction.moebius (hb.prod * ps.prod) : ℝ)) *
            (W [] hb ps) * fineKernel N q (hb.prod * ps.prod)) =
      ∑ hb ∈ H,
        if actualPrimeLabelBlocksWord blocks = [] ∧ hb.prod = N then
          (((c [] hb) * (ArithmeticFunction.moebius N : ℝ)) *
            W [] hb []) *
            (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹))
        else 0 := by
          apply Finset.sum_congr rfl
          intro hb hhb
          exact exact_target_N_signed_mass
            N τr blocks Q rho hb.prod
            (c [] hb) (W [] hb) hcop
    _ = ∑ hb ∈ H,
          if hb.prod = N then
            (((c [] hb) * (ArithmeticFunction.moebius N : ℝ)) *
              W [] hb []) *
              (∑ q ∈ Q, rho q *
                (1 - (Nat.totient q : ℝ)⁻¹))
          else 0 := by
          apply Finset.sum_congr rfl
          intro hb hhb
          simp [hresidual]
    _ = _ := by rw [Finset.sum_filter]

end
end ImbalancedChen.P3ActualHybridHBPrimeDiagonal
