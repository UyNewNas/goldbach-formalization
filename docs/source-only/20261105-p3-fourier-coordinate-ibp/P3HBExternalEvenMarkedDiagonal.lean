import ImbalancedChen.P3HBOriginalMarkedFineTarget
import Mathlib.Tactic

/-!
P3.6: the remaining external marked-integer complete-product=N diagonal.

This is NOT a claim that an arbitrary even outside marked integer can be
discarded. For a genuine strict rough-HB ordered occurrence with z >= 2 and
even N, a NONZERO complete-target occurrence forces 2 | marked.prod.
Consequently the original finite signed same-Q/rho target contribution
can be restricted EXACTLY to even outside marked products, preserving
all integer HB positions, the genuine roughTupleWeight, the full product,
and the literal fineKernel (congruence minus exact coprime mean).

Unlike the previous original fine-prime box proof, the marked carrier M
here may contain arbitrary integer lists. Example: N=30, marked=[2],
residual product=15, z=2 is NOT ruled out. This statement identifies that
unpaid exceptional family; it neither supplies a bound nor admits it to
the final causal compiler. Frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b
prime-product completion §§2-4. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBExternalEvenMarkedDiagonal

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBEvenRoughTarget
open ImbalancedChen.P3ActualWeightedFineSameRho

/-- For the genuine ordered integer HB fibre, a surviving full-even-target
occurrence must carry the factor 2 in the OUTSIDE marked product.
No primality or fine-alphabet assumption on the marked integers. -/
theorem surviving_target_requires_even_marked
    (N n j : ℕ) (z y : ℝ) (marked hb : List ℕ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hfull : marked.prod * hb.prod = N)
    (hsurvive : roughTupleWeight z y (roles j) hb ≠ 0) :
    2 ∣ marked.prod := by
  by_contra hodd
  have htwo : 2 ∣ marked.prod * hb.prod := by
    rw [hfull]
    exact even_iff_two_dvd.mp hN
  have htwoHB : 2 ∣ hb.prod :=
    ((Nat.prime_two.dvd_mul).mp htwo).resolve_left hodd
  have hprod : hb.prod = n :=
    (factorTuples_spec (2 * (j + 1)) n hb hhb).2.1
  have hnEven : Even n :=
    even_iff_two_dvd.mpr (hprod ▸ htwoHB)
  exact hsurvive
    (literal_occurrence_target_zero z y j n hz hnEven hb hhb)

/-- Any ODD outside marked product forces zero on the full-even-target
fibre. The restriction is simply 2 ∤ marked.prod, not a distribution
hypothesis or an invented prime support field. -/
theorem odd_marked_target_occurrence_zero
    (N n j : ℕ) (z y : ℝ) (marked hb : List ℕ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hhb : hb ∈ factorTuples (2 * (j + 1)) n)
    (hfull : marked.prod * hb.prod = N)
    (hodd : ¬ 2 ∣ marked.prod) :
    roughTupleWeight z y (roles j) hb = 0 := by
  by_contra hsurvive
  exact hodd (surviving_target_requires_even_marked
    N n j z y marked hb hz hN hhb hfull hsurvive)

/-- Literal finite target contribution at ONE physical modulus q.
M holds arbitrary OUTSIDE marked integer labels (not just fine primes).
Both count and coprime mean test marked.prod * hb.prod. -/
def markedRoughTargetAtQ
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ) : ℂ :=
  ∑ marked ∈ M,
    ∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
        (fun hb => marked.prod * hb.prod = N),
      W (marked, hb) * roughTupleWeight z y (roles j) hb *
        ((fineKernel N q (marked.prod * hb.prod) : ℝ) : ℂ)

/-- Exact support localization to the even marked integers; nothing
bounds or deletes that exceptional part. All ordered HB multiplicities
and the original physical kernel survive this equality. -/
theorem markedRoughTargetAtQ_eq_even_marked
    (N n j q : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    markedRoughTargetAtQ N n j q z y M W =
      markedRoughTargetAtQ N n j q z y
        (M.filter (fun marked => 2 ∣ marked.prod)) W := by
  classical
  unfold markedRoughTargetAtQ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro marked hmarked
  by_cases heven : 2 ∣ marked.prod
  · simp [heven]
  · have hzero :
        (∑ hb ∈ (factorTuples (2 * (j + 1)) n).filter
            (fun hb => marked.prod * hb.prod = N),
          W (marked, hb) * roughTupleWeight z y (roles j) hb *
            ((fineKernel N q (marked.prod * hb.prod) : ℝ) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro hb hhbmem
      obtain ⟨hhb, hfull⟩ := Finset.mem_filter.mp hhbmem
      have hw := odd_marked_target_occurrence_zero
        N n j z y marked hb hz hN hhb hfull heven
      rw [hw]
      simp
    simp [heven, hzero]

/-- Keep the SAME integer rho, physical Q and original HB signs. Only
the even outside marked products can survive the exact-target fibre.
The even contribution is not claimed small. -/
theorem signed_three_target_eq_even_marked
    (N n : ℕ) (z y : ℝ)
    (M : Finset (List ℕ))
    (W : List ℕ × List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          markedRoughTargetAtQ N n j q z y M W) =
    (∑ q ∈ Q, (rho q : ℂ) *
      ∑ j ∈ Finset.range 3,
        (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
          markedRoughTargetAtQ N n j q z y
            (M.filter (fun marked => 2 ∣ marked.prod)) W) := by
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [markedRoughTargetAtQ_eq_even_marked N n j q z y M W hz hN]

end
end ImbalancedChen.P3HBExternalEvenMarkedDiagonal
