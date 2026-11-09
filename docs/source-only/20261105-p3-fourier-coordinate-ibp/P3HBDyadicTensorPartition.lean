import ImbalancedChen.P3HBFinitePartitionRestore
import Mathlib.Tactic

/-!
P3.6: a CONCRETE, finite dyadic positional partition for the literal
ordered 2/4/6-slot HB fibres. This replaces the abstract partition
hypothesis from P3HBFinitePartitionRestore for one canonical full grid.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Frozen paper: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b
prime-product completion §2 (dyadic psi = chi - chi(2·)) and §4 (F).
Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The grid is the COMPLETE six-coordinate dyadic index box. Padding
unused HB coordinates by 1 makes the SAME label family work for all
actual ranks 2,4,6, while respecting ordered positions and units.
This does NOT claim that the ultimately RETAINED subset of rectangles
has already been shown to cover the actual geometric support, nor
that any separate rectangle has the signed HB cancellation.
-/

namespace ImbalancedChen.P3HBDyadicTensorPartition

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P3HBFinitePartitionRestore

/-- The literal dyadic difference psi(x/2^j), with psi(t)=chi(t)-chi(2t). -/
def dyadicPiece (chi : ℝ → ℂ) (x : ℝ) (j : ℕ) : ℂ :=
  chi (x / (2 : ℝ) ^ j) - chi (2 * x / (2 : ℝ) ^ j)

/-- Exact finite telescoping, including both endpoints and j=0. -/
theorem dyadic_telescope (chi : ℝ → ℂ) (x : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicPiece chi x j) =
      chi (x / (2 : ℝ) ^ J) - chi (2 * x) := by
  induction J with
  | zero =>
      simp [dyadicPiece]
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow : (2 : ℝ) ^ J ≠ 0 := by positivity
      have hscale : 2 * x / (2 : ℝ) ^ (J + 1) =
          x / (2 : ℝ) ^ J := by
        rw [pow_succ]
        field_simp [hpow]
        <;> ring
      simp only [dyadicPiece, hscale]
      ring

/-- For 1 ≤ x ≤ 2^J, the whole finite dyadic range is exactly one.
This needs only the two plateau values of chi, not a Fourier estimate. -/
theorem dyadic_one (chi : ℝ → ℂ) (x : ℝ) (J : ℕ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hx : 1 ≤ x) (hJ : x ≤ (2 : ℝ) ^ J) :
    (∑ j ∈ Finset.range (J + 1), dyadicPiece chi x j) = 1 := by
  rw [dyadic_telescope]
  have hpower : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have hquot : x / (2 : ℝ) ^ J ≤ 1 := by
    apply (div_le_iff₀ hpower).2
    simpa using hJ
  rw [hsmall _ hquot, hlarge _ (by nlinarith : 2 ≤ 2 * x)]
  ring

/-- A single common finite family of six positional rectangle labels.
It simultaneously covers the original HB 2-, 4-, and 6-variable words. -/
def dyadicLabels (J : ℕ) : Finset (Fin 6 → ℕ) :=
  Finset.piFinset (fun _ : Fin 6 => Finset.range (J + 1))

/-- Pad unused original HB positions by the unit integer 1.
The value of chi at these dummy positions forces only dyadic index 0. -/
def hbDyadicCut (chi : ℝ → ℂ) (label : Fin 6 → ℕ)
    (_marked hb : List ℕ) : ℂ :=
  ∏ i : Fin 6,
    dyadicPiece chi (((hb.getD i.val 1 : ℕ) : ℝ)) (label i)

/-- Actual factorTuples positivity and complete product give the bounds
for ALL six positions, including the padded unit slots. No abstract
"original rectangle covers the fibre" assumption is used. -/
theorem factorTuple_getD_bounds {r n : ℕ} {hb : List ℕ}
    (hhb : hb ∈ factorTuples r n) (hn : 1 ≤ n) (i : Fin 6) :
    1 ≤ hb.getD i.val 1 ∧ hb.getD i.val 1 ≤ n := by
  obtain ⟨_, hprod, hpos⟩ := factorTuples_spec r n hb hhb
  by_cases hi : i.val < hb.length
  · rw [List.getD_eq_getElem hb 1 hi]
    have hmem : hb[i.val] ∈ hb := List.getElem_mem hi
    have hpositive : 0 < hb[i.val] := hpos _ hmem
    have hle : hb[i.val] ≤ hb.prod := List.le_prod_of_mem hmem
    rw [hprod] at hle
    exact ⟨by omega, hle⟩
  · have hi' : hb.length ≤ i.val := Nat.le_of_not_gt hi
    rw [List.getD_eq_default hb 1 hi']
    exact ⟨le_refl _, hn⟩

/-- The tensor sum of the ACTUAL six-coordinate dyadic cuts is one on
each original ordered HB fibre when n lies under the common scale 2^J.
The fixed grid does not depend on the HB rank, rho, modulus, or sign. -/
theorem factorTuple_dyadic_partition (chi : ℝ → ℂ)
    (J r n : ℕ) (hb : List ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    (∑ label ∈ dyadicLabels J, hbDyadicCut chi label [] hb) = 1 := by
  change
    (∑ label ∈ Finset.piFinset (fun _ : Fin 6 => Finset.range (J + 1)),
      ∏ i : Fin 6,
        dyadicPiece chi (((hb.getD i.val 1 : ℕ) : ℝ)) (label i)) = 1
  rw [Finset.sum_prod_piFinset]
  calc
    (∏ i : Fin 6,
       ∑ j ∈ Finset.range (J + 1),
         dyadicPiece chi (((hb.getD i.val 1 : ℕ) : ℝ)) j) =
       ∏ i : Fin 6, (1 : ℂ) := by
         apply Finset.prod_congr rfl
         intro i _
         obtain ⟨hlo, hhi⟩ := factorTuple_getD_bounds hhb hn i
         have hloR : (1 : ℝ) ≤ ((hb.getD i.val 1 : ℕ) : ℝ) := by
           exact_mod_cast hlo
         have hhiR : (((hb.getD i.val 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ J := by
           have hle : (((hb.getD i.val 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
             exact_mod_cast hhi
           exact hle.trans hnJ
         exact dyadic_one chi _ J hsmall hlarge hloR hhiR
    _ = 1 := by simp

/-- The preceding cutoff does not use marked variables: the empty
marked argument can be replaced by the REAL marked occurrence label. -/
theorem factorTuple_dyadic_partition_marked (chi : ℝ → ℂ)
    (J r n : ℕ) (marked hb : List ℕ)
    (hhb : hb ∈ factorTuples r n)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    (∑ label ∈ dyadicLabels J, hbDyadicCut chi label marked hb) = 1 := by
  simpa only [hbDyadicCut] using
    factorTuple_dyadic_partition chi J r n hb hhb hn hnJ hsmall hlarge

/-- Instantiate the PREVIOUS abstract labelled-partition theorem with
a genuinely constructed dyadic product family on every original
ordered 2/4/6-slot HB occurrence. The original +3,-3,+1 is restored
only after summation over the WHOLE canonical grid. -/
theorem original_hb_dyadic_signed_restoration
    (chi : ℝ → ℂ) (J n : ℕ) (z y : ℝ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3) :
    (∑ label ∈ dyadicLabels J,
      ∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece G (hbDyadicCut chi) label) marked) =
      (G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n) := by
  apply signed_three_partition_restores
    (dyadicLabels J) n z y G (hbDyadicCut chi) marked hz hy hcube
  intro j hj hb hhb _
  exact factorTuple_dyadic_partition_marked
    chi J (2 * (j + 1)) n marked hb hhb hn hnJ hsmall hlarge

/-- Same ORIGINAL integer rho and physical Q, including the complete
product condition. The finite dyadic grid never changes the exact
coprime mean. No arithmetic PP saving is asserted. -/
theorem original_hb_dyadic_offshift_same_rho
    (chi : ℝ → ℂ) (J N n : ℕ) (z y : ℝ)
    (G : List ℕ → ℕ → ℂ) (marked : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hn : 1 ≤ n) (hnJ : (n : ℝ) ≤ (2 : ℝ) ^ J)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (hcube : (n : ℝ) ≤ y ^ 3)
    (hoff : marked.prod * n ≠ N) :
    (∑ label ∈ dyadicLabels J,
      (∑ j ∈ Finset.range 3,
        ((((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ)) *
          originalHBFixedOccurrenceMass n j z y
            (partitionPiece G (hbDyadicCut chi) label) marked) *
        offMarkedPhysicalResponse marked.prod N n Q rho) =
      ((G marked n *
        (((ArithmeticFunction.moebius (marked.prod * n) : ℝ) : ℂ))) *
          (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            roughOneSlot z n)) *
        offMarkedPhysicalResponse marked.prod N n Q rho := by
  apply same_rho_offshift_partition_restores
    (dyadicLabels J) N n z y G (hbDyadicCut chi) marked Q rho
    hz hy hcube hoff
  intro j hj hb hhb _
  exact factorTuple_dyadic_partition_marked
    chi J (2 * (j + 1)) n marked hb hhb hn hnJ hsmall hlarge

end ImbalancedChen.P3HBDyadicTensorPartition
