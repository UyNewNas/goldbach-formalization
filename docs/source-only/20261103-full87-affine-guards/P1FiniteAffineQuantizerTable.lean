import ImbalancedChen.P4AOriginalFourthFifthAffinePrograms

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The previous floor quantizer is expressed as a FINITE threshold program,
not left as a real-valued oracle after compiling the raw guards. Each
output leaf is a rational constant. The threshold test is nonstrict, so
rounding walls have exactly the previous floor convention.
-/
namespace ImbalancedChen.P1FiniteAffineQuantizerTable
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P4AOriginalFourthFifthAffinePrograms
open P1GuardFrozenFiniteCapAlgebra P1OriginalVariableFourthContinuation
open P4AOriginalFull87FiniteEighthCap (downCap downCap_cast)

def denominator (n : ℕ) : ℝ := (n : ℝ) + 1
def indices (n : ℕ) : Finset ℤ := Finset.Icc 0 (n : ℤ)
def gridValue (n : ℕ) (j : ℤ) : ℚ := (j : ℚ) / ((n : ℚ) + 1)

theorem denominator_pos (n : ℕ) : 0 < denominator n := by unfold denominator; positivity
@[simp] theorem gridValue_cast (n : ℕ) (j : ℤ) :
    (gridValue n j : ℝ) = (j : ℝ) / denominator n := by
  simp [gridValue, denominator]

def threshold (n : ℕ) (j : ℤ) (x : ℝ) : Prop :=
  ((j : ℝ) + 1) / denominator n ≤ clamp x

theorem threshold_iff_floor (n : ℕ) (j : ℤ) (x : ℝ) :
    threshold n j x ↔ j + 1 ≤ ⌊denominator n * clamp x⌋ := by
  rw [Int.le_floor, Int.cast_add, Int.cast_one]
  unfold threshold
  rw [div_le_iff₀ (denominator_pos n)]
  rw [mul_comm]

/-- The finite max equals the ORIGINAL biased floor at EVERY real input,
including outside the physical source, due to the original clamp. -/
theorem rounded_eq_threshold_max (n : ℕ) (x : ℝ) :
    (rounded n x : ℝ) =
      finiteMax (indices n) (fun j => threshold n j x)
        (fun j => (gridValue n j : ℝ)) 0 := by
  let z : ℤ := ⌊denominator n * clamp x⌋
  have hd := denominator_pos n
  have hz0 : 0 ≤ z := Int.floor_nonneg.mpr (mul_nonneg hd.le (clamp_bounds x).1)
  have hzn : z < (n : ℤ) + 1 := by
    apply Int.floor_lt.mpr
    push_cast
    have hc : clamp x < 1 := (clamp_bounds x).2.trans_lt (by norm_num [VariableEnvelope.cap])
    have hh := mul_lt_mul_of_pos_left hc hd
    simpa [denominator] using hh
  have hround : (rounded n x : ℝ) = max 0 (((z : ℝ) - 1) / denominator n) := by
    rw [rounded, Rat.cast_max, Rat.cast_zero, downCap_cast]
    rfl
  rw [hround]
  apply le_antisymm
  · apply max_le
    · exact finiteMax_seed_le _ _ _ _
    · by_cases hz1 : z ≤ 1
      · have hzR : (z : ℝ) ≤ 1 := by exact_mod_cast hz1
        exact (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le).trans
          (finiteMax_seed_le _ _ _ _)
      · have hj : z - 1 ∈ indices n := by
          simp only [indices, Finset.mem_Icc]
          omega
        have ht : threshold n (z - 1) x := by
          rw [threshold_iff_floor]
          change z - 1 + 1 ≤ z
          omega
        have h := finiteMax_row_le (indices n) (fun j => threshold n j x)
          (fun j => (gridValue n j : ℝ)) 0 (z - 1) hj ht
        simpa only [gridValue_cast, Int.cast_sub, Int.cast_one] using h
  · apply finiteMax_le
    · exact le_max_left _ _
    · intro j hj htest
      have hjz : j ≤ z - 1 := by
        have hh := (threshold_iff_floor n j x).mp htest
        change j + 1 ≤ z at hh
        omega
      have hjzR : (j : ℝ) ≤ (z : ℝ) - 1 := by exact_mod_cast hjz
      rw [gridValue_cast]
      exact (div_le_div_of_nonneg_right hjzR hd.le).trans (le_max_right _ _)

def clampedProgram {k : ℕ} (p : Program k) : Program k :=
  .sup (atom (K 0)) (.inf (atom (K VariableEnvelope.cap)) p)

def thresholdTests {k : ℕ} (n : ℕ) (p : Program k) (j : ℤ) : List (Gate k) :=
  [LE (atom (K (((j : ℝ) + 1) / denominator n))) (clampedProgram p)]

def roundedProgram {k : ℕ} (n : ℕ) (p : Program k) : Program k :=
  maxRows (thresholdTests n p) (fun j => atom (K (gridValue n j : ℝ)))
    (atom (K 0)) (indices n).toList

def protectedProgram {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k) : Program k :=
  .sup (atom (K (b : ℝ))) (roundedProgram n p)

@[simp] theorem clampedProgram_exact {k : ℕ} (p : Program k) (t : Fin k → ℝ) :
    (clampedProgram p).eval t = clamp (p.eval t) := by
  simp [clampedProgram, Program.eval, clamp]
@[simp] theorem thresholdTests_exact {k : ℕ} (n : ℕ) (p : Program k)
    (j : ℤ) (t : Fin k → ℝ) :
    Passed t (thresholdTests n p j) ↔ threshold n j (p.eval t) := by
  simp [thresholdTests, Passed, LE, Gate.holds, threshold, Program.eval,
    clampedProgram, clamp]

theorem roundedProgram_exact {k : ℕ} (n : ℕ) (p : Program k) (t : Fin k → ℝ) :
    (roundedProgram n p).eval t = (rounded n (p.eval t) : ℝ) := by
  rw [rounded_eq_threshold_max]
  simp only [roundedProgram, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext j
    exact propext (thresholdTests_exact n p j t)
  · funext j
    exact Affine.eval_const _ _
  · exact Affine.eval_const _ _

theorem protectedProgram_exact {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k) (t : Fin k → ℝ) :
    (protectedProgram n b p).eval t = protect n (b : ℝ) (p.eval t) := by
  simp only [protectedProgram, Program.eval, Affine.eval_const, roundedProgram_exact, protect]

private theorem allGates_select_property {k : ℕ} (gs : List (Gate k))
    (yes no : Program k) (cmp : Affine k → Affine k → Bool × Bool)
    (P : Affine k → Prop) (hy : P (yes.select cmp)) (hn : P (no.select cmp)) :
    P ((allGates gs yes no).select cmp) := by
  induction gs with
  | nil => exact hy
  | cons g gs ih =>
      cases hgs : g.strict <;>
        simp only [allGates, Gate.branch, hgs, Bool.false_eq_true, if_false, if_true, Program.select]
      all_goals split_ifs <;> assumption

private theorem maxRows_select_property {k : ℕ} {ι : Type*} (tests : ι → List (Gate k))
    (candidate : ι → Program k) (seed : Program k) (xs : List ι)
    (cmp : Affine k → Affine k → Bool × Bool) (P : Affine k → Prop)
    (hs : P (seed.select cmp)) (hc : ∀ i ∈ xs, P ((candidate i).select cmp)) :
    P ((maxRows tests candidate seed xs).select cmp) := by
  revert hc
  induction xs with
  | nil => intro _; exact hs
  | cons i is ih =>
      intro hc
      have hrest := ih (fun j hj => hc j (by simp [hj]))
      have hrow := hc i (by simp)
      apply allGates_select_property _ _ _ _ P
      · simp only [Program.select]
        split_ifs <;> assumption
      · exact hrest

def outputAlphabet (n : ℕ) (b : ℚ) : Finset ℚ :=
  insert b (insert 0 ((indices n).image (gridValue n)))

/-- Even unrealizable signatures select only one of these constant leaves.
The actual program's affine comparisons do not leak into its output. -/
theorem protected_select_constant {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (cmp : Affine k → Affine k → Bool × Bool) :
    ∃ a ∈ outputAlphabet n b,
      (protectedProgram n b p).select cmp = Affine.const (a : ℝ) := by
  have hrounded : ∃ a ∈ outputAlphabet n b,
      (roundedProgram n p).select cmp = Affine.const (a : ℝ) := by
    apply maxRows_select_property _ _ _ _ cmp
      (fun v => ∃ a ∈ outputAlphabet n b, v = Affine.const (a : ℝ))
    · exact ⟨0, by simp [outputAlphabet], by simp [Program.select]⟩
    · intro j hj
      refine ⟨gridValue n j, ?_, rfl⟩
      have hm : j ∈ indices n := by simpa using hj
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨j, hm, rfl⟩))
  simp only [protectedProgram, Program.select]
  split_ifs
  · exact hrounded
  · exact ⟨b, by simp [outputAlphabet], rfl⟩

def scalarTable {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (s : (protectedProgram n b p).Signature) : ℝ :=
  ((protectedProgram n b p).table s).constant

theorem scalarTable_mem {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (s : (protectedProgram n b p).Signature) :
    scalarTable n b p s ∈ (outputAlphabet n b).image (fun a => (a : ℝ)) := by
  obtain ⟨a, ha, heq⟩ := protected_select_constant n b p
    ((protectedProgram n b p).lookup s)
  exact Finset.mem_image.mpr ⟨a, ha, by simp [scalarTable, Program.table, heq, Affine.const]⟩

theorem scalarTable_on_region {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k)
    (s : (protectedProgram n b p).Signature) (t : Fin k → ℝ)
    (ht : t ∈ (protectedProgram n b p).region s) :
    scalarTable n b p s = protect n (b : ℝ) (p.eval t) := by
  obtain ⟨a, ha, heq⟩ := protected_select_constant n b p
    ((protectedProgram n b p).lookup s)
  have htab := (protectedProgram n b p).table_on_region s t ht
  rw [protectedProgram_exact] at htab
  simpa only [scalarTable, Program.table, heq, Affine.eval_const, Affine.const] using htab

theorem scalarTable_exact {k : ℕ} (n : ℕ) (b : ℚ) (p : Program k) (t : Fin k → ℝ) :
    scalarTable n b p ((protectedProgram n b p).signature t) = protect n (b : ℝ) (p.eval t) :=
  scalarTable_on_region n b p _ t rfl

end
end ImbalancedChen.P1FiniteAffineQuantizerTable
