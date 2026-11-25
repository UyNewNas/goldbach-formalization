import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ChenInitialPrimeSource
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

After the exact TRUE physical d|n prime-source invoice, the retained
fifth and rank-six-spliced policies carry DIFFERENT original rho's.
Their signed difference must first be put on ONE true-d carrier. This
file uses the union of their OWN physical supports (not a new branch
mask) and an exact pointwise signed zero extension. All operations
remain finite, with the original full small/rough attachment and modulus-prime
correction. The original ordered-87 occurrence pushforward remains open.

This proves an exact single-coefficient difference, NOT an identification
with the manuscript's certified full87 rho_N, nor a PP coefficient licence.
In particular the automatic absolute bound is 2, not 1.
-/

namespace ImbalancedChen.P1Full87TrueDPolicyDelta

noncomputable section
open Classical
open scoped BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFifthContinuation

/-- One genuine physical carrier for the difference of two original
retained policies; both summands keep their own, unmodified supports. -/
def trueDDeltaSupport (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli fresh N cap w z ∪
    actualSmallRoughModuli old N cap w z

/-- The exact difference of the two original physical coefficients,
zero-extended only by each one's OWN physical support. -/
def trueDDeltaRho (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ) : ℝ :=
  (if d ∈ actualSmallRoughModuli fresh N cap w z then
    actualSmallRoughRho fresh N cap w z L d else 0) -
  (if d ∈ actualSmallRoughModuli old N cap w z then
    actualSmallRoughRho old N cap w z L d else 0)

theorem trueDDeltaSupport_coprime_target
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {d : ℕ} (hd : d ∈ trueDDeltaSupport old fresh N cap w z) :
    Nat.Coprime d N := by
  change d ∈ actualSmallRoughModuli fresh N cap w z ∪
    actualSmallRoughModuli old N cap w z at hd
  rcases Finset.mem_union.mp hd with h | h
  · exact actualSmallRoughModuli_coprime_target fresh N cap w z h
  · exact actualSmallRoughModuli_coprime_target old N cap w z h

theorem trueDDeltaSupport_squarefree
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {d : ℕ} (hd : d ∈ trueDDeltaSupport old fresh N cap w z) :
    Squarefree d := by
  change d ∈ actualSmallRoughModuli fresh N cap w z ∪
    actualSmallRoughModuli old N cap w z at hd
  rcases Finset.mem_union.mp hd with h | h
  · exact actualSmallRoughModuli_squarefree fresh N cap w z h
  · exact actualSmallRoughModuli_squarefree old N cap w z h

theorem trueDDeltaRho_zero_outside
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    {d : ℕ} (hd : d ∉ trueDDeltaSupport old fresh N cap w z) :
    trueDDeltaRho old fresh N cap w z L d = 0 := by
  have hnew : d ∉ actualSmallRoughModuli fresh N cap w z := by
    intro h
    exact hd (by simp [trueDDeltaSupport, h])
  have hold : d ∉ actualSmallRoughModuli old N cap w z := by
    intro h
    exact hd (by simp [trueDDeltaSupport, h])
  simp [trueDDeltaRho, hnew, hold]

/-- A signed policy difference can be twice as large as either original
coefficient. This is NOT the original one-bound PP licence. -/
theorem trueDDeltaRho_abs_le_two
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ) :
    |trueDDeltaRho old fresh N cap w z L d| ≤ (2 : ℝ) := by
  let a : ℝ := if d ∈ actualSmallRoughModuli fresh N cap w z then
      actualSmallRoughRho fresh N cap w z L d else 0
  let b : ℝ := if d ∈ actualSmallRoughModuli old N cap w z then
      actualSmallRoughRho old N cap w z L d else 0
  have ha : |a| ≤ 1 := by
    dsimp [a]
    split_ifs with h
    · exact actualSmallRoughRho_abs_le_one fresh N cap w z L d
    · norm_num
  have hb : |b| ≤ 1 := by
    dsimp [b]
    split_ifs with h
    · exact actualSmallRoughRho_abs_le_one old N cap w z L d
    · norm_num
  change |a - b| ≤ (2 : ℝ)
  calc
    |a - b| ≤ |a| + |b| := by
      simpa using (abs_sub_le a (0 : ℝ) b)
    _ ≤ 1 + 1 := add_le_add ha hb
    _ = (2 : ℝ) := by norm_num

/-- Every test of the ONE signed delta coefficient is literally the
difference of tests of the two original physical coefficients. This
preserves the true small divisor d and never attaches a survivor mask. -/
theorem trueDDeltaRho_test
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (G : ℕ → ℝ) :
    (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
      trueDDeltaRho old fresh N cap w z L d * G d) =
      (∑ d ∈ actualSmallRoughModuli fresh N cap w z,
        actualSmallRoughRho fresh N cap w z L d * G d) -
      (∑ d ∈ actualSmallRoughModuli old N cap w z,
        actualSmallRoughRho old N cap w z L d * G d) := by
  let A := actualSmallRoughModuli fresh N cap w z
  let B := actualSmallRoughModuli old N cap w z
  let a := actualSmallRoughRho fresh N cap w z L
  let b := actualSmallRoughRho old N cap w z L
  have hA :
      (∑ d ∈ A ∪ B, (if d ∈ A then a d else 0) * G d) =
        ∑ d ∈ A, a d * G d := by
    calc
      _ = ∑ d ∈ A ∪ B, if d ∈ A then a d * G d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h : d ∈ A <;> simp [h]
      _ = ∑ d ∈ (A ∪ B).filter (fun d => d ∈ A), a d * G d := by
        rw [Finset.sum_filter]
      _ = _ := by
        have hf : (A ∪ B).filter (fun d => d ∈ A) = A := by
          ext d
          simp
        rw [hf]
  have hB :
      (∑ d ∈ A ∪ B, (if d ∈ B then b d else 0) * G d) =
        ∑ d ∈ B, b d * G d := by
    calc
      _ = ∑ d ∈ A ∪ B, if d ∈ B then b d * G d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h : d ∈ B <;> simp [h]
      _ = ∑ d ∈ (A ∪ B).filter (fun d => d ∈ B), b d * G d := by
        rw [Finset.sum_filter]
      _ = _ := by
        have hf : (A ∪ B).filter (fun d => d ∈ B) = B := by
          ext d
          simp
        rw [hf]
  change (∑ d ∈ A ∪ B,
      ((if d ∈ A then a d else 0) -
       (if d ∈ B then b d else 0)) * G d) = _
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hA, hB]

/-- Exact finite primitive AP invoice for the SINGLE signed delta.
The modulus-prime correction is still negative and the carrier is
the true small physical d. Signed PP remains an external obligation. -/
theorem trueDDeltaRho_primitive_invoice
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hN : Even N) :
    (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
      trueDDeltaRho old fresh N cap w z L d *
        (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum
          (trueDDeltaSupport old fresh N cap w z)
          (trueDDeltaRho old fresh N cap w z L) +
      (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        trueDDeltaRho old fresh N cap w z L d *
          finitePrimitiveDiscrepancy
            (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
      (∑ d ∈ trueDDeltaSupport old fresh N cap w z,
        trueDDeltaRho old fresh N cap w z L d *
          (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
  let S := trueDDeltaSupport old fresh N cap w z
  let rho := trueDDeltaRho old fresh N cap w z L
  let M : ℝ := ((chenAdditivePrimeCarrier N).card : ℝ)
  change (∑ d ∈ S,
    rho d * (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) =
    M * physicalDensitySum S rho +
    (∑ d ∈ S, rho d *
      finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
        (fun _ => 1) N d) -
    (∑ d ∈ S, rho d *
      (chenPrimeDivisorCount N d / (Nat.totient d : ℝ)))
  calc
    _ = ∑ d ∈ S, rho d *
        (M / (Nat.totient d : ℝ) +
          finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
            (fun _ => 1) N d -
          chenPrimeDivisorCount N d / (Nat.totient d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hcop : Nat.Coprime d N :=
        trueDDeltaSupport_coprime_target old fresh N cap w z hd
      have hrem :=
        chenInitialBoundingSieve_rem_eq_source_discrepancy N z hN hcop
      rw [chenInitialBoundingSieve_rem] at hrem
      have heq :
          chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d =
            M / (Nat.totient d : ℝ) +
              finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
                (fun _ => 1) N d -
              chenPrimeDivisorCount N d / (Nat.totient d : ℝ) := by
        dsimp [M]
        linarith
      rw [heq]
    _ = (∑ d ∈ S, rho d * (M / (Nat.totient d : ℝ))) +
        (∑ d ∈ S, rho d *
          finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
            (fun _ => 1) N d) -
        (∑ d ∈ S, rho d *
          (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
      simp only [mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      have hmean :
          (∑ d ∈ S, rho d * (M / (Nat.totient d : ℝ))) =
            M * physicalDensitySum S rho := by
        unfold physicalDensitySum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      rw [hmean]

/-- Concrete fifth parent and its genuine rank-six splice: the SAME
delta coefficient is used for AP, exact mean and modulus exceptions.
The complete saved-87 fresh policy and event occurrence link are NOT
asserted or fabricated here. -/
theorem actual_fifth_sixth_delta_primitive_invoice
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (rows5 : Finset (FifthRow m))
    (fresh : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (hN : Even N) :
    let R := policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5
    let R6 := firstExitDepthSplicePolicy 6 R fresh
    let S := trueDDeltaSupport (R false) (R6 false) N cap w z
    let rho := trueDDeltaRho (R false) (R6 false) N cap w z L
    (∑ d ∈ S, rho d *
      (chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum S rho +
      (∑ d ∈ S, rho d *
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N d) -
      (∑ d ∈ S, rho d *
        (chenPrimeDivisorCount N d / (Nat.totient d : ℝ))) := by
  dsimp only
  exact trueDDeltaRho_primitive_invoice
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
    ((firstExitDepthSplicePolicy 6
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      fresh) false) N cap w z L hN

end
end ImbalancedChen.P1Full87TrueDPolicyDelta
