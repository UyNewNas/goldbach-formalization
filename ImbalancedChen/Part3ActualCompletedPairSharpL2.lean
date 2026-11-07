import ImbalancedChen.Part3ActualCompletedPairYFibres

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Exact finite-level decomposition of the original completed-pair source
and its sharp q^2 bound at fixed c,z. BOTH true collision energies are
kept. In particular the right coefficient counts every original ordered
f,u,v fibre before residue reduction; it is not a new arbitrary beta.

The only completed-m input is the common finite K and common eta already
used literally on the source. No per-y window or phase is introduced.
eta=1 gives the original raw finite restriction. A proved uniform common
truncation and its infinite Poisson tail remain separate OPEN obligations.
No z/c aggregate estimate or full retained spectral 7/32 is asserted.
-/

namespace ImbalancedChen.Part3.ActualCompletedPairSharpL220261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedPairYFibres20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open scoped BigOperators

def actualZCarrier (T : Finset ℕ) (H : ℕ) (F : ℝ) : Finset ℕ :=
  (originalFuvCarrier T H F).image originalZ

def actualCompletedQWindow (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ)
    (K : Finset ℤ) (eta : ℤ → ℂ) : ℂ :=
  (scaledDyadicCutoff N q : ℂ) *
    ∑ i ∈ originalFuvCarrier T H F,
      if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧ q.Coprime (originalZ i) then
        (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
          ∑ m ∈ K, eta m * frequency M q a (originalY i) (originalZ i : ℤ) m else 0

/-- Exact original level split. Repeated equal levels remain in the
corresponding signed coefficient, including output y=0. -/
theorem actualCompletedQWindow_eq_sum_level_fibres
    (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualCompletedQWindow A q a T H F lambda omega M N K eta =
      ∑ z ∈ actualZCarrier T H F,
        actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta := by
  unfold actualCompletedQWindow actualFixedZCompletedWindow
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hz : originalZ i ∈ actualZCarrier T H F := Finset.mem_image_of_mem originalZ hi
  rw [Finset.sum_eq_single (originalZ i)]
  · simp only [and_true]
  · intro z hz' hne
    simp only [show originalZ i ≠ z from Ne.symm hne,and_false,if_false]
  · exact fun hnot => (hnot hz).elim

/-- The actual finite completedPiece restriction, with its original c
range, physical M,N and original f,T,H. No uniform cutoff is claimed. -/
def actualFiniteCompletedPiece (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C F : ℝ)
    (K : Finset ℤ) (eta : ℤ → ℂ) : ℂ :=
  ∑ q ∈ Ioc 0 (Nat.floor (10*C)), actualCompletedQWindow A q a T H F lambda omega M N K eta

theorem actualFiniteCompletedPiece_original_loops
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C F : ℝ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualFiniteCompletedPiece A a T H lambda omega M N C F K eta =
      ∑ q ∈ Ioc 0 (Nat.floor (10*C)), ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
        if f ≠ 0 then (scaledDyadicCutoff N q : ℂ) *
          (∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
            if fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧ q.Coprime (level u v) then
              (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                ∑ m ∈ K, eta m * frequency M q a (outputY f u v) (level u v : ℤ) m else 0) else 0 := by
  unfold actualFiniteCompletedPiece actualCompletedQWindow originalFuvCarrier originalFWindow
  simp only [Finset.sum_product,Finset.mul_sum,originalY,originalZ]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · simp only [hfn,true_and,if_true]
  · simp [hfn]

theorem actualFiniteCompletedPiece_eq_sum_level_fibres
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C F : ℝ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualFiniteCompletedPiece A a T H lambda omega M N C F K eta =
      ∑ q ∈ Ioc 0 (Nat.floor (10*C)), ∑ z ∈ actualZCarrier T H F,
        actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta := by
  unfold actualFiniteCompletedPiece
  simp_rw [actualCompletedQWindow_eq_sum_level_fibres]

def actualLeftCollision (q z : ℕ) [NeZero q] (K : Finset ℤ)
    (eta : ℤ → ℂ) (M N : ℝ) : ZMod q → ℂ :=
  packetLeftCoefficient q K (fun m => actualCommonScalar q z N * eta m) M (z : ℤ)

def actualRightCollision (A q : ℕ) [NeZero q] (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (z : ℕ) : ZMod q → ℂ :=
  packetRightCoefficient q (actualYCarrier T H F) (actualBetaZ A a T H F lambda omega z) a

/-- The right collision energy really contains every original f,u,v
coefficient. Equal integer y and equal residue a*y are BOTH aggregated. -/
theorem actualRightCollision_original_fibres
    (A q : ℕ) [NeZero q] (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (z : ℕ) (v : ZMod q) :
    actualRightCollision A q a T H F lambda omega z v =
      ∑ i ∈ originalFuvCarrier T H F,
        if ((a*originalY i : ℤ) : ZMod q) = v then originalFibreWeight A a lambda omega z i else 0 := by
  unfold actualRightCollision packetRightCoefficient
  calc
    _ = ∑ y ∈ actualYCarrier T H F, actualBetaZ A a T H F lambda omega z y *
        (if ((a*y : ℤ) : ZMod q) = v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      split_ifs <;> simp
    _ = ∑ i ∈ originalFuvCarrier T H F, originalFibreWeight A a lambda omega z i *
        (if ((a*originalY i : ℤ) : ZMod q) = v then 1 else 0) :=
      (actual_y_fibre_sum A a T H F lambda omega z _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

/-- Sharp finite analytic bound on this ACTUAL original source fibre.
No rank1 premise, no unnamed replacement beta and no deleted collision. -/
theorem actualFixedZCompletedWindow_sharp_norm_sq_le
    (A q : ℕ) [NeZero q] (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    ‖actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta‖^2 ≤
      (q : ℝ)^2 * (energy q (actualLeftCollision q z K eta M N) *
        energy q (actualRightCollision A q a T H F lambda omega z)) := by
  rw [actualFixedZCompletedWindow_eq_separablePhysicalPacket]
  exact separablePhysicalPacket_norm_sq_le q K (actualYCarrier T H F)
    (fun m => actualCommonScalar q z N * eta m)
    (actualBetaZ A a T H F lambda omega z) M a (z : ℤ)

end
end ImbalancedChen.Part3.ActualCompletedPairSharpL220261026b
