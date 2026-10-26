import ImbalancedChen.Part3ActualReciprocalSquarePoisson
import ImbalancedChen.Part3OriginalSeparableKloostermanPacket

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Literal finite restriction of ActualReciprocalSquarePoisson.completedPiece
at fixed physical c,z. The original f interval, f!=0, both fixedUnit gates,
ordered u,v, original lambda/omega, and level(u,v)=z are retained. The
physical c-unit condition becomes the single exact c.Coprime z scalar.
Beta_z(y) is DERIVED by a finite signed fibre pushforward; it has no c,
completed-m, smoothing M/N or completed-window argument. Repeated fibres
and y=0 stay. The actual two Schwartz scales remain M and N.

K and eta below are ONE common finite completed-frequency window/weight,
chosen before f,u,v. eta=1 is the unmodulated raw completed restriction.
No claim selects a global truncation or pays its infinite Poisson tail.
No claim bounds the remaining z/c aggregation or full spectral 7/32.
-/

namespace ImbalancedChen.Part3.ActualCompletedPairYFibres20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open scoped BigOperators

abbrev FibreIndex := ℤ × (Inner × Inner)

def originalFWindow (F : ℝ) : Finset ℤ := Icc (Int.ceil (-F)) (Int.floor F)
def originalFuvCarrier (T : Finset ℕ) (H : ℕ) (F : ℝ) : Finset FibreIndex :=
  originalFWindow F ×ˢ (finiteInnerCarrier T H ×ˢ finiteInnerCarrier T H)
def originalY (i : FibreIndex) : ℤ := outputY i.1 i.2.1 i.2.2
def originalZ (i : FibreIndex) : ℕ := level i.2.1 i.2.2

def originalFibreWeight (A : ℕ) (a : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (z : ℕ) (i : FibreIndex) : ℂ :=
  if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧ originalZ i = z then
    atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2) else 0

def actualYCarrier (T : Finset ℕ) (H : ℕ) (F : ℝ) : Finset ℤ :=
  (originalFuvCarrier T H F).image originalY

/-- No completed-m argument exists: its independence is structural,
derived from the actual original f,u,v coefficient and unit gates. -/
def actualBetaZ (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (z : ℕ) (y : ℤ) : ℂ :=
  ∑ i ∈ (originalFuvCarrier T H F).filter (fun i => originalY i = y),
    originalFibreWeight A a lambda omega z i

def actualCommonScalar (q z : ℕ) (N : ℝ) : ℂ :=
  if q.Coprime z then (scaledDyadicCutoff N q : ℂ) else 0

/-- Literal original completedPiece restriction, with one common finite
completed-m window/weight, and one level fibre. This is not a rank1 premise. -/
def actualFixedZCompletedWindow (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) : ℂ :=
  (scaledDyadicCutoff N q : ℂ) *
    ∑ i ∈ originalFuvCarrier T H F,
      if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
          q.Coprime (originalZ i) ∧ originalZ i = z then
        (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
          ∑ m ∈ K, eta m * frequency M q a (originalY i) (originalZ i : ℤ) m else 0

/-- Original f/u/v loops, including their original repeated labels. -/
theorem actualFixedZCompletedWindow_original_loops
    (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta =
      (scaledDyadicCutoff N q : ℂ) *
        ∑ f ∈ Icc (Int.ceil (-F)) (Int.floor F),
          ∑ u ∈ finiteInnerCarrier T H, ∑ v ∈ finiteInnerCarrier T H,
            if f ≠ 0 ∧ fixedUnit A a u.1 ∧ fixedUnit A a v.1 ∧
                q.Coprime (level u v) ∧ level u v = z then
              (atomCoeff lambda omega u * star (atomCoeff lambda omega v)) *
                ∑ m ∈ K, eta m * frequency M q a (outputY f u v) (level u v : ℤ) m else 0 := by
  simp only [actualFixedZCompletedWindow,originalFuvCarrier,originalFWindow,
    Finset.sum_product,originalY,originalZ]

theorem actualFixedZCompletedWindow_pull_level
    (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta =
      actualCommonScalar q z N * ∑ i ∈ originalFuvCarrier T H F,
        originalFibreWeight A a lambda omega z i *
          ∑ m ∈ K, eta m * frequency M q a (originalY i) (z : ℤ) m := by
  unfold actualFixedZCompletedWindow actualCommonScalar
  by_cases hq : q.Coprime z
  · rw [if_pos hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hf : i.1 ≠ 0 <;> by_cases hu : fixedUnit A a i.2.1.1 <;>
      by_cases hv : fixedUnit A a i.2.2.1 <;> by_cases hz : originalZ i = z <;>
      simp [originalFibreWeight,hf,hu,hv,hz,hq]
  · rw [if_neg hq,zero_mul]
    have hzero (i : FibreIndex) :
        (if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
            q.Coprime (originalZ i) ∧ originalZ i = z then
          (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
            ∑ m ∈ K, eta m * frequency M q a (originalY i) (originalZ i : ℤ) m else 0) = 0 := by
      apply if_neg
      intro hgate
      exact hq (hgate.2.2.2.2 ▸ hgate.2.2.2.1)
    simp_rw [hzero]
    simp

/-- Signed finite fibre regrouping: all multiplicities remain inside beta. -/
theorem actual_y_fibre_sum (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (z : ℕ) (g : ℤ → ℂ) :
    (∑ i ∈ originalFuvCarrier T H F, originalFibreWeight A a lambda omega z i * g (originalY i)) =
      ∑ y ∈ actualYCarrier T H F, actualBetaZ A a T H F lambda omega z y * g y := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem originalY hi)
    (fun i => originalFibreWeight A a lambda omega z i * g (originalY i))]
  apply Finset.sum_congr rfl
  intro y hy
  unfold actualBetaZ
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem actual_completed_window_fibre_regroup
    (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    (∑ i ∈ originalFuvCarrier T H F, originalFibreWeight A a lambda omega z i *
      ∑ m ∈ K, eta m * frequency M q a (originalY i) (z : ℤ) m) =
      ∑ m ∈ K, eta m * ∑ y ∈ actualYCarrier T H F,
        actualBetaZ A a T H F lambda omega z y * frequency M q a y (z : ℤ) m := by
  calc
    _ = ∑ m ∈ K, eta m * ∑ i ∈ originalFuvCarrier T H F,
        originalFibreWeight A a lambda omega z i * frequency M q a (originalY i) (z : ℤ) m := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp_rw [actual_y_fibre_sum]

/-- A proved actual-source factorization, not an arbitrary factorizable
coefficient hypothesis. The common window/phase enters ONLY the left side. -/
theorem actualFixedZCompletedWindow_eq_separablePhysicalPacket
    (A q : ℕ) [NeZero q] (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (z : ℕ)
    (K : Finset ℤ) (eta : ℤ → ℂ) :
    actualFixedZCompletedWindow A q a T H F lambda omega M N z K eta =
      separablePhysicalPacket q K (actualYCarrier T H F)
        (fun m => actualCommonScalar q z N * eta m)
        (actualBetaZ A a T H F lambda omega z) M a (z : ℤ) := by
  rw [actualFixedZCompletedWindow_pull_level,actual_completed_window_fibre_regroup]
  unfold separablePhysicalPacket
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro y hy
  ring

end
end ImbalancedChen.Part3.ActualCompletedPairYFibres20261026b
