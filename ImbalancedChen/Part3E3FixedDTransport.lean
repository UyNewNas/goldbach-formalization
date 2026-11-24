import ImbalancedChen.Part3E2Reciprocity
import ImbalancedChen.Part3E2RectangularVariation

/-!
# The fixed-d E3 rectangle before and after exact reciprocity

Equations (4)–(6) of `lichtman-E2-retained-phase-unified-interface-20261010.txt`
use the original q variable and the denominator `q*w₁*w₂`. All clean CRT
conditions remain inside the bare coefficient, including the congruence,
close-pair cut and both signs of the nonzero h box. The `n₂` sum stays
inside each five-coordinate cell.
-/

namespace ImbalancedChen.Part3.E3Finite

noncomputable section

open Classical Finset
open scoped BigOperators FourierTransform SchwartzMap
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (reciprocalPhase)

/-- Conditions (5) on the two ordered rough and sample slots, together
with the actual signed nonzero cut. The fixed-d outer weight is external. -/
def cleanGate (d : ℕ) (a : ℤ) (H sep : ℝ) (q w₁ w₂ n₁ n₂ : ℕ) (h : ℤ) : Prop :=
  q.Coprime a.natAbs ∧ w₁.Coprime (a.natAbs * w₂) ∧ w₂.Coprime (a.natAbs * q * d * w₁) ∧
    Nat.ModEq (q * d) n₁ n₂ ∧ n₁.Coprime (n₂ * q * d * w₁) ∧ n₂.Coprime (n₁ * q * d * w₂) ∧
    sep ≤ |(n₁ : ℝ) - (n₂ : ℝ)| ∧ h ≠ 0 ∧ |(h : ℝ)| ≤ H

private def reciprocalAt (m n : ℕ) (A : ℤ) : ℂ :=
  if hm : m ≠ 0 then @reciprocalPhase m ⟨hm⟩ A (n : ZMod m) else 0

private theorem reciprocalAt_eq (m n : ℕ) (A : ℤ) [NeZero m] :
    reciprocalAt m n A = reciprocalPhase m A (n : ZMod m) := by
  unfold reciprocalAt
  rw [dif_pos (NeZero.ne m)]

private def signedFrequency (h₀ : ℤ) (x : E2GridIndex → ℕ) : ℤ := h₀ + (x (.inr ()) : ℤ)

/-- The natural offset enumerates a signed integer interval one-to-one. -/
theorem sum_offset_eq_signed_Icc (h₀ : ℤ) (lo hi : ℕ) (f : ℤ → ℂ) :
    (∑ j ∈ Icc lo hi, f (h₀ + (j : ℤ))) =
      ∑ h ∈ Icc (h₀ + (lo : ℤ)) (h₀ + (hi : ℤ)), f h := by
  refine sum_bij' (fun j _ => h₀ + (j : ℤ)) (fun h _ => (h - h₀).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_Icc] at hj ⊢
    omega
  · intro h hh
    rw [mem_Icc] at hh ⊢
    omega
  · intro j _
    omega
  · intro h hh
    rw [mem_Icc] at hh
    omega
  · intro j _
    rfl

/-- Equation (4) on one positive q cell. `coeff` is the original pair of
Lambda and alpha factors, or the same array with extra fixed support masks. -/
def source (lo hi : E2GridIndex → ℕ) (N₂ : Finset ℕ) (d : ℕ) (a h₀ : ℤ)
    (Q M H sep : ℝ) (ψ ψhat : ℝ → ℂ) (coeff : (E2GridIndex → ℕ) → ℕ → ℂ) : ℂ :=
  ∑ x ∈ RectangularAbel.rectangle lo hi, ∑ n₂ ∈ N₂,
    let q := x (.inl 0)
    let w₁ := x (.inl 1)
    let w₂ := x (.inl 2)
    let n₁ := x (.inl 3)
    let h := signedFrequency h₀ x
    if cleanGate d a H sep q w₁ w₂ n₁ n₂ h then
      (coeff x n₂ / ((q * w₁ * w₂ : ℕ) : ℂ)) * ψ ((q : ℝ) / Q) *
        ψhat ((h : ℝ) * M / ((q : ℝ) * d * w₁ * w₂)) *
        (reciprocalAt (q * d * w₁) (n₁ * w₂) (a * h) *
          reciprocalAt w₂ (n₂ * q * d * w₁) (a * h))
    else 0

/-- The bare coefficient after (21), including the full original `n₂`
cell and the same arithmetic conditions and denominator. -/
def bareCoefficient (N₂ : Finset ℕ) (d : ℕ) (a h₀ : ℤ) (H sep : ℝ)
    (coeff : (E2GridIndex → ℕ) → ℕ → ℂ) (x : E2GridIndex → ℕ) : ℂ :=
  ∑ n₂ ∈ N₂,
    let q := x (.inl 0)
    let w₁ := x (.inl 1)
    let w₂ := x (.inl 2)
    let n₁ := x (.inl 3)
    let h := signedFrequency h₀ x
    if cleanGate d a H sep q w₁ w₂ n₁ n₂ h then
      (coeff x n₂ / ((q * w₁ * w₂ : ℕ) : ℂ)) *
        reciprocalAt (n₁ * w₂) (n₂ * q * d * w₁) (a * h * ((n₁ : ℤ) - n₂))
    else 0

private theorem cleanGate_phase (d q w₁ w₂ n₁ n₂ : ℕ) (a h : ℤ) (H sep : ℝ)
    [NeZero d] [NeZero q] [NeZero w₁] [NeZero w₂] [NeZero n₁]
    (hg : cleanGate d a H sep q w₁ w₂ n₁ n₂ h) :
    reciprocalAt (q * d * w₁) (n₁ * w₂) (a * h) *
        reciprocalAt w₂ (n₂ * q * d * w₁) (a * h) =
      reciprocalAt (n₁ * w₂) (n₂ * q * d * w₁) (a * h * ((n₁ : ℤ) - n₂)) *
        fourier 1 (((((a * h : ℤ) : ℝ) / ((q : ℝ) * d * w₁ * w₂ * n₁)) : ℝ) : UnitAddCircle) := by
  have hn₁ := hg.2.2.2.2.1
  have hn₂ := hg.2.2.2.2.2.1
  have hw₂ := hg.2.2.1
  have hc₁ : n₁.Coprime (q * d * w₁) := hn₁.coprime_dvd_right ⟨n₂, by ring⟩
  have hc₂ : w₂.Coprime (q * d * w₁) := hw₂.coprime_dvd_right ⟨a.natAbs, by ring⟩
  have hc₃ : n₂.Coprime w₂ := hn₂.coprime_dvd_right (dvd_mul_left _ _)
  have hc₄ : (n₂ * q * d * w₁).Coprime w₂ := by
    simpa only [mul_assoc] using hc₃.mul_left hc₂.symm
  simp only [reciprocalAt_eq]
  exact e2ReciprocalPhase_eq21 q d w₁ w₂ n₁ n₂ (hc₁.mul_left hc₂) (hn₁.symm.mul_right hc₄) a h

/-- Exact transport to the five-coordinate physical weight of equation
(22), keeping the full bare coefficient independent of the smooth profile. -/
theorem source_eq_weighted_rectangle (lo hi : E2GridIndex → ℕ) (N₂ : Finset ℕ)
    (d : ℕ) (a h₀ : ℤ) (Q M H sep : ℝ) (ψ ψhat : ℝ → ℂ)
    (coeff : (E2GridIndex → ℕ) → ℕ → ℂ) (hd : 0 < d)
    (hlo : ∀ i : Fin 4, 0 < lo (.inl i)) :
    source lo hi N₂ d a h₀ Q M H sep ψ ψhat coeff =
      ∑ x ∈ RectangularAbel.rectangle lo hi,
        bareCoefficient N₂ d a h₀ H sep coeff x * e2PhysicalGridWeight ψ ψhat Q M d a h₀ x := by
  unfold source bareCoefficient
  simp only [sum_mul]
  apply sum_congr rfl
  intro x hx
  have hpos (i : Fin 4) : 0 < x (.inl i) := (hlo i).trans_le ((RectangularAbel.mem_rectangle.mp hx).1 _)
  let _ : NeZero d := ⟨hd.ne'⟩
  let _ : NeZero (x (.inl 0)) := ⟨(hpos 0).ne'⟩
  let _ : NeZero (x (.inl 1)) := ⟨(hpos 1).ne'⟩
  let _ : NeZero (x (.inl 2)) := ⟨(hpos 2).ne'⟩
  let _ : NeZero (x (.inl 3)) := ⟨(hpos 3).ne'⟩
  apply sum_congr rfl
  intro n₂ _
  by_cases hg : cleanGate d a H sep (x (.inl 0)) (x (.inl 1)) (x (.inl 2)) (x (.inl 3)) n₂
      (signedFrequency h₀ x)
  · simp only [if_pos hg, cleanGate_phase _ _ _ _ _ _ _ _ _ _ hg]
    unfold e2PhysicalGridWeight signedFrequency
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast]
    ring
  · simp only [if_neg hg, zero_mul]

/-- A cutoff below one leaves no signed nonzero frequency. -/
theorem source_eq_zero_of_short_H (lo hi : E2GridIndex → ℕ) (N₂ : Finset ℕ)
    (d : ℕ) (a h₀ : ℤ) (Q M H sep : ℝ) (ψ ψhat : ℝ → ℂ)
    (coeff : (E2GridIndex → ℕ) → ℕ → ℂ) (hH : H < 1) :
    source lo hi N₂ d a h₀ Q M H sep ψ ψhat coeff = 0 := by
  have hnone (q w₁ w₂ n₁ n₂ : ℕ) (h : ℤ) : ¬ cleanGate d a H sep q w₁ w₂ n₁ n₂ h := by
    intro hg
    obtain ⟨_, _, _, _, _, _, _, hne, hbound⟩ := hg
    have hone : (1 : ℝ) ≤ (h.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hne
    have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs h)
    linarith
  exact sum_eq_zero (fun x _ => sum_eq_zero (fun n₂ _ => if_neg (hnone _ _ _ _ n₂ _)))

/-- The (22) variation bound applied to the actual E3 rectangle. Its
analytic hypothesis is a uniform prefix bound for the exact bare cells. -/
theorem exists_source_rectangular_rpow {κ ε Cq Cd : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hCq : 0 ≤ Cq) (hCd : 0 ≤ Cd)
    (ψ ψhat : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X M N Q D R q₀ H sep : ℝ) (d : ℕ) (a h₀ : ℤ),
      1 ≤ X → X = N * M → 0 < M → 0 < N → 0 < Q → 0 ≤ D → 0 < R →
      0 < q₀ → 0 < d → 0 < H → q₀ ≤ 2 * Q → Q / q₀ ≤ Cq → D / (d : ℝ) ≤ Cd →
      H ≤ Q * D * R^2 * (Real.log X)^5 / M → |(a : ℝ)| ≤ X ^ (1 + κ) →
      ∀ (lo hi : E2GridIndex → ℕ), lo ≤ hi →
      (∀ (i : Fin 4) (n : ℕ), n ∈ Set.Icc (lo (.inl i)) (hi (.inl i)) →
        e2PositiveScales q₀ R N i ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * e2PositiveScales q₀ R N i) →
      (∀ n : ℕ, n ∈ Set.Icc (lo (.inr ())) (hi (.inr ())) → |(h₀ : ℝ) + (n : ℝ)| ≤ H) →
      ∀ (N₂ : Finset ℕ) (coeff : (E2GridIndex → ℕ) → ℕ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ y ∈ RectangularAbel.rectangle lo hi,
        ‖∑ x ∈ RectangularAbel.rectangle lo y, bareCoefficient N₂ d a h₀ H sep coeff x‖ ≤ B) →
      ‖source lo hi N₂ d a h₀ Q M H sep ψ ψhat coeff‖ ≤ C * X ^ (5 * κ + ε) * B := by
  obtain ⟨C, hC, hbound⟩ := exists_e2PhysicalWeight_rectangular_rpow hκ hε hCq hCd ψ ψhat
  refine ⟨C, hC, ?_⟩
  intro X M N Q D R q₀ H sep d a h₀ hX hscale hM hN hQ hD hR hq₀ hd hH hqUpper hqRatio hdRatio
    hcut ha lo hi hbox hboxPos hboxH N₂ coeff B hB0 hB
  have hlo (i : Fin 4) : 0 < lo (.inl i) := by
    have hscalePos : 0 < e2PositiveScales q₀ R N i := by fin_cases i <;> assumption
    exact Nat.cast_pos.mp (hscalePos.trans_le (hboxPos i _ ⟨le_rfl, hbox _⟩).1)
  rw [source_eq_weighted_rectangle lo hi N₂ d a h₀ Q M H sep ψ ψhat coeff hd hlo]
  exact hbound X M N Q D R q₀ d H a hX hscale hM hN hQ hD hR hq₀ (Nat.cast_pos.mpr hd) hH
    hqUpper hqRatio hdRatio hcut ha lo hi hbox h₀ hboxPos hboxH
    (bareCoefficient N₂ d a h₀ H sep coeff) B hB0 hB

end

end ImbalancedChen.Part3.E3Finite
