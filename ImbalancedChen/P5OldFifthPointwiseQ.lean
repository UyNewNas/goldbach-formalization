import ImbalancedChen.P5OldFifthChildGapIntegral
import ImbalancedChen.ActualRosserLowerLimit

/-! SOURCE ONLY / UNCOMPILED / READY=false / ZERO FORMAL CREDIT.
This candidate isolates the strict own-cube profile-to-Q_b theorem on
the actual frozen U_P surrogate. The one remaining local calculus input
is firstF concavity on [2,4], stated explicitly below; its derivative
proof is in the companion mathematical source, not claimed compiled.
No integral lower bound or floor is assumed. -/

namespace ImbalancedChen.P5OldFifthPointwiseQ
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity

abbrev Point := Fin 5 → ℝ

def sum5 (t : Point) : ℝ := ∑ i : Fin 5, t i
def residual (λ : ℝ) (t : Point) : ℝ := (λ - sum5 t) / t 4
def firstF (s : ℝ) : ℝ := Real.log (s - 1) / s
def Q (b u : ℝ) : ℝ := firstF b - firstF (b - u)

theorem firstF_two : firstF 2 = 0 := by
  simp [firstF]

/-- Concavity makes backward increments decrease as their right
endpoint moves right. This is the precise comparison needed for Q. -/
theorem backward_increment_of_concave
    (hconc : ConcaveOn ℝ (Icc (2 : ℝ) 4) firstF)
    {s b u : ℝ} (hs2 : 2 ≤ s - u) (hu : 0 ≤ u)
    (hsb : s ≤ b) (hb4 : b ≤ 4) :
    Q b u ≤ firstF s - firstF (s - u) := by
  by_cases hzero : b - s + u = 0
  · have hbs : b = s := by linarith
    have hu0 : u = 0 := by linarith
    simp [Q, hbs, hu0]
  · have hD : 0 < b - s + u := by linarith
    let α := (b - s) / (b - s + u)
    let β := u / (b - s + u)
    have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr hsb) hD.le
    have hβ : 0 ≤ β := div_nonneg hu hD.le
    have hsum : α + β = 1 := by
      dsimp [α, β]
      field_simp [hD.ne']
      ring
    have ha : s - u ∈ Icc (2 : ℝ) 4 :=
      ⟨hs2, by linarith⟩
    have hb : b ∈ Icc (2 : ℝ) 4 :=
      ⟨by linarith, hb4⟩
    have hfirst := hconc.2 ha hb hα hβ hsum
    have hsecond := hconc.2 ha hb hβ hα (by linarith [hsum])
    have hm1 : α * (s - u) + β * b = s := by
      dsimp [α, β]
      field_simp [hD.ne']
      ring
    have hm2 : β * (s - u) + α * b = b - u := by
      dsimp [α, β]
      field_simp [hD.ne']
      ring
    simp only [smul_eq_mul, hm1] at hfirst
    simp only [smul_eq_mul, hm2] at hsecond
    have heq :
        (α * firstF (s - u) + β * firstF b) +
          (β * firstF (s - u) + α * firstF b) =
            firstF (s - u) + firstF b := by
      calc
        _ = (α + β) * (firstF (s - u) + firstF b) := by ring
        _ = _ := by rw [hsum]; ring
    unfold Q
    linarith

/-- The literal strict own-cube gate agrees with the clamped first
Rosser interval profile, including equality at the threshold. -/
theorem gatedProfile_eq_first (λ : ℝ) (t : Point)
    (ht : 0 < t 4)
    (hfour : max 2 (residual λ t) ≤ 4) :
    primeOwnCubeGatedProfile λ t =
      (4 / t 4) * firstF (max 2 (residual λ t)) := by
  have htwo : 2 ≤ max 2 (residual λ t) := le_max_left _ _
  by_cases hg : ownCubeThreshold t < λ
  · have hg' : primeTupleOwnCubeForm t < λ := by
      simpa [primeTupleOwnCubeForm, ownCubeThreshold, sum5] using hg
    have hres : 2 < residual λ t := by
      apply (lt_div_iff₀ ht).2
      dsimp [residual, sum5, ownCubeThreshold] at *
      linarith
    have hmax : max 2 (residual λ t) = residual λ t :=
      max_eq_right hres.le
    simp only [primeOwnCubeGatedProfile, if_pos hg',
      primeTupleMinusProfile]
    rw [suzukiContinuousLowerFactor_firstInterval_eq
      (max 2 (residual λ t)) htwo hfour]
    simp only [firstF, residual, sum5, Real.exp_neg]
    field_simp [ht.ne', Real.exp_ne_zero]
    ring
  · have hng : ¬ primeTupleOwnCubeForm t < λ := by
      simpa [primeTupleOwnCubeForm, ownCubeThreshold, sum5] using hg
    have hres : residual λ t ≤ 2 := by
      apply (div_le_iff₀ ht).2
      dsimp [residual, sum5, ownCubeThreshold] at *
      linarith
    have hmax : max 2 (residual λ t) = 2 := max_eq_left hres
    simp [primeOwnCubeGatedProfile, hng, hmax, firstF_two]

/-- Original strict-gate pointwise bridge for the positive-part
unbuffered frozen-parent surrogate. The ratio upper bound b is the
child's two-plane A/B enclosure, not a bound assumed on the integral. -/
theorem frozenUpperPositiveKernel_ge_Q
    (hconc : ConcaveOn ℝ (Icc (2 : ℝ) 4) firstF)
    (picks : ParentPicks) (raw : FifthWireRow)
    (t : Point) (ht : ∀ i : Fin 5, 0 < t i)
    (b : ℝ) (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : residual (rawCandidate 0 raw t) t ≤ b) :
    (4 / t 4) * (∏ i : Fin 5, 1 / t i) *
        Q b (max 0 (frozenGap picks raw t) / t 4) ≤
      frozenUpperPositiveKernel picks raw t := by
  let M := rawCandidate 0 raw t
  let U := frozenParentUpper picks t
  let H := ownCubeThreshold t
  let g := frozenGap picks raw t
  let sM := residual M t
  let sU := residual U t
  let u := max 0 g / t 4
  have ht4 := ht 4
  have hw : 0 ≤ ∏ i : Fin 5, 1 / t i :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (ht i).le)
  have hu : 0 ≤ u := div_nonneg (le_max_left _ _) ht4.le
  by_cases hg : g ≤ 0
  · have hu0 : u = 0 := by simp [u, max_eq_left hg]
    have hq0 : Q b u = 0 := by simp [hu0, Q]
    rw [hq0]
    simp only [mul_zero]
    exact frozenUpperPositiveKernel_nonneg picks raw t
  · have hgp : 0 < g := lt_of_not_ge hg
    have hM : max U H < M := by
      dsimp [g, frozenGap, frozenCeiling, M, U, H] at hgp ⊢
      linarith
    have hMH : H < M := (le_max_right U H).trans_lt hM
    have hsM2 : 2 < sM := by
      apply (lt_div_iff₀ ht4).2
      dsimp [sM, residual, M, H, ownCubeThreshold, sum5] at *
      linarith
    have huEq : u = g / t 4 := by simp [u, max_eq_right hgp.le]
    have hlink : sM - u = max 2 sU := by
      by_cases hUH : U ≤ H
      · have hmax : max U H = H := max_eq_right hUH
        have hsU : sU ≤ 2 := by
          apply (div_le_iff₀ ht4).2
          dsimp [sU, residual, U, H, ownCubeThreshold, sum5] at *
          linarith
        rw [max_eq_left hsU, huEq]
        dsimp [sM, sU, residual, g, frozenGap,
          frozenCeiling, M, U, H, ownCubeThreshold, sum5]
        rw [hmax]
        field_simp [ht4.ne']
        ring
      · have hHU : H < U := lt_of_not_ge hUH
        have hmax : max U H = U := max_eq_left hHU.le
        have hsU : 2 < sU := by
          apply (lt_div_iff₀ ht4).2
          dsimp [sU, residual, U, H, ownCubeThreshold, sum5] at *
          linarith
        rw [max_eq_right hsU.le, huEq]
        dsimp [sM, sU, residual, g, frozenGap,
          frozenCeiling, M, U, H]
        rw [hmax]
        field_simp [ht4.ne']
        ring
    have hsOld2 : 2 ≤ sM - u := by rw [hlink]; exact le_max_left _ _
    have hsM4 : max 2 sM ≤ 4 := by
      rw [max_eq_right hsM2.le]
      exact hnew.trans hb4
    have hsU4 : max 2 sU ≤ 4 := by
      rw [← hlink]
      linarith [hnew, hu]
    have hnewProfile := gatedProfile_eq_first M t ht4 hsM4
    have holdProfile := gatedProfile_eq_first U t ht4 hsU4
    have hback := backward_increment_of_concave hconc
      hsOld2 hu hnew hb4
    have hfour : 0 ≤ 4 / t 4 := div_nonneg (by norm_num) ht4.le
    unfold frozenUpperPositiveKernel
    calc
      (4 / t 4) * (∏ i : Fin 5, 1 / t i) * Q b u =
          ((4 / t 4) * Q b u) * (∏ i : Fin 5, 1 / t i) := by ring
      _ ≤ ((4 / t 4) * (firstF sM - firstF (sM - u))) *
          (∏ i : Fin 5, 1 / t i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hback hfour) hw
      _ = (primeOwnCubeGatedProfile M t -
          primeOwnCubeGatedProfile U t) *
          (∏ i : Fin 5, 1 / t i) := by
        rw [hnewProfile, holdProfile,
          max_eq_right hsM2.le, ← hlink]
        ring
      _ ≤ max 0 ((primeOwnCubeGatedProfile M t -
          primeOwnCubeGatedProfile U t) *
          (∏ i : Fin 5, 1 / t i)) := le_max_right _ _

end
end ImbalancedChen.P5OldFifthPointwiseQ
