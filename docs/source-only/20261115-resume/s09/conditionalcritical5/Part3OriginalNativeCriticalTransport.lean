import ImbalancedChen.Part3OriginalNativeCriticalPrices
import ImbalancedChen.Part3OriginalSwitchedReturnedWindow

/-! Critical transport on the original positive marks. Its premise only
concerns actual Fourier coordinates at infinity and exceptional orders
above one half. No mean-value or level recurrence is supplied as input. -/
namespace ImbalancedChen.Part3.OriginalNativeCriticalTransport20261113
noncomputable section
open Finset Complex
open scoped Classical BigOperators MatrixGroups
open ActualCuspBasisWhittakerCoefficients20261102 (basisRhoK)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedMellinRows20261113 (twistedRow nativeRow)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels)
open OriginalNativeCriticalPrices20261113 (height benchmark normPrice)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def positiveHalfSupport : Prop := ∀ (q m : ℕ+) (i : ↥(exceptional q)),1/2<tau q i.val →
  basisRhoK q.val q.property i.val 1 (m.val:ℤ)=0

theorem transport (coeff : positiveHalfSupport) (S : Finset ℕ+) {X Z : ℝ} (zp : 0<Z) (zx : Z≤X)
    (ω : ℝ) {a : ℕ} (ap : 0<a) (b : ℕ) :
    intervalEnergy S X ω a b 0≤Real.sqrt (X/Z)*intervalEnergy S Z ω a b 0 := by
  have one : 1≤X/Z := (le_div_iff₀ zp).mpr (by simpa only [one_mul] using zx)
  have xp := zp.trans_le zx
  simp only [intervalEnergy,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro i _
  by_cases elim : 1/2<tau q i.val
  · have row : twistedRow (Ico a b) (nativeRow q i.val ω) 0=0 := by
      apply sum_eq_zero
      intro m hm
      have mp := ap.trans_le (mem_Ico.mp hm).1
      simp only [nativeRow,coeff q ⟨m,mp⟩ i elim,mul_zero,zero_mul]
    simp only [row,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
  have sep : X^(tau q i.val)=(X/Z)^(tau q i.val)*Z^(tau q i.val) := by
    rw [←Real.mul_rpow (div_nonneg xp.le zp.le) zp.le,div_mul_cancel₀ _ zp.ne']
  have h := Real.rpow_le_rpow_of_exponent_le one (le_of_not_gt elim)
  rw [←Real.sqrt_eq_rpow] at h
  rw [sep,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg zp.le _)) (sq_nonneg _)

theorem prefix_child (coeff : positiveHalfSupport) (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b)
    {B Y : ℝ} (bl : height (classicalMScale j)≤B) (yb : B^2/classicalMScale j≤Y)
    (ω : ℝ) {p ε : ℝ}
    (ih : ∀ u, a≤u → u≤b → intervalEnergy (classicalLevels B)
      (benchmark (classicalMScale j) B) ω a u 0≤p*normPrice (classicalMScale j) B ε) :
    prefixMax (classicalLevels B) Y ω a b ab≤
      Real.sqrt (Y/(B^2/classicalMScale j))*(p*normPrice (classicalMScale j) B ε) := by
  let M := classicalMScale j
  let H := height M
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have h1 : 1≤H := le_max_left _ _
  have mh : M≤H := le_max_right _ _
  have bp := zero_lt_one.trans_le (h1.trans bl)
  have wp : 0<B^2/M := div_pos (sq_pos_of_pos bp) mp
  have hb : H≤B^2/M := (le_div_iff₀ mp).mpr (by
    have hu := mul_le_mul bl (mh.trans bl) mp.le bp.le
    nlinarith only [hu])
  have form : benchmark M B=B^2/M := max_eq_right hb
  have ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  apply Finset.sup'_le
  intro n hn
  let u := min b (n+1)
  have bound := ih u (le_min ab (by have k := (Finset.mem_Icc.mp hn).1;omega)) (min_le_left _ _)
  rw [form] at bound
  exact (transport coeff (classicalLevels B) wp yb ω ap u).trans
    (mul_le_mul_of_nonneg_left bound (Real.sqrt_nonneg _))

end
end ImbalancedChen.Part3.OriginalNativeCriticalTransport20261113

