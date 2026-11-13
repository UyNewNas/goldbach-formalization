import ImbalancedChen.Part3OriginalSwitchedHolShellPrice

/-! Sum the reflected odd-order transform through both native marked
linear forms, all period modes and every positive Petersson slot. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHolomorphicReturn20261113
noncomputable section
open Finset Complex
open scoped BigOperators MatrixGroups
open OriginalSwitchedUniformHolBudget20261113 (uniform_order_budget)
open OriginalSwitchedHolShellPrice20261113 (mixed gamma gamma_pos native mixed_price multiplier_price)
open OriginalSwitchedFourCoordinateSymbol20261113 (coefficient lattice_budget)
open OriginalSwitchedFourCoordinateRows20261113 (ratio)
open OriginalSwitchedSeparatedBlocks20261113 (block multiplier holomorphic_block)
open OriginalSwitchedSeparatedNativeSlots20261113 (legs)
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex)
open scoped OriginalHolomorphicPeterssonSpace20261112
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open OriginalRegularPacketTest20261113 (energy energy_nonneg)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private rectangle from ImbalancedChen.Part3OriginalSwitchedMaassExchange

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def absolute (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (k : D4→ℤ) (h : ℕ) :=
  ‖multiplier k (ratio (j:=j) Y Q d)‖*‖holWeight h (spectralTest (mode (k 0)) Y⁻¹)‖*mixed d j h ω k u

def physical (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (h : ℕ) (i : BasisIndex d.val (h+1)) :=
  let R := fun m : ℕ => u m*native d h i m
  (gamma h:ℂ)*block j ω R R (fun m n => holWeight h (switchedTest Y ((d.val:ℝ)*Q) m n))

def modeSlot (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ)
    (k : D4→ℤ) (h : ℕ) (i : BasisIndex d.val (h+1)) :=
  let R := fun m => u m*native d h i m
  multiplier k (ratio (j:=j) Y Q d)*((gamma h:ℂ)*holWeight h (spectralTest (mode (k 0)) Y⁻¹))*legs j ω k R

theorem physical_modes {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (j : ℕ) (ω : ℝ)
    (u : ℕ→ℂ) (h : ℕ) (i : BasisIndex d.val (h+1)) :
    HasSum (fun k => modeSlot d j Y Q ω u k h i) (physical d j Y Q ω u h i) := by
  let R := fun m => u m*native d h i m
  exact ((holomorphic_block j ω yp qp d h R R).mul_left (gamma h:ℂ)).congr_fun
    (fun k => by dsimp only [modeSlot,legs,R];ring)

theorem shell_norm (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (h : ℕ) (k : D4→ℤ) :
    (∑ i : BasisIndex d.val (h+1),‖modeSlot d j Y Q ω u k h i‖)=absolute d j Y Q ω u k h := by
  simp only [modeSlot,absolute,mixed,norm_mul,Complex.norm_real,Real.norm_of_nonneg (gamma_pos h).le,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  ring

private theorem all_slots {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (j : ℕ) (ω : ℝ)
    (u : ℕ→ℂ) (h : ℕ) :
    (∑ i : BasisIndex d.val (h+1),‖physical d j Y Q ω u h i‖)≤∑' k,absolute d j Y Q ω u k h := by
  have hs := physical_modes yp qp d j ω u h
  have bars := hasSum_sum (s:=univ) (fun i (_ : i∈(univ:Finset (BasisIndex d.val (h+1)))) =>
    (hs i).summable.norm.hasSum)
  simp_rw [shell_norm] at bars
  rw [bars.tsum_eq]
  apply sum_le_sum
  intro i _
  rw [←(hs i).tsum_eq]
  exact norm_tsum_le_tsum_norm (hs i).summable.norm

/-- The complete absolute physical Petersson return, not just the cost
of a single transform. u can in particular be any subinterval mask. -/
theorem reflected_absolute {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (d : ℕ+) (j : ℕ) (Y Q ω : ℝ),1≤Y → 0<Q → ∀ u : ℕ→ℂ,
      let p := fun h : ℕ => ∑ i : BasisIndex d.val (h+1),‖physical d j Y Q ω u h i‖
      Summable (fun z : (D4→ℤ)×ℕ => absolute d j Y Q ω u z.1 z.2) ∧
      Summable p ∧ (∑' h,p h)≤D*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u := by
  obtain ⟨b,sb,bp,B⟩ := uniform_order_budget
  obtain ⟨C,cp,U⟩ := mixed_price ep
  obtain ⟨A,ap,S,E⟩ := lattice_budget 0
  have S0 : Summable (fun k : D4→ℤ => ‖coefficient k‖) := by simpa using S
  have E0 : (∑' k : D4→ℤ,‖coefficient k‖)≤A := by simpa using E
  let D := A*(∑' h,b h)*C
  have sum_nn := tsum_nonneg bp
  refine ⟨D,mul_nonneg (mul_nonneg ap.le sum_nn) cp.le,fun d j Y Q ω y1 qp u => ?_⟩
  let a := fun k : D4→ℤ => ‖coefficient k‖
  let marks := dyadicWindow j
  let M := classicalMScale j
  let T := M^(1+ε)/(d.val:ℝ)
  let V := C*(1+T)*energy marks u
  let p := fun h : ℕ => ∑ i : BasisIndex d.val (h+1),‖physical d j Y Q ω u h i‖
  have Tp : 0≤T := div_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤1/2).trans (classicalMScale_bounds j).1) _)
    (Nat.cast_nonneg _)
  have Vp : 0≤V := mul_nonneg (mul_nonneg cp.le (by linarith only [Tp])) (energy_nonneg _ _)
  have bound (h : ℕ) (k : D4→ℤ) : absolute d j Y Q ω u k h≤a k*(b h*V) := by
    let H : ℝ := (2*h+1:ℕ)
    let W := ‖holWeight h (spectralTest (mode (k 0)) Y⁻¹)‖
    have h1 : 1≤H := by exact_mod_cast (show 1≤2*h+1 by omega)
    have quad : H^2+T≤H^2*(1+T) := by
      have one : (1:ℝ)≤H^2 := one_le_pow₀ h1
      nlinarith only [mul_nonneg (sub_nonneg.mpr one) Tp]
    have source := U d j h ω k u
    have scaled : mixed d j h ω k u≤H^2*V :=
      source.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left quad cp.le) (energy_nonneg _ _)).trans_eq (by
        dsimp only [V];ring))
    have w : W*mixed d j h ω k u≤b h*V := by
      apply (mul_le_mul_of_nonneg_left scaled (norm_nonneg _)).trans
      rw [show W*(H^2*V)=(H^2*W)*V by ring]
      exact mul_le_mul_of_nonneg_right (B (k 0) Y y1 h) Vp
    have mp : 0≤mixed d j h ω k u := sum_nonneg (fun _ _ => mul_nonneg (gamma_pos h).le (norm_nonneg _))
    change ‖multiplier k _‖*W*mixed d j h ω k u≤_
    rw [mul_assoc]
    exact mul_le_mul (multiplier_price k _) w (mul_nonneg (norm_nonneg _) mp) (norm_nonneg _)
  have hp (h : ℕ) : p h≤(∑' k,a k)*(b h*V) := by
    let q := fun k : D4→ℤ => absolute d j Y Q ω u k h
    have nn (k : D4→ℤ) : 0≤q k := mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (sum_nonneg (fun _ _ => mul_nonneg (gamma_pos h).le (norm_nonneg _)))
    have s := (S0.mul_right (b h*V)).of_nonneg_of_le nn (bound h)
    exact (all_slots (zero_lt_one.trans_le y1) qp d j ω u h).trans
      ((s.tsum_le_tsum (bound h) (S0.mul_right (b h*V))).trans_eq (by rw [tsum_mul_right]))
  have major := (sb.mul_right V).mul_left (∑' k,a k)
  have sp := major.of_nonneg_of_le (fun h => show 0≤p h from sum_nonneg fun _ _ => norm_nonneg _) hp
  have prod := rectangle S0 (sb.mul_right V) (fun k => norm_nonneg (coefficient k)) (fun h => mul_nonneg (bp h) Vp)
  have sa : Summable (fun z : (D4→ℤ)×ℕ => absolute d j Y Q ω u z.1 z.2) :=
    prod.of_nonneg_of_le (fun z => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (sum_nonneg (fun _ _ => mul_nonneg (gamma_pos z.2).le (norm_nonneg _)))) (fun z => bound z.2 z.1)
  refine ⟨sa,sp,(sp.tsum_le_tsum hp major).trans ?_⟩
  rw [tsum_mul_left,tsum_mul_right]
  exact (mul_le_mul_of_nonneg_right E0 (mul_nonneg sum_nn Vp)).trans_eq (by dsimp only [D,V,T,M,marks];ring)

theorem reflected {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (d : ℕ+) (j : ℕ) (Y Q ω : ℝ),1≤Y → 0<Q → ∀ u : ℕ→ℂ,
      let p := fun h : ℕ => ∑ i : BasisIndex d.val (h+1),‖physical d j Y Q ω u h i‖
      Summable p ∧ (∑' h,p h)≤D*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u := by
  obtain ⟨D,dp,H⟩ := reflected_absolute ep
  exact ⟨D,dp,fun d j Y Q ω y1 qp u => (H d j Y Q ω y1 qp u).2⟩

end
end ImbalancedChen.Part3.OriginalSwitchedHolomorphicReturn20261113
