import ImbalancedChen.Part3OriginalSwitchedHolomorphicReturn
import ImbalancedChen.Part3OriginalExceptionalJInitialAverage

/-! The positive-weight error on the first trace and the finite-level
price on either side of the level exchange. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHolomorphicInitial20261113
noncomputable section
open Finset Complex
open scoped BigOperators
open OriginalRegularPacketTest20261113 (energy energy_nonneg)
open OriginalSwitchedUniformHolBudget20261113 (uniform_order_budget)
open OriginalSwitchedHolShellPrice20261113 (mixed gamma gamma_pos native mixed_price)
open OriginalSwitchedHolomorphicReturn20261113 (physical reflected)
open OriginalSwitchedSeparatedBlocks20261113 (rowSum)
open OriginalSwitchedSeparatedNativeSlots20261113 (legs)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalSwitchedCutoffModes20261113 (mode mode_budget coefficient)
open OriginalSwitchedModeTransforms20261113 (tested_transforms)
open OriginalSwitchedLevelIdentity20261113 (single)
open ActualPositiveHolomorphicWeights20261112 (holWeight)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels mem_classicalLevels)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private card_levels from ImbalancedChen.Part3OriginalExceptionalJInitialAverage

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def input (d : ℕ+) (j : ℕ) (Y ω : ℝ) (u : ℕ→ℂ) (h : ℕ) :=
  ∑ i : BasisIndex d.val (h+1),‖(gamma h:ℂ)*holWeight h (single Y)‖*
    ‖rowSum j ω (fun m => u m*native d h i m)‖^2

private theorem single_price :
    ∃ b : ℕ→ℝ,Summable b ∧ (∀ h,0≤b h) ∧ ∀ Y : ℝ,1≤Y → ∀ h : ℕ,
      ((2*h+1:ℕ):ℝ)^2*‖holWeight h (single Y)‖≤b h := by
  obtain ⟨B,S,nb,R⟩ := uniform_order_budget
  obtain ⟨A,ap,H⟩ := mode_budget 0
  let c := coefficient false 0
  have s : Summable (fun l : ℤ => ‖c l‖) := by simpa [c] using (H false 0).1
  have cap : (∑' l : ℤ,‖c l‖)≤A := by simpa [c] using (H false 0).2
  refine ⟨fun h => A*B h,S.mul_left A,fun h => mul_nonneg ap.le (nb h),?_⟩
  intro Y y1 h
  let T := ((2*h+1:ℕ):ℝ)^2
  let W := fun l : ℤ => holWeight h (spectralTest (mode l) Y⁻¹)
  have raw := (tested_transforms false 0 Y (zero_lt_one.trans_le y1)).2.2.1 h
  have hs : HasSum (fun l : ℤ => c l*W l) (holWeight h (single Y)) := by
    simpa only [OriginalSwitchedCutoffFamily20261113.profile,Bool.false_eq_true,if_false,mul_one,c,W,single] using raw
  have tp : 0≤T := sq_nonneg _
  have point (l : ℤ) : T*‖c l*W l‖≤‖c l‖*B h := by
    have E := mul_le_mul_of_nonneg_left (R l Y y1 h) (norm_nonneg (c l))
    rw [norm_mul];dsimp only [T,W];nlinarith only [E]
  rw [←hs.tsum_eq]
  apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs.summable.norm) tp).trans
  have p := (hs.summable.norm.mul_left T).tsum_le_tsum point (s.mul_right (B h))
  rw [tsum_mul_left,tsum_mul_right] at p
  exact p.trans (mul_le_mul_of_nonneg_right cap (nb h))

theorem unreflected {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (d : ℕ+) (j : ℕ) (Y ω : ℝ),1≤Y → ∀ u : ℕ→ℂ,
      Summable (input d j Y ω u) ∧ (∑' h,input d j Y ω u h)≤
        D*(1+(classicalMScale j)^(1+ε)/(d.val:ℝ))*energy (dyadicWindow j) u := by
  obtain ⟨b,S,nb,B⟩ := single_price
  obtain ⟨C,cp,U⟩ := mixed_price ep
  let D := (∑' h,b h)*C
  refine ⟨D,mul_nonneg (tsum_nonneg nb) cp.le,fun d j Y ω y1 u => ?_⟩
  let A := (classicalMScale j)^(1+ε)/(d.val:ℝ)
  let E := energy (dyadicWindow j) u
  have ap : 0≤A := div_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤1/2).trans (classicalMScale_bounds j).1) _)
    (Nat.cast_nonneg _)
  have pp : 0≤C*(1+A)*E := mul_nonneg (mul_nonneg cp.le (by linarith only [ap])) (energy_nonneg _ _)
  have p (h : ℕ) : input d j Y ω u h≤b h*(C*(1+A)*E) := by
    let H : ℝ := (2*h+1:ℕ)
    let W := ‖holWeight h (single Y)‖
    have id : input d j Y ω u h=W*mixed d j h ω 0 u := by
      simp only [input,mixed,W,legs,Pi.zero_apply,Int.cast_zero,zero_div,sub_zero,add_zero,
        norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (gamma_pos h).le,Finset.mul_sum,pow_two]
      apply sum_congr rfl
      intro i _
      ring
    have h1 : 1≤H := by exact_mod_cast (show 1≤2*h+1 by omega)
    have q : H^2+A≤H^2*(1+A) := by
      have one : (1:ℝ)≤H^2 := one_le_pow₀ h1
      nlinarith only [mul_nonneg (sub_nonneg.mpr one) ap]
    have m : mixed d j h ω 0 u≤H^2*(C*(1+A)*E) :=
      (U d j h ω 0 u).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left q cp.le)
        (energy_nonneg _ _)).trans_eq (by dsimp only [A,E,H];ring))
    rw [id]
    calc
      W*mixed d j h ω 0 u ≤ W*(H^2*(C*(1+A)*E)) := mul_le_mul_of_nonneg_left m (norm_nonneg _)
      _ = (H^2*W)*(C*(1+A)*E) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (B Y y1 h) pp
  have sm := (S.mul_right (C*(1+A)*E)).of_nonneg_of_le
    (fun h => show 0≤input d j Y ω u h from sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) p
  refine ⟨sm,(sm.tsum_le_tsum p (S.mul_right (C*(1+A)*E))).trans ?_⟩
  rw [tsum_mul_right]
  dsimp only [D,A,E];ring_nf

private theorem sum_levels {B M D ε : ℝ} (bp : 0<B) (mp : 0≤M) (dp : 0≤D)
    {f : ℕ+→ℝ} (H : ∀ d,f d≤D*(1+M^(1+ε)/(d.val:ℝ))) :
    (∑ d∈classicalLevels B,f d)≤2*D*(B+M^(1+ε)) := by
  let A := M^(1+ε)
  have nn : 0≤A := Real.rpow_nonneg mp _
  have w := sum_le_sum (s:=classicalLevels B) (fun d hd =>
    (H d).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_left nn bp ((mem_classicalLevels B d).mp hd).1.le)) dp))
  simp only [sum_const,nsmul_eq_mul] at w
  apply w.trans
  apply (mul_le_mul_of_nonneg_right (card_levels bp) (mul_nonneg dp (by positivity : 0≤1+A/B))).trans
  dsimp only [A]
  apply le_of_eq
  field_simp [bp.ne'] <;> ring

theorem dyadic_prices {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (j : ℕ) (Y Q B ω : ℝ),1≤Y → 0<Q → 0<B → ∀ u : ℕ→ℂ,
      (∑ d∈classicalLevels B,∑' h,input d j Y ω u h)≤D*(B+(classicalMScale j)^(1+ε))*energy (dyadicWindow j) u ∧
      (∑ d∈classicalLevels B,∑' h,∑ i,‖physical d j Y Q ω u h i‖)≤
        D*(B+(classicalMScale j)^(1+ε))*energy (dyadicWindow j) u := by
  obtain ⟨A,ap,p⟩ := unreflected ep
  obtain ⟨C,cp,q⟩ := reflected ep
  let D := max A C
  refine ⟨2*D,mul_nonneg (by norm_num) (ap.trans (le_max_left _ _)),fun j Y Q B ω y1 qp bp u => ?_⟩
  let M := classicalMScale j
  let E := energy (dyadicWindow j) u
  have mp : 0≤M := (by norm_num : (0:ℝ)≤1/2).trans (classicalMScale_bounds j).1
  have e := energy_nonneg (dyadicWindow j) u
  have dp : 0≤D := ap.trans (le_max_left _ _)
  have com (d : ℕ+) (K : ℝ) (k : K≤D) :
      K*(1+M^(1+ε)/(d.val:ℝ))*E≤(D*E)*(1+M^(1+ε)/(d.val:ℝ)) := by
    have nn : 0≤1+M^(1+ε)/(d.val:ℝ) := add_nonneg zero_le_one (div_nonneg (Real.rpow_nonneg mp _) (Nat.cast_nonneg _))
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k nn) e).trans_eq (by ring)
  constructor
  · apply (sum_levels bp mp (mul_nonneg dp e) (ε:=ε) (fun d => (p d j Y ω y1 u).2.trans (com d A (le_max_left _ _)))).trans_eq
    dsimp only [M,E];ring
  · apply (sum_levels bp mp (mul_nonneg dp e) (ε:=ε) (fun d => (q d j Y Q ω y1 qp u).2.trans (com d C (le_max_right _ _)))).trans_eq
    dsimp only [M,E];ring

end
end ImbalancedChen.Part3.OriginalSwitchedHolomorphicInitial20261113
