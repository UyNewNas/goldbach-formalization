import ImbalancedChen.Part3OriginalHolomorphicInfinityPacket

/-! The complete holomorphic cumulative large sieve for the original
identity observation at arbitrary level, length and height. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicInfinityCumulative20261113
open Finset Real
open OriginalRegularPacketTest20261113 (Dyadic energy energy_nonneg)
open OriginalRegularHolomorphicWeight20261113 (order)
open OriginalRegularHolomorphicCumulative20261113 (WeightBasis shell weights mem_weights manuscript_holomorphic)
open OriginalHolomorphicOddWindow20261113 (weight floorConstant floorConstant_pos original_odd_order_floor)
open OriginalHolomorphicInfinityGram20261113 (naturalShell shell_nonnegative)
open OriginalHolomorphicInfinityWeighted20261113 (spectralTerm spectralTerm_nonnegative weighted_infinity_bound)
open OriginalHolomorphicInfinityPacket20261113 (start extension extension_energy extension_shell start_rpow)
open OriginalHolomorphicAngularOffDiagonal20261113 (cost)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)

private theorem remove_first {e : ℝ} (he : 0<e) {K : ℝ} (hK : 1≤K)
    (z M : ℕ) [NeZero z] (hM : 0<M) (a : ℕ → ℂ) (bases : ∀ j,WeightBasis z j) :
    (4*π*floorConstant)*(∑ j∈(weights K).erase 0,naturalShell z M j a (bases j)) ≤
      (4*K^2+2*cost e*((M:ℝ)^(1+e)/z))*dyadEnergy M a := by
  let t := 1/K
  let U := (weights K).erase 0
  let F := fun h => 4*π*spectralTerm z M t a bases h
  have kp := zero_lt_one.trans_le hK
  have t1 : t≤1 := (div_le_one kp).mpr hK
  obtain ⟨S,B⟩ := weighted_infinity_bound he hK z M hM a bases
  have term (j : ℕ) (hj : j∈U) :
      (4*π*floorConstant)*naturalShell z M j a (bases j)≤F (order j) := by
    have ne := (mem_erase.mp hj).1
    have cut := mem_weights.mp (mem_erase.mp hj).2
    have oh : Odd (order j) := ⟨j,by dsimp only [order]; omega⟩
    have div : order j/2=j := by dsimp only [order]; omega
    have p := original_odd_order_floor hK (by dsimp only [order]; omega : 3≤order j) cut
    dsimp only [F,spectralTerm]
    rw [if_pos oh,div,mul_assoc (4*π) floorConstant]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p (shell_nonnegative _ _ _ _ _))
      (by positivity)
  have inj : Set.InjOn order ↑U := by
    intro i _ j _ q
    dsimp only [order] at q
    omega
  calc
    _ = ∑ j∈U,(4*π*floorConstant)*naturalShell z M j a (bases j) := mul_sum _ _ _
    _ ≤ ∑ j∈U,F (order j) := sum_le_sum term
    _ = ∑ h∈U.image order,F h := (sum_image inj).symm
    _ ≤ ∑' h,F h := S.sum_le_tsum _ (fun h _ =>
      mul_nonneg (by positivity) (spectralTerm_nonnegative z M t1 a bases h))
    _ ≤ _ := B

private def highConstant (e : ℝ) : ℝ := (4+2*|cost e|*(3:ℝ)^(1+e))/(4*π*floorConstant)

private theorem highConstant_pos (e : ℝ) : 0<highConstant e := by
  have c := abs_nonneg (cost e)
  have t := floorConstant_pos
  dsimp [highConstant]
  positivity

private theorem native_high {e K L : ℝ} (he : 0<e) (hK : 1≤K) (hL : 1/2≤L)
    (z : ℕ) [NeZero z] (S : Finset ℕ) (a : ℕ → ℂ) (band : Dyadic L S)
    (bases : ∀ j,WeightBasis z j) :
    (∑ j∈(weights K).erase 0,shell z j false S a (bases j)) ≤
      highConstant e*(K^2+L^(1+e)/(z:ℝ))*energy S a := by
  let M := start L
  have mp : 0<M := by dsimp only [M,start]; omega
  have q := remove_first he hK z M mp (extension S a) bases
  simp only [M,extension_energy hL S band,extension_shell z _ hL S band] at q
  let A := (3:ℝ)^(1+e)
  let x := L^(1+e)/(z:ℝ)
  have lp : 0≤L := by linarith
  have xn : 0≤x := div_nonneg (rpow_nonneg lp _) (Nat.cast_nonneg _)
  have a0 : 0≤A := rpow_nonneg (by norm_num) _
  have bound : (start L:ℝ)^(1+e)/(z:ℝ)≤A*x := by
    have h := div_le_div_of_nonneg_right (start_rpow he hL) (Nat.cast_nonneg z)
    simpa only [A,x,mul_div_assoc] using h
  have left := mul_le_mul_of_nonneg_right
    (show 2*cost e≤2*|cost e| from mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
    (show 0≤(start L:ℝ)^(1+e)/(z:ℝ) from
      div_nonneg (rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  have right := mul_le_mul_of_nonneg_left bound (show 0≤2*|cost e| by positivity)
  have bill : 4*K^2+2*cost e*((start L:ℝ)^(1+e)/z)≤(4+2*|cost e|*A)*(K^2+x) := by
    nlinarith only [left.trans right,mul_nonneg (mul_nonneg (by positivity : 0≤2*|cost e|) a0) (sq_nonneg K),xn]
  have p := q.trans (mul_le_mul_of_nonneg_right bill (energy_nonneg S a))
  have den : 0<4*π*floorConstant := mul_pos (mul_pos (by norm_num) pi_pos) floorConstant_pos
  apply (mul_le_mul_iff_right₀ den).mp
  convert p using 1 <;> dsimp only [highConstant,A,x] <;> field_simp [den.ne',pi_ne_zero,floorConstant_pos.ne'] <;> ring

/-- Original gamma-weighted Fourier coefficients, any complete Petersson
basis at every weight, and one constant before every parameter. -/
theorem manuscript_holomorphic_infinity (e : ℝ) (he : 0<e) :
    ∃ C : ℝ,0<C ∧ ∀ (z : ℕ) [NeZero z] {K L : ℝ},1≤K → 1/2≤L →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ),Dyadic L S → ∀ (bases : ∀ j,WeightBasis z j),
        (∑ j∈weights K,shell z j false S a (bases j))≤
          C*(K^2+L^(1+e)/(z:ℝ))*energy S a := by
  obtain ⟨D,dpos,base⟩ := manuscript_holomorphic e he
  refine ⟨highConstant e+D,add_pos (highConstant_pos e) dpos,?_⟩
  intro z _ K L hK hL S a band bases
  have zmem : 0∈weights K := mem_weights.mpr (by simpa only [order,Nat.mul_zero,Nat.zero_add,Nat.cast_one] using hK)
  have baseSet : weights 1={0} := by
    ext j
    rw [mem_weights,mem_singleton]
    have hj : (order j:ℝ)≤1 ↔ order j≤1 := by exact_mod_cast Iff.rfl
    rw [hj]
    dsimp only [order]
    omega
  have low := base z false (K:=1) (by norm_num) hL (Or.inr (Or.inr (by norm_num))) S a band bases
  rw [baseSet,sum_singleton] at low
  have kk : (1:ℝ)^2≤K^2 := pow_le_pow_left₀ zero_le_one hK 2
  have lift := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add kk (le_refl (L^(1+e)/(z:ℝ)))) dpos.le)
    (energy_nonneg S a)
  have high := native_high he hK hL z S a band bases
  rw [←sum_erase_add _ _ zmem]
  convert add_le_add high (low.trans lift) using 1 <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicInfinityCumulative20261113
end
