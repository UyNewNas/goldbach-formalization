import ImbalancedChen.Part3OriginalSwitchedHolomorphicInitial

/-! Identify the two bounded positive-weight quantities with the exact
holSum sector used in the complete cutoff trace. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHolTraceError20261113
noncomputable section
open Finset Complex
open scoped BigOperators MatrixGroups ComplexConjugate
open OriginalSwitchedNativeBilinearTrace20261113
open private mark from ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace
open OriginalSwitchedSeparatedBlocks20261113 (block rowSum)
open OriginalSwitchedHolShellPrice20261113 (gamma gamma_pos native)
open OriginalSwitchedHolomorphicReturn20261113 (physical modeSlot physical_modes shell_norm reflected_absolute)
open OriginalSwitchedHolomorphicInitial20261113 (input dyadic_prices)
open OriginalSwitchedLevelIdentity20261113 (single levelWeight)
open CommonSmoothCutoff (dyadicCutoff_nonneg dyadicCutoff_le_one)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSwitchedCutoffModes20261113 (mode coefficient mode_budget)
open OriginalSwitchedModeTransforms20261113 (tested_transforms)
open OriginalSwitchedUniformHolBudget20261113 (uniform_order_budget)
open OriginalSameInfinityWeightedHol20261113 (basisTerm holSum)
open OriginalHolomorphicBasisMass20261112 (basisCost)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex)
open scoped OriginalHolomorphicPeterssonSpace20261112
open ActualPositiveHolomorphicWeights20261112 (holWeight moment)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalRegularPacketTest20261113 (energy)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open P3NativePeriod64SamplingSourceOnly (D4)
open private cost from ImbalancedChen.Part3OriginalSameInfinityPeriodTrace
open private cut_eq from ImbalancedChen.Part3OriginalSwitchedLevelIdentity

local instance (d : ℕ+) : NeZero d.val := ⟨d.property.ne'⟩

def test (s : Bool) (d : ℕ+) (Y Q : ℝ) (m n : ℕ) :=
  if s then switchedTest Y ((d.val:ℝ)*Q) m n else single Y

def component (s : Bool) (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
    star (phaseAt ω m.val*u m.val)*(phaseAt ω n.val*u n.val)*
      holSum d (mark m) (mark n) (test s d Y Q m.val n.val)

private theorem paired (s : Bool) (d m n : ℕ+) (Y Q : ℝ) (y1 : 1≤Y) (qp : 0<Q) :
    Summable (fun h : ℕ => ∑ i : BasisIndex d.val (h+1),basisTerm d m n (test s d Y Q m.val n.val) h i) := by
  let L := Y*(4*Real.pi*Real.sqrt ((m.val:ℝ)*(n.val:ℝ)))/((d.val:ℝ)*Q)
  let f := test s d Y Q m.val n.val
  have yp := zero_lt_one.trans_le y1
  have eq : (fun x => profile s L (Y*x))=f := by
    cases s
    · funext x;simp only [f,test,Bool.false_eq_true,if_false,single,profile,mul_one]
    · exact cut_eq m n d yp qp
  let c := coefficient s L
  obtain ⟨A,ap,H⟩ := mode_budget 0
  have S : Summable (fun l : ℤ => ‖c l‖) := by simpa [c] using (H s L).1
  have E : (∑' l : ℤ,‖c l‖)≤A := by simpa [c] using (H s L).2
  obtain ⟨b,sb,bp,U⟩ := uniform_order_budget
  let D := (basisCost d.val m.val 1+basisCost d.val n.val 1)/Real.pi
  have dp : 0≤D := by dsimp [D,basisCost];positivity
  apply Summable.of_norm
  apply (sb.mul_left (D*A)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  let N : ℝ := (2*h+1:ℕ)
  let W := fun l : ℤ => holWeight h (spectralTest (mode l) Y⁻¹)
  have pos : 1≤N := by exact_mod_cast (show 1≤2*h+1 by omega)
  have T : HasSum (fun l : ℤ => c l*W l) (holWeight h f) := eq ▸ (tested_transforms s L Y yp).2.2.1 h
  have paid (l : ℤ) : N*‖c l*W l‖≤‖c l‖*b h := by
    have n : N≤N^2 := by nlinarith only [mul_nonneg (by linarith only [pos] : 0≤N-1) (zero_le_one.trans pos)]
    have z := (mul_le_mul_of_nonneg_right n (norm_nonneg (W l))).trans (U l Y y1 h)
    rw [norm_mul]
    exact (show N*(‖c l‖*‖W l‖)=‖c l‖*(N*‖W l‖) by ring).le.trans
      (mul_le_mul_of_nonneg_left z (norm_nonneg _))
  have price : N*‖holWeight h f‖≤A*b h := by
    rw [←T.tsum_eq]
    apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm T.summable.norm) (zero_le_one.trans pos)).trans
    have p := (T.summable.norm.mul_left N).tsum_le_tsum paid (S.mul_right (b h))
    rw [tsum_mul_left,tsum_mul_right] at p
    exact p.trans (mul_le_mul_of_nonneg_right E (bp h))
  have nm : ‖holWeight h f‖=4*‖moment (2*h+1) f‖ := by
    simp only [holWeight,norm_mul,norm_pow,Complex.norm_I,one_pow,Complex.norm_ofNat,mul_one]
  rw [nm] at price
  have z : N*‖moment (2*h+1) f‖≤A*b h := by
    nlinarith only [price,mul_nonneg (zero_le_one.trans pos) (norm_nonneg (moment (2*h+1) f))]
  exact (norm_sum_le _ _).trans ((cost d m n f h).trans ((mul_le_mul_of_nonneg_left z dp).trans_eq (by ring)))

def ordered (s : Bool) (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (h : ℕ) (i : BasisIndex d.val (h+1)) :=
  let R := fun m => u m*native d h i m
  (gamma h:ℂ)*block j ω R R (fun m n => holWeight h (test s d Y Q m n))

theorem original_sector (s : Bool) (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (y1 : 1≤Y) (qp : 0<Q) (u : ℕ→ℂ) :
    HasSum (fun h => ∑ i : BasisIndex d.val (h+1),ordered s d j Y Q ω u h i) (component s d j Y Q ω u) := by
  let I := ↥(dyadicWindow j)
  let a (m n : I) := star (phaseAt ω m.val*u m.val)*(phaseAt ω n.val*u n.val)
  let T (m n : I) (h : ℕ) (i : BasisIndex d.val (h+1)) :=
    basisTerm d (mark m) (mark n) (test s d Y Q m.val n.val) h i
  have H (m n : I) : HasSum (fun h => a m n*(∑ i,T m n h i))
      (a m n*holSum d (mark m) (mark n) (test s d Y Q m.val n.val)) :=
    (paired s d (mark m) (mark n) Y Q y1 qp).hasSum.mul_left _
  have full := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) =>
    hasSum_sum (s:=univ) (fun n (_ : n∈(univ:Finset I)) => H m n))
  apply full.congr_fun
  intro h
  simp only [ordered,block,Finset.mul_sum]
  rw [sum_comm (s:=(univ:Finset (BasisIndex d.val (h+1)))) (t:=(univ:Finset I))]
  apply sum_congr rfl
  intro m _
  rw [sum_comm (s:=(univ:Finset (BasisIndex d.val (h+1)))) (t:=(univ:Finset I))]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro i _
  simp only [T,a,basisTerm,gamma,native,mark,star_mul',Complex.star_def,map_mul]
  ring

/-- Reverse the full complex series, with the complete native basis
at each weight. The common value is the literal marked holSum. -/
theorem full_fourier_exchange (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (y1 : 1≤Y) (qp : 0<Q) (u : ℕ→ℂ) :
    let F := fun (k : D4→ℤ) (h : ℕ) => ∑ i : BasisIndex d.val (h+1),modeSlot d j Y Q ω u k h i
    Summable (fun z : (D4→ℤ)×ℕ => ∑ i : BasisIndex d.val (z.2+1),‖modeSlot d j Y Q ω u z.1 z.2 i‖) ∧
    HasSum (fun k => ∑' h,F k h) (component true d j Y Q ω u) := by
  obtain ⟨_,_,A⟩ := reflected_absolute (by norm_num : (0:ℝ)<1)
  let F := fun (k : D4→ℤ) (h : ℕ) => ∑ i : BasisIndex d.val (h+1),modeSlot d j Y Q ω u k h i
  have price := (A d j Y Q ω y1 qp u).1
  refine ⟨by simpa only [shell_norm] using price,?_⟩
  have sf : Summable (Function.uncurry F) := price.of_norm_bounded (fun z => by
    change ‖∑ i : BasisIndex d.val (z.2+1),modeSlot d j Y Q ω u z.1 z.2 i‖≤_
    exact (norm_sum_le _ _).trans_eq (shell_norm d j Y Q ω u z.2 z.1))
  have shell (h : ℕ) : (∑' k,F k h)=∑ i : BasisIndex d.val (h+1),physical d j Y Q ω u h i :=
    (hasSum_sum (s:=univ) (fun i (_ : i∈(univ:Finset (BasisIndex d.val (h+1)))) =>
      physical_modes (zero_lt_one.trans_le y1) qp d j ω u h i)).tsum_eq
  have back : HasSum (fun h => ∑ i : BasisIndex d.val (h+1),physical d j Y Q ω u h i)
      (component true d j Y Q ω u) := original_sector true d j Y Q ω y1 qp u
  have val : (∑' k,∑' h,F k h)=component true d j Y Q ω u := calc
    _ = ∑' h,∑' k,F k h := sf.tsum_comm.symm
    _ = ∑' h,∑ i : BasisIndex d.val (h+1),physical d j Y Q ω u h i := by simp_rw [shell]
    _ = _ := back.tsum_eq
  rw [←val]
  exact sf.prod.hasSum

private theorem single_row (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) (h : ℕ) :
    (∑ i : BasisIndex d.val (h+1),‖ordered false d j Y Q ω u h i‖)=input d j Y ω u h := by
  have p (R : ℕ→ℂ) : block j ω R R (fun _ _ => holWeight h (single Y))=
      (star (rowSum j ω R)*rowSum j ω R)*holWeight h (single Y) := by
    simp only [block,rowSum,star_sum,Finset.sum_mul]
    simp only [Finset.mul_sum,Finset.sum_mul]
  unfold input
  apply sum_congr rfl
  intro i _
  simp only [ordered,test,Bool.false_eq_true,if_false,p,norm_mul,norm_star,pow_two]
  ring

/-- The actual two finite mark contractions of the full holSum in
the original trace, including the common interval and any fixed coefficient mask. -/
theorem trace_dyadic {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (j : ℕ) (Y Q B ω : ℝ),1≤Y → 0<Q → 0<B → ∀ u : ℕ→ℂ,
      (∑ d∈classicalLevels B,‖component false d j Y Q ω u‖)≤D*(B+(classicalMScale j)^(1+ε))*energy (dyadicWindow j) u ∧
      (∑ d∈classicalLevels B,‖component true d j Y Q ω u‖)≤D*(B+(classicalMScale j)^(1+ε))*energy (dyadicWindow j) u := by
  obtain ⟨D,dp,H⟩ := dyadic_prices ep
  obtain ⟨A,_,sm1⟩ := OriginalSwitchedHolomorphicInitial20261113.unreflected ep
  obtain ⟨C,_,sm2⟩ := OriginalSwitchedHolomorphicReturn20261113.reflected ep
  refine ⟨D,dp,fun j Y Q B ω y1 qp bp u => ?_⟩
  have ind (s : Bool) (d : ℕ+) :
      ‖component s d j Y Q ω u‖≤∑' h,∑ i : BasisIndex d.val (h+1),‖ordered s d j Y Q ω u h i‖ := by
    have hs := original_sector s d j Y Q ω y1 qp u
    have sb : Summable (fun h => ∑ i : BasisIndex d.val (h+1),‖ordered s d j Y Q ω u h i‖) := by
      cases s
      · simpa only [single_row] using (sm1 d j Y ω y1 u).1
      · exact (sm2 d j Y Q ω y1 qp u).1
    rw [←hs.tsum_eq]
    exact (norm_tsum_le_tsum_norm hs.summable.norm).trans
      (hs.summable.norm.tsum_le_tsum (fun h => norm_sum_le _ _) sb)
  constructor
  · apply (sum_le_sum (s:=classicalLevels B) (fun d _ => ind false d)).trans
    simpa only [single_row] using (H j Y Q B ω y1 qp bp u).1
  · exact (sum_le_sum (s:=classicalLevels B) (fun d _ => ind true d)).trans (H j Y Q B ω y1 qp bp u).2

/-- The extra smooth q cutoff on the input side of the actual
double trace is uniform before or after its four-window covering. -/
theorem weighted_input {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (j : ℕ) (Y Q B ω : ℝ),1≤Y → 0<Q → 0<B → ∀ u : ℕ→ℂ,
      (∑ d∈classicalLevels B,‖levelWeight Q d*component false d j Y Q ω u‖)≤
        D*(B+(classicalMScale j)^(1+ε))*energy (dyadicWindow j) u := by
  obtain ⟨D,dp,H⟩ := trace_dyadic ep
  refine ⟨D,dp,fun j Y Q B ω y1 qp bp u => ?_⟩
  apply (Finset.sum_le_sum (fun d _ => ?_)).trans (H j Y Q B ω y1 qp bp u).1
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simp only [levelWeight,Complex.norm_real,Real.norm_of_nonneg (dyadicCutoff_nonneg _)]
  exact dyadicCutoff_le_one _

end
end ImbalancedChen.Part3.OriginalSwitchedHolTraceError20261113
