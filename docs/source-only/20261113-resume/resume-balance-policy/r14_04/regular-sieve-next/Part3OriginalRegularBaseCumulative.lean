import ImbalancedChen.Part3OriginalRegularPacketTest
import ImbalancedChen.Part3OriginalRegularBaseProbe
import Batteries.Tactic.OpenPrivate

/-! The first cumulative interval of (4.24) and (4.25) on the original
two observations.  The two-sided continuous measure has one factor 1/(4π);
the discrete measure includes λ=1/4. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularBaseCumulative20261113
open Set Filter MeasureTheory Complex
open scoped Classical BigOperators MatrixGroups
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open ActualUnitBandSpectralMass20261112 OriginalContinuousPoincarePackets20261110
open OriginalExceptionalHeightWindow20261112 OriginalRegularPacketTest20261113
open OriginalCumulativeContinuousRemoval20261110 OriginalRegularBaseProbe20261113
open private nonnegative_sum from ImbalancedChen.Part3ActualUnitBandSpectralMass

variable (N : ℕ) [NeZero N]
local notation "Idx" => actualCuspBasisIndex N (NeZero.pos N)

def baseTerm (one neg : Bool) (K : ℝ) (S : Finset ℕ) (a : ℕ→ℂ) (i : Idx) : ℝ :=
  if ¬exceptional N i ∧ height N i≤K then
    ‖discreteRow N one neg S a i‖^2/Real.cosh (Real.pi*height N i) else 0

def lineTerm (one neg : Bool) (S : Finset ℕ) (a : ℕ→ℂ) (t : ℝ) : ℝ :=
  lineMass N one neg S a t/Real.cosh (Real.pi*t)

def baseConstant : ℝ := 32/baseFloor^2
theorem baseConstant_pos : 0<baseConstant := div_pos (by norm_num) (sq_pos_of_pos baseFloor_pos)

private theorem absorb (L : ℝ) (S : Finset ℕ) (a : ℕ→ℂ) {b : ℝ}
    (h : baseFloor^2*b≤(8+32*(L/(N:ℝ)))*energy S a) :
    b≤baseConstant*(1+L/(N:ℝ))*energy S a := by
  have ee := energy_nonneg S a
  calc
    _ ≤ ((8+32*(L/(N:ℝ)))*energy S a)/baseFloor^2 :=
      (le_div_iff₀ (sq_pos_of_pos baseFloor_pos)).mpr (by rwa [mul_comm])
    _ ≤ (32*(1+L/(N:ℝ))*energy S a)/baseFloor^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [ee]
    _ = _ := by unfold baseConstant; ring

private theorem dominated {t x : ℝ} (ht : |t|≤2) (hx : 0≤x) :
    baseFloor^2*(x/Real.cosh (Real.pi*t)) ≤ ‖orderProbe 1 (seed 1).toFun ((t:ℂ)*I)‖^2*x := by
  have pw := pow_le_pow_left₀ baseFloor_pos.le (regular_base_probe ht) 2
  have div : x/Real.cosh (Real.pi*t) ≤ x := div_le_self hx (Real.one_le_cosh _)
  exact (mul_le_mul_of_nonneg_left div (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right pw hx)

theorem base_cumulative (one neg : Bool) {L K : ℝ} (hL : 0<L) (hK : K≤2)
    (S : Finset ℕ) (a : ℕ→ℂ) (band : Dyadic L S) :
    Summable (baseTerm N one neg K S a) ∧
    (∑' i,baseTerm N one neg K S a i) ≤ baseConstant*(1+L/(N:ℝ))*energy S a ∧
    IntegrableOn (lineTerm N one neg S a) (Icc (-K) K) ∧
    (∫ t in Icc (-K) K,lineTerm N one neg S a t) ≤ baseConstant*(1+L/(N:ℝ))*energy S a := by
  obtain ⟨hd,hi,hc⟩ := packet_test N one neg (H:=1) hL (by norm_num) S a band
  simp only [mul_one] at hd hc
  let F := fun t : ℝ => ‖orderProbe 1 (seed 1).toFun ((t:ℂ)*I)‖^2*lineMass N one neg S a t
  have hn (i : Idx) : 0≤baseTerm N one neg K S a i := by unfold baseTerm; split <;> positivity
  have discrete := nonnegative_sum hn (A:=baseConstant*(1+L/(N:ℝ))*energy S a) (by
    intro J
    apply absorb N L S a
    rw [Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum ?_) (hd J)
    intro i _
    rw [baseTerm]
    split
    next h =>
      have hp : 0≤height N i := Real.sqrt_nonneg _
      have ht : |height N i|≤2 := by rw [abs_of_nonneg hp]; exact h.2.trans hK
      rw [order_regular N h.1,norm_mul,mul_pow]
      exact dominated ht (sq_nonneg _)
    next => rw [mul_zero]; positivity)
  have cont : Continuous (lineTerm N one neg S a) :=
    marked_density_cont N S a (mark neg) one
  have localI := cont.continuousOn.integrableOn_compact (isCompact_Icc (a:=-K) (b:=K))
  refine ⟨discrete.1,discrete.2,localI,absorb N L S a ?_⟩
  have hF : Integrable F := hi
  calc
    _ = ∫ t in Icc (-K) K,baseFloor^2*lineTerm N one neg S a t := (integral_const_mul _ _).symm
    _ ≤ ∫ t in Icc (-K) K,F t := integral_mono_ae (localI.const_mul _) hF.integrableOn (by
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Icc : MeasurableSet (Icc (-K) K))] with t ht
      exact dominated ((abs_le.mpr ht).trans hK) (lineMass_nonneg N one neg S a t))
    _ ≤ ∫ t,F t := setIntegral_le_integral hF (ae_of_all _ (fun t =>
      mul_nonneg (sq_nonneg _) (lineMass_nonneg N one neg S a t)))
    _ ≤ _ := hc

/-- One numerical constant, chosen before level, height, length, sign,
observing cusp and coefficients. The left sides are exactly the original
regular measures. This theorem concerns only the fixed initial interval. -/
theorem manuscript_base (ε : ℝ) (hε : 0<ε) : ∃ C : ℝ, 0<C ∧
    ∀ (z : ℕ) [NeZero z] (one neg : Bool) {K L : ℝ}, 1≤K → K≤2 → 1/2≤L →
    ∀ (S : Finset ℕ) (a : ℕ→ℂ), Dyadic L S →
      Summable (baseTerm z one neg K S a) ∧
      (∑' i,baseTerm z one neg K S a i)≤C*(K^2+L^(1+ε)/(z:ℝ))*energy S a ∧
      IntegrableOn (lineTerm z one neg S a) (Icc (-K) K) ∧
      (∫ t in Icc (-K) K,lineTerm z one neg S a t)≤C*(K^2+L^(1+ε)/(z:ℝ))*energy S a := by
  refine ⟨2*baseConstant,mul_pos (by norm_num) baseConstant_pos,?_⟩
  intro z inst one neg K L k1 k2 Lh S a band
  have LP : 0<L := by linarith
  have zp : 0<(z:ℝ) := by exact_mod_cast NeZero.pos z
  have z1 : (1:ℝ)≤z := by exact_mod_cast Nat.succ_le_of_lt (NeZero.pos z)
  have Kq : 1≤K^2 := by nlinarith only [k1,sq_nonneg (K-1)]
  have scale : 1+L/(z:ℝ)≤2*(K^2+L^(1+ε)/(z:ℝ)) := by
    by_cases u : 1≤L
    · have p := Real.self_le_rpow_of_one_le u (show 1≤1+ε by linarith)
      have j := div_le_div_of_nonneg_right p zp.le
      nlinarith only [Kq,j,div_nonneg (Real.rpow_nonneg LP.le (1+ε)) zp.le]
    · have j : L/(z:ℝ)≤1 := (div_le_one zp).mpr ((le_of_not_ge u).trans z1)
      nlinarith only [Kq,j,div_nonneg (Real.rpow_nonneg LP.le (1+ε)) zp.le]
  have pay : baseConstant*(1+L/(z:ℝ))*energy S a≤
      (2*baseConstant)*(K^2+L^(1+ε)/(z:ℝ))*energy S a := by
    apply mul_le_mul_of_nonneg_right _ (energy_nonneg S a)
    calc
      _ ≤ baseConstant*(2*(K^2+L^(1+ε)/(z:ℝ))) := mul_le_mul_of_nonneg_left scale baseConstant_pos.le
      _ = _ := by ring
  obtain ⟨summ,dis,loc,cont⟩ := base_cumulative z one neg LP k2 S a band
  exact ⟨summ,dis.trans pay,loc,cont.trans pay⟩

end ImbalancedChen.Part3.OriginalRegularBaseCumulative20261113
end
