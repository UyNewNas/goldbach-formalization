import ImbalancedChen.Part3OriginalInverseShortSums
import ImbalancedChen.Part3ActualInfinityKloostermanSeed
import ImbalancedChen.Part3SmallHeightReducedMatrixBounds
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-! Lift the two *oppositely shifted* residues of the inverse short-sum mean
to a single integral determinant-one matrix. Physical entry estimates hold
before either point is reduced into the modular fundamental domain. -/
namespace ImbalancedChen.Part3.OriginalInversePairMatrix20261113
noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane
open ActualInfinityKloostermanSeed20261025a OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.CoprimeCRTSourceOnly
open SmallHeightReducedMatrixBounds20261026b Gamma0ActualHighCuspTail20261025a
open ModularFundamentalFiniteMeasure20261024z Gamma0GeneralCuspUnitPeriod20261025a

local instance (k : ℕ+) : NeZero k.val := ⟨k.property.ne'⟩

private def residue (k : ℕ+) (u : ℕ) (hu : Nat.Coprime u k.val) : UnitResidue k.val :=
  ⟨(u : ZMod k.val),(ZMod.isUnit_iff_coprime u k.val).mpr hu⟩

/-- The lower-right entry carries u/k+ω and the upper-left carries
u⁻¹/k−ω; the independent integers choose representatives of the circles. -/
def lift (k : ℕ+) (u : ℕ) (hu : Nat.Coprime u k.val) (l r : ℤ) : SL(2,ℤ) :=
  ModularGroup.T^(-l) * canonicalMatrix k.val (residue k u hu) * ModularGroup.T^(-r)

theorem lift_entries (k : ℕ+) (u : ℕ) (hk : u<k.val) (hu : Nat.Coprime u k.val) (l r : ℤ) :
    lift k u hu l r 0 0 = inverseResidue k.val u - l*k.val ∧
      lift k u hu l r 1 0 = (k.val:ℤ) ∧ lift k u hu l r 1 1 = (u:ℤ) - k.val*r := by
  simp [lift,canonicalMatrix,residue,upperRepresentative,lowerRepresentative,inverseResidue,
    coe_mul,ModularGroup.coe_T_zpow,Matrix.mul_fin_two,ZMod.val_natCast_of_lt hk] <;> ring

/-- Positive c is recoverable before reading the residue off d modulo c.
The nearest-integer choices need no tie-breaking for this injection. -/
theorem recover_pair {k k' : ℕ+} {u v : ℕ} (hk : u<k.val) (hk' : v<k'.val)
    (hu : Nat.Coprime u k.val) (hv : Nat.Coprime v k'.val) (l r l' r' : ℤ)
    (h : lift k u hu l r = lift k' v hv l' r') : k=k' ∧ u=v := by
  obtain ⟨_,hc,hd⟩ := lift_entries k u hk hu l r
  obtain ⟨_,hc',hd'⟩ := lift_entries k' v hk' hv l' r'
  have eqk : k = k' := by
    apply Subtype.ext
    exact_mod_cast hc.symm.trans ((congrArg (fun g : SL(2,ℤ) => g 1 0) h).trans hc')
  subst k'
  have e := hd.symm.trans ((congrArg (fun g : SL(2,ℤ) => g 1 1) h).trans hd')
  have ez := congrArg (fun t : ℤ => (t : ZMod k.val)) e
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,sub_zero] at ez
  exact ⟨rfl,by simpa only [ZMod.val_natCast_of_lt hk,ZMod.val_natCast_of_lt hk'] using
    congrArg ZMod.val ez⟩

/-- Numerators of the upper-right entry after centering the two real
coordinates. This identity is the determinant saving in the count. -/
private theorem centered_entry (g : SL(2,ℤ)) {k : ℝ} (hk : 0<k) (hc : (g 1 0:ℝ)=k)
    (x : ℝ) :
    ((g 0 0:ℝ)*x+(g 0 1:ℝ)-x*(k*x+(g 1 1:ℝ))) =
      k*((g 0 0:ℝ)/k-x)*((g 1 1:ℝ)/k+x)-1/k := by
  have hdet : (g 0 0:ℝ)*(g 1 1:ℝ)-(g 0 1:ℝ)*k=1 := by
    rw [← hc]
    exact_mod_cast (show g 0 0*g 1 1-g 0 1*g 1 0=1 by simpa only [Matrix.det_fin_two] using g.det_coe)
  have hb : (g 0 1:ℝ)=((g 0 0:ℝ)*(g 1 1:ℝ)-1)/k := by
    apply (eq_div_iff hk.ne').mpr
    linarith
  rw [hb]
  field_simp [hk.ne'] <;> ring

/-- Bounds for the four entries of the centering of g. The horizontal
translations, heights and determinant-one correction are all retained.
The first, second and fourth bounds are the numerators of the usual
normalized SL(2,ℝ) entries. -/
theorem lifted_rectangle (k : ℕ+) {u : ℕ} (hk : u<k.val) (hu : Nat.Coprime u k.val)
    (ω : ℝ) (l r : ℤ) {α β : ℝ}
    (ha : |(inverseResidue k.val u:ℝ)/(k.val:ℝ)-ω-(l:ℝ)|≤α)
    (hb : |(u:ℝ)/(k.val:ℝ)+ω-(r:ℝ)|≤β) :
    let g := lift k u hu l r
    g 1 0=(k.val:ℤ) ∧ |(g 0 0:ℝ)-ω*(k.val:ℝ)|≤(k.val:ℝ)*α ∧
      |(k.val:ℝ)*ω+(g 1 1:ℝ)|≤(k.val:ℝ)*β ∧
      |(g 0 0:ℝ)*ω+(g 0 1:ℝ)-ω*((k.val:ℝ)*ω+(g 1 1:ℝ))| ≤ (k.val:ℝ)*α*β+1/(k.val:ℝ) := by
  let g := lift k u hu l r
  have hp : (0:ℝ)<k.val := by exact_mod_cast k.property
  obtain ⟨A,C,D⟩ := lift_entries k u hk hu l r
  have a : |(g 0 0:ℝ)/(k.val:ℝ)-ω|≤α := by
    change |((lift k u hu l r 0 0 : ℤ):ℝ)/(k.val:ℝ)-ω|≤α
    rw [A,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    convert ha using 2 <;> field_simp [hp.ne'] <;> ring
  have d : |(g 1 1:ℝ)/(k.val:ℝ)+ω|≤β := by
    change |((lift k u hu l r 1 1 : ℤ):ℝ)/(k.val:ℝ)+ω|≤β
    rw [D,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    convert hb using 2 <;> field_simp [hp.ne'] <;> ring
  have A' : (g 0 0:ℝ)-ω*(k.val:ℝ)=(k.val:ℝ)*((g 0 0:ℝ)/(k.val:ℝ)-ω) := by field_simp [hp.ne'] <;> ring
  have D' : (k.val:ℝ)*ω+(g 1 1:ℝ)=(k.val:ℝ)*((g 1 1:ℝ)/(k.val:ℝ)+ω) := by field_simp [hp.ne'] <;> ring
  refine ⟨C,?_,?_,?_⟩
  · rw [A',abs_mul,abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left a hp.le
  · rw [D',abs_mul,abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left d hp.le
  · rw [centered_entry g hp (by exact_mod_cast C)]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul,abs_of_pos hp,abs_of_pos (one_div_pos.mpr hp)]
    gcongr

/-- For every small positive height the actual reduced point has height
between 1/2 and its reciprocal. This bound includes the parabolic case. -/
theorem reduced_height_cap (z : ℍ) (hz : z.im≤1) :
    ∃ h : SL(2,ℤ), h • z ∈ ModularGroup.fd ∧ 1/2 < (h • z).im ∧ (h • z).im ≤ 1/z.im := by
  obtain ⟨h,hr⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨h,hr,modularFD_half_lt_im hr,(le_div_iff₀ z.im_pos).mpr ?_⟩
  by_cases h0 : h 1 0=0
  · have hright := zero_lowerLeft_abs_lowerRight h h0
    have hsq : (h 1 1:ℝ)^2=1 := by nlinarith [sq_abs (h 1 1:ℝ)]
    have e := integral_image_height_denominator h z
    simp only [h0,Int.cast_zero,zero_mul,zero_pow (by decide : 2≠0),zero_add,hsq,mul_one] at e
    rw [e]
    exact (mul_le_mul hz hz z.im_pos.le zero_le_one).trans_eq (one_mul 1)
  · exact im_smul_mul_im_le_one h h0 z

/-- Independent reductions of the two points preserve exactly the metric
used for counting. The transformation on the lifted residue matrices is
injective because both reduction factors are fixed for the whole rectangle. -/
theorem reduce_both (z w : ℍ) (hz : z.im≤1) (hw : w.im≤1) :
    ∃ h₁ h₂ : SL(2,ℤ), h₁ • z ∈ ModularGroup.fd ∧ h₂ • w ∈ ModularGroup.fd ∧
      (h₁ • z).im ≤ 1/z.im ∧ (h₂ • w).im ≤ 1/w.im ∧
      Function.Injective (fun g : SL(2,ℤ) => h₂*g*h₁⁻¹) ∧
      ∀ g : SL(2,ℤ), dist ((h₂*g*h₁⁻¹) • (h₁ • z)) (h₂ • w) = dist (g • z) w := by
  obtain ⟨h₁,H₁,_,A⟩ := reduced_height_cap z hz
  obtain ⟨h₂,H₂,_,B⟩ := reduced_height_cap w hw
  refine ⟨h₁,h₂,H₁,H₂,A,B,fun g g' he => mul_left_cancel (mul_right_cancel he),fun g => ?_⟩
  simp only [mul_smul,inv_smul_smul]
  rw [← integralReal_smul h₂ (g • z),← integralReal_smul h₂ w]
  exact dist_smul_left _ _ _

end
end ImbalancedChen.Part3.OriginalInversePairMatrix20261113
