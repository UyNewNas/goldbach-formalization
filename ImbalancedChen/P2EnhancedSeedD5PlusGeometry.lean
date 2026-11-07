import ImbalancedChen.P2EnhancedSeedPairD6Primitive

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal D5+ from second-seed-finite-feedback.tex, with the constant seed
support intersected before slicing. The physical cutoff is La0, the total
level Q is unchanged, and rho is s0(1-u-v), including its rho<2 part.
This proves geometry and cutoff inheritance, not an enhanced-count licence.
-/

namespace ImbalancedChen.P2EnhancedSeedD5PlusGeometry

noncomputable section

open Set MeasureTheory Classical
open P2EnhancedSeedSingletonPrimitive (S s0 a0 parameters parameters_geometry seedUpper)
open P2EnhancedSeedPairD6Primitive (fixedProfile pairKernel)
open P5OriginalActionMassBound (Point)

def cap : ℝ := 10/29
def supportSum : ℝ := 117/227
def cutOne : ℝ := 117/454
def cutTwo : ℝ := 19/58
def top : ℝ := 1/3
def D5plus : Set Point := P5OriginalActionMassBound.W2Pair5 parameters
def supportedD5 : Set Point := {x | x ∈ D5plus ∧ supportSum ≤ x 0+x 1}
def lower (u : ℝ) : ℝ := max u (supportSum-u)
def upper (u : ℝ) : ℝ := min cap (1-2*u)
def closedRectangle : Set Point := Icc ![a0,a0] ![top,cap]
def feedback (J : ℝ) (x : Point) : ℝ := seedUpper J (fixedProfile x)*pairKernel x

theorem D5plus_dictionary (x : Point) :
    x ∈ D5plus ↔ a0<x 0 ∧ x 0<x 1 ∧ x 1<cap ∧ x 1+2*x 0<1 := by
  norm_num [D5plus,P5OriginalActionMassBound.W2Pair5,parameters,
    P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a2,a0,cap]

theorem measurableSet_D5plus : MeasurableSet D5plus :=
  P5OriginalActionMassBound.W2Pair5_measurable parameters

theorem measurableSet_supportedD5 : MeasurableSet supportedD5 :=
  measurableSet_D5plus.inter
    (measurableSet_le measurable_const ((measurable_pi_apply 0).add (measurable_pi_apply 1)))

theorem actual_profile_bounds {x : Point} (hx : x ∈ D5plus) :
    1<fixedProfile x ∧ fixedProfile x<s0-2 := by
  have h := P5OriginalFeedbackDomains.W2PairDomain_profile_bounds parameters_geometry (0 : Fin 4) hx
  exact ⟨h.1,h.2.1⟩

theorem support_iff (x : Point) : fixedProfile x≤S ↔ supportSum≤x 0+x 1 := by
  dsimp [fixedProfile,s0,S,supportSum]
  constructor <;> intro h <;> linarith only [h]

theorem supportedD5_dictionary (x : Point) :
    x ∈ supportedD5 ↔ a0<x 0 ∧ x 0<x 1 ∧ x 1<cap ∧
      x 1+2*x 0<1 ∧ supportSum≤x 0+x 1 := by
  simp only [supportedD5,mem_setOf_eq,D5plus_dictionary]
  tauto

theorem supportedD5_vec (u v : ℝ) :
    (![u,v] : Point) ∈ supportedD5 ↔
      a0<u ∧ u<v ∧ v<cap ∧ v+2*u<1 ∧ supportSum≤u+v := by
  simp only [supportedD5_dictionary,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem supportedD5_u {x : Point} (hx : x ∈ supportedD5) : x 0 ∈ Ioo a0 top := by
  have h := (supportedD5_dictionary x).mp hx
  exact ⟨h.1,by dsimp [top]; linarith only [h.2.1,h.2.2.2.1]⟩

theorem D5plus_subset_closed : D5plus ⊆ closedRectangle := by
  intro x hx
  have h := (D5plus_dictionary x).mp hx
  constructor <;> intro i <;> fin_cases i
  · exact h.1.le
  · exact h.1.le.trans h.2.1.le
  · dsimp [top]; linarith only [h.2.1,h.2.2.2]
  · exact h.2.2.1.le

theorem closed_geometry {x : Point} (hx : x ∈ closedRectangle) :
    0<x 0 ∧ 0<x 1 ∧ 0<1-x 0-x 1 := by
  have hu0 := hx.1 0
  have hv0 := hx.1 1
  have hu1 := hx.2 0
  have hv1 := hx.2 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,a0,cap,top] at hu0 hv0 hu1 hv1
  constructor
  · linarith only [hu0]
  constructor
  · linarith only [hv0]
  · linarith only [hu1,hv1]

/-- The larger S comparison is BELOW the actual physical cutoff La0,
not a new replacement of that cutoff. This covers the genuine rho<2 case. -/
theorem cutoff_inheritance {L chi alpha : ℝ} (hL : 0<L)
    (hchi : L/S<chi) (ha : 2≤alpha) {x : Point} (hx : x ∈ supportedD5) :
    0<L*(1-x 0-x 1) ∧
      (L*(1-x 0-x 1))/S≤L*a0 ∧
      (L*(1-x 0-x 1))/(fixedProfile x)=L*a0 ∧
      L*a0<L*x 0 ∧ L*x 0<L*x 1 ∧ L*x 1<L/S ∧ L/S<chi ∧
      2*x 1<1 ∧ x 1+2*x 0<1 ∧
      alpha≤P5OriginalFeedbackDomains.pairChildAlpha alpha x := by
  have h := (supportedD5_dictionary x).mp hx
  have hgeo := closed_geometry (D5plus_subset_closed hx.1)
  have hr : 0<1-x 0-x 1 := hgeo.2.2
  have hscalar : (1-x 0-x 1)/S≤a0 := by
    dsimp [S,a0,supportSum] at *
    linarith only [h.2.2.2.2]
  have hcompare := mul_le_mul_of_nonneg_left hscalar hL.le
  have hphysical : (L*(1-x 0-x 1))/(fixedProfile x)=L*a0 := by
    dsimp [fixedProfile,s0,a0]
    field_simp [hr.ne'] <;> ring
  have hv : x 1<1/S := by
    have hc := h.2.2.1
    dsimp [cap] at hc
    dsimp [S]
    linarith only [hc]
  have hvL : L*x 1<L/S := by
    have hm := mul_lt_mul_of_pos_left hv hL
    convert hm using 1 <;> ring
  have hsquare : 2*x 1<1 := by
    have hc := h.2.2.1
    dsimp [cap] at hc
    linarith only [hc]
  have hA := P5OriginalFeedbackDomains.pairChildAlpha_ge_parent parameters_geometry
    (0 : Fin 4) ha hx.1
  exact ⟨mul_pos hL hr,by convert hcompare using 1 <;> ring,hphysical,
    mul_lt_mul_of_pos_left h.1 hL,mul_lt_mul_of_pos_left h.2.1 hL,hvL,hchi,
    hsquare,h.2.2.2.1,hA⟩

/-- Literal same-Q residual equation: only the specified exponent T changes. -/
theorem same_total_level (nu T L : ℝ) (hL : L=nu-T) (x : Point) :
    nu-(T+L*(x 0+x 1))=L*(1-x 0-x 1) := by
  rw [hL]
  ring

theorem transported_alpha (alpha : ℝ) {x : Point} (hx : x ∈ D5plus) :
    P5OriginalFeedbackDomains.pairChildAlpha alpha x=
      (alpha-x 0-x 1)/(1-x 0-x 1) :=
  P5OriginalFeedbackDomains.pairChildAlpha_eq_ratio parameters_geometry (0 : Fin 4) alpha hx

theorem feedback_support (J : ℝ) {x : Point} (hx : x ∈ D5plus) :
    feedback J x=supportedD5.indicator (fun x => J*pairKernel x) x := by
  have hp := actual_profile_bounds hx
  by_cases hs : supportSum≤x 0+x 1
  · have hm : fixedProfile x ∈ Icc (1 : ℝ) S := ⟨hp.1.le,(support_iff x).mpr hs⟩
    rw [feedback,seedUpper,indicator_of_mem hm,indicator_of_mem (show x∈supportedD5 from ⟨hx,hs⟩)]
  · have hm : fixedProfile x ∉ Icc (1 : ℝ) S := fun hh => hs ((support_iff x).mp hh.2)
    rw [feedback,seedUpper,indicator_of_notMem hm,zero_mul,
      indicator_of_notMem (show x∉supportedD5 from fun hh => hs hh.2)]

theorem slice_geometry {u : ℝ} (hu : u ∈ Icc a0 top) :
    0<u ∧ 0<lower u ∧ lower u≤upper u ∧ upper u<1-u := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [a0]) hu.1
  have hleft : u≤cap ∧ u≤1-2*u := by
    dsimp [top] at hu
    dsimp [cap]
    constructor <;> linarith only [hu.2]
  have hright : supportSum-u≤cap ∧ supportSum-u≤1-2*u := by
    dsimp [a0,top] at hu
    dsimp [supportSum,cap]
    constructor <;> linarith only [hu.1,hu.2]
  refine ⟨hu0,hu0.trans_le (le_max_left _ _),?_,?_⟩
  · exact max_le (le_min hleft.1 hleft.2) (le_min hright.1 hright.2)
  · have hm : upper u≤cap := min_le_left _ _
    dsimp [cap,top] at *
    linarith only [hm,hu.2]

theorem three_cut_order : a0<cutOne ∧ cutOne<cutTwo ∧ cutTwo<top := by
  norm_num [a0,cutOne,cutTwo,top]

theorem first_affine {u : ℝ} (hu : u ∈ Icc a0 cutOne) :
    lower u=supportSum-u ∧ upper u=cap := by
  have hl : u≤supportSum-u := by dsimp [cutOne,supportSum] at *; linarith only [hu.2]
  have hr : cap≤1-2*u := by dsimp [cutOne,cap] at *; linarith only [hu.2]
  exact ⟨max_eq_right hl,min_eq_left hr⟩

theorem second_affine {u : ℝ} (hu : u ∈ Icc cutOne cutTwo) :
    lower u=u ∧ upper u=cap := by
  have hl : supportSum-u≤u := by dsimp [cutOne,supportSum] at *; linarith only [hu.1]
  have hr : cap≤1-2*u := by dsimp [cutTwo,cap] at *; linarith only [hu.2]
  exact ⟨max_eq_left hl,min_eq_left hr⟩

theorem third_affine {u : ℝ} (hu : u ∈ Icc cutTwo top) :
    lower u=u ∧ upper u=1-2*u := by
  have hl : supportSum-u≤u := by dsimp [cutTwo,supportSum] at *; linarith only [hu.1]
  have hr : 1-2*u≤cap := by dsimp [cutTwo,cap] at *; linarith only [hu.1]
  exact ⟨max_eq_left hl,min_eq_right hr⟩

/-- Only the affine support wall can distinguish the literal closed seed
support from these open vertical slices. Its v-singleton will be paid in Fubini. -/
theorem slice_dictionary {u v : ℝ} (hu : u ∈ Ioo a0 top) (hne : v≠supportSum-u) :
    (![u,v] : Point) ∈ supportedD5 ↔ v ∈ Ioo (lower u) (upper u) := by
  rw [supportedD5_vec]
  simp only [mem_Ioo,lower,upper,max_lt_iff,lt_min_iff]
  constructor
  · intro h
    have hs : supportSum-u<v := lt_of_le_of_ne (by linarith only [h.2.2.2.2]) hne.symm
    exact ⟨⟨h.2.1,hs⟩,h.2.2.1,by linarith only [h.2.2.2.1]⟩
  · rintro ⟨⟨huv,hs⟩,hcap,hgate⟩
    exact ⟨hu.1,huv,hcap,by linarith only [hgate],by linarith only [hs]⟩

end
end ImbalancedChen.P2EnhancedSeedD5PlusGeometry
