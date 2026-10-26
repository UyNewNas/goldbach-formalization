import ImbalancedChen.P2EnhancedSeedInheritedCellBounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal final pair D8 of the manuscript's seven-piece seed feedback.
The support gate is a larger-S comparison for the SAME total Q, with
physical cutoff Lu. It is not a max-two replacement. The original
full/selected square gates and the transported alpha are retained.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD8Geometry

noncomputable section
open Set MeasureTheory Classical
open P2EnhancedSeedSingletonPrimitive (S s0 parameters seedUpper)
open P5OriginalActionMassBound (Point)

def uLo : ℝ := 50/227
def uHi : ℝ := 100/353
def vLo : ℝ := 100/353
def vHi : ℝ := 10/29
def cut : ℝ := 1265/5648
def supportLine (u : ℝ) : ℝ := 1-(16/5)*u
def D8 : Set Point := P5OriginalActionMassBound.W2Pair8 parameters
def profile (x : Point) : ℝ := (1-x 0-x 1)/x 0
def support : Set Point := {x | x ∈ D8 ∧ supportLine (x 0)≤x 1}
def closedRectangle : Set Point := Icc ![uLo,vLo] ![uHi,vHi]

theorem D8_dictionary (x : Point) :
    x ∈ D8 ↔ uLo<x 0 ∧ x 0<uHi ∧ vLo<x 1 ∧ x 1<vHi := by
  norm_num [D8,P5OriginalActionMassBound.W2Pair8,parameters,
    P5OriginalActionMassBound.a0,P5OriginalActionMassBound.a1,
    P5OriginalActionMassBound.a2,uLo,uHi,vLo,vHi]

theorem D8_vec (u v : ℝ) : (![u,v] : Point) ∈ D8 ↔
    u ∈ Ioo uLo uHi ∧ v ∈ Ioo vLo vHi := by
  rw [D8_dictionary]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mem_Ioo]
  tauto

theorem measurableSet_D8 : MeasurableSet D8 :=
  P5OriginalActionMassBound.W2Pair8_measurable parameters

theorem measurableSet_support : MeasurableSet support := by
  exact measurableSet_D8.inter (measurableSet_le (by unfold supportLine; fun_prop) (by fun_prop))

theorem D8_subset_closed : D8 ⊆ closedRectangle := by
  intro x hx
  have h := (D8_dictionary x).mp hx
  constructor <;> intro i <;> fin_cases i
  · exact h.1.le
  · exact h.2.2.1.le
  · exact h.2.1.le
  · exact h.2.2.2.le

theorem closed_geometry {x : Point} (hx : x ∈ closedRectangle) :
    0<x 0 ∧ 0<x 1 ∧ 0<1-x 0-x 1 := by
  have hu0 := hx.1 0
  have hu1 := hx.2 0
  have hv0 := hx.1 1
  have hv1 := hx.2 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,uLo,uHi,vLo,vHi] at hu0 hu1 hv0 hv1
  constructor
  · linarith only [hu0]
  constructor
  · linarith only [hv0]
  · linarith only [hu1,hv1]

theorem profile_eq_original (x : Point) :
    profile x=P5OriginalFeedbackDomains.movingPairProfile x := rfl

theorem D8_profile_range {x : Point} (hx : x ∈ D8) :
    1<profile x ∧ profile x<s0-2 ∧ s0-2≤3 := by
  exact P5OriginalFeedbackDomains.W2PairDomain_profile_bounds
    P2EnhancedSeedSingletonPrimitive.parameters_geometry (3 : Fin 4) hx

theorem support_iff_profile {x : Point} (hx : x ∈ D8) :
    x ∈ support ↔ profile x ∈ Icc (1 : ℝ) S := by
  have hu := (closed_geometry (D8_subset_closed hx)).1
  have hr := D8_profile_range hx
  simp only [support,mem_setOf_eq,hx,true_and,mem_Icc]
  constructor
  · intro h
    exact ⟨hr.1.le,(div_le_iff₀ hu).mpr (by dsimp [supportLine,S] at *; linarith only [h])⟩
  · intro h
    have hh := (div_le_iff₀ hu).mp h.2
    dsimp [supportLine,S] at *
    linarith only [hh]

theorem support_cut_dictionary (u : ℝ) :
    supportLine u≤vLo ↔ cut≤u := by
  dsimp [supportLine,vLo,cut]
  constructor <;> intro h <;> linarith only [h]

theorem literal_geometry : uLo<cut ∧ cut<uHi ∧
    0<vLo ∧ vLo<vHi ∧ vHi<1-uHi := by
  norm_num [uLo,uHi,cut,vLo,vHi]

/-- Both original affine subpieces are nonempty; the upper endpoint is
the literal a2 on both, and the lower endpoint switches exactly at cut. -/
theorem affine_subpieces {u : ℝ} (hu : u ∈ Ioo uLo uHi) :
    (u≤cut → vLo≤supportLine u ∧ 0<supportLine u ∧ supportLine u<vHi) ∧
    (cut≤u → supportLine u≤vLo) := by
  constructor
  · intro hc
    have hL : vLo≤supportLine u := by dsimp [vLo,supportLine,cut] at *; linarith only [hc]
    refine ⟨hL,lt_of_lt_of_le literal_geometry.2.2.1 hL,?_⟩
    dsimp [uLo,vHi,supportLine] at *
    linarith only [hu.1]
  · exact fun hc => (support_cut_dictionary u).mpr hc

/-- Total-Q conservation, physical prime ceiling, comparison cutoff,
all pair square gates, actual range (including 1<rho<2), and real alpha. -/
theorem sameQ_cutoff_and_squares {L chi alpha : ℝ} (hL : 0<L)
    (hchi : L/S<chi) (ha : 2≤alpha) {x : Point} (hx : x ∈ support) :
    L*(1-x 0-x 1)+L*x 0+L*x 1=L ∧
    0<L*(1-x 0-x 1) ∧
    (L*(1-x 0-x 1))/S≤L*x 0 ∧
    L*x 0<L*x 1 ∧ L*x 1<L/S ∧ L/S<chi ∧
    2*x 1<1 ∧ x 1+2*x 0<1 ∧
    1<profile x ∧ profile x≤S ∧
    alpha≤P5OriginalFeedbackDomains.pairChildAlpha alpha x := by
  have hd := hx.1
  have h := (D8_dictionary x).mp hd
  have hg := closed_geometry (D8_subset_closed hd)
  have hp := (support_iff_profile hd).mp hx
  have hcomp : (1-x 0-x 1)/S≤x 0 := by
    apply (div_le_iff₀ (by norm_num [S] : 0<S)).mpr
    dsimp [supportLine,S] at hx
    linarith only [hx.2]
  have hV : x 1<1/S := by dsimp [vHi,S] at *; linarith only [h.2.2.2]
  have hs := P5OriginalFeedbackDomains.W2PairDomain_gates
    P2EnhancedSeedSingletonPrimitive.parameters_geometry (3 : Fin 4) hd
  have hA := P5OriginalFeedbackDomains.pairChildAlpha_ge_parent
    P2EnhancedSeedSingletonPrimitive.parameters_geometry (3 : Fin 4) ha hd
  refine ⟨by ring,mul_pos hL hg.2.2,?_,mul_lt_mul_of_pos_left hs.2.1 hL,
    ?_,hchi,hs.2.2.1,hs.2.2.2,(D8_profile_range hd).1,hp.2,hA⟩
  · convert mul_le_mul_of_nonneg_left hcomp hL.le using 1 <;> ring
  · convert mul_lt_mul_of_pos_left hV hL using 1 <;> ring

/-- A literal positive-width sub-two region is preserved by the seed.
This is not merely a nonempty boundary example. -/
theorem sub_two_rectangle {u v : ℝ}
    (hu : u ∈ Ioo (27/100 : ℝ) (7/25))
    (hv : v ∈ Ioo (3/10 : ℝ) (31/100)) :
    (![u,v] : Point) ∈ support ∧ 1<profile ![u,v] ∧ profile ![u,v]<2 := by
  have hd : (![u,v] : Point) ∈ D8 := by
    rw [D8_vec]
    norm_num [uLo,uHi,vLo,vHi] at *
    constructor <;> constructor <;> linarith only [hu.1,hu.2,hv.1,hv.2]
  have hu0 : 0<u := by linarith only [hu.1]
  have hs : (![u,v] : Point) ∈ support := by
    refine ⟨hd,?_⟩
    dsimp [supportLine]
    linarith only [hu.1,hv.1]
  refine ⟨hs,(D8_profile_range hd).1,?_⟩
  apply (div_lt_iff₀ hu0).mpr
  dsimp
  linarith only [hu.1,hv.1]

end
end ImbalancedChen.P2EnhancedSeedPairD8Geometry
