import ImbalancedChen.ActualPrimePolyhedralTestFunctions
import ImbalancedChen.P5OriginalActionMassBound
import ImbalancedChen.P2OriginalChildPhysicalNormalization
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine target-deleted prime-tuple limits for every original W1 window
and all seven original W2 feedback domains, at each fixed positive
residual exponent. No Riemann-limit, boundary-nullity, KI/8, W2 count
estimate, seed or endpoint is an input. This does not assert uniformity
over moving residual exponents or a licence for the complete old bank.
-/
namespace ImbalancedChen.P2OriginalBankChildPrimeMass

noncomputable section
open MeasureTheory Filter Set
open P5OriginalActionMassBound
open P2OriginalChildPhysicalNormalization
open scoped Classical BigOperators Topology Pointwise

abbrev Coord (d : ℕ) := Fin d → ℝ
def cube (d : ℕ) : Set (Coord d) :=
  logPrimeBox (fun _ => (1/10:ℝ)) (fun _ => (3/5:ℝ))
def coord {d : ℕ} (i : Fin d) : Coord d →L[ℝ] ℝ := ContinuousLinearMap.proj i

def scaledPrimeSum {d : ℕ} (N : ℕ) (L : ℝ) (D : Set (Coord d))
    (f : Coord d → ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin d => L/10) (fun _ => 3*L/5)
    (fun x => D.indicator f (L⁻¹ • x))

theorem integral_log_density_dilation {d : ℕ} {L : ℝ} (hL : 0<L)
    (D : Set (Coord d)) (f : Coord d → ℝ) :
    (∫ x in L • D, f (L⁻¹ • x)*(∏ i,1/x i)) =
      ∫ x in D,f x*(∏ i,1/x i) := by
  let g (x : Coord d) := f (L⁻¹ • x)*(∏ i,1/x i)
  have hg (x : Coord d) : g (L • x)=(L^d)⁻¹*(f x*(∏ i,1/x i)) := by
    simp only [g, inv_smul_smul₀ hL.ne', Pi.smul_apply, smul_eq_mul,
      one_div, mul_inv_rev, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← inv_pow]
    ring
  have hs := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Coord d)) g D hL
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,smul_eq_mul] at hs
  simp_rw [hg] at hs
  rw [integral_const_mul] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hL.ne')) hs).symm

theorem scaled_region {d r : ℕ} {L : ℝ} (hL : 0<L)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ) :
    logPrimeBox (fun _ : Fin d => L/10) (fun _ => 3*L/5) ∩
      primeAffineGateRegion A (fun j => L*c j) =
        L • (cube d ∩ primeAffineGateRegion A c) := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  simp only [mem_inter_iff,cube,mem_logPrimeBox,primeAffineGateRegion,mem_setOf_eq]
  have hg (j : Fin r) : A j x<L*c j ↔ A j (L⁻¹ • x)<c j := by
    rw [map_smul,smul_eq_mul,← div_eq_inv_mul,div_lt_iff₀ hL]
    simpa only [mul_comm]
  have hb (i : Fin d) : L/10≤x i ∧ x i<3*L/5 ↔
      (1/10:ℝ)≤(L⁻¹ • x) i ∧ (L⁻¹ • x) i<3/5 := by
    simp only [Pi.smul_apply,smul_eq_mul,← div_eq_inv_mul,
      le_div_iff₀ hL,div_lt_iff₀ hL]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith
  exact and_congr (forall_congr' hb) (forall_congr' hg)

/-- Scaling cancels in the logarithmic density. The actual target is
still N, not a surrogate integer floor of N^L. -/
theorem tendsto_scaledPrimeSum_affine {d r : ℕ} {L : ℝ} (hL : 0<L)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hA : ∀ j,A j≠0) (f : Coord d → ℝ) (hf : Continuous f) :
    Tendsto (fun N : ℕ => scaledPrimeSum N L (primeAffineGateRegion A c) f)
      atTop (𝓝 (∫ x in cube d ∩ primeAffineGateRegion A c,
        f x*(∏ i,1/x i))) := by
  have ht := tendsto_actualPrimeBoxTestSum_cube_affineGates
    (a:=L/10) (b:=3*L/5) (by positivity) (by linarith)
    A (fun j => L*c j) hA (fun x => f (L⁻¹ • x))
    (hf.comp (continuous_const.smul continuous_id)).continuousOn
  have hg (x : Coord d) :
      (primeAffineGateRegion A (fun j => L*c j)).indicator
        (fun y => f (L⁻¹ • y)) x =
      (primeAffineGateRegion A c).indicator f (L⁻¹ • x) := by
    have hm : x∈primeAffineGateRegion A (fun j => L*c j) ↔
        L⁻¹ • x∈primeAffineGateRegion A c := by
      apply forall_congr'
      intro j
      rw [map_smul,smul_eq_mul,← div_eq_inv_mul,div_lt_iff₀ hL]
      simpa only [mul_comm]
    by_cases hx : x∈primeAffineGateRegion A (fun j => L*c j)
    · simp only [indicator_of_mem hx,indicator_of_mem (hm.mp hx)]
    · simp only [indicator_of_notMem hx,indicator_of_notMem (mt hm.mpr hx)]
  simp_rw [hg] at ht
  rw [scaled_region hL A c, integral_log_density_dilation hL] at ht
  exact ht

def singleForms : Fin 2 → Coord 1 →L[ℝ] ℝ := ![-coord 0,coord 0]
def singleBounds (lo hi : ℝ) : Fin 2 → ℝ := ![-lo,hi]
def singleDomain (lo hi : ℝ) : Set (Coord 1) := {x | lo<x 0 ∧ x 0<hi}

theorem single_as_affine (lo hi : ℝ) :
    singleDomain lo hi=primeAffineGateRegion singleForms (singleBounds lo hi) := by
  ext x
  simp [singleDomain,primeAffineGateRegion,singleForms,singleBounds,coord,
    Fin.forall_fin_succ]

theorem singleForms_ne (i : Fin 2) : singleForms i≠0 := by
  intro h
  have hh := congrArg (fun A : Coord 1 →L[ℝ] ℝ => A (fun _ => 1)) h
  fin_cases i <;> norm_num [singleForms,coord] at hh

theorem single_integral_coordinates (lo hi : ℝ) (f : ℝ → ℝ) :
    (∫ x in singleDomain lo hi,f (x 0))=∫ u in Ioo lo hi,f u := by
  have hm : MeasurableSet (singleDomain lo hi) := by
    rw [single_as_affine]
    exact measurableSet_primeAffineGateRegion _ _
  have hh := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    ((Ioo lo hi).indicator f)
  change (∫ x : Coord 1,(Ioo lo hi).indicator f (x 0))=
    ∫ u : ℝ,(Ioo lo hi).indicator f u at hh
  have he : (fun x : Coord 1 => (Ioo lo hi).indicator f (x 0))=
      (singleDomain lo hi).indicator (fun x => f (x 0)) := by
    funext x
    by_cases hx : lo<x 0 ∧ x 0<hi
    · simp only [indicator_of_mem (show x 0∈Ioo lo hi from hx),
        indicator_of_mem (show x∈singleDomain lo hi from hx)]
    · simp only [indicator_of_notMem (show x 0∉Ioo lo hi from hx),
        indicator_of_notMem (show x∉singleDomain lo hi from hx)]
  rw [he,integral_indicator hm,integral_indicator measurableSet_Ioo] at hh
  exact hh

def residualSingle (x : Coord 1) : ℝ := 1/max (1/10:ℝ) (1-x 0)
def residualPair (x : Coord 2) : ℝ := 1/max (1/10:ℝ) (1-x 0-x 1)

theorem residualSingle_continuous : Continuous residualSingle := by
  apply continuous_const.div
    (continuous_const.max (continuous_const.sub (continuous_apply 0)))
  intro x
  exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/10) (le_max_left _ _)).ne'

theorem residualPair_continuous : Continuous residualPair := by
  apply continuous_const.div
    (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1)))
  intro x
  exact (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/10) (le_max_left _ _)).ne'

theorem single_in_cube {lo hi : ℝ} (hlo : (1/5:ℝ)≤lo) (hhi : hi≤1/2) :
    singleDomain lo hi ⊆ cube 1 := by
  intro x hx
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  change lo<x 0 ∧ x 0<hi at hx
  constructor <;> linarith

theorem single_kernel {lo hi : ℝ} (hhi : hi≤1/2) {x : Coord 1}
    (hx : x∈singleDomain lo hi) :
    residualSingle x*(∏ i,1/x i)=1/(x 0*(1-x 0)) := by
  have hd : (1/10:ℝ)≤1-x 0 := by linarith [hx.2]
  simp only [residualSingle,max_eq_right hd,Fin.prod_univ_one,one_div,mul_inv_rev]
  ring

/-- The rational singleton kernel is proved from a genuine prime sum.
The integral is in the one-coordinate Euclidean space, without a
change of the target, a fitted scalar mass, or an assumed limit. -/
theorem tendsto_single_mass {L lo hi : ℝ} (hL : 0<L)
    (hlo : (1/5:ℝ)≤lo) (hhi : hi≤1/2) :
    Tendsto (fun N : ℕ => scaledPrimeSum N L (singleDomain lo hi) residualSingle)
      atTop (𝓝 (∫ x in singleDomain lo hi,1/(x 0*(1-x 0)))) := by
  have ht := tendsto_scaledPrimeSum_affine hL singleForms (singleBounds lo hi)
    singleForms_ne residualSingle residualSingle_continuous
  rw [← single_as_affine lo hi,
    inter_eq_right.mpr (single_in_cube hlo hhi)] at ht
  have he : (∫ x in singleDomain lo hi,residualSingle x*(∏ i,1/x i)) =
      ∫ x in singleDomain lo hi,1/(x 0*(1-x 0)) := by
    apply setIntegral_congr_fun
    · rw [single_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx; exact single_kernel hhi hx
  rw [he] at ht
  exact ht

def W1PrimeMass (N : ℕ) (L : ℝ) (i : Fin 7) (j : Fin 10) : ℝ :=
  scaledPrimeSum N L (singleDomain (1/W1Anchor j) (1/W1Target i)) residualSingle

theorem all70_W1_prime_mass {L : ℝ} (hL : 0<L) (i : Fin 7) (j : Fin 10) :
    Tendsto (fun N : ℕ => W1PrimeMass N L i j) atTop
      (𝓝 (∫ x in singleDomain (1/W1Anchor j) (1/W1Target i),
        1/(x 0*(1-x 0)))) := by
  have hj : (j.val:ℝ)≤9 := by exact_mod_cast (show j.val≤9 by omega)
  have hs : (2:ℝ)≤W1Target i := by
    unfold W1Target
    linarith [show (0:ℝ)≤i.val from Nat.cast_nonneg _]
  have ha : 0<W1Anchor j := by unfold W1Anchor; positivity
  apply tendsto_single_mass hL
  · exact one_div_le_one_div_of_le ha (by unfold W1Anchor; linarith)
  · exact one_div_le_one_div_of_le (by norm_num) hs

def singletonTop (p : W2Parameters) : Fin 3 → ℝ := ![b p,a2 p,a3 p]
def W2SingletonPrimeMass (N : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 3) : ℝ :=
  scaledPrimeSum N L (singleDomain (a0 p) (singletonTop p k)) residualSingle

theorem all36_three_singleton_prime_masses {L : ℝ} (hL : 0<L)
    (j : Fin 36) (k : Fin 3) :
    Tendsto (fun N : ℕ => W2SingletonPrimeMass N L (originalW2At j) k) atTop
      (𝓝 (∫ x in singleDomain (a0 (originalW2At j)) (singletonTop (originalW2At j) k),
        1/(x 0*(1-x 0)))) := by
  have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  apply tendsto_single_mass hL hp.1
  rcases hp with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
  fin_cases k <;> simp only [singletonTop,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] <;> linarith

def pairForms : Fin 4 → Fin 4 → Coord 2 →L[ℝ] ℝ
  | 0 => ![-coord 0,coord 0-coord 1,coord 1,2 • coord 0+coord 1]
  | 1 => ![-coord 0,coord 0,-coord 1,coord 1]
  | 2 => ![-coord 0,coord 0-coord 1,coord 1,coord 1]
  | 3 => ![-coord 0,coord 0,-coord 1,coord 1]

def pairBounds (p : W2Parameters) : Fin 4 → Fin 4 → ℝ
  | 0 => ![-a0 p,0,a2 p,1]
  | 1 => ![-a0 p,a1 p,-a2 p,a3 p]
  | 2 => ![-a0 p,0,a1 p,a1 p]
  | 3 => ![-a0 p,a1 p,-a1 p,a2 p]

theorem pair_as_affine (p : W2Parameters) (k : Fin 4) :
    W2PairDomain p k=primeAffineGateRegion (pairForms k) (pairBounds p k) := by
  ext x
  fin_cases k <;>
    simp [W2PairDomain,W2Pair5,W2Pair6,W2Pair7,W2Pair8,primeAffineGateRegion,
      pairForms,pairBounds,coord,Fin.forall_fin_succ,and_assoc,add_comm]

theorem pairForms_ne (k i : Fin 4) : pairForms k i≠0 := by
  intro h
  have h0 := congrArg (fun A : Coord 2 →L[ℝ] ℝ => A ![1,0]) h
  have h1 := congrArg (fun A : Coord 2 →L[ℝ] ℝ => A ![0,1]) h
  fin_cases k <;> fin_cases i <;> norm_num [pairForms,coord] at h0 h1

theorem pair_in_cube {p : W2Parameters} (hp : W2Geometry p) (k : Fin 4) :
    W2PairDomain p k ⊆ cube 2 := by
  intro x hx
  have hb := W2PairDomain_subset hp k hx
  apply mem_logPrimeBox.mpr
  intro i
  have hlo := hb.1 i
  have hhi := hb.2 i
  constructor <;> linarith

theorem pair_residual_floor {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) {x : Coord 2} (hx : x∈W2PairDomain p k) :
    (1/5:ℝ)≤1-x 0-x 1 := by
  fin_cases k
  · exact (W2Pair5_geometry hp hx).2
  · exact (W2Pair6_geometry hp hx).2
  · exact (W2Pair7_geometry hp hx).2
  · exact (W2Pair8_geometry hp hx).2

theorem pair_kernel {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) {x : Coord 2} (hx : x∈W2PairDomain p k) :
    residualPair x*(∏ i,1/x i)=1/(x 0*x 1*(1-x 0-x 1)) := by
  have hd := pair_residual_floor hp k hx
  simp only [residualPair,max_eq_right (show (1/10:ℝ)≤1-x 0-x 1 by linarith),
    Fin.prod_univ_two,one_div,mul_inv_rev]
  ring

def W2PairPrimeMass (N : ℕ) (L : ℝ) (p : W2Parameters) (k : Fin 4) : ℝ :=
  scaledPrimeSum N L (W2PairDomain p k) residualPair

theorem all36_four_good_pair_prime_masses {L : ℝ} (hL : 0<L)
    (j : Fin 36) (k : Fin 4) :
    Tendsto (fun N : ℕ => W2PairPrimeMass N L (originalW2At j) k) atTop
      (𝓝 (∫ x in W2PairDomain (originalW2At j) k,
        1/(x 0*x 1*(1-x 0-x 1)))) := by
  have hp := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have ht := tendsto_scaledPrimeSum_affine hL (pairForms k)
    (pairBounds (originalW2At j) k) (pairForms_ne k)
    residualPair residualPair_continuous
  rw [← pair_as_affine,inter_eq_right.mpr (pair_in_cube hp k)] at ht
  have he : (∫ x in W2PairDomain (originalW2At j) k,residualPair x*(∏ i,1/x i)) =
      ∫ x in W2PairDomain (originalW2At j) k,1/(x 0*x 1*(1-x 0-x 1)) := by
    apply setIntegral_congr_fun
    · rw [pair_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx; exact pair_kernel hp k hx
  rw [he] at ht
  exact ht

/-- Both physical square gates hold on every named good domain, not
only the residual positivity needed by the rational kernel. -/
theorem all_good_pair_squares {p : W2Parameters} (hp : W2Geometry p)
    (k : Fin 4) {x : Coord 2} (hx : x∈W2PairDomain p k) :
    2*x 1<1 ∧ 2*x 0+x 1<1 := by
  rcases hp with ⟨h0,h01,h12,h23,h3,hb,hg6,hg7,hg8⟩
  fin_cases k
  · change a0 p<x 0 ∧ x 0<x 1 ∧ x 1<a2 p ∧ x 1+2*x 0<1 at hx
    constructor <;> linarith [hx.2.2.1,hx.2.2.2]
  · change a0 p<x 0 ∧ x 0<a1 p ∧ a2 p<x 1 ∧ x 1<a3 p at hx
    constructor <;> linarith [hx.2.1,hx.2.2.2]
  · change a0 p<x 0 ∧ x 0<x 1 ∧ x 1<a1 p at hx
    constructor <;> linarith [hx.2.1,hx.2.2]
  · change a0 p<x 0 ∧ x 0<a1 p ∧ a1 p<x 1 ∧ x 1<a2 p at hx
    constructor <;> linarith [hx.2.1,hx.2.2.2]

def excludedD5 (p : W2Parameters) : Set (Coord 2) :=
  {x | a0 p<x 0 ∧ x 0<x 1 ∧ x 1<a2 p ∧ 1≤x 1+2*x 0}

theorem D5_exact_partition (p : W2Parameters) (x : Coord 2) :
    (a0 p<x 0 ∧ x 0<x 1 ∧ x 1<a2 p) ↔
      x∈W2Pair5 p ∨ x∈excludedD5 p := by
  simp only [W2Pair5,excludedD5,mem_setOf_eq]
  constructor
  · rintro ⟨h0,h1,h2⟩
    rcases lt_or_ge (x 1+2*x 0) 1 with h | h
    · exact Or.inl ⟨h0,h1,h2,h⟩
    · exact Or.inr ⟨h0,h1,h2,h⟩
  · rintro (h | h) <;> exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem excludedD5_fails_square {p : W2Parameters} {x : Coord 2}
    (hx : x∈excludedD5 p) : ¬(2*x 0+x 1<1) := by
  change _ ∧ _ ∧ _ ∧ _ at hx
  linarith [hx.2.2.2]

theorem D5_cost_exact_split {ι : Type*} (T : Finset ι)
    (p : W2Parameters) (x : ι → Coord 2) (cost : ι → ℝ) :
    (∑ a∈T,if a0 p<x a 0 ∧ x a 0<x a 1 ∧ x a 1<a2 p then cost a else 0) =
      (∑ a∈T,if x a∈W2Pair5 p then cost a else 0)+
      (∑ a∈T,if x a∈excludedD5 p then cost a else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hbase : a0 p<x a 0 ∧ x a 0<x a 1 ∧ x a 1<a2 p
  · by_cases hgood : x a 1+2*x a 0<1
    · have hg : x a∈W2Pair5 p := ⟨hbase.1,hbase.2.1,hbase.2.2,hgood⟩
      have hb : x a∉excludedD5 p := fun h => (not_le_of_gt hgood) h.2.2.2
      simp only [if_pos hbase,if_pos hg,if_neg hb,add_zero]
    · have hb : x a∈excludedD5 p := ⟨hbase.1,hbase.2.1,hbase.2.2,le_of_not_gt hgood⟩
      have hg : x a∉W2Pair5 p := fun h => hgood h.2.2.2
      simp only [if_pos hbase,if_pos hb,if_neg hg,zero_add]
  · have hg : x a∉W2Pair5 p := fun h => hbase ⟨h.1,h.2.1,h.2.2.1⟩
    have hb : x a∉excludedD5 p := fun h => hbase ⟨h.1,h.2.1,h.2.2.1⟩
    simp only [if_neg hbase,if_neg hg,if_neg hb,zero_add]

/-- Every rejected arithmetic atom is retained with its original
positive cost. A unit term may be any of these atoms. This is a finite
partition, not an analytic bound on the positive-product cost. -/
theorem excludedD5_positive_cost {ι : Type*} (T : Finset ι)
    (p : W2Parameters) (x : ι → Coord 2) (cost : ι → ℝ)
    (hc : ∀a∈T,0≤cost a) :
    (∑ a∈T,if x a∈W2Pair5 p then cost a else 0) ≤
      ∑ a∈T,if a0 p<x a 0 ∧ x a 0<x a 1 ∧ x a 1<a2 p then cost a else 0 := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases hg : x a∈W2Pair5 p
  · have hb := (D5_exact_partition p (x a)).mpr (Or.inl hg)
    simp only [if_pos hg,if_pos hb]
  · simp only [if_neg hg]
    split_ifs <;> first | exact hc a ha | exact le_rfl

end
end ImbalancedChen.P2OriginalBankChildPrimeMass
