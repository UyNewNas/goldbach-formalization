import ImbalancedChen.Part3OriginalHeckeStripPairing
import ImbalancedChen.Part3OriginalHolomorphicCuspFilter
import ImbalancedChen.Part3FixedMarkEulerSummability
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace ImbalancedChen.Part3.OriginalHolomorphicPoincare20261112

noncomputable section
open MeasureTheory Filter UpperHalfPlane Complex Set
open scoped MatrixGroups ModularForm UpperHalfPlane ComplexConjugate Topology InnerProductSpace
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonPretrace20261112 OriginalHeckeStripPairing20261112
open OriginalHolomorphicCuspFilter20261112 Gamma0FiniteMeasureCarrier20261024z
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0ActualParabolicUnfolding20261025a

def heckeSeed (m : ℕ) (s : ℝ) (w : ℍ) : ℂ := (w.im^s : ℝ) * q w^m

def heckeP (N r m : ℕ) (s : ℝ) (w : ℍ) : ℂ :=
  ∑' Q : GammaInfinityCosets N,
    (heckeSeed m s ∣[2*(r:ℤ)] (parabolicRepresentative N Q : SL(2,ℤ))) w

private theorem density {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) (w : ℍ) :
    petersson (2*(r:ℤ)) (heckeSeed m s) f w = weightSeed f m s w := by
  have h : w.im^(2*(r:ℝ)+s) = w.im^((2*r:ℕ):ℤ)*w.im^s := by
    rw [Real.rpow_add w.im_pos]
    norm_cast
  rw [weightSeed,h,heckeSeed,petersson]
  simp only [map_mul, Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_zpow,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem density_term {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ)
    (g : CongruenceSubgroup.Gamma0 N) (w : ℍ) :
    petersson (2*(r:ℤ)) (heckeSeed m s ∣[2*(r:ℤ)] (g:SL(2,ℤ))) f w =
      weightSeed f m s (g • w) := by
  rw [← density, ← petersson_slash_SL]
  congr 2
  exact (SlashInvariantFormClass.slash_action_eq f _
    (Subgroup.mem_map.mpr ⟨g.val,g.property,rfl⟩)).symm

theorem density_sum {N r : ℕ} (f : Forms N r) (m : ℕ) (s : ℝ) (w : ℍ) :
    petersson (2*(r:ℤ)) (heckeP N r m s) f w =
      parabolicTraceComplex N (weightSeed f m s) w := by
  rw [parabolicTraceComplex]
  simp_rw [← density_term]
  simp only [petersson,heckeP,Complex.conj_tsum,tsum_mul_right]

theorem hecke_pairing (N r : ℕ) [NeZero N] (hr : 0<r) (f : Forms N r) {m : ℕ} (hm : 0<m)
    {s : ℝ} (hs : 0<s) :
    (∫ w in gamma0Carrier N, petersson (2*(r:ℤ)) (heckeP N r m s) f w) =
      (heckeMass r m s : ℂ)*raw N (NeZero.pos N) r 1 m f := by
  simp_rw [density_sum]
  rw [unfolded N r hr f hm hs]
  have hF : (⇑(frameForm N (NeZero.pos N) r f 1) : ℍ→ℂ)=f := by
    funext w
    rw [frameForm_apply,(two_actual_frames N (NeZero.pos N)).1]
    simp
  simp [raw,hF]

/-- Actual Petersson pairings against the full ONB give the holomorphic component
of the regularized Poincaré sum in each original weight. -/
def holComponent (N r m : ℕ) [NeZero N] (s : ℝ) : Forms N r :=
  ∑ i, conj (∫ w in gamma0Carrier N,
    petersson (2*(r:ℤ)) (heckeP N r m s) (formsBasis N r i) w) • formsBasis N r i

def rawVector (N r m : ℕ) [NeZero N] : Forms N r :=
  (InnerProductSpace.toDual ℂ (Forms N r)).symm
    ((raw N (NeZero.pos N) r 1 m).toContinuousLinearMap)

theorem holComponent_eq (N r : ℕ) [NeZero N] (hr : 0<r) {m : ℕ} (hm : 0<m)
    {s : ℝ} (hs : 0<s) :
    holComponent N r m s = (heckeMass r m s : ℂ) • rawVector N r m := by
  rw [holComponent,← basis_complete N r (rawVector N r m), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hecke_pairing N r hr _ hm hs, map_mul,Complex.conj_ofReal,smul_smul]
  congr 2
  rw [← inner_conj_symm,rawVector,InnerProductSpace.toDual_symm_apply]
  rfl

theorem heckeMass_at_zero {r m : ℕ} (hr : 0<r) (hm : 0<m) :
    ContinuousAt (heckeMass r m) 0 ∧ heckeMass r m 0=mass r m := by
  have hp : 0<2*(r:ℝ)-1 := by have h : 1≤(r:ℝ) := by exact_mod_cast hr;linarith
  constructor
  · unfold heckeMass
    apply ContinuousAt.mul
    · exact (Real.continuousAt_const_rpow (by positivity)).comp (by fun_prop)
    · exact (Real.differentiableAt_Gamma (by intro n; simp only [add_zero];
        linarith [Nat.cast_nonneg (α:=ℝ) n])).continuousAt.comp (by fun_prop)
  · unfold mass heckeMass
    rw [add_zero, show 2*(r:ℝ)-1=((2*r-1:ℕ):ℝ) by
      rw [Nat.cast_sub (by omega : 1≤2*r)];push_cast;ring, Real.rpow_natCast]

/-- A norm limit of the actual finite projections even in the lowest holomorphic weight. -/
theorem holComponent_limit (N r : ℕ) [NeZero N] (hr : 0<r) {m : ℕ} (hm : 0<m) :
    Tendsto (holComponent N r m) (𝓝[>] (0:ℝ)) (𝓝 (Pvector N r 1 m)) := by
  obtain ⟨hc,hz⟩ := heckeMass_at_zero hr hm
  have ht := (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left nhdsWithin_le_nhds
  have h := ht.smul (tendsto_const_nhds (x:=rawVector N r m))
  rw [hz] at h
  exact h.congr' ((self_mem_nhdsWithin : Ioi (0:ℝ)∈𝓝[>] 0).mono
    fun s hs => (holComponent_eq N r hr hm hs).symm)

/-- Common positive-denominator majorant for every Fourier coefficient at *every* cusp. -/
theorem all_cusps_majorant (N : ℕ) [NeZero N] {m : ℤ} (hm : m≠0) :
    ∃ b : ℕ+→ℝ, Summable b ∧
      ∀ (g : SL(2,ℤ)) (n : ℤ) (C : ℕ+), ‖cuspSum N C g m n‖/(C:ℝ)^2 ≤ b C := by
  let b := fun C : ℕ+ => (N:ℝ)*FixedMarkTail.price m 0 C
  refine ⟨b,((FixedMarkTail.summable_majorant_price hm (by norm_num : (0:ℝ)<1/4)).comp_injective
    (fun _ _ h => Subtype.ext h)).mul_left _,?_⟩
  intro g n C
  have h := cuspSum_bound N C g m n (FixedMarkTail.majorant_nonneg m C) (fun h => by
    rw [inverse_swap];exact FixedMarkTail.physical_le_majorant m C h)
  have hC : (0:ℝ)<C := by exact_mod_cast C.property
  apply (div_le_div_of_nonneg_right h (sq_nonneg _)).trans_eq
  simp [b,FixedMarkTail.price,Real.rpow_neg hC.le,Real.rpow_two,C.property.ne',div_eq_mul_inv,mul_assoc]

end
end ImbalancedChen.Part3.OriginalHolomorphicPoincare20261112
