import ImbalancedChen.Part3Gamma0CompactInteriorLocalization
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Finite-error assembly of the actual compact-interior localization and the
support-preserving weighted local tensor approximation. Every continuous
compact target inside the genuine reduced-carrier chart is approximated
in the actual y^-1 L2 seminorm by a genuine finite smooth tensor span
element whose ENTIRE topological support stays inside that actual chart.

Neither arbitrary Lp compact approximation nor quotient density is assumed.
The finite error budget is epsilon/(number of pieces+1), so empty support
and the empty partition are handled without a division by zero.
-/

namespace ImbalancedChen.Part3.Gamma0CompactWeightedTensorApproximation20261025a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.Gamma0LocalWeightedTensorApproximation20261025a
open ImbalancedChen.Part3.Gamma0CompactInteriorLocalization20261025a

theorem divideByHeight_sub (F G : (ℝ×ℝ)→ℂ) :
    divideByHeight (F-G)=divideByHeight F-divideByHeight G := by
  funext p
  simp only [divideByHeight,Pi.sub_apply,mul_sub]

theorem exists_compact_interior_weighted_tensor_approx
    (N : ℕ) [NeZero N] (F : (ℝ×ℝ)→ℂ)
    (hFcont : Continuous F) (hFc : HasCompactSupport F)
    (hinside : ∀ p∈tsupport F,0<p.2 ∧ chartLift p∈reducedCarrier N)
    (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ H∈planeTensorSpan,HasCompactSupport H ∧
      (∀ p∈tsupport H,0<p.2 ∧ chartLift p∈reducedCarrier N) ∧
      eLpNorm (divideByHeight (F-H)) 2 volume<ENNReal.ofReal epsilon := by
  classical
  obtain ⟨S,r,G,hballs,hG,hFG⟩ := exists_finite_actual_interior_localization
    N F hFcont hFc hinside
  let I := {i : tsupport F // i∈S}
  let eta : ℝ := epsilon/((Fintype.card I:ℝ)+1)
  have heta : 0<eta := by dsimp [eta]; positivity
  have hGpos (i : I) : ∀ p∈tsupport (G i),0<p.2 := by
    intro p hp
    have hi := hballs i.1 i.2
    exact (hi.2 p (((hG i).2.2 hp).trans (by linarith [hi.1]))).1
  have hlocal : ∀ i : I,∃ H∈planeTensorSpan,
      (∀ p∈tsupport H,0<p.2 ∧ chartLift p∈reducedCarrier N) ∧
      eLpNorm (divideByHeight (G i-H)) 2 volume<ENNReal.ofReal eta := by
    intro i
    have hi := hballs i.1 i.2
    have hp := (hinside i.1 i.1.property).1
    have hcoord : ((chartLift (i.1:ℝ×ℝ)).re,(chartLift (i.1:ℝ×ℝ)).im)=(i.1:ℝ×ℝ) := by
      rw [chartLift_of_positive hp]
      rfl
    have hb : ∀ p∈Metric.ball
        ((chartLift (i.1:ℝ×ℝ)).re,(chartLift (i.1:ℝ×ℝ)).im) (r i.1),
        0<p.2 ∧ chartLift p∈reducedCarrier N := by
      simpa only [hcoord] using hi.2
    have hs : tsupport (G i)⊆Metric.ball
        ((chartLift (i.1:ℝ×ℝ)).re,(chartLift (i.1:ℝ×ℝ)).im) (r i.1/4) := by
      simpa only [hcoord] using (hG i).2.2
    obtain ⟨H,hH,_hrect,hpos,herr⟩ := exists_local_interior_weighted_tensor_L2_approx
      N (chartLift (i.1:ℝ×ℝ)) (r i.1) hi.1 hb (G i)
      (hG i).1 (hG i).2.1 hs (ENNReal.ofReal eta) (by positivity)
    exact ⟨H,hH,hpos,herr⟩
  choose H hHspan hHpos herr using hlocal
  let A : (ℝ×ℝ)→ℂ := ∑ i : I,H i
  have hAspan : A∈planeTensorSpan := planeTensorSpan.sum_mem (fun i _ => hHspan i)
  have hsupp : tsupport A⊆⋃ i : I,tsupport (H i) := by
    apply closure_minimal _ (isClosed_iUnion (fun _ => isClosed_tsupport))
    intro p hp
    by_contra hn
    have hall : ∀ i : I,H i p=0 := by
      intro i
      apply image_eq_zero_of_notMem_tsupport
      intro hi
      exact hn (mem_iUnion.mpr ⟨i,hi⟩)
    exact hp (by simp only [A,Finset.sum_apply,hall,Finset.sum_const_zero])
  have hApos : ∀ p∈tsupport A,0<p.2 ∧ chartLift p∈reducedCarrier N := by
    intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hsupp hp)
    exact hHpos i p hi
  refine ⟨A,hAspan,(span_continuous_compact hAspan).2,hApos,?_⟩
  have heq : divideByHeight (F-A)=∑ i : I,divideByHeight (G i-H i) := by
    rw [hFG]
    funext p
    simp only [divideByHeight,A,Pi.sub_apply,Finset.sum_apply,
      Finset.sum_sub_distrib,Finset.mul_sum,mul_sub]
  have hmeas : ∀ i : I,AEStronglyMeasurable (divideByHeight (G i-H i)) volume := by
    intro i
    rw [divideByHeight_sub]
    exact ((divideByHeight_continuous (G i) (hG i).1 (hGpos i)).sub
      (divideByHeight_continuous (H i) (span_continuous_compact (hHspan i)).1
        (fun p hp => (hHpos i p hp).1))).aestronglyMeasurable
  have hbudget : (∑ _i : I,ENNReal.ofReal eta)=
      ENNReal.ofReal ((Fintype.card I:ℝ)*eta) := by
    rw [Finset.sum_const,Finset.card_univ,← ENNReal.ofReal_nsmul]
    simp only [nsmul_eq_mul]
  have hsmall : (Fintype.card I:ℝ)*eta<epsilon := by
    have hn : (0:ℝ)<(Fintype.card I:ℝ)+1 := by positivity
    have he : eta*((Fintype.card I:ℝ)+1)=epsilon := by
      dsimp [eta]
      exact div_mul_cancel₀ epsilon hn.ne'
    nlinarith
  rw [heq]
  calc
    _ ≤ ∑ i : I,eLpNorm (divideByHeight (G i-H i)) 2 volume :=
      eLpNorm_sum_le (fun i _ => hmeas i) (by norm_num)
    _ ≤ ∑ _i : I,ENNReal.ofReal eta := Finset.sum_le_sum (fun i _ => (herr i).le)
    _ = ENNReal.ofReal ((Fintype.card I:ℝ)*eta) := hbudget
    _ < ENNReal.ofReal epsilon := (ENNReal.ofReal_lt_ofReal_iff hepsilon).mpr hsmall

end
end ImbalancedChen.Part3.Gamma0CompactWeightedTensorApproximation20261025a
