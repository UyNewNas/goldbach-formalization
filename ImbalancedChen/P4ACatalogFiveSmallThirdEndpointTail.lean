import ImbalancedChen.P4ACatalogFiveGlobalLossReduction
import ImbalancedChen.P4ACatalogFiveSmallThirdMass
import ImbalancedChen.P1ActualVariableFifthTailPointwise

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original second guard supplies a fixed physical residual gap rho/2
for both literal endpoint lower residuals when t3<rho/6. Existing generic
actual-minus bounds then pay the moving tiny part and the whole middle
part. Only their arbitrary-level arithmetic statements are reused: no
variable-fifth policy, source carrier or alternative dyadic policy is
identified with the actual catalog-five action.
-/

namespace ImbalancedChen.P4ACatalogFiveSmallThirdEndpointTail
noncomputable section
open Set Filter Topology VariableEnvelope
open scoped Classical BigOperators
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4ACatalogFiveActualPairDecomposition P4AOriginalSecondPhysicalIntegral
open P4ACatalogFiveSmallThirdMass
open P1OriginalSmallCutoffActualLowerTail P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit P1FifthMiddleNormalizedPointwise

def endpointDifference (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 1)) p -
    actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 0)) p

def quotient (N : ℕ) (p : Fin 3 → ℕ) (i : Fin 3) : ℝ :=
  (N:ℝ)^v (actualPrimeTupleLog N p i)/(∏ j, p j : ℕ)

def tupleGuard (N : ℕ) (p : Fin 3 → ℕ) : Prop :=
  secondGuard (N:ℝ) [p 2,p 1,p 0]

def tailAbsolute (N : ℕ) (h : ℝ) : ℝ :=
  ∑ p ∈ tailBox N h, (∏ i, 1/((p i:ℝ)-1)) *
    (if tupleGuard N p then |endpointDifference N p| else 0)

/-- Q's exact guard-to-original-domain dictionary supplies both first
coordinate lower bounds and the two fixed physical numerator gaps. -/
theorem guard_geometry (N : ℕ) (p : Fin 3 → ℕ) (hg : tupleGuard N p) :
    (3/16:ℝ) ≤ actualPrimeTupleLog N p 0 ∧
    (3/16:ℝ) ≤ actualPrimeTupleLog N p 1 ∧
    (19/96:ℝ) ≤ v (actualPrimeTupleLog N p 0)-actualPrimeTupleLog N p 0-actualPrimeTupleLog N p 1 ∧
    (19/96:ℝ) ≤ v (actualPrimeTupleLog N p 1)-actualPrimeTupleLog N p 0-actualPrimeTupleLog N p 1 := by
  have hr : SecondRegion (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1) := by
    simpa [tupleGuard,secondGuard,rosserAncestor,primeHistoryLogCoordinates,
      primeHistoryTuple,actualPrimeTupleLog] using hg
  obtain ⟨hx,hy⟩ := (physicalDomain_iff _ _).mp ((secondRegion_iff_catalog_domain _ _).mp hr)
  have hb := physical_denominator_bounds ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩
  refine ⟨?_,hb.2.1,?_,?_⟩
  · have hm : (3/16:ℝ) ≤ Certificates.AboveMuSecondCoarse.mu := by norm_num [Certificates.AboveMuSecondCoarse.mu]
    exact hm.trans hb.1
  · simpa only [v_eq_catalog_endpoint] using hb.2.2.1
  · simpa only [v_eq_catalog_endpoint] using hb.2.2.2

theorem tail_physical_gaps (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < p i) (hg : tupleGuard N p)
    (hz : actualPrimeTupleLog N p 2 < (19/96:ℝ)/6) :
    (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 0) ∧
    (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 1) ∧
    (N:ℝ)^((19/96:ℝ)/2) ≤ quotient N p 0 ∧
    (N:ℝ)^((19/96:ℝ)/2) ≤ quotient N p 1 := by
  obtain ⟨_,_,ho,hn⟩ := guard_geometry N p hg
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hP : (0:ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hlevel (i : Fin 3) : quotient N p i =
      (N:ℝ)^(v (actualPrimeTupleLog N p i)-∑ j, actualPrimeTupleLog N p j) := by
    rw [actualPrimeTupleLog_sum_prod p hpos]
    exact (residual_rpow_level_div (N:ℝ) (∏ i, p i : ℕ)
      (v (actualPrimeTupleLog N p i)) hNr hP).symm
  refine ⟨?_,?_,?_,?_⟩
  · apply (actualPrimeTupleOwnCube_iff hN p hpos _).mpr
    simp only [primeTupleOwnCubeForm,Fin.sum_univ_three]
    change actualPrimeTupleLog N p 0+actualPrimeTupleLog N p 1+actualPrimeTupleLog N p 2+
      2*actualPrimeTupleLog N p 2 < _
    linarith
  · apply (actualPrimeTupleOwnCube_iff hN p hpos _).mpr
    simp only [primeTupleOwnCubeForm,Fin.sum_univ_three]
    change actualPrimeTupleLog N p 0+actualPrimeTupleLog N p 1+actualPrimeTupleLog N p 2+
      2*actualPrimeTupleLog N p 2 < _
    linarith
  · rw [hlevel]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    rw [Fin.sum_univ_three]
    linarith
  · rw [hlevel]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    rw [Fin.sum_univ_three]
    linarith

theorem endpointDifference_eq_actual (N : ℕ) (p : Fin 3 → ℕ)
    (ho : (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 0))
    (hn : (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 1)) :
    endpointDifference N p =
      (actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 1)-
        actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 0))*Real.log (N:ℝ)/singularSeries N := by
  unfold endpointDifference actualPrimeTupleOwnCubeMinus quotient
  change (if (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 1) then _ else 0)-
    (if (∏ i, p i : ℕ)*(p 2:ℝ)^2 < (N:ℝ)^v (actualPrimeTupleLog N p 0) then _ else 0) = _
  rw [if_pos hn,if_pos ho]
  ring

/-- Both constants and the moving-scale threshold precede h and every
tuple. The complete actual lower deficits are bounded, not just their
explicit asymptotic error. -/
theorem exists_eventually_endpointDifference_tail_bound :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      1 < N ∧ ∀ h : ℝ, h ≤ (19/96:ℝ)/6 → Even N →
      ∀ p ∈ tailBox N h, tupleGuard N p →
        |endpointDifference N p| ≤
          A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N)+
            B*(actualPrimeTupleLog N p 2)^2 := by
  obtain ⟨A0,B0,K,hA0,hB0,_hK,hsource⟩ := exists_actualMinus_pair_exp_bound
  obtain ⟨C,hC,hmiddle⟩ := exists_eventually_actualMinus_middle_quadratic_bound
  let A := 2*(A0+B0*Real.exp (Real.sqrt K))
  let B := C/(19/96:ℝ)^3
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A,B,hA,hB,?_⟩
  filter_upwards [eventually_moving_scale_budgets (19/96:ℝ) (by norm_num),
    hmiddle (19/96:ℝ) (by norm_num)] with N hb hmid
  obtain ⟨hN,_,_,hT,haT,hbudget,hlog⟩ := hb
  have hN1 : 1 < N := by omega
  have hNr : (1:ℝ) < N := by exact_mod_cast hN1
  refine ⟨hN1,?_⟩
  intro h hh hEven p hp hg
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht := (mem_actualPrimeBoxTuples_log_iff hN1 lower (upper h) p).mp hp
  have hz : actualPrimeTupleLog N p 2 < h := by
    simpa [upper] using (mem_logPrimeBox.mp ht.2 2).2
  obtain ⟨hgo,hgn,hRo,hRn⟩ := tail_physical_gaps N hN1 p hpos hg (hz.trans_le hh)
  have hy : (1:ℝ) < p 2 := by exact_mod_cast (hpi 2).1.one_lt
  have hcap : (p 2:ℝ) ≤ N := by
    have hph : (p 2:ℝ) < (N:ℝ)^h := by simpa [upper] using (hpi 2).2.2.2
    exact hph.le.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith : h ≤ 1))
  by_cases hsmall : actualPrimeTupleLog N p 2 < movingCutoff (19/96:ℝ) N
  · have hcut : (p 2:ℝ) ≤ (N:ℝ)^movingCutoff (19/96:ℝ) N := by
      rw [← actualPrimeTupleLog_rpow hN1 p hpos 2]
      exact Real.rpow_le_rpow_of_exponent_le hNr.le hsmall.le
    have ho := P1ActualVariableFifthTailPointwise.sourceBudget_of_power_cutoff N hN1
      (19/96:ℝ) (movingCutoff (19/96:ℝ) N) (movingBudget N) (p 2:ℝ) (quotient N p 0)
      (Nat.cast_nonneg _) hcut hRo hT haT hbudget hlog
    have hn := P1ActualVariableFifthTailPointwise.sourceBudget_of_power_cutoff N hN1
      (19/96:ℝ) (movingCutoff (19/96:ℝ) N) (movingBudget N) (p 2:ℝ) (quotient N p 1)
      (Nat.cast_nonneg _) hcut hRn hT haT hbudget hlog
    have hypow : (p 2:ℝ) ≤ (p 2:ℝ)^movingBudget N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy.le (by linarith : 1 ≤ movingBudget N)
    have hpair := hsource N N hEven (p 2:ℝ) (quotient N p 0) (quotient N p 1)
      (movingBudget N) (movingBudget N) hcap hy
      (hypow.trans ho.2.1) (hypow.trans hn.2.1) ho.1 hn.1 ho.2.1 hn.2.1
      ho.2.2.1 hn.2.2.1 ho.2.2.2 hn.2.2.2
    have he : (1:ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0:ℝ) ≤ 1)
    have hto := tailEnvelope_le_uniform_exp A0 B0 K (quotient N p 0)
      (movingBudget N) (movingBudget N) hA0.le hB0.le le_rfl (he.trans ho.2.2.2)
    have htn := tailEnvelope_le_uniform_exp A0 B0 K (quotient N p 1)
      (movingBudget N) (movingBudget N) hA0.le hB0.le le_rfl (he.trans hn.2.2.2)
    have hraw : |actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 1)-
        actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 0)| ≤ A*Real.exp (-movingBudget N) := by
      calc
        _ ≤ actualSmallEulerProduct N N (p 2:ℝ) *
            (tailEnvelope A0 B0 K (quotient N p 0) (movingBudget N)+
              tailEnvelope A0 B0 K (quotient N p 1) (movingBudget N)) := hpair
        _ ≤ actualSmallEulerProduct N N (p 2:ℝ) * (A*Real.exp (-movingBudget N)) := by
          apply mul_le_mul_of_nonneg_left _ (actualSmallEulerProduct_pos N N _ hEven).le
          dsimp [A]
          linarith
        _ ≤ 1*(A*Real.exp (-movingBudget N)) :=
          mul_le_mul_of_nonneg_right (actualSmallEulerProduct_le_one N N _) (by positivity)
        _ = _ := one_mul _
    rw [endpointDifference_eq_actual N p hgo hgn,mul_div_assoc,abs_mul]
    have hnrm := mul_le_mul_of_nonneg_right hraw (abs_nonneg (Real.log (N:ℝ)/singularSeries N))
    have hq : 0 ≤ B*(actualPrimeTupleLog N p 2)^2 := mul_nonneg hB.le (sq_nonneg _)
    nlinarith only [hnrm,hq]
  · have hbound := hmid N hEven (p 2:ℝ) (quotient N p 0) (quotient N p 1) h
      (by exact_mod_cast hpos 2) hcap hh (le_of_not_gt hsmall) hz hRo hRn
    rw [endpointDifference_eq_actual N p hgo hgn]
    change |(actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 1)-
      actualSmallRosserMinusDensity N N (p 2:ℝ) (quotient N p 0))*Real.log (N:ℝ)/singularSeries N| ≤ _
    have hE : 0 ≤ A*|Real.log (N:ℝ)/singularSeries N|*Real.exp (-movingBudget N) := by positivity
    change _ ≤ B*(actualPrimeTupleLog N p 2)^2 at hbound
    linarith

end
end ImbalancedChen.P4ACatalogFiveSmallThirdEndpointTail
