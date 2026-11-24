import ImbalancedChen.P4AOrderedThirdArithmeticCells
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.P4AOrderedThirdFifthOwnersAndTail

namespace ImbalancedChen.P4AOrderedThirdFixedOmegaLimit
noncomputable section
open Set Filter Topology MeasureTheory HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (gateForms gateBounds gateForms_ne_zero)
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87RawChronology (rawRoot)
open P4ACatalogFiveCoarseWeightedPayment (weight)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalHistoricalThirdOccurrence (base primes)
open P4AOriginalHistoricalThirdMajorant (boxRegion ordered)
open P4AOriginalOrderedThirdTable (Point retained capValue)
open P4AOrderedThirdArithmeticOccurrence (fresh region localDiff)
open scoped Classical BigOperators

abbrev evenFilter : Filter ℕ := atTop ⊓ Filter.principal {N : ℕ | 0<N ∧ Even N}

def integralOnCell {m : ℕ} (w lam : ℝ) (j : Cell m) : ℝ :=
  ∫ t in boxRegion w ∩ region j,primeTupleMinusProfile lam t*∏ i,1/t i

def functional (e : ℝ) (m : ℕ) (w : ℝ) : ℝ :=
  ∑ j∈retained e m, integralOnCell w (initial e) j-integralOnCell w (capValue e m j) j

theorem test_limit {m : ℕ} (j : Cell m) {w : ℝ} (hw : 0<w) (hw' : w<thirdPrefixRho)
    (lam : ℝ) :
    Tendsto (fun N => actualPrimeBoxTestSum N (fun _ : Fin 3 => w) (fun _ => thirdPrefixRho)
      ((region j).indicator (primeTupleMinusProfile lam))) atTop (𝓝 (integralOnCell w lam j)) := by
  let lo := logPrimeMeshLo 0 (19/96) m j
  let hi := logPrimeMeshHi 0 (19/96) m j
  let c := gateBounds 2 2
  have hlo : primeAffineGateRegion (primeIcoBoxGateForms gateForms) (primeIcoBoxGateBounds lo hi c)
      ⊆ region j := by
    intro t ht
    obtain ⟨hbox,hg⟩ := (mem_primeIcoBoxStrictGateRegion lo hi gateForms c t).mp ht
    exact ⟨mem_logPrimeBox.mpr (fun i => ⟨(hbox i).1.le,(hbox i).2⟩),hg⟩
  have hhi : ∀ t∈region j,∀ i,primeIcoBoxGateForms gateForms i t≤primeIcoBoxGateBounds lo hi c i := by
    intro t ht
    simp only [primeIcoBoxGateForms,primeIcoBoxGateBounds,Fin.forall_fin_add,Fin.append_left,
      Fin.append_right,neg_apply,ContinuousLinearMap.proj_apply,neg_le_neg_iff]
    exact ⟨fun i => (mem_logPrimeMeshCell.mp ht.1 i).1,fun i => (mem_logPrimeMeshCell.mp ht.1 i).2.le,
      fun i => (ht.2 i).le⟩
  exact tendsto_actualPrimeBoxTestSum_cube_affineSandwich hw hw' (primeIcoBoxGateForms gateForms)
    (primeIcoBoxGateBounds lo hi c) (primeIcoBoxGateForms_ne_zero _ gateForms_ne_zero) (region j)
    ((measurableSet_logPrimeMeshCell _ _ _ _).inter (measurableSet_primeAffineGateRegion _ _))
    hlo hhi _ (continuousOn_primeTupleMinusProfile hw lam)

theorem actual_limit {m : ℕ} (j : Cell m) {w : ℝ} (hw : 0<w) (hw' : w<thirdPrefixRho)
    (lam : ℝ) :
    Tendsto (fun N => actualPrimeBoxOwnCubeMinusSum 2 N N w thirdPrefixRho lam (region j))
      evenFilter (𝓝 (integralOnCell w lam j)) := by
  have hN : ∀ᶠ N : ℕ in evenFilter,1<N := (eventually_ge_atTop 2).filter_mono inf_le_left
  have hc : ∀ᶠ N : ℕ in evenFilter,(N:ℝ)^thirdPrefixRho≤N := hN.mono (fun N hn =>
    P4AOriginalFull87JointPhysicalBudget.cutoff_le_target N (by exact_mod_cast hn.le))
  have herror := tendsto_actualPrimeBoxOwnCubeMinus_error 2 w thirdPrefixRho lam hw hw' (region j) id hc
  have hlim := (test_limit j hw hw' lam).mono_left (show evenFilter≤atTop from inf_le_left)
  have hh := herror.add hlim
  rw [zero_add] at hh
  apply hh.congr'
  filter_upwards [hN] with N hn
  have heq : actualPrimeBoxTestSum N (fun _ : Fin 3 => w) (fun _ => thirdPrefixRho)
      (fun t => if t∈region j then (if primeTupleOwnCubeForm t < lam then primeTupleMinusProfile lam t else 0) else 0)
        =actualPrimeBoxTestSum N (fun _ : Fin 3 => w) (fun _ => thirdPrefixRho)
          ((region j).indicator (primeTupleMinusProfile lam)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hb := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hn _ _ p).mp hp).2
    rw [primeTupleMinusProfile_ownCube_gate _ _ (hw.trans_le (hb 2).1)]
    rfl
  dsimp only [id_eq,Pi.add_apply] at ⊢
  rw [heq,sub_add_cancel]

theorem cell_limit (d : OriginalData) (j : Cell d.m) {w : ℝ} (hw : 0<w) (hw' : w<thirdPrefixRho) :
    Tendsto (fun N => ∑ p∈primes w N,(∏ i,weight (p i))*localDiff d N j p)
      evenFilter (𝓝 (integralOnCell w (initial (d.e:ℝ)) j-integralOnCell w (capValue (d.e:ℝ) d.m j) j)) := by
  apply ((actual_limit j hw hw' (initial (d.e:ℝ))).sub (actual_limit j hw hw' (capValue (d.e:ℝ) d.m j))).congr
  intro N
  simp only [actualPrimeBoxOwnCubeMinusSum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hr : actualPrimeTupleLog N p∈region j <;> simp [localDiff,hr,weight,mul_sub]

/-- The normalized ordinary third-root change on the actual target-deleted carrier
tends, at the fixed physical rough cutoff, to the entire corrected-cell integral.
The precomputed cutoff d.omega does not enter the new third policy. -/
theorem root_limit (d : OriginalData) {w : ℝ} (hw : 0<w) (hw' : w<thirdPrefixRho)
    (he : 0<(d.e:ℝ)) (hsmall : (d.e:ℝ)≤1/384)
    (hstep : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) :
    Tendsto (fun N => normalize N (rawRoot (fresh d w N) N-rawRoot (base d N) N))
      evenFilter (𝓝 (functional (d.e:ℝ) d.m w)) := by
  have hh := tendsto_finsetSum (retained (d.e:ℝ) d.m) (fun j _ => cell_limit d j hw hw')
  apply hh.congr'
  filter_upwards [(eventually_ge_atTop 2).filter_mono (show evenFilter≤atTop from inf_le_left)] with N hn
  exact (P4AOrderedThirdArithmeticCells.source_cells d w he hsmall hstep hn).symm

end
end ImbalancedChen.P4AOrderedThirdFixedOmegaLimit

