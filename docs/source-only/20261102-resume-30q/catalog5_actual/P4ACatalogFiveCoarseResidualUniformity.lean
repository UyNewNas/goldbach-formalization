import ImbalancedChen.P4ACatalogFiveActualPairDecomposition
import ImbalancedChen.ActualExtendedThirdCompactResidualProfile
import ImbalancedChen.ActualExtendedThirdCompactKernelApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine, uniform rawLevel-to-v(x) supplier on the ACTUAL selected coarse
third histories, at any fixed positive last-prime cutoff.  Old-rejected and
old-retained thirds are handled by the same strict own-cube-gated density.
The canonical lower factor is zero at s=2, so the change in this gate needs
no invented discarded cube wall.  The actual old first cube is supplied
from the selected historical cell.

Only the analytic modulus theorem for the canonical lower factor is reused
from the dyadic extended-third work. Its dyadic policy, retained region and
finite lookup are not used. This is a compact summand estimate; its final
weighted sum, the order strips and the small-third tail remain unpaid.
-/

namespace ImbalancedChen.P4ACatalogFiveCoarseResidualUniformity
noncomputable section
open Set Filter Topology VariableEnvelope HistoricalThirdCoarse
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonThirdScreenedSource
open P5OriginalCommonFourthSourceNavigation
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

private def residualWindow (h : ℝ) : Set (ℝ × ℝ) :=
  {q | h ≤ q.2 ∧ q.2 ≤ (19 / 96 : ℝ) ∧ 2 * q.2 ≤ q.1 ∧ q.1 ≤ thirdPrefixTheta}

private theorem compact_residualWindow (h : ℝ) (hh : 0 < h) :
    IsCompact (residualWindow h) := by
  have hc : IsClosed (residualWindow h) :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_const).inter
        ((isClosed_le (by fun_prop) continuous_fst).inter
          (isClosed_le continuous_fst continuous_const)))
  apply (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (0 : ℝ) thirdPrefixTheta ×ˢ Icc h (19 / 96 : ℝ))).of_isClosed_subset hc
  intro q hq
  exact ⟨⟨by linarith [hq.1,hq.2.2.1],hq.2.2.2⟩,⟨hq.1,hq.2.1⟩⟩

/-- One N0 covers EVERY real cap below Theta, including caps that depend on
the actual finite history. A fixed-lambda theorem alone cannot supply this. -/
theorem exists_all_caps_ownCube_uniform_threshold (h eta : ℝ)
    (hh : 0 < h) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19 / 96 : ℝ)),
      ∀ lam : ℝ, lam ≤ thirdPrefixTheta →
        |actualPrimeTupleOwnCubeMinus N cap lam p -
          primeTupleMinusProfile lam (actualPrimeTupleLog N p)| < eta := by
  have hparam : ∀ q ∈ residualWindow h, 0 < q.2 ∧ 2 * q.2 ≤ q.1 :=
    fun q hq => ⟨hh.trans_le hq.1,hq.2.2.1⟩
  obtain ⟨N0,hN0,hbound⟩ :=
    exists_actualSmallRosserMinusDensity_quotient_compact_normalized_threshold
      (residualWindow h) (compact_residualWindow h hh) hparam eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven cap hcap p hp lam hlam
  have hN1 : 1 < N := by omega
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
  have hcoords (i : Fin 3) : h ≤ actualPrimeTupleLog N p i ∧
      actualPrimeTupleLog N p i < (19 / 96 : ℝ) := mem_logPrimeBox.mp ht i
  have hz : 0 < actualPrimeTupleLog N p 2 := hh.trans_le (hcoords 2).1
  have hsum : 0 ≤ ∑ i, actualPrimeTupleLog N p i :=
    Finset.sum_nonneg (fun i _ => (hh.trans_le (hcoords i).1).le)
  have hdict := actualPrimeTupleOwnCube_iff hN1 p hpos lam
  by_cases hg : primeTupleOwnCubeForm (actualPrimeTupleLog N p) < lam
  · have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
      exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p 2 := by exact_mod_cast hpos 2
    have hparams : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
        (p 2 : ℝ) lam = (lam - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p 2) := by
      unfold actualRosserQuotientParameters
      rw [actualPrimeTupleLog_sum_prod p hpos]
      rfl
    have hmem : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ)
        (p 2 : ℝ) lam ∈ residualWindow h := by
      rw [hparams]
      refine ⟨(hcoords 2).1,(hcoords 2).2.le,?_,by linarith⟩
      change (∑ i, actualPrimeTupleLog N p i) + 2 * actualPrimeTupleLog N p 2 < lam at hg
      linarith
    have hb := hbound N hN hEven _ _ lam hP hy hmem cap
      ((hpi 2).2.2.2.le.trans hcap)
    rw [actualPrimeTupleOwnCubeMinus, if_pos (hdict.mpr hg),
      primeTupleMinusProfile_of_ownCube hz hg.le]
    simpa only [hparams] using hb
  · have hzprofile : primeTupleMinusProfile lam (actualPrimeTupleLog N p) = 0 := by
      have hhgate := primeTupleMinusProfile_ownCube_gate lam (actualPrimeTupleLog N p) hz
      simpa only [if_neg hg] using hhgate.symm
    simp only [actualPrimeTupleOwnCubeMinus, if_neg (mt hdict.mp hg),
      hzprofile, sub_self, abs_zero]
    exact heta

/-- The existing canonical-factor modulus is applied to arbitrary real
caps, not to its separate dyadic finite policy. -/
theorem exists_actual_profile_cap_modulus (h eta : ℝ) (hh : 0 < h) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ lam L : ℝ,
      lam ≤ thirdPrefixTheta → L ≤ thirdPrefixTheta → |lam-L| ≤ delta →
      ∀ t : Fin 3 → ℝ, (∀ i, h ≤ t i ∧ t i ≤ (19 / 96 : ℝ)) →
        |primeTupleMinusProfile lam t - primeTupleMinusProfile L t| ≤ eta := by
  obtain ⟨delta,hd,hmod⟩ := actualExtendedThirdCapKernel_uniform_approx hh heta
  refine ⟨delta,hd,?_⟩
  intro lam L hlam hL hclose t ht
  have hx : 0 < t 0 := hh.trans_le (ht 0).1
  have hy : 0 < t 1 := hh.trans_le (ht 1).1
  have hz : 0 < t 2 := hh.trans_le (ht 2).1
  have hb := hmod 0 lam L (t 0) (t 1) (t 2) (by norm_num) (by linarith)
    hlam hL hclose (ht 0).1 (ht 1).1 (ht 2).1
  have hmul : 0 ≤ t 0 * t 1 * t 2 := by positivity
  have hle (i : Fin 3) : t i ≤ 1 := (ht i).2.trans (by norm_num)
  have hxy : t 0 * t 1 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (hle 0) (hle 1) hy.le (by norm_num : (0 : ℝ) ≤ 1)
  have hprod : t 0 * t 1 * t 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hxy (hle 2) hz.le (by norm_num : (0 : ℝ) ≤ 1)
  have hid : primeTupleMinusProfile lam t - primeTupleMinusProfile L t =
      -(actualExtendedThirdCapKernel 0 lam (t 0) (t 1) (t 2) -
        actualExtendedThirdCapKernel 0 L (t 0) (t 1) (t 2)) * (t 0 * t 1 * t 2) := by
    rw [primeTupleMinusProfile_eq_extendedThirdFactor lam t hz,
      primeTupleMinusProfile_eq_extendedThirdFactor L t hz]
    unfold actualExtendedThirdCapKernel
    field_simp [hx.ne',hy.ne',hz.ne'] <;> ring
  rw [hid,abs_mul,abs_neg,abs_of_nonneg hmul]
  calc
    _ ≤ eta * (t 0 * t 1 * t 2) := mul_le_mul_of_nonneg_right hb hmul
    _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hprod heta.le
    _ = eta := mul_one _

def rawGatedMinus (N cap : ℕ) (Q : ℝ) (p : Fin 3 → ℕ) : ℝ :=
  if (∏ i, p i : ℕ) * (p 2 : ℝ)^2 < Q then
    actualSmallRosserMinusDensity N cap (p 2 : ℝ) (Q / (∏ i, p i : ℕ)) *
      Real.log (N : ℝ) / singularSeries N
  else 0

/-- This quantified estimate is on the literal selected rawLevel and on
the original cap N. The only smallness condition is the already explicit
mesh/buffer width; no density error or convergence is assumed. -/
theorem exists_actual_coarse_rawLevel_to_endpoint_threshold (h eps : ℝ)
    (hh : 0 < h) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData,
        0 < (d.e : ℝ) → (d.e : ℝ) < (3 / 256 : ℝ) / 100 → d.chi < (d.e : ℝ) / 10 →
        (3 / 2 : ℝ) * d.chi + 2 * (d.e : ℝ) ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19 / 96 : ℝ)),
        selectedThird d (N : ℝ) [p 2,p 1,p 0] → secondGuard (N : ℝ) [p 2,p 1,p 0] →
        (p 0 : ℝ)^3 < rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) [p 2,p 1,p 0] ∧
        |rawGatedMinus N N
            (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) [p 2,p 1,p 0]) p -
          actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 0)) p| < eps := by
  have heps3 : 0 < eps / 3 := by positivity
  obtain ⟨delta,hd,hmod⟩ := exists_actual_profile_cap_modulus h (eps/3) hh heps3
  obtain ⟨N0,hN0,hbound⟩ := exists_all_caps_ownCube_uniform_threshold h (eps/3) hh heps3
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro d he hesmall hchi hwidth N hN hEven p hp hsel hg
  have hN1 : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN1
  have hpi := mem_actualPrimeBoxTuples_iff.mp hp
  have ht := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
  have hcoords : ∀ i, h ≤ actualPrimeTupleLog N p i ∧ actualPrimeTupleLog N p i ≤ (19/96:ℝ) :=
    fun i => ⟨(mem_logPrimeBox.mp ht i).1,(mem_logPrimeBox.mp ht i).2.le⟩
  have hsource : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      [p 2,p 1,p 0] := by
    simpa only [selectedThird, P1ThirdFallbackSupport.frozenSupported,
      rosserAncestor_self_of_length 3 _ (by simp)] using hsel
  obtain ⟨hrough,j,hj,hcell⟩ := (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mp hsource
  have hcube := rawLevel_first_cube_on_cell (d.e : ℝ) d.chi he hesmall hchi d.m d.omega
    (N : ℝ) hNr (p 0) (p 1) (p 2) (hpi 0).1.pos hrough j hj hcell
  refine ⟨hcube,?_⟩
  let lam := originalSeed d (N : ℝ) [p 2,p 1,p 0]
  let L := v (actualPrimeTupleLog N p 0)
  have hfirst : firstCoordinate (N : ℝ) [p 2,p 1,p 0] = actualPrimeTupleLog N p 0 := by
    simp [firstCoordinate, rosserAncestor, primeHistoryLogCoordinates, primeHistoryTuple,
      actualPrimeTupleLog]
  have hmu : mu < firstCoordinate (N : ℝ) [p 2,p 1,p 0] := by
    have hx := hg.1
    simpa [secondGuard, SecondRegion, firstCoordinate, rosserAncestor,
      primeHistoryLogCoordinates, primeHistoryTuple] using hx
  have hi := originalSeed_supported_interval d he.le (N : ℝ) [p 2,p 1,p 0]
    (by simp) hsel hmu
  rw [hfirst] at hi
  have hclose : |lam-L| ≤ delta := abs_le.mpr ⟨by dsimp [lam,L]; linarith,
    by dsimp [lam,L]; linarith⟩
  have hL : L ≤ thirdPrefixTheta := by
    have hhcap := v_le_cap (actualPrimeTupleLog N p 0)
    dsimp [L,cap,thirdPrefixTheta] at *
    linarith
  have hlam : lam ≤ thirdPrefixTheta := by dsimp [lam,L] at *; linarith
  have hcap : (N : ℝ) ^ (19/96:ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (by norm_num : (19/96:ℝ) ≤ 1)
  have ho := hbound N hN hEven N hcap p hp lam hlam
  have hn := hbound N hN hEven N hcap p hp L hL
  have hm := hmod lam L hlam hL hclose (actualPrimeTupleLog N p) hcoords
  have hraw : rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) [p 2,p 1,p 0] =
      (N : ℝ)^lam := by
    have hlev := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
      (d.e : ℝ) d.chi d.m d.omega (N : ℝ) [p 2,p 1,p 0]
    simpa [frozenLevel, rosserAncestor, lam, originalSeed] using hlev
  have hrawG : rawGatedMinus N N
      (rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) [p 2,p 1,p 0]) p =
        actualPrimeTupleOwnCubeMinus N N lam p := by
    rw [hraw]
    rfl
  rw [hrawG]
  have ht1 := abs_sub_le (actualPrimeTupleOwnCubeMinus N N lam p)
    (primeTupleMinusProfile lam (actualPrimeTupleLog N p)) (actualPrimeTupleOwnCubeMinus N N L p)
  have ht2 := abs_sub_le (primeTupleMinusProfile lam (actualPrimeTupleLog N p))
    (primeTupleMinusProfile L (actualPrimeTupleLog N p)) (actualPrimeTupleOwnCubeMinus N N L p)
  rw [abs_sub_comm (primeTupleMinusProfile L _)] at ht2
  change |actualPrimeTupleOwnCubeMinus N N lam p - actualPrimeTupleOwnCubeMinus N N L p| < eps
  linarith

end
end ImbalancedChen.P4ACatalogFiveCoarseResidualUniformity
