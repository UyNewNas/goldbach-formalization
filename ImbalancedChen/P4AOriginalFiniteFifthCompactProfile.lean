import ImbalancedChen.P1VariableOwnCubeResidualUniformity
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Minimal compact cap-parameter adaptation of the existing genuine
lower-factor continuity and actual own-cube residual suppliers.
All strict own-cube endpoints, the actual density and normalization are
retained. This does not supply the full weighted frontier or its tail.
-/
namespace ImbalancedChen.P4AOriginalFiniteFifthCompactProfile
noncomputable section
open Set Filter Topology
open MathlibNt.SieveTheory
open scoped Classical BigOperators

def gatedProfile {k : ℕ} (lam : ℝ) (t : Fin (k + 1) → ℝ) : ℝ :=
  if primeTupleOwnCubeForm t < lam then primeTupleMinusProfile lam t else 0

theorem profile_eq_lowerFactor {k : ℕ} (lam : ℝ) (t : Fin (k + 1) → ℝ)
    (hz : 0 < t (Fin.last k)) :
    primeTupleMinusProfile lam t =
      4 * actualExtendedThirdLowerFactor ((lam - ∑ i, t i) / t (Fin.last k)) /
        t (Fin.last k) := by
  unfold primeTupleMinusProfile actualExtendedThirdLowerFactor thirdTailLowerFactor
  rw [Real.exp_neg]
  field_simp [hz.ne', (Real.exp_pos Real.eulerMascheroniConstant).ne']; ring

/-- The continuous limiting profile retains the exact strict gate, including equality. -/
theorem gatedProfile_eq {k : ℕ} (lam : ℝ) (t : Fin (k + 1) → ℝ)
    (hz : 0 < t (Fin.last k)) : gatedProfile lam t = primeTupleMinusProfile lam t := by
  unfold gatedProfile
  split_ifs with hg
  · rfl
  · have hlin := le_of_not_gt hg
    change lam ≤ (∑ i, t i) + 2 * t (Fin.last k) at hlin
    have hratio : (lam - ∑ i, t i) / t (Fin.last k) ≤ 2 :=
      (div_le_iff₀ hz).mpr (by linarith only [hlin])
    rw [profile_eq_lowerFactor lam t hz,
      actualExtendedThirdLowerFactor_of_le_two hratio, mul_zero, zero_div]

/-- Monotonicity of the limiting profile, without monotonicity of finite lower weights. -/
theorem gatedProfile_mono {k : ℕ} (t : Fin (k + 1) → ℝ)
    (hz : 0 < t (Fin.last k)) : Monotone (fun lam : ℝ => gatedProfile lam t) := by
  intro a b hab
  change gatedProfile a t ≤ gatedProfile b t
  rw [gatedProfile_eq a t hz, gatedProfile_eq b t hz,
    profile_eq_lowerFactor a t hz, profile_eq_lowerFactor b t hz]
  apply div_le_div_of_nonneg_right _ hz.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply monotone_actualExtendedThirdLowerFactor
  exact div_le_div_of_nonneg_right (sub_le_sub_right hab _) hz.le

/-- Existing canonical-factor continuity is joint in cap and tuple. -/
theorem joint_continuousOn (k : ℕ) (a b lower upper : ℝ) (ha : 0 < a) :
    ContinuousOn (fun q : ℝ × (Fin (k + 1) → ℝ) => primeTupleMinusProfile q.1 q.2)
      (Icc lower upper ×ˢ univ.pi (fun _ => Icc a b)) := by
  let C : Set (ℝ × (Fin (k + 1) → ℝ)) :=
    Icc lower upper ×ˢ univ.pi (fun _ => Icc a b)
  have hlast : Continuous (fun q : ℝ × (Fin (k + 1) → ℝ) => q.2 (Fin.last k)) := by
    fun_prop
  have hsum : Continuous (fun q : ℝ × (Fin (k + 1) → ℝ) => ∑ i, q.2 i) := by
    fun_prop
  have hne : ∀ q ∈ C, q.2 (Fin.last k) ≠ 0 :=
    fun q hq => (ha.trans_le (hq.2 _ (mem_univ _)).1).ne'
  have harg : ContinuousOn (fun q : ℝ × (Fin (k + 1) → ℝ) =>
      max 2 ((q.1 - ∑ i, q.2 i) / q.2 (Fin.last k))) C :=
    continuousOn_const.sup ((continuous_fst.continuousOn.sub hsum.continuousOn).div
      hlast.continuousOn hne)
  change ContinuousOn (fun q : ℝ × (Fin (k + 1) → ℝ) =>
    (2 * Real.exp (-Real.eulerMascheroniConstant) / q.2 (Fin.last k)) *
      suzukiContinuousLowerFactor (max 2 ((q.1 - ∑ i, q.2 i) / q.2 (Fin.last k)))) C
  exact (continuousOn_const.div hlast.continuousOn hne).mul
    (continuousOn_suzukiContinuousLowerFactor.comp harg
      (fun q _ => le_max_left (2 : ℝ) ((q.1 - ∑ i, q.2 i) / q.2 (Fin.last k))))

/-- One compact modulus covers every real cap, tuple and row wall. -/
theorem exists_gatedProfile_cap_modulus (k : ℕ) (a b lower upper eta : ℝ)
    (ha : 0 < a) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ lam L : ℝ,
      lam ∈ Icc lower upper → L ∈ Icc lower upper → |lam - L| ≤ delta →
      ∀ t : Fin (k + 1) → ℝ, (∀ i, a ≤ t i ∧ t i ≤ b) →
        |gatedProfile lam t - gatedProfile L t| ≤ eta := by
  let C : Set (ℝ × (Fin (k + 1) → ℝ)) :=
    Icc lower upper ×ˢ univ.pi (fun _ => Icc a b)
  have hC : IsCompact C := isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have huc : UniformContinuousOn
      (fun q : ℝ × (Fin (k + 1) → ℝ) => primeTupleMinusProfile q.1 q.2) C :=
    hC.uniformContinuousOn_of_continuous (joint_continuousOn k a b lower upper ha)
  obtain ⟨delta, hd, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc eta heta
  refine ⟨delta / 2, half_pos hd, ?_⟩
  intro lam L hlam hL hcap t ht
  have hmem : t ∈ univ.pi (fun _ : Fin (k + 1) => Icc a b) := fun i _ => ht i
  have hdist : dist (lam, t) (L, t) < delta := by
    rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist lam L), Real.dist_eq]
    exact hcap.trans_lt (half_lt_self hd)
  have hb := hclose (lam, t) ⟨hlam, hmem⟩ (L, t) ⟨hL, hmem⟩ hdist
  rw [Real.dist_eq] at hb
  rw [gatedProfile_eq lam t (ha.trans_le (ht _).1),
    gatedProfile_eq L t (ha.trans_le (ht _).1)]
  exact hb.le

/-- The modulus and arithmetic threshold precede all real levels and all
finite policies. Both literal strict arithmetic gates are preserved. -/
theorem exists_actual_levels_close_threshold
    (k : ℕ) (a b lower upper eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ) ^ b ≤ (cap : ℝ) →
      ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
      ∀ lam L : ℝ, lam ∈ Icc lower upper → L ∈ Icc lower upper →
        |lam - L| ≤ delta →
        |actualPrimeTupleOwnCubeMinus N cap lam p -
          actualPrimeTupleOwnCubeMinus N cap L p| < eta := by
  have heta3 : 0 < eta / 3 := by positivity
  obtain ⟨delta, hd, hmod⟩ :=
    exists_gatedProfile_cap_modulus k a b lower upper (eta / 3) ha heta3
  obtain ⟨N0, hN0, hactual⟩ :=
    P1VariableOwnCubeResidualUniformity.exists_actualPrimeTupleOwnCubeMinus_uniform_levels_threshold
      k a b lower upper ha (eta / 3) heta3
  refine ⟨delta, hd, N0, hN0, ?_⟩
  intro N hN hEven cap hcap p hp lam L hlam hL hclose
  have hN1 : 1 < N := by omega
  have ht := ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2
  have hcoords : ∀ i, a ≤ actualPrimeTupleLog N p i ∧ actualPrimeTupleLog N p i ≤ b :=
    fun i => ⟨(mem_logPrimeBox.mp ht i).1, (mem_logPrimeBox.mp ht i).2.le⟩
  have ho := hactual N hN hEven cap hcap p hp lam hlam
  have hn := hactual N hN hEven cap hcap p hp L hL
  change |actualPrimeTupleOwnCubeMinus N cap lam p -
    gatedProfile lam (actualPrimeTupleLog N p)| < eta / 3 at ho
  change |actualPrimeTupleOwnCubeMinus N cap L p -
    gatedProfile L (actualPrimeTupleLog N p)| < eta / 3 at hn
  have hm := hmod lam L hlam hL hclose (actualPrimeTupleLog N p) hcoords
  have htri1 := abs_sub_le (actualPrimeTupleOwnCubeMinus N cap lam p)
    (gatedProfile lam (actualPrimeTupleLog N p)) (actualPrimeTupleOwnCubeMinus N cap L p)
  have htri2 := abs_sub_le (gatedProfile lam (actualPrimeTupleLog N p))
    (gatedProfile L (actualPrimeTupleLog N p)) (actualPrimeTupleOwnCubeMinus N cap L p)
  rw [abs_sub_comm (gatedProfile L (actualPrimeTupleLog N p))] at htri2
  linarith only [ho, hn, hm, htri1, htri2]

end
end ImbalancedChen.P4AOriginalFiniteFifthCompactProfile
