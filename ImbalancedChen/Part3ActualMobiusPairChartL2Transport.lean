import ImbalancedChen.Part3ActualMobiusRawJetL2Transport
import ImbalancedChen.Part3ActualMobiusMaassEquivariance

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The native complex-plane Mobius L2 transports are joined to the literal
real mobiusChart used by H1 tensor approximants.  Both sides use ordinary
unweighted real planar Lebesgue measure.  Scalar squared-L2 error has a
produced compact constant; raw real first-jet transpose-Jacobian errors
have EXACT integrated energy transport.  No raw jet is assumed to be a
weak derivative.  Weak all-test closure/covariance is a separate owner.
-/
namespace ImbalancedChen.Part3.ActualMobiusPairChartL2Transport20261026b
noncomputable section
open Set MeasureTheory Matrix
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a ActualMobiusMaassEquivariance20261025a
open ActualMobiusConformalTwoJet20261025a ActualMobiusCompactLpTransport20261026b
open ActualMobiusRawJetL2Transport20261026b

def complexSet (K : Set (ℝ × ℝ)) : Set ℂ := complexOfPair '' K

theorem complexOfPair_pair (z : ℂ) : complexOfPair (pairOfComplex z) = z := by
  apply Complex.ext <;> rfl

theorem pair_complexOfPair (p : ℝ × ℝ) : pairOfComplex (complexOfPair p) = p := rfl

theorem complexSet_eq_preimage (K : Set (ℝ × ℝ)) :
    complexSet K = Complex.measurableEquivRealProd ⁻¹' K := by
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp
  · intro hz
    exact ⟨pairOfComplex z,hz,complexOfPair_pair z⟩

theorem complexSet_isCompact {K : Set (ℝ × ℝ)} (hK : IsCompact K) : IsCompact (complexSet K) :=
  hK.image (by unfold complexOfPair; fun_prop)

theorem complexSet_positive {K : Set (ℝ × ℝ)} (hKp : ∀ p ∈ K, 0 < p.2) :
    ∀ z ∈ complexSet K, 0 < z.im := by
  rintro z ⟨p,hp,rfl⟩
  exact hKp p hp

theorem complexSet_lintegral (K : Set (ℝ × ℝ)) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in complexSet K, f z) = ∫⁻ p in K, f (complexOfPair p) := by
  rw [complexSet_eq_preimage]
  have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p => f (complexOfPair p)) K
  change (∫⁻ z in Complex.measurableEquivRealProd ⁻¹' K,
    f (complexOfPair (pairOfComplex z))) = ∫⁻ p in K, f (complexOfPair p) at h
  simpa only [complexOfPair_pair] using h

/-- Restricted real/complex coordinate equivalence preserves the literal
unweighted planar Lebesgue measures. -/
theorem memLp_complexSet_iff {K : Set (ℝ × ℝ)} {p : ℝ≥0∞} {F : ℝ × ℝ → ℂ} :
    MemLp F p ((volume : Measure (ℝ × ℝ)).restrict K) ↔
      MemLp (complexFunction F) p ((volume : Measure ℂ).restrict (complexSet K)) := by
  have hp := Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding K
  rw [← complexSet_eq_preimage] at hp
  rw [← hp.map_eq]
  exact Complex.measurableEquivRealProd.measurableEmbedding.memLp_map_measure_iff
/-- Exact pointwise join to the ACTUAL existing real rational chart. -/
theorem complexOfPair_mobiusChart (g : SL(2, ℤ)) {p : ℝ × ℝ} (hp : 0 < p.2) :
    complexOfPair (mobiusChart g p) = actualMobius g (complexOfPair p) := by
  let Z : UpperHalfPlane := ⟨complexOfPair p,hp⟩
  have h := mobiusChart_eq_actual g hp
  rw [chartLift_of_positive hp] at h
  have hcomplex : complexOfPair (mobiusChart g p) = ((g • Z : UpperHalfPlane) : ℂ) := by
    apply Complex.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  exact hcomplex.trans (actualMobius_eq_smul g Z).symm

theorem pair_actualMobius (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    pairOfComplex (actualMobius g z) = mobiusChart g (pairOfComplex z) := by
  have h := congrArg pairOfComplex (complexOfPair_mobiusChart g (p := pairOfComplex z) hz)
  simpa only [pair_complexOfPair,complexOfPair_pair] using h.symm

theorem complexSet_mobius_image (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hKp : ∀ p ∈ K, 0 < p.2) :
    actualMobius g '' complexSet K = complexSet (mobiusChart g '' K) := by
  ext z
  constructor
  · rintro ⟨w,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨mobiusChart g p,⟨p,hp,rfl⟩,complexOfPair_mobiusChart g (hKp p hp)⟩
  · rintro ⟨q,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨complexOfPair p,⟨p,hp,rfl⟩,(complexOfPair_mobiusChart g (hKp p hp)).symm⟩

/-- The exact native value-L2 composition bound in the literal real
chart used by genuine local-H1 tensor density. -/
theorem pairchart_scalar_L2_error_le (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) (F G : ℝ × ℝ → ℂ) :
    (∫⁻ p in K, ENNReal.ofReal (‖F (mobiusChart g p)-G (mobiusChart g p)‖^2)) ≤
      ENNReal.ofReal (compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)) *
        ∫⁻ q in mobiusChart g '' K, ENNReal.ofReal (‖F q-G q‖^2) := by
  have h := compact_composition_L2_error_le g (complexSet_isCompact hK)
    (complexSet_positive hKp) (complexFunction F) (complexFunction G)
  rw [complexSet_mobius_image g hKp,complexSet_lintegral,complexSet_lintegral] at h
  apply le_trans (le_of_eq ?_) h
  apply setLIntegral_congr_fun hK.measurableSet
  intro p hp
  unfold complexFunction
  rw [← complexOfPair_mobiusChart g (hKp p hp),pair_complexOfPair]

/-- Native Lp integrability is also transported in the literal real chart. -/
theorem pairchart_memLp_comp (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) {p : ℝ≥0∞} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F p ((volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K))) :
    MemLp (fun q => F (mobiusChart g q)) p ((volume : Measure (ℝ × ℝ)).restrict K) := by
  have hFc := memLp_complexSet_iff.mp hF
  rw [← complexSet_mobius_image g hKp] at hFc
  have hcomp := memLp_comp_actualMobius g (complexSet_isCompact hK) (complexSet_positive hKp) hFc
  apply memLp_complexSet_iff.mpr
  apply hcomp.ae_eq
  filter_upwards [ae_restrict_mem (complexSet_isCompact hK).measurableSet] with z hz
  unfold complexFunction
  rw [pair_actualMobius g (complexSet_positive hKp z hz)]
def pairRawJetX (g : SL(2, ℤ)) (U V : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (factor g (complexOfPair p)).re • U (mobiusChart g p)+
    (factor g (complexOfPair p)).im • V (mobiusChart g p)

def pairRawJetY (g : SL(2, ℤ)) (U V : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (-(factor g (complexOfPair p)).im) • U (mobiusChart g p)+
    (factor g (complexOfPair p)).re • V (mobiusChart g p)

/-- The literal two real-coordinate raw first-jet energy is transported
exactly, with no assumed weak-gradient or covariance identity. -/
theorem pairchart_rawJet_L2_energy (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) (U V : ℝ × ℝ → ℂ) :
    (∫⁻ p in K, ENNReal.ofReal (‖pairRawJetX g U V p‖^2+‖pairRawJetY g U V p‖^2)) =
      ∫⁻ q in mobiusChart g '' K, ENNReal.ofReal (‖U q‖^2+‖V q‖^2) := by
  have h := rawJet_lintegral_norm_sq g (complexSet_isCompact hK).measurableSet
    (complexSet_positive hKp) (complexFunction U) (complexFunction V)
  rw [complexSet_mobius_image g hKp,complexSet_lintegral,complexSet_lintegral] at h
  calc
    _ = ∫⁻ p in K, ENNReal.ofReal
        (‖rawJetX g (complexFunction U) (complexFunction V) (complexOfPair p)‖^2+
          ‖rawJetY g (complexFunction U) (complexFunction V) (complexOfPair p)‖^2) := by
      apply setLIntegral_congr_fun hK.measurableSet
      intro p hp
      unfold pairRawJetX pairRawJetY rawJetX rawJetY complexFunction
      rw [← complexOfPair_mobiusChart g (hKp p hp),pair_complexOfPair]
    _ = _ := by simpa only [complexFunction,pair_complexOfPair] using h

/-- Both literal real-coordinate transformed raw jets have derived L2
integrability; there is no transported-gradient structure input. -/
theorem pairchart_rawJet_memLp (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) {U V : ℝ × ℝ → ℂ}
    (hU : MemLp U 2 ((volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K)))
    (hV : MemLp V 2 ((volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K))) :
    MemLp (pairRawJetX g U V) 2 ((volume : Measure (ℝ × ℝ)).restrict K) ∧
      MemLp (pairRawJetY g U V) 2 ((volume : Measure (ℝ × ℝ)).restrict K) := by
  have hUc := memLp_complexSet_iff.mp hU
  have hVc := memLp_complexSet_iff.mp hV
  rw [← complexSet_mobius_image g hKp] at hUc hVc
  obtain ⟨hX,hY⟩ := rawJet_memLp g (complexSet_isCompact hK) (complexSet_positive hKp) hUc hVc
  constructor
  · apply memLp_complexSet_iff.mpr
    apply hX.ae_eq
    filter_upwards [ae_restrict_mem (complexSet_isCompact hK).measurableSet] with z hz
    unfold rawJetX complexFunction pairRawJetX
    rw [pair_actualMobius g (complexSet_positive hKp z hz),complexOfPair_pair]
  · apply memLp_complexSet_iff.mpr
    apply hY.ae_eq
    filter_upwards [ae_restrict_mem (complexSet_isCompact hK).measurableSet] with z hz
    unfold rawJetY complexFunction pairRawJetY
    rw [pair_actualMobius g (complexSet_positive hKp z hz),complexOfPair_pair]

end
end ImbalancedChen.Part3.ActualMobiusPairChartL2Transport20261026b
