import ImbalancedChen.Part3ActualMarkedSpectralMajorants
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Absolute convergence of both marked spectral terms for the
literal period-64 test. Measurability of the complex covariance
follows from the compact physical packets before the cutoffs are removed. -/
namespace ImbalancedChen.Part3.OriginalPrescribedSpectralConvergence20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedTraceWeights20261112 ActualMarkedSpectralMajorants20261112
open ActualUnitBandMellinProbe20261112 ActualUnitBandHeightSeeds20261112
open ActualCuspBasisWhittakerCoefficients20261102 ActualFullCuspEigenbasis20261026b
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110
open ActualCriticalCuspEvaluation20261110 ActualContinuousClassFourier20261110
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110
open OriginalContinuousClassRemoval20261110 OriginalNativeCuspFunctionals20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open ActualOppositeBesselTransform20261112 OriginalOppositeMarkedKuznetsov20261112
open OriginalMarkedArithmeticTrace20261112
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private regular_density from ImbalancedChen.Part3OriginalMarkedArithmeticTrace

private theorem covariance_measurable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue≠0) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    AEStronglyMeasurable (fun t => nativeProduct z.val
      (fun a => M J j ell (fun h => nativeR a false h t))
      (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))) volume := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let X := fun t (a : Parameters z.val) => M J j ell (fun h => nativeR a false h t)
  let Z := fun t (a : Parameters z.val) => source D r k z upper negativeM ell (fun h => nativeR a true h t)
  let P := fun t => nativeProduct z.val (X t) (Z t)
  let f := fun n : ℕ => seed (rate 1) 1 n
  let b := fun n t => radialProbe 1 (f n).toFun t
  let v := fun t : ℝ => 2*probeIntegral 1 ((t:ℂ)*I)
  let q := fun t : ℝ => ‖v t‖^2
  let F := fun n (t : ℝ) => (star (b n t)*b n t)*P t
  have MF (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    let ξ := f n
    have A := (original_marked_arithmetic_trace D r k z ha upper negativeM J j ell ξ.toFun ξ.toFun
      ξ.continuous ξ.compact ξ.positive ξ.continuous ξ.compact ξ.positive).1
    exact A.aestronglyMeasurable.congr (ae_of_all _ (fun t => (regular_density z.val ξ.toFun ξ.toFun t (X t) (Z t)).symm))
  have L (t : ℝ) : Tendsto (fun n => b n t) atTop (𝓝 (v t)) := by
    have o : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint; ring
    change Tendsto (fun n => orderProbe 1 (f n).toFun (criticalPoint t-1/2)) atTop _
    rw [o]
    exact cutoff_limit 1 (by norm_num) 1 (by simp [Complex.mul_re])
  have MF' : AEStronglyMeasurable (fun t => (q t:ℂ)*P t) volume := by
    apply aestronglyMeasurable_of_tendsto_ae atTop MF
    exact ae_of_all _ (fun t => by
      have L' := ((L t).star.mul (L t)).mul_const (P t)
      have sq : star (v t)*v t=(q t:ℂ) := by rw [mul_comm,Complex.star_def,Complex.mul_conj'] <;> norm_cast
      simpa only [sq] using L')
  have E (t : ℝ) : q t=4*((Real.pi^3/4)*Real.sinh Real.pi/
      (Real.cosh Real.pi+Real.cosh (Real.pi*t))^2) := by
    dsimp only [q,v]
    rw [norm_mul,mul_pow,gamma_norm 1 t (by norm_num)]
    norm_num
  have Q : Continuous q := by rw [funext E]; fun_prop (disch := positivity)
  have nz (t : ℝ) : (q t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by rw [E]; positivity)
  apply (MF'.div (Complex.continuous_ofReal.comp Q).aestronglyMeasurable).congr
  exact ae_of_all _ (fun t => by change (q t:ℂ)*P t/(q t:ℂ)=P t; field_simp [nz t])

/-- Both original Poisson choices give absolutely convergent evaluations
of this K weight. Its equality to the geometric trace uses the
opposite-sign branch in the original prescribed trace theorem. -/
theorem original_prescribed_spectral_convergence (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue≠0) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let Φ := spectralTest ell Y
    let F := fun i : actualCuspBasisIndex z.val (NeZero.pos z.val) =>
      (8*kTransform (basisOrder z.val (NeZero.pos z.val) i) Φ)*
        (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
          originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)
    let G := fun t => continuousDensity Φ z.val t
      (fun a => M J j ell (fun h => nativeR a false h t))
      (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))
    Integrable G ∧ Summable (fun i => ‖F i‖) ∧ Summable F := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let Φ := spectralTest ell Y
  let S := commonMBlock J j
  let T := nCarrier D k z.val
  let w := fun p => star ((commonPoissonCompleted J j (ell 1)).weight p)
  let b := traceBeta D r k upper negativeM ell z.val
  let f := fun p : ℕ => (p:ℤ)
  let jn := traceIndex D k negativeM z.val
  let X := fun t (a : Parameters z.val) => M J j ell (fun h => nativeR a false h t)
  let Z := fun t (a : Parameters z.val) => source D r k z upper negativeM ell (fun h => nativeR a true h t)
  have R := discrete_pair z.val (originalFrame false) (originalFrame true) S T w b f jn
    (common_nonzero J j) (row_nonzero D k z ha negativeM) ell hY
  have cM := covariance_measurable D r k z ha upper negativeM J j ell
  let G := fun t => continuousDensity Φ z.val t (X t) (Z t)
  have E (t : ℝ) : G t=(oppositeWeight Φ t/(Real.cosh (Real.pi*t):ℂ))*nativeProduct z.val (X t) (Z t) := by
    rw [nativeProduct,← Finset.sum_div]
    dsimp only [G,continuousDensity]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.cosh_pos (Real.pi*t)).ne',
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  have mg : AEStronglyMeasurable G volume := by
    rw [funext E]
    exact ((regular_measurable ell hY).aestronglyMeasurable.div
      (by fun_prop : Continuous (fun t : ℝ => (Real.cosh (Real.pi*t):ℂ))).aestronglyMeasurable).mul cM
  have L := continuous_row_budget z.val false S w f (common_nonzero J j) ell hY
  have K := continuous_row_budget z.val true T b jn (row_nonzero D k z ha negativeM) ell hY
  have I : Integrable G := (L.add K).mono' mg (ae_of_all _ (continuous_pair_bound z.val false true S T w b f jn Φ))
  exact ⟨I,R.norm,R⟩

end
end ImbalancedChen.Part3.OriginalPrescribedSpectralConvergence20261112
