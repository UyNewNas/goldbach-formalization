import ImbalancedChen.Part3ActualPositiveNativeDiagonal
import ImbalancedChen.Part3OriginalPrescribedSpectralConvergence
import Batteries.Tactic.OpenPrivate

/-! The original positive branch in the normalization of (4.9)-(4.17).
The regular and complementary Maaß sums, and all incoming cusps of the
continuous term, have absolute convergence on this particular row. -/
namespace ImbalancedChen.Part3.OriginalPrescribedPositiveSpectralWeights20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators MatrixGroups Classical
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualPrescribedPositiveJ20261112 ActualPositiveNativeDiagonal20261112
open ActualSingleModeSpectralEnergy20261112 ActualFullCuspEigenbasis20261026b
open ActualCuspBasisWhittakerCoefficients20261102 ActualCuspDenominatorClasses20261110
open ActualContinuousPoincarePairing20261110 ActualContinuousClassFourier20261110
open OriginalContinuousPoincarePackets20261110 OriginalContinuousClassRemoval20261110 OriginalContinuousCuspGram20261110
open OriginalNativeCuspFunctionals20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalSignedTraceInput20261102 OriginalMarkedArithmeticTrace20261112
open OriginalTwoZFourierAssembly20261102 OriginalOppositeMarkedKuznetsov20261112
open private cost marked_sq product_le from ImbalancedChen.Part3ActualMarkedSpectralMajorants
open private common_nonzero row_nonzero from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private covariance_measurable from ImbalancedChen.Part3OriginalPrescribedSpectralConvergence

private theorem row_sq (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (h : ∀ p∈S,f p≠0) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Summable (fun i : actualCuspBasisIndex N (NeZero.pos N) => ‖nativeWeight N (spectralTest ell Y) i‖*
      ‖markedRow S w f (basisR N (NeZero.pos N) i g)‖^2) := by
  have H := (summable_sum (s:=S) (fun p hp => discrete_diagonal N g (f p) (h p hp) ell hY)).mul_left (cost S w)
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) _ H
  intro i
  have U := mul_le_mul_of_nonneg_left (marked_sq S w f (basisR N (NeZero.pos N) i g))
    (norm_nonneg (nativeWeight N (spectralTest ell Y) i))
  simpa only [Finset.mul_sum,mul_comm,mul_assoc,mul_left_comm] using U

private def budget (N : ℕ) [NeZero N] (b : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (Φ : ℝ → ℂ) (t : ℝ) : ℝ := cost S w*∑ p∈S,contMass N b (f p) Φ t

private theorem cont_sq (N : ℕ) [NeZero N] (b : Bool) (S : Finset ℕ) (w : ℕ → ℂ) (f : ℕ → ℤ)
    (Φ : ℝ → ℂ) (t : ℝ) :
    (‖positiveWeight Φ t‖/(4*Real.pi*Real.cosh (Real.pi*t)))*
      (∑ a : Parameters N,‖markedRow S w f (fun m => nativeR a b m t)‖^2) ≤ budget N b S w f Φ t := by
  let c := ‖positiveWeight Φ t‖/(4*Real.pi*Real.cosh (Real.pi*t))
  have e (m : ℤ) : c*(∑ a : Parameters N,‖nativeR a b m t‖^2)=contMass N b m Φ t := by
    rw [contMass,continuousMass]
    dsimp [c]
    field_simp [Real.pi_ne_zero,(Real.cosh_pos _).ne'] <;> ring
  have H := Finset.sum_le_sum (s:=(Finset.univ:Finset (Parameters N))) (fun a _ =>
    marked_sq S w f (fun m => nativeR a b m t))
  apply (mul_le_mul_of_nonneg_left H (by dsimp [c]; positivity : 0≤c)).trans_eq
  rw [← Finset.mul_sum,Finset.sum_comm,budget,mul_left_comm,Finset.mul_sum]
  simp only [e]

/-- The scalar uses exactly dt/(4 pi cosh(pi t)); nativeProduct already
contains 1/(4 pi) and the complex conjugation on the infinity marking. -/
theorem original_positive_spectral_convergence (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue≠0) (upper negativeM : Bool)
    (J j : ℕ) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let Φ := spectralTest ell Y
    let F := fun i : actualCuspBasisIndex z.val (NeZero.pos z.val) => nativeWeight z.val Φ i*
      (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
        originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)
    let G := fun t => (positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))*nativeProduct z.val
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
  let l := traceIndex D k negativeM z.val
  let X := fun t (a : Parameters z.val) => M J j ell (fun h => nativeR a false h t)
  let Z := fun t (a : Parameters z.val) => source D r k z upper negativeM ell (fun h => nativeR a true h t)
  let G := fun t : ℝ => (positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))*nativeProduct z.val (X t) (Z t)
  have L := row_sq z.val (originalFrame false) S w f (common_nonzero J j) ell hY
  have R := row_sq z.val (originalFrame true) T b l (row_nonzero D k z ha negativeM) ell hY
  have F : Summable (fun i : actualCuspBasisIndex z.val (NeZero.pos z.val) => nativeWeight z.val Φ i*
      (star (originalMFunctional J j ell z.val (NeZero.pos z.val) i)*
        originalNFunctional D r k upper negativeM ell z.val (NeZero.pos z.val) i)) := by
    apply Summable.of_norm_bounded (L.add R)
    intro i
    simp only [norm_mul,norm_star,← mul_add]
    exact mul_le_mul_of_nonneg_left (product_le _ _) (norm_nonneg _)
  have P := covariance_measurable D r k z ha upper negativeM J j ell
  have e : positiveWeight Φ=(weightSchwartz ell hY:ℝ → ℂ) := funext fun t => (regular_transform ell hY t).2
  have mG : AEStronglyMeasurable G volume := by
    dsimp only [G]; rw [e]
    exact ((weightSchwartz ell hY).continuous.aestronglyMeasurable.div
      (by fun_prop : Continuous (fun t : ℝ => (Real.cosh (Real.pi*t):ℂ))).aestronglyMeasurable).mul P
  have B : Integrable (budget z.val false S w f Φ) :=
    (integrable_finsetSum S fun p hp => continuous_diagonal z.val false (f p) (common_nonzero J j p hp) ell hY).const_mul _
  have C : Integrable (budget z.val true T b l Φ) :=
    (integrable_finsetSum T fun p hp => continuous_diagonal z.val true (l p) (row_nonzero D k z ha negativeM p hp) ell hY).const_mul _
  refine ⟨(B.add C).mono' mG (ae_of_all _ fun t => ?_),F.norm,F⟩
  let c := ‖positiveWeight Φ t‖/(4*Real.pi*Real.cosh (Real.pi*t))
  have h0 : 0≤c := by dsimp [c]; positivity
  have eq : ‖G t‖=c*‖∑ a,star (X t a)*Z t a‖ := by
    rw [G,nativeProduct,← Finset.sum_div,norm_mul,norm_div,norm_div]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_of_nonneg (Real.cosh_pos _).le,c,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [eq]
  have H : ‖∑ a,star (X t a)*Z t a‖≤(∑ a,‖X t a‖^2)+(∑ a,‖Z t a‖^2) := by
    rw [← Finset.sum_add_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by rw [norm_mul,norm_star]; exact product_le _ _)
  apply (mul_le_mul_of_nonneg_left H h0).trans
  rw [mul_add]
  exact add_le_add (cont_sq z.val false S w f Φ t) (cont_sq z.val true T b l Φ t)

end
end ImbalancedChen.Part3.OriginalPrescribedPositiveSpectralWeights20261112

