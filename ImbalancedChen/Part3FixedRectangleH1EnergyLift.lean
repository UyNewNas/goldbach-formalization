import ImbalancedChen.Part3FixedRectangleH1JetSpace
import ImbalancedChen.Part3CompactH1SupportedEnergyApproximation

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every element of the closed fixed-rectangle H1 jet subspace has a literal
compact H1 representative and an actual quotient EnergyCompletion lift.
The representative is the rectangle indicator of its three L2 classes,
and its jet class is proved exactly the original triple. A fixed enlarged
positive rectangle gives an explicit energy norm bound, passed through
the genuine finite tensor approximants. No representative, approximation,
energy limit or norm bound is assumed.
-/
namespace ImbalancedChen.Part3.FixedRectangleH1EnergyLift20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open SupportedH1FiniteTensorDensity20261026a ProductKernelL2TranslationAverage20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1QuotientEnergyLimit20261026b CompactH1CanonicalSeedL220261026b
open CompactH1SupportedEnergyApproximation20261026b FixedRectangleH1JetSpace20261026b

abbrev RectangleJet (L R a b : ℝ) := rectangleH1Jets L R a b

def representative {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3) : Plane → ℂ :=
  (rect L R a b).indicator (v.val i)

theorem representative_memLp {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3) :
    MemLp (representative v i) 2 volume :=
  (Lp.memLp (v.val i)).indicator (measurableSet_Icc.prod measurableSet_Icc)

theorem representative_ae {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3) :
    representative v i =ᵐ[volume] (v.val i) := by
  filter_upwards [v.property.1 i] with p hp
  by_cases hK : p ∈ rect L R a b
  · simp only [representative,indicator_of_mem hK]
  · simp only [representative,indicator_of_notMem hK,hp hK]

theorem representative_support {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3) :
    tsupport (representative v i) ⊆ rect L R a b := by
  apply closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  by_contra hn
  exact hp (by simp only [representative,indicator_of_notMem hn])

theorem representative_compact {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3) :
    HasCompactSupport (representative v i) :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_tsupport (representative_support v i)

theorem test_pair_representative {L R a b : ℝ} (v : RectangleJet L R a b) (i : Fin 3)
    (ψ : Plane → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    inner ℂ (testClass ψ hψ hc) (v.val i) = ∫ p, star (ψ p) * representative v i p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hc (p := (2 : ℝ≥0∞))).coeFn_toLp,
    representative_ae v i] with p hp hrep
  rw [hp,hrep]
  simp only [RCLike.inner_apply',Complex.star_def]

/-- The literal global weak derivatives of the compact representative
are derived from the closed-subspace identities. -/
theorem representative_weak_derivative {L R a b : ℝ} (v : RectangleJet L R a b) (vertical : Bool) :
    HasWeakDirectionalDerivative (representative v 0) (representative v (derivativeIndex vertical))
      (derivativeDirection vertical) := by
  intro ψ hψ hc
  let φ : Plane → ℂ := fun p => star (ψ p)
  have hφ : ContDiff ℝ ∞ φ := hψ.star
  have hφc : HasCompactSupport φ := hc.comp_left (g := star) (by simp)
  have h := v.property.2 vertical φ hφ hφc
  change inner ℂ (testClass φ hφ hφc) (v.val (derivativeIndex vertical)) +
    inner ℂ (testClass (directional (derivativeDirection vertical) φ)
      (directional_smooth _ hφ) (directional_compact _ hφc)) (v.val 0) = 0 at h
  rw [test_pair_representative,test_pair_representative] at h
  have hstar : directional (derivativeDirection vertical) φ =
      fun p => star (directional (derivativeDirection vertical) ψ p) := by
    funext p
    simp [φ,directional,fderiv_star]
  simp only [φ,hstar,star_star] at h
  linear_combination h

def compactJet {L R a b : ℝ} (v : RectangleJet L R a b) : CompactH1Jet where
  value := representative v 0
  dx := representative v 1
  dy := representative v 2
  value_memLp := representative_memLp v 0
  dx_memLp := representative_memLp v 1
  dy_memLp := representative_memLp v 2
  value_compact := representative_compact v 0
  weak_dx := representative_weak_derivative v false
  weak_dy := representative_weak_derivative v true

theorem compactJet_class {L R a b : ℝ} (v : RectangleJet L R a b) : h1JetClass (compactJet v) = v.val := by
  have hc (i : Fin 3) : component (compactJet v) i = representative v i := by fin_cases i <;> rfl
  funext i
  apply Lp.ext
  filter_upwards [(component_memLp (compactJet v) i).coeFn_toLp,representative_ae v i] with p hp hrep
  rw [hp,hc i,hrep]

def fixedEnergyBound (N : ℕ) (L R a b : ℝ) : ℝ :=
  energyTransferSq N (L-1) (R+1) (a/2) (b+1) + 1

theorem fixedEnergyBound_pos (N : ℕ) (L R a b : ℝ) : 0 < fixedEnergyBound N L R a b := by
  have h := energyTransferSq_nonneg N (L-1) (R+1) (a/2) (b+1)
  dsimp [fixedEnergyBound]
  linarith

/-- An actual energy lift with a DERIVED fixed-rectangle norm bound and
literal raw compact-seed periodization. -/
theorem exists_bounded_energy_lift (N : ℕ) [NeZero N]
    (L R a b : ℝ) (hLR : L ≤ R) (ha : 0 < a) (hab : a ≤ b)
    (v : RectangleJet L R a b) :
    ∃ e : EnergyCompletion N,
      ‖e‖ ≤ fixedEnergyBound N L R a b * ‖v‖ ∧
      (((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        complexPoincare N (upperSeed (representative v 0))) := by
  let J := compactJet v
  have houter : rect L R a b ⊆ openRect (L-1) (R+1) (a/2) (b+1) := by
    intro p hp
    constructor <;> constructor <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]
  have hLR' : L-1 < R+1 := by linarith
  have hab' : a/2 < b+1 := by linarith
  have hJ : tsupport J.value ⊆ openRect (L-1) (R+1) (a/2) (b+1) :=
    (representative_support v 0).trans houter
  obtain ⟨P⟩ := exists_normalizedH1TensorSequence J (representative_compact v 1) (representative_compact v 2)
    (L-1) (R+1) (a/2) (b+1) (half_pos ha) hLR' hab' hJ
  obtain ⟨e,he,hphysical⟩ := normalized_sequence_energy_limit N P (half_pos ha)
  let B := energyTransferSq N (L-1) (R+1) (a/2) (b+1)
  have hB : 0 ≤ B := energyTransferSq_nonneg _ _ _ _ _
  have hb (k : ℕ) : ‖coreEmbedding N (familyEnergyCore N (P.tensors k))‖^2 ≤
      B * ‖smoothJetClass (Gamma0SmoothCompactTensorCore20261025a.finiteSmoothChart_contDiff
        Finset.univ (P.tensors k)) (P.compact k)‖^2 := by
    rw [coreEmbedding_norm]
    exact finiteFamily_energy_norm_sq_le N (P.tensors k) _ _ _ _ (half_pos ha) (P.compact k)
      (fun i => ⟨P.horizontal_support k i,P.vertical_support k i⟩)
  have hsq : ‖e‖^2 ≤ B * ‖v‖^2 := by
    have h := le_of_tendsto_of_tendsto (he.norm.pow 2)
      (tendsto_const_nhds.mul (P.jet_tendsto.norm.pow 2)) (Eventually.of_forall hb)
    simpa only [J,compactJet_class] using h
  have hnorm : ‖e‖ ≤ (B+1) * ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg _))).mp
    calc
      _ ≤ B * ‖v‖^2 := hsq
      _ ≤ (B+1)^2 * ‖v‖^2 := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg B]) (sq_nonneg _)
      _ = _ := by ring
  exact ⟨e,hnorm,normalized_energy_limit_physical_ae N P (half_pos ha) hJ e he⟩

end
end ImbalancedChen.Part3.FixedRectangleH1EnergyLift20261026b
