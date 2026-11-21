import ImbalancedChen.P1OriginalSingletonMediumReconstruction
import ImbalancedChen.P5ActualLowerNormalizedHBSource

/-!
SOURCE ONLY / NOT COMPILED.

Use the existing normalized singleton chart, including its reciprocal
group logarithm, complete trim, grouped psi and closed occurrence plateau.
The generic all-order budget is not reproved. The new integer dictionary
includes unit HB blocks and is shared by count and exact coprime mean.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumFourier
noncomputable section
open Classical MeasureTheory Filter Set
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P1OriginalSingletonMediumReconstruction (scalar onWord boxedErrors)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualLowerNormalizedAtlasOccurrence (integerProfile scalarProfile scalarProfile_eq_ambient)
open P5Z.ActualLowerNormalizedHBSource (ambient chart_smooth chart_compact)
open P5Z.ActualEtaPsiOccurrenceBudget (actualEta actualPsi)
open P5Z.ActualOccurrencePlateauWordBudget (plateau c_eq_one)
open P5Z.ActualAllRankOccurrenceFourierBridge
  (integerGroupProduct logOccurrence occurrenceMode physicalPhase_occurrenceMode groupProduct_logOccurrence)
open P5Z.ActualEuclideanPhysicalFourier
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P5Z.OccurrenceEuclideanMixedIntegral (euclideanLift_smooth euclideanLift_compact euclideanLift_toLp)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos)
open P4BUpperPairOrderedRowGeometry (blockScales)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalHigherLowTensor (restore)
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy functional residueKernel)

variable {modeOrder : ℕ} {kap zeta kap0 : ℝ} (I : Index modeOrder kap zeta kap0)

def assignment : Fin (size I.j)→Fin 1 := fun _ => 0
def radii : Fin 1→ℝ := fun _ => R I.cj

def physicalChart : V (size I.j)→ℂ :=
  P5Z.ActualLowerNormalizedHBSource.euclideanChart kap 6 I.P.N
    (assignment I) (blockScales I.bv) (radii I) kap0

def amplitude (xi : Fin (size I.j)→ℝ) : ℂ :=
  (frequencyScale^(size I.j))⁻¹ • physicalFourier (size I.j) (physicalChart I) xi

theorem chart_smooth_actual : ContDiff ℝ ∞ (physicalChart I) :=
  euclideanLift_smooth _ _ (chart_smooth kap 6 I.P.N (assignment I) (blockScales I.bv) (radii I) kap0)

theorem chart_compact_actual : HasCompactSupport (physicalChart I) :=
  euclideanLift_compact _ _ (chart_compact kap 6 I.P.N (assignment I) (blockScales I.bv) (radii I) kap0)

theorem amplitude_integrable : Integrable (amplitude I) :=
  (physicalFourier_integrable _ _ (chart_smooth_actual I) (chart_compact_actual I)).const_smul _

/-- Closed atom endpoints include the unit block n=U=1. No arithmetic
point is deleted to satisfy a strict-left Fourier convenience lemma. -/
theorem plateau_integer {n : Fin (size I.j)→ℕ} (hn : n∈rectangle I.bv) :
    plateau (size I.j) (logOccurrence (blockScales I.bv) n)=1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro a _
  have ho := (mem_rectangle I.bv n).mp hn a
  have hp : 0<(blockScales I.bv) a := by exact_mod_cast lower_pos (I.bv a)
  have hnP : 0<(n a:ℝ) := by exact_mod_cast owns_pos ho
  obtain ⟨hlo,hhi⟩ := owns_bounds ho
  apply c_eq_one
  constructor
  · apply Real.log_nonneg
    apply (le_div_iff₀ hp).mpr
    simpa only [one_mul,blockScales] using (show (lower (I.bv a):ℝ)≤n a by exact_mod_cast hlo)
  · apply Real.log_le_log (div_pos hnP hp)
    apply (div_le_iff₀ hp).mpr
    simpa only [blockScales] using (show (n a:ℝ)≤2*(lower (I.bv a):ℝ) by exact_mod_cast hhi)

/-- The physical smooth extension is exactly the source64 normalized
integerProfile on every original rectangle, with the same independent trim. -/
theorem physicalChart_integer {n : Fin (size I.j)→ℕ} (hn : n∈rectangle I.bv) :
    physicalChart I (WithLp.toLp 2 (logOccurrence (blockScales I.bv) n))=
      (integerProfile kap 6 I.P.N I.cj kap0 n:ℂ) := by
  have hU : ∀ a,0<(blockScales I.bv) a := fun a => by exact_mod_cast lower_pos (I.bv a)
  have hnP : ∀ a,0<n a := fun a => owns_pos ((mem_rectangle I.bv n).mp hn a)
  have group (a : Fin 1) : integerGroupProduct (assignment I) n a=completeProduct n := by
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    simp only [integerGroupProduct,assignment,if_true,completeProduct]
  unfold physicalChart P5Z.ActualLowerNormalizedHBSource.euclideanChart
  rw [euclideanLift_toLp]
  unfold P5Z.ActualLowerNormalizedHBSource.chart actualEta actualPsi
  simp_rw [groupProduct_logOccurrence (assignment I) (blockScales I.bv) n hU hnP,group]
  rw [plateau_integer I hn]
  simp only [Fin.prod_univ_one,mul_one,radii]
  exact congrArg (fun r : ℝ => (r:ℂ)) (scalarProfile_eq_ambient kap 6 I.P.N I.cj kap0 (completeProduct n)).symm

theorem mode_integrable (n : Fin (size I.j)→ℕ) :
    Integrable (fun xi => amplitude I xi*occurrenceMode (blockScales I.bv) n xi) := by
  let z := WithLp.toLp 2 (logOccurrence (blockScales I.bv) n)
  have ha := amplitude_integrable I
  have h : Integrable (fun xi => amplitude I xi*physicalPhase (size I.j) z xi) := by
    apply ha.norm.mono'
      (ha.aestronglyMeasurable.mul (physicalPhase_continuous _ z).aestronglyMeasurable)
    exact Eventually.of_forall (fun xi => by rw [norm_mul,physicalPhase_norm,mul_one])
  simpa only [z,physicalPhase_occurrenceMode] using h

theorem integerProfile_fourier {n : Fin (size I.j)→ℕ} (hn : n∈rectangle I.bv) :
    (integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)=
      ∫ xi,amplitude I xi*occurrenceMode (blockScales I.bv) n xi := by
  let z := WithLp.toLp 2 (logOccurrence (blockScales I.bv) n)
  calc
    _=physicalChart I z := (physicalChart_integer I hn).symm
    _=(frequencyScale^(size I.j))⁻¹ •
        ∫ xi,physicalFourier (size I.j) (physicalChart I) xi*physicalPhase (size I.j) z xi :=
      (physical_inverse _ _ (chart_smooth_actual I) (chart_compact_actual I) z).symm
    _=_ := by
      rw [←integral_smul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun xi => by
        rw [physicalPhase_occurrenceMode]
        simp only [amplitude,smul_mul_assoc])

def frequencyMode (K : ℕ) (xi : Fin (size I.j)→ℝ) (n : Fin (size I.j)→ℕ) : ℂ :=
  hbSlots (I.Z K) I.truncations I.roles n*occurrenceMode (blockScales I.bv) n xi

def original (K : ℕ) : ℂ :=
  exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
    completeProduct I.P.N (fun n => hbSlots (I.Z K) I.truncations I.roles n*
      (integerProfile kap 6 I.P.N I.cj kap0 n:ℂ))

/-- The scalar amplitude is identical for the complete count and exact
coprime mean; no physical modulus enters its chart or its frequency. -/
theorem original_eq_fourier (K : ℕ) :
    original I K=∫ xi,amplitude I xi*
      exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
        completeProduct I.P.N (frequencyMode I K xi) := by
  let kernel := fun n : Fin (size I.j)→ℕ =>
    ∑ q∈products I.P,(free I.P q:ℂ)*residueKernel q I.P.N (completeProduct n)
  have hint (n : Fin (size I.j)→ℕ) : Integrable (fun xi => amplitude I xi*frequencyMode I K xi n) := by
    have h := (mode_integrable I n).const_mul (hbSlots (I.Z K) I.truncations I.roles n)
    exact h.congr (Eventually.of_forall (fun xi => by dsimp [frequencyMode]; ring))
  have rep (n : Fin (size I.j)→ℕ) (hn : n∈fibre I.bv I.i I.C) :
      hbSlots (I.Z K) I.truncations I.roles n*(integerProfile kap 6 I.P.N I.cj kap0 n:ℂ)=
        ∫ xi,amplitude I xi*frequencyMode I K xi n := by
    rw [integerProfile_fourier I (Finset.mem_filter.mp hn).1,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun xi => by dsimp [frequencyMode]; ring)
  change functional (fibre I.bv I.i I.C) kernel _=_
  calc
    _=functional (fibre I.bv I.i I.C) kernel
        (fun n => ∫ xi,amplitude I xi*frequencyMode I K xi n) := by
      unfold functional
      exact Finset.sum_congr rfl (fun n hn => by rw [rep n hn])
    _=∫ xi,functional (fibre I.bv I.i I.C) kernel
        (fun n => amplitude I xi*frequencyMode I K xi n) :=
      PrimeProducts.MellinInsertion20261028.functional_integral _ kernel _ (fun n _ => hint n)
    _=_ := by
      simp_rw [PrimeProducts.MellinInsertion20261028.functional_mul]
      rfl

def retained (K : ℕ) : ℂ :=
  exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
    completeProduct I.P.N (fun n => hbSlots (I.Z K) I.truncations I.roles n*
      truncatedPhysical (size I.j) (physicalChart I)
        (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder)
        (WithLp.toLp 2 (logOccurrence (blockScales I.bv) n)))

/-- The exact retained band uses the original source71 cutoff H. The
complete signed level sum is already inside the integral; no moduluswise
tail estimate or H^dimension restoration is inserted. -/
theorem retained_eq_band (K : ℕ) :
    retained I K=∫ xi in
      (outsideCube (size I.j) (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder))ᶜ,
      amplitude I xi*exactDiscrepancy (fibre I.bv I.i I.C) (products I.P)
        (fun q => (free I.P q:ℂ)) completeProduct I.P.N (frequencyMode I K xi) := by
  let kernel := fun n : Fin (size I.j)→ℕ =>
    ∑ q∈products I.P,(free I.P q:ℂ)*residueKernel q I.P.N (completeProduct n)
  have hint (n : Fin (size I.j)→ℕ) : Integrable (fun xi => amplitude I xi*frequencyMode I K xi n) := by
    have h := (mode_integrable I n).const_mul (hbSlots (I.Z K) I.truncations I.roles n)
    exact h.congr (Eventually.of_forall (fun xi => by dsimp [frequencyMode]; ring))
  have rep (n : Fin (size I.j)→ℕ) :
      hbSlots (I.Z K) I.truncations I.roles n*
        truncatedPhysical (size I.j) (physicalChart I)
          (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder)
          (WithLp.toLp 2 (logOccurrence (blockScales I.bv) n))=
      ∫ xi in (outsideCube (size I.j) (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder))ᶜ,
        amplitude I xi*frequencyMode I K xi n := by
    unfold truncatedPhysical
    rw [←integral_smul,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun xi => by
      rw [physicalPhase_occurrenceMode]
      simp only [amplitude,frequencyMode,Complex.real_smul,smul_eq_mul]
      ring)
  change functional (fibre I.bv I.i I.C) kernel _=_
  simp_rw [rep]
  rw [PrimeProducts.MellinInsertion20261028.functional_integral _ kernel _
    (fun n _ => (hint n).integrableOn)]
  simp_rw [PrimeProducts.MellinInsertion20261028.functional_mul]
  rfl

def atMode (xi : Fin (size I.j)→ℝ)
    (hxi : xi∈(outsideCube (size I.j) (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder))ᶜ) :
    Index modeOrder kap zeta kap0 := { I with xi := xi,band := hxi }

/-- Every retained integrand reaches the actual native signed atom sum
on the same assignment. The imported reconstruction has no signed-M input. -/
theorem retained_mode_reconstruction (K : ℕ) (hN : 1<I.P.N) (hu : 1<I.U)
    (xi : Fin (size I.j)→ℝ)
    (hxi : xi∈(outsideCube (size I.j) (P4BOriginalHighRankPostModulusRow.H I.P.N modeOrder))ᶜ) :
    exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (frequencyMode I K xi)=
      (scalar I:ℂ)*∑ J∈I.P.words.attach,
        (restore I.P J.val (onWord (atMode I xi hxi) J).groups:ℂ)*
          boxedErrors (onWord (atMode I xi hxi) J) K :=
  P1OriginalSingletonMediumReconstruction.all_free_words (atMode I xi hxi) K hN hu

/-- The already proved singleton mixed-derivative/Fourier budget is
instantiated at the actual row. Units and real cutoffs do not change it. -/
theorem amplitude_l1_budget :
    ∃ C : ℝ,0≤C ∧ ∀ (modeOrder : ℕ) (kap zeta kap0 : ℝ)
      (I : Index modeOrder kap zeta kap0),
      (∫ xi,‖amplitude I xi‖)≤C*Real.log ((I.P.N:ℝ)+2)^72/2^(size I.j) := by
  obtain ⟨C,hC,HC⟩ := P5Z.ActualLowerNormalizedHBSource.actual_fourier_l1_budget 6
  refine ⟨C,hC,?_⟩
  intro modeOrder kap zeta kap0 I
  have hl : (∫ xi,‖amplitude I xi‖)=
      (∫ xi,‖physicalFourier (size I.j) (physicalChart I) xi‖)/frequencyScale^(size I.j) := by
    simp only [amplitude,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyScale_pos.le _))]
    rw [integral_const_mul]
    ring
  rw [hl]
  exact HC kap I.P.N (size I.j) (assignment I) (blockScales I.bv) (radii I) kap0
    (by exact_mod_cast I.N_pos) (fun a => by exact_mod_cast lower_pos (I.bv a))
    (fun _ => R_pos I.cj) (by dsimp [size]; omega)

end
end ImbalancedChen.P1OriginalSingletonMediumFourier
