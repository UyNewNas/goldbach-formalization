import ImbalancedChen.P3OriginalU789ActualAtlasLicence

/-!
SUPPLEMENT2 / SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.
The true native Fourier amplitude of each actual U789 HB atom is supplied,
and its finite SAME-Q/rho count/exact-coprime-mean functional is separated.
The HB role coefficients, original real Moebius cutoffs, rough projector,
single logarithmic roles, signed restoring scalar and COMPLETE integer are
all the actual inventory's objects. No hrep, Fubini or mode estimate is an
input. A retained arithmetic mode saving is not asserted.
-/
namespace ImbalancedChen.P3OriginalU789ActualModes
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open P3OriginalU789AffinePhaseBudget P3OriginalU789ComplexChartFourier
open P3OriginalU789ActualAtlasLicence
open P5OriginalU789SmoothChartRoughOne
open P5Z.ActualHBAtlasScalarInventory P5Z.ActualHBPostModulusLogCutoff
open P5Z.ActualRoughHeathBrownWords P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.AllRankCoordinateFourierIBP P5Z.AllRankMixedOperatorBudget
open P5Z.ActualEuclideanPhysicalFourier P5Z.AllRankCauchyCubeTail
open P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.PrimeProducts

def slotWeight (s : Source) (cap K : ℕ) (js : List ℕ) (cs : ActualPieces s cap)
    (n : Fin (dimension cs.val) → ℕ) : ℂ :=
  hbSlots (beforeHBCutoff K js)
    (occurrenceCutoff (hbBank_spec cap (rank s) cs.val cs.property).1 js)
    (pieceRoles cs.val) n

def amplitude (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (ξ : Fin (dimension cs.val) → ℝ) : ℂ :=
  (frequencyScale^(dimension cs.val))⁻¹ •
    physicalFourier (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) ξ

theorem amplitude_integrable (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    Integrable (amplitude s N cap width js cs label child κ₀ t) :=
  (physicalFourier_integrable (dimension cs.val) _
    (actualPiece_smooth s N cap width js cs label child κ₀ t)
    (actualPiece_compact s N cap width js cs label child κ₀ t)).const_smul _

theorem amplitude_mode_integrable (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (n : Fin (dimension cs.val) → ℕ) :
    Integrable (fun ξ => amplitude s N cap width js cs label child κ₀ t ξ *
      occurrenceMode (pieceScales cs.val) n ξ) := by
  have hA := amplitude_integrable s N cap width js cs label child κ₀ t
  have hphase := physicalPhase_continuous (dimension cs.val)
    (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n))
  apply hA.norm.mono'
  · simpa only [physicalPhase_occurrenceMode] using
      hA.aestronglyMeasurable.mul hphase.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul,← physicalPhase_occurrenceMode,physicalPhase_norm,mul_one])

/-- Genuine source representation; both inversion and its required
absolute integrability have been proved for THIS concrete complex chart. -/
theorem actual_integer_fourier (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (n : Fin (dimension cs.val) → ℕ) (hn : n∈actualRectangle s cap cs) :
    actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n =
      ∫ ξ : Fin (dimension cs.val) → ℝ,
        amplitude s N cap width js cs label child κ₀ t ξ*occurrenceMode (pieceScales cs.val) n ξ := by
  have hrep := physical_inverse (dimension cs.val)
    (actualPiece s N cap width js cs label child κ₀ t)
    (actualPiece_smooth s N cap width js cs label child κ₀ t)
    (actualPiece_compact s N cap width js cs label child κ₀ t)
    (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n))
  rw [actualPiece_integer s N cap width js cs label child κ₀ t n hn] at hrep
  rw [← hrep,← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [physicalPhase_occurrenceMode]
    simp only [amplitude,smul_mul_assoc])

def originalAtom (s : Source) (N cap K : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  hbScalar cs.val*MellinInsertion20261028.exactDiscrepancy (actualRectangle s cap cs) Q rho
    completeProduct N (fun n => slotWeight s cap K js cs n*
      (actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n))

def separatedMode (s : Source) (cap K : ℕ) (js : List ℕ) (cs : ActualPieces s cap)
    (ξ : Fin (dimension cs.val) → ℝ) (n : Fin (dimension cs.val) → ℕ) : ℂ :=
  slotWeight s cap K js cs n*occurrenceMode (pieceScales cs.val) n ξ

/-- True full-modulus source-to-mode identity with original signs and
the same complete integer in residue count and exact coprime mean. -/
theorem originalAtom_eq_actual_modes (s : Source) (N cap K : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    originalAtom s N cap K width js cs label child κ₀ t Q rho =
      ∫ ξ : Fin (dimension cs.val) → ℝ,
        amplitude s N cap width js cs label child κ₀ t ξ *
          (hbScalar cs.val*MellinInsertion20261028.exactDiscrepancy (actualRectangle s cap cs)
            Q rho completeProduct N (separatedMode s cap K js cs ξ)) := by
  let c := fun n : Fin (dimension cs.val) → ℕ =>
    ∑ q∈Q,rho q*MellinInsertion20261028.residueKernel q N (completeProduct n)
  have hrep (n : Fin (dimension cs.val) → ℕ) (hn : n∈actualRectangle s cap cs) :
      slotWeight s cap K js cs n*(actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n) =
      ∫ ξ,amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n := by
    rw [actual_integer_fourier s N cap width js cs label child κ₀ t n hn,← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by unfold separatedMode; ring)
  have hint (n : Fin (dimension cs.val) → ℕ) :
      Integrable (fun ξ => amplitude s N cap width js cs label child κ₀ t ξ*
        separatedMode s cap K js cs ξ n) := by
    have h := (amplitude_mode_integrable s N cap width js cs label child κ₀ t n).const_mul
      (slotWeight s cap K js cs n)
    apply h.congr
    exact Filter.Eventually.of_forall (fun ξ => by unfold separatedMode; ring)
  unfold originalAtom MellinInsertion20261028.exactDiscrepancy
  change hbScalar cs.val*MellinInsertion20261028.functional (actualRectangle s cap cs) c _ = _
  calc
    _ = hbScalar cs.val*MellinInsertion20261028.functional (actualRectangle s cap cs) c
        (fun n => ∫ ξ,amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n) := by
      congr 1
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro n hn
      rw [hrep n hn]
    _ = hbScalar cs.val*∫ ξ,MellinInsertion20261028.functional (actualRectangle s cap cs) c
        (fun n => amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n) := by
      rw [MellinInsertion20261028.functional_integral _ _ _ (fun n hn => hint n)]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ξ => by
        rw [MellinInsertion20261028.functional_mul]
        ring)

/-- Expanded physical count minus the exact coprime mean for the SAME
Q/rho. No unrestricted mean or reduced/residual product is substituted. -/
theorem originalAtom_count_mean_eq_modes (s : Source) (N cap K : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    hbScalar cs.val*(∑ q∈Q,rho q*
      (MellinInsertion20261028.residueCount (actualRectangle s cap cs) completeProduct N q
        (fun n => slotWeight s cap K js cs n*(actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n))-
       MellinInsertion20261028.exactCoprimeMean (actualRectangle s cap cs) completeProduct q
        (fun n => slotWeight s cap K js cs n*(actualIntegerWeight s N cap width js cs κ₀ t n*smoothGrid label child n)))) =
      ∫ ξ,amplitude s N cap width js cs label child κ₀ t ξ*
        (hbScalar cs.val*(∑ q∈Q,rho q*
          (MellinInsertion20261028.residueCount (actualRectangle s cap cs) completeProduct N q
            (separatedMode s cap K js cs ξ)-
           MellinInsertion20261028.exactCoprimeMean (actualRectangle s cap cs) completeProduct q
            (separatedMode s cap K js cs ξ)))) := by
  rw [← MellinInsertion20261028.exactDiscrepancy_eq_count_sub_mean]
  change originalAtom s N cap K width js cs label child κ₀ t Q rho = _
  rw [originalAtom_eq_actual_modes]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [MellinInsertion20261028.exactDiscrepancy_eq_count_sub_mean])

def retainedAtom (s : Source) (N cap K : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (H : ℝ) : ℂ :=
  hbScalar cs.val*MellinInsertion20261028.exactDiscrepancy (actualRectangle s cap cs) Q rho
    completeProduct N (fun n => slotWeight s cap K js cs n*
      truncatedPhysical (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) H
        (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n)))

/-- Retained full-Q integration has the same actual amplitude and the
same arithmetic tensor modes. No cube-volume/H^d factor is charged. -/
theorem retainedAtom_eq_actual_modes (s : Source) (N cap K : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) (H : ℝ) :
    retainedAtom s N cap K width js cs label child κ₀ t Q rho H =
      ∫ ξ in (outsideCube (dimension cs.val) H)ᶜ,
        amplitude s N cap width js cs label child κ₀ t ξ*
          (hbScalar cs.val*MellinInsertion20261028.exactDiscrepancy (actualRectangle s cap cs)
            Q rho completeProduct N (separatedMode s cap K js cs ξ)) := by
  let c := fun n : Fin (dimension cs.val) → ℕ =>
    ∑ q∈Q,rho q*MellinInsertion20261028.residueKernel q N (completeProduct n)
  have hrep (n : Fin (dimension cs.val) → ℕ) :
      slotWeight s cap K js cs n*
        truncatedPhysical (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) H
          (WithLp.toLp 2 (logOccurrence (pieceScales cs.val) n)) =
      ∫ ξ in (outsideCube (dimension cs.val) H)ᶜ,
        amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n := by
    rw [truncatedPhysical,← integral_smul,← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [physicalPhase_occurrenceMode]
      simp only [amplitude,separatedMode,smul_eq_mul]
      ring)
  have hint (n : Fin (dimension cs.val) → ℕ) :
      Integrable (fun ξ => amplitude s N cap width js cs label child κ₀ t ξ*
        separatedMode s cap K js cs ξ n) (volume.restrict (outsideCube (dimension cs.val) H)ᶜ) := by
    have h := ((amplitude_mode_integrable s N cap width js cs label child κ₀ t n).const_mul
      (slotWeight s cap K js cs n)).integrableOn
    apply h.congr
    exact Filter.Eventually.of_forall (fun ξ => by unfold separatedMode; ring)
  unfold retainedAtom MellinInsertion20261028.exactDiscrepancy
  change hbScalar cs.val*MellinInsertion20261028.functional (actualRectangle s cap cs) c _ = _
  calc
    _ = hbScalar cs.val*MellinInsertion20261028.functional (actualRectangle s cap cs) c
        (fun n => ∫ ξ in (outsideCube (dimension cs.val) H)ᶜ,
          amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n) := by
      congr 1
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro n hn
      rw [hrep n]
    _ = hbScalar cs.val*∫ ξ in (outsideCube (dimension cs.val) H)ᶜ,
        MellinInsertion20261028.functional (actualRectangle s cap cs) c
          (fun n => amplitude s N cap width js cs label child κ₀ t ξ*separatedMode s cap K js cs ξ n) := by
      rw [MellinInsertion20261028.functional_integral _ _ _ (fun n hn => hint n)]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ξ => by
        rw [MellinInsertion20261028.functional_mul]
        ring)

theorem amplitude_norm_integral (s : Source) (N cap : ℕ) (width : ℝ) (js : List ℕ)
    (cs : ActualPieces s cap) (label : SmoothLabels (dimension cs.val) cap)
    (child : Fin (dimension cs.val) → Fin 3) (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    (∫ ξ,‖amplitude s N cap width js cs label child κ₀ t ξ‖) =
      (∫ ξ,‖physicalFourier (dimension cs.val) (actualPiece s N cap width js cs label child κ₀ t) ξ‖) /
        frequencyScale^(dimension cs.val) := by
  have hs : 0<(frequencyScale^(dimension cs.val))⁻¹ :=
    inv_pos.mpr (pow_pos frequencyScale_pos _)
  simp only [amplitude,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  rw [integral_const_mul]
  ring

def actualAmplitudeMass (s : Source) (N cap : ℕ) (width : ℝ) (κ₀ : ℝ)
    (t : Fin (rank s) → ℝ) : ℝ :=
  ∑ js∈chartBank cap (rank s),∑ cs∈(hbBank cap (rank s)).attach,‖hbScalar cs.val‖*
    ∑ label : SmoothLabels (dimension cs.val) cap,∑ child : Fin (dimension cs.val) → Fin 3,
      ∫ ξ,‖amplitude s N cap width js cs label child κ₀ t ξ‖

/-- The actual separated amplitudes' total norm is the already proved
actual atlas Fourier mass, including every true signed HB scalar. -/
theorem actualAmplitudeMass_eq_fourierMass (s : Source) (N cap : ℕ) (width : ℝ)
    (κ₀ : ℝ) (t : Fin (rank s) → ℝ) :
    actualAmplitudeMass s N cap width κ₀ t=atlasFourierMass s N cap width κ₀ t := by
  unfold actualAmplitudeMass atlasFourierMass
  simp_rw [amplitude_norm_integral]

theorem exists_chosen_actual_amplitude_mass (B F : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Source) (N : ℕ),1≤Real.log (N : ℝ) →
      ∀ (κ₀ : ℝ) (t : Fin (rank s) → ℝ),t∈(outsideCube (rank s) (chosenRadius F N))ᶜ →
      actualAmplitudeMass s N (sourceCap N) (chosenWidth B N) κ₀ t ≤
        C*P5Z.CompleteProductTailDivisorBudgets.logScale (sourceScale N)^(52+48*max B F) := by
  obtain ⟨C,hC,hb⟩ := exists_chosen_actual_source_fourier_licence B F
  refine ⟨C,hC,?_⟩
  intro s N hell κ₀ t ht
  rw [actualAmplitudeMass_eq_fourierMass]
  exact (hb s N hell κ₀ t ht).2.1

end
end ImbalancedChen.P3OriginalU789ActualModes
