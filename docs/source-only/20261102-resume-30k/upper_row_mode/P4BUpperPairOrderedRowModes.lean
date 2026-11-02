import ImbalancedChen.P4BUpperPairOrderedRowGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact frequency insertion for the literal arbitrary-width upper rows.
The actual signed coefficient is untouched; no arithmetic mode bound,
Family coverage, source equality or Fourier representation is assumed.
-/
namespace ImbalancedChen.P4BUpperPairOrderedRowModes
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators
open P4BUpperPairOrderedRowGeometry
open P5Z.OrderedFactorTupleRectangleReindex P5Z.AllGroupOrderedRectangleReindex
open P5Z.ActualHBPostModulusLogCutoff P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.ActualEuclideanPhysicalFourier P5Z.OccurrenceEuclideanMixedIntegral
open P5Z.HBRightClosedDyadicRoles P5Z.ActualRoughHeathBrownWords
open P5Z.ActualHBDyadicOccurrenceFamily P5Z.PerGroupIntegerHBAtlasPushforward
open P5Z.ExactOriginalSmoothDyadicPartition P5Z.LicensedOriginalIntegerProfile
open P5Z.IndependentPrimeSourceWordDictionary P5Z.OriginalPrimeAllGroupHBDiscrepancy
open P4BArbitraryWidthUpperPairProfile P4BArbitraryWidthUpperPairHBNormalization
open P4BArbitraryWidthUpperPairOccurrence P4BOuterRampRoughness
open ImbalancedChen.PrimeProducts
open ImbalancedChen.Part3.OriginalProperPowerActualChart

section Row
variable {a d : ℕ} {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
variable (hgap : 2*width ≤ baseline b kappa - nu*r)

def amplitude (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) (xi : Fin (a+d) → ℝ) : ℂ :=
  (frequencyScale^(a+d))⁻¹ •
    physicalFourier (a+d) (rowChart b kappa width N kappa0 cj ck bs) xi

include hb hnu hr hw hgap in
theorem amplitude_integrable (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) : Integrable (amplitude b kappa width N kappa0 cj ck bs) := by
  exact (physicalFourier_integrable (a+d) _
    (euclideanLift_smooth (a+d) _
      (occurrenceChart_smooth hb hnu hr hw hgap N (pairOwner a d)
        (blockScales bs) (![R cj, R ck]) kappa0))
    (euclideanLift_compact (a+d) _
      (occurrenceChart_compact b kappa width N (pairOwner a d)
        (blockScales bs) (![R cj, R ck]) kappa0))).const_smul _

include hb hnu hr hw hgap in
theorem amplitude_mode_integrable (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) (n : Fin (a+d) → ℕ) :
    Integrable (fun xi => amplitude b kappa width N kappa0 cj ck bs xi *
      occurrenceMode (blockScales bs) n xi) := by
  have hA := amplitude_integrable hb hnu hr hw hgap N kappa0 cj ck bs
  have hphase := physicalPhase_continuous (a+d)
    (WithLp.toLp 2 (logOccurrence (blockScales bs) n))
  apply hA.norm.mono'
  · simpa only [physicalPhase_occurrenceMode] using
      hA.aestronglyMeasurable.mul hphase.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun xi => by
      rw [norm_mul, ← physicalPhase_occurrenceMode, physicalPhase_norm, mul_one])

/-- Fourier inversion is proved for the actual chart, including units. -/
include hb hnu hr hw hgap in
theorem integerProfile_fourier (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) {n : Fin (a+d) → ℕ}
    (hn : n ∈ rectangle bs) :
    (integerProfile b kappa width N kappa0 cj ck n : ℂ) =
      ∫ xi : Fin (a+d) → ℝ, amplitude b kappa width N kappa0 cj ck bs xi *
        occurrenceMode (blockScales bs) n xi := by
  have hprod : (fun xi : Fin (a+d) → ℝ =>
      amplitude b kappa width N kappa0 cj ck bs xi * occurrenceMode (blockScales bs) n xi) =
      fun xi => (frequencyScale^(a+d))⁻¹ •
        (physicalFourier (a+d) (rowChart b kappa width N kappa0 cj ck bs) xi *
          physicalPhase (a+d) (WithLp.toLp 2 (logOccurrence (blockScales bs) n)) xi) := by
    funext xi
    rw [physicalPhase_occurrenceMode]
    simp only [amplitude, smul_mul_assoc]
  rw [hprod, integral_smul, physical_inverse (a+d) _
    (euclideanLift_smooth (a+d) _
      (occurrenceChart_smooth hb hnu hr hw hgap N (pairOwner a d)
        (blockScales bs) (![R cj, R ck]) kappa0))
    (euclideanLift_compact (a+d) _
      (occurrenceChart_compact b kappa width N (pairOwner a d)
        (blockScales bs) (![R cj, R ck]) kappa0)),
    rowChart_integer b kappa width N kappa0 cj ck bs hn]

def rowAtom (b kappa width : ℝ) (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) (Z : ℝ) (ys : Fin (a+d) → ℝ)
    (rs : Fin (a+d) → Role) (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs) Q rho completeProduct N
    (fun n => hbSlots Z ys rs n * (integerProfile b kappa width N kappa0 cj ck n : ℂ))

/-- Both the AP count and EXACT coprime mean use the same complete
integer, signed rho, ordered role product, and frequency coordinate. -/
include hb hnu hr hw hgap in
theorem rowAtom_eq_modes (N : ℕ) (kappa0 : ℝ) (cj ck : ℕ)
    (bs : Fin (a+d) → Block) (Z : ℝ) (ys : Fin (a+d) → ℝ)
    (rs : Fin (a+d) → Role) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    rowAtom b kappa width N kappa0 cj ck bs Z ys rs Q rho =
      ∫ xi : Fin (a+d) → ℝ, amplitude b kappa width N kappa0 cj ck bs xi *
        MellinInsertion20261028.exactDiscrepancy (rectangle bs) Q rho completeProduct N
          (fun n => hbSlots Z ys rs n * occurrenceMode (blockScales bs) n xi) := by
  let c := fun n : Fin (a+d) → ℕ =>
    ∑ q ∈ Q, rho q * MellinInsertion20261028.residueKernel q N (completeProduct n)
  have hrep (n : Fin (a+d) → ℕ) (hn : n ∈ rectangle bs) :
      hbSlots Z ys rs n * (integerProfile b kappa width N kappa0 cj ck n : ℂ) =
      ∫ xi : Fin (a+d) → ℝ, amplitude b kappa width N kappa0 cj ck bs xi *
        (hbSlots Z ys rs n * occurrenceMode (blockScales bs) n xi) := by
    rw [integerProfile_fourier hb hnu hr hw hgap N kappa0 cj ck bs hn,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun xi => by ring)
  have hint (n : Fin (a+d) → ℕ) : Integrable (fun xi =>
      amplitude b kappa width N kappa0 cj ck bs xi *
        (hbSlots Z ys rs n * occurrenceMode (blockScales bs) n xi)) := by
    have hi := (amplitude_mode_integrable hb hnu hr hw hgap N kappa0 cj ck bs n).const_mul
      (hbSlots Z ys rs n)
    exact hi.congr (Filter.Eventually.of_forall (fun xi => by ring))
  change MellinInsertion20261028.functional (rectangle bs) c _ = _
  calc
    _ = MellinInsertion20261028.functional (rectangle bs) c (fun n =>
        ∫ xi : Fin (a+d) → ℝ, amplitude b kappa width N kappa0 cj ck bs xi *
          (hbSlots Z ys rs n * occurrenceMode (blockScales bs) n xi)) := by
      unfold MellinInsertion20261028.functional
      apply Finset.sum_congr rfl
      intro n hn
      rw [hrep n hn]
    _ = ∫ xi : Fin (a+d) → ℝ, MellinInsertion20261028.functional (rectangle bs) c
        (fun n => amplitude b kappa width N kappa0 cj ck bs xi *
          (hbSlots Z ys rs n * occurrenceMode (blockScales bs) n xi)) :=
      MellinInsertion20261028.functional_integral (rectangle bs) c _ (fun n hn => hint n)
    _ = _ := by
      simp_rw [MellinInsertion20261028.functional_mul]
      rfl

end Row

section Source
variable {b kappa nu r width : ℝ}
variable (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
variable (hgap : 2*width ≤ baseline b kappa - nu*r)

def upperTest (N : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (rows : List Row) : ℂ :=
  (listExtension (normalizedLicence hb hnu hr hw hgap N) (originalProducts rows) : ℂ) *
    (P5Z.ActualEtaPsiOccurrenceBudget.eta
      (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) *
    wordKernel Q rho N (originalProducts rows)

/-- The cap assertion is derived from the actual support, and the
eventual consumer below supplies this support uniformly for ALL widths. -/
theorem upperTest_capSupported (N : ℕ)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    CapSupported N (upperTest hb hnu hr hw hgap N kappa0 Q rho) := by
  intro rows row hrow hlarge
  by_contra htest
  have hWc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp htest).1).1
  have hW : listExtension (normalizedLicence hb hnu hr hw hgap N)
      (originalProducts rows) ≠ 0 := by
    intro hz
    exact hWc (by rw [hz]; rfl)
  have hlen : (originalProducts rows).length = 2 := by
    by_contra hn
    exact hW (by simp only [listExtension, dif_neg hn])
  have hnorm : normalizedProfile b kappa width N
      (fun i => (wordVector 2 (originalProducts rows) i : ℝ)) ≠ 0 := by
    change integerExtension (normalizedLicence hb hnu hr hw hgap N)
      (wordVector 2 (originalProducts rows)) ≠ 0
    rw [← listExtension_ofFn, ofFn_wordVector hlen]
    exact hW
  have hc := hsupport _ (P5Z.ActualIndependentGroupLogNormalization.normalize_nonzero hnorm)
  have hm : row.factors.prod ∈ originalProducts rows := List.mem_map.mpr ⟨row, hrow, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hm
  have hi2 : i < 2 := by omega
  have hs := hc ⟨i, hi2⟩
  have heq : wordVector 2 (originalProducts rows) ⟨i, hi2⟩ = row.factors.prod := by
    simpa only [wordVector, List.getD_eq_getElem _ _ hi] using hget
  rw [heq] at hs
  have hsmall : row.factors.prod < N := by exact_mod_cast hs
  omega

/-- The exact double row is now one full Fin(a+d) occurrence rectangle. -/
theorem pair_row_reindex (N : ℕ) (kappa0 : ℝ) (cj ck j l : ℕ)
    (bs : Fin (2*(j+1)) → Block) (cs : Fin (2*(l+1)) → Block)
    (Z : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    (∑ u ∈ rectangle bs, ∑ v ∈ rectangle cs,
      roughTupleWeight Z (hbCutoff cj) (roles j) (List.ofFn u) *
      roughTupleWeight Z (hbCutoff ck) (roles l) (List.ofFn v) *
      (psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((completeProduct u : ℝ)/R cj) *
       psi P5Z.ActualEtaPsiOccurrenceBudget.chi ((completeProduct v : ℝ)/R ck) *
       upperTest hb hnu hr hw hgap N kappa0 Q rho
        [{order := j, blocks := List.ofFn bs, factors := List.ofFn u},
         {order := l, blocks := List.ofFn cs, factors := List.ofFn v}])) =
    rowAtom b kappa width N kappa0 cj ck (Fin.append bs cs) Z
      (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) Q rho := by
  unfold rowAtom MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  rw [← sum_rectangle_append]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [integerProfile_original_groups hb hnu hr hw hgap, ← pair_role_weight]
  simp only [leftPart_append, rightPart_append, completeProduct_append,
    originalProducts, List.map_cons, List.map_nil, List.prod_ofFn,
    List.prod_cons, List.prod_nil, mul_one, upperTest, wordKernel,
    P5Z.ActualEtaPsiOccurrenceBudget.psi, psi, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

def rowBank (b kappa width : ℝ) (N K cj ck : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
      ∑ l ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar l *
        ∑ cs ∈ blockWords (hbCap ck) (2*(l+1)),
          rowAtom b kappa width N kappa0 cj ck
            (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
            (beforeHBCutoff K [cj,ck])
            (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
            (Fin.append (rowRoles j) (rowRoles l)) Q rho

theorem fullEval_pair_eq_rowBank (N K cj ck : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    fullEval P5Z.ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff K [cj,ck]) [cj,ck]
      (upperTest hb hnu hr hw hgap N kappa0 Q rho) = rowBank b kappa width N K cj ck kappa0 Q rho := by
  simp only [fullEval, rowBank]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro bs hbs
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cs hcs
  have hbslen := (blockWords_spec _ _ _ hbs).1
  have hcslen := (blockWords_spec _ _ _ hcs).1
  rw [← pair_row_reindex hb hnu hr hw hgap N kappa0 cj ck j l
    (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs)
    (beforeHBCutoff K [cj,ck]) Q rho]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [ofFn_blockVector hbslen, ofFn_blockVector hcslen]
  ring

theorem normalizedAtlas_pair_eq_rowBank (N K cj ck : ℕ)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℂ) :
    normalizedAtlas hb hnu hr hw hgap N K kappa0 Q rho [cj,ck] =
      rowBank b kappa width N K cj ck kappa0 Q rho := by
  unfold normalizedAtlas
  change (∑ ps ∈ integerWords N [cj,ck].length,
    P5ActualUpperPairHBLogTransport.numeratorAtlas P5Z.ActualEtaPsiOccurrenceBudget.chi
      (beforeHBCutoff K [cj,ck]) [cj,ck] ps
      (upperTest hb hnu hr hw hgap N kappa0 Q rho)) = _
  rw [numerator_source_eq_full_rectangles N _ _ _ _
    (upperTest_capSupported hb hnu hr hw hgap N hsupport kappa0 Q rho),
    fullEval_pair_eq_rowBank hb hnu hr hw hgap]

def restoredRows (N K : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  trimReserve (licence hb hnu hr hw hgap N) N N kappa0 Q (fun q => (rho q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (rowBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0 Q (fun q => (rho q : ℂ)) -
        properPowerReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js +
        roughPrimeReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js)

/-- Every frequency has one coordinate for every literal occurrence.
The signed HB scalars are outside the frequency integral, in their
original order. No marked modulus slot is inserted among these modes. -/
def modeBank (b kappa width : ℝ) (N K cj ck : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
      ∑ l ∈ Finset.range 3, P5Z.SmoothChartHBDyadicPartition.scalar l *
        ∑ cs ∈ blockWords (hbCap ck) (2*(l+1)),
          ∫ xi : Fin (2*(j+1)+2*(l+1)) → ℝ,
            amplitude b kappa width N kappa0 cj ck
              (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs)) xi *
            MellinInsertion20261028.exactDiscrepancy
              (rectangle (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs)))
              Q rho completeProduct N (fun n =>
                hbSlots (beforeHBCutoff K [cj,ck])
                  (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
                  (Fin.append (rowRoles j) (rowRoles l)) n *
                occurrenceMode
                  (blockScales (Fin.append (blockVector (2*(j+1)) bs)
                    (blockVector (2*(l+1)) cs))) n xi)

include hb hnu hr hw hgap in
theorem rowBank_eq_modeBank (N K cj ck : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℂ) :
    rowBank b kappa width N K cj ck kappa0 Q rho =
      modeBank b kappa width N K cj ck kappa0 Q rho := by
  unfold rowBank modeBank
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro bs hbs
  apply Finset.sum_congr rfl
  intro l hl
  congr 1
  apply Finset.sum_congr rfl
  intro cs hcs
  exact rowAtom_eq_modes hb hnu hr hw hgap N kappa0 cj ck _ _ _ _ Q rho

def restoredModes (N K : ℕ) (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℂ :=
  trimReserve (licence hb hnu hr hw hgap N) N N kappa0 Q (fun q => (rho q : ℂ)) +
    ∑ js ∈ chartBank N 2,
      (modeBank b kappa width N K (js.getD 0 0) (js.getD 1 0) kappa0 Q
          (fun q => (rho q : ℂ)) -
        properPowerReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js +
        roughPrimeReserve (licence hb hnu hr hw hgap N)
          K N N kappa0 Q (fun q => (rho q : ℂ)) js)

theorem restoredRows_eq_modes (N K : ℕ) (kappa0 : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    restoredRows hb hnu hr hw hgap N K kappa0 Q rho =
      restoredModes hb hnu hr hw hgap N K kappa0 Q rho := by
  unfold restoredRows restoredModes
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [rowBank_eq_modeBank hb hnu hr hw hgap]

theorem restoredAtlas_eq_rows (N K : ℕ)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (kappa0 : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    restoredAtlas hb hnu hr hw hgap N K kappa0 Q rho =
      restoredRows hb hnu hr hw hgap N K kappa0 Q rho := by
  unfold restoredAtlas restoredRows
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  have hlen := (words_spec _ _ _ hjs).1
  have hs : js = [js.getD 0 0, js.getD 1 0] := by
    cases js with
    | nil => simp at hlen
    | cons cj tail =>
      cases tail with
      | nil => simp at hlen
      | cons ck rest =>
        have he : rest = [] := List.length_eq_zero.mp (by simpa using hlen)
        subst rest
        rfl
  rw [hs, normalizedAtlas_pair_eq_rowBank hb hnu hr hw hgap N K _ _ hsupport]

/-- Actual current raw upper source, every legal width, all reserves.
The two-level row bank above has a proved frequency identity per row. -/
theorem attachedUpper_source_rows {N : ℕ} (hN : 2 ≤ N)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
    restoredRows hb hnu hr hw hgap N K kappa0
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [attachedUpper_normalized_HB hb hnu hr hw hgap hN K kappa0 epsilon retain cap,
    restoredAtlas_eq_rows hb hnu hr hw hgap N K hsupport]

theorem attachedUpper_source_modes {N : ℕ} (hN : 2 ≤ N)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    (Part3.primeProductSignedError 2 N N
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N)
      (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
    restoredModes hb hnu hr hw hgap N K kappa0
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [attachedUpper_source_rows hb hnu hr hw hgap hN hsupport,
    restoredRows_eq_modes hb hnu hr hw hgap]

/-- Actual noninjective product fibres retain their original labelled
multiplicity, including repeated-prime diagonal and products above N. -/
theorem attachedUpper_physical_fibre_modes {N : ℕ} (hN : 2 ≤ N)
    (hsupport : ∀ p : Fin 2 → ℝ, profile b kappa width N p ≠ 0 → ∀ i, p i < (N : ℝ))
    (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ((∑ q ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N q *
        finitePrimitiveDiscrepancy (P4BLabelledOuterPushforward.productCarrier N)
          (P4BLabelledOuterPushforward.productWeight N
            (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width))
          N q) : ℂ) =
    restoredModes hb hnu hr hw hgap N K kappa0
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N) := by
  rw [P4BLabelledOuterPushforward.signed_productWeight_eq_primeProductSignedError]
  exact attachedUpper_source_modes hb hnu hr hw hgap hN hsupport K kappa0 epsilon retain cap

end Source

/-- One threshold is chosen BEFORE width, all row/chart choices, the
physical coefficient parameters and the Fourier frequency. -/
theorem eventually_attachedUpper_source_rows {b kappa nu r : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa - nu*r,
      ∀ (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
      restoredRows hb hnu hr hw hgap N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  filter_upwards [eventually_full_support_inside_original_cap hb hnu hr,
    Filter.eventually_ge_atTop (2 : ℕ)] with N hs hN
  intro width hw hgap K kappa0 epsilon retain cap
  exact attachedUpper_source_rows hb hnu hr hw hgap hN (hs width hw hgap)
    K kappa0 epsilon retain cap

theorem eventually_attachedUpper_source_modes {b kappa nu r : ℝ}
    (hb : 0 < b) (hnu : 0 < nu) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa - nu*r,
      ∀ (K : ℕ) (kappa0 epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (Part3.primeProductSignedError 2 N N
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)
        (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) =
      restoredModes hb hnu hr hw hgap N K kappa0
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) := by
  filter_upwards [eventually_attachedUpper_source_rows hb hnu hr] with N hs
  intro width hw hgap K kappa0 epsilon retain cap
  rw [hs width hw hgap K kappa0 epsilon retain cap,
    restoredRows_eq_modes hb hnu hr hw hgap]

end
end ImbalancedChen.P4BUpperPairOrderedRowModes
