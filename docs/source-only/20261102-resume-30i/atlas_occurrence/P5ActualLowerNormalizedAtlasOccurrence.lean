import ImbalancedChen.P5OrderedFactorTupleRectangleReindex

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual H narrow singleton lower source, flattened onto its literal
order-three HB occurrence rectangles. No Family or source-equality input.
Every original group log stays in the actual normalized integer profile.
-/
namespace ImbalancedChen.P5Z.ActualLowerNormalizedAtlasOccurrence
noncomputable section
open Classical
open scoped BigOperators
open OrderedFactorTupleRectangleReindex
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open PerGroupIntegerHBAtlasPushforward AllGroupHBLogNormalization
open ActualLowerNormalizedHBSource ActualHBPostModulusLogCutoff
open ExactOriginalSmoothDyadicPartition LicensedOriginalIntegerProfile
open ExistingIndependentFamilyLogNormalization P5CanonicalTentNarrowSingletonTransfer
open OriginalPrimeAllGroupHBDiscrepancy IndependentPrimeSourceWordDictionary
open ImbalancedChen.P5ActualUpperPairHBLogTransport
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.PrimeProducts

def scalarProfile (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (p : ℕ) : ℝ :=
  ActualSingletonLogCollarFamily.integerWeight (1-kappa)
      (ActualSingletonLogCollarFamily.logWidth B N) N (fun _ : Fin 1 => p) /
    Real.log (p : ℝ) *
    ActualEtaPsiOccurrenceBudget.eta ((p : ℝ) / (N : ℝ)^(1-kappa0)) *
    ActualEtaPsiOccurrenceBudget.psi ((p : ℝ) / R cj)

def integerProfile {m : ℕ} (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (n : Fin m → ℕ) : ℝ := scalarProfile kappa B N cj kappa0 (completeProduct n)

def rowRoles (j : ℕ) : Fin (2*(j+1)) → Role :=
  fun a => (roles j)[a.val]'(by rw [roles_length]; exact a.isLt)

theorem ofFn_rowRoles (j : ℕ) : List.ofFn (rowRoles j) = roles j := by
  apply List.ext_getElem
  · simp [roles_length]
  · intro i hi hj
    simp [rowRoles]

theorem roughTupleWeight_ofFn (Z y : ℝ) : ∀ m (rs : Fin m → Role) (n : Fin m → ℕ),
    roughTupleWeight Z y (List.ofFn rs) (List.ofFn n) =
      hbSlots Z (fun _ => y) rs n := by
  intro m
  induction m with
  | zero => intro rs n; simp [roughTupleWeight, hbSlots]
  | succ m ih =>
    intro rs n
    simpa only [List.ofFn_succ, roughTupleWeight, hbSlots, Fin.prod_univ_succ]
      using congrArg (fun c => actual Z y (rs 0) (n 0) * c)
        (ih (fun a => rs a.succ) (fun a => n a.succ))

theorem row_weight (Z y : ℝ) (j : ℕ) (n : Fin (2*(j+1)) → ℕ) :
    roughTupleWeight Z y (roles j) (List.ofFn n) =
      hbSlots Z (fun _ => y) (rowRoles j) n := by
  rw [← ofFn_rowRoles]
  exact roughTupleWeight_ofFn Z y _ _ _

/-- The real cutoff in each original Mobius occurrence survives the
dictionary literally. No floor or different cube cutoff is introduced. -/
theorem row_mobius_cutoff (Z : ℝ) (cj j : ℕ) (n : Fin (2*(j+1)) → ℕ)
    (hn : hbSlots Z (fun _ => hbCutoff cj) (rowRoles j) n ≠ 0)
    (a : Fin (2*(j+1))) (ha : rowRoles j a = .mobius) :
    (n a : ℝ) ≤ hbCutoff cj := by
  have hp : actual Z (hbCutoff cj) (rowRoles j a) (n a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hn) a (Finset.mem_univ a)
  rw [ha] at hp
  by_contra hc
  exact hp (by simp only [actual, roughMuTrunc, if_neg hc])

theorem scalarProfile_eq_ambient (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (p : ℕ) :
    scalarProfile kappa B N cj kappa0 p =
      ambient kappa B N (fun _ : Fin 1 => (p : ℝ)) *
        ActualEtaPsiOccurrenceBudget.eta ((p : ℝ) / (N : ℝ)^(1-kappa0)) *
        ActualEtaPsiOccurrenceBudget.psi ((p : ℝ) / R cj) := by
  rw [ambient_integer kappa B N (fun _ : Fin 1 => p)]
  simp only [Fin.prod_univ_one, scalarProfile]

theorem scalarProfile_support (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) {p : ℕ}
    (hp : scalarProfile kappa B N cj kappa0 p ≠ 0) : p ≤ 2*N := by
  rw [scalarProfile_eq_ambient] at hp
  have hamb : ambient kappa B N (fun _ : Fin 1 => (p : ℝ)) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1
  have hs := (ambient_support kappa hkappa B N _ hamb).2
  simp only [Fin.prod_univ_one] at hs
  exact_mod_cast hs

theorem normalized_singleton_profile (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (p : ℕ) :
    (listExtension (normalizedLicence (actualLicence kappa B N)) [p] : ℂ) *
        (ActualEtaPsiOccurrenceBudget.eta ((p : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) *
        ExactOriginalSmoothDyadicPartition.psi ActualEtaPsiOccurrenceBudget.chi
          ((p : ℝ)/R cj) =
      (scalarProfile kappa B N cj kappa0 p : ℂ) := by
  have he : listExtension (normalizedLicence (actualLicence kappa B N)) [p] =
      ambient kappa B N (fun _ : Fin 1 => (p : ℝ)) := by
    calc
      _ = listExtension (normalizedLicence (actualLicence kappa B N))
          (List.ofFn (fun _ : Fin 1 => p)) := by simp [List.ofFn_succ]
      _ = integerExtension (normalizedLicence (actualLicence kappa B N))
          (fun _ : Fin 1 => p) := listExtension_ofFn _ _
      _ = _ := rfl
  rw [he, scalarProfile_eq_ambient]
  simp only [Complex.ofReal_mul, ExactOriginalSmoothDyadicPartition.psi,
    bump, ActualEtaPsiOccurrenceBudget.psi, Complex.ofReal_sub]

def lowerQ (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :=
  actualLowerSmallRoughModuli retainEven N cap w z

def lowerRho (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℕ → ℂ :=
  fun q => (actualLowerSmallRoughRho retainEven N cap w z L q : ℂ)

def occurrenceAtom (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ)
    (bs : List Block) (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle (blockVector (2*(j+1)) bs))
    (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
    completeProduct N (fun n =>
      hbSlots (beforeHBCutoff 1 [cj]) (fun _ => hbCutoff cj) (rowRoles j) n *
        (integerProfile kappa B N cj kappa0 n : ℂ))

def Meets (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ) (bs : List Block) : Prop :=
  ∃ n ∈ rectangle (blockVector (2*(j+1)) bs), integerProfile kappa B N cj kappa0 n ≠ 0

def activeBlocks (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ) : Finset (List Block) :=
  (blockWords (hbCap cj) (2*(j+1))).filter (Meets kappa B N cj kappa0 j)

def occurrenceChart (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
    ∑ bs ∈ activeBlocks kappa B N cj kappa0 j,
      occurrenceAtom kappa B N cj kappa0 j bs retainEven cap w z L

theorem occurrenceAtom_zero_of_not_meets (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (j : ℕ) (bs : List Block) (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ)
    (h : ¬ Meets kappa B N cj kappa0 j bs) :
    occurrenceAtom kappa B N cj kappa0 j bs retainEven cap w z L = 0 := by
  unfold occurrenceAtom MellinInsertion20261028.exactDiscrepancy
    MellinInsertion20261028.functional
  apply Finset.sum_eq_zero
  intro n hn
  have hz : integerProfile kappa B N cj kappa0 n = 0 := by
    by_contra hne
    exact h ⟨n, hn, hne⟩
  simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]

/-- Exact row-to-rectangle identity, before any Fourier or modulus
estimate. The source cap is removed by the proved real profile support. -/
theorem actual_row_reindex (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ) (bs : List Block)
    (hbs : bs ∈ blockWords (hbCap cj) (2*(j+1)))
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    (∑ p ∈ Finset.Icc 1 (2*N), ∑ fs ∈ factorTuples (2*(j+1)) p,
      assignedWeight (beforeHBCutoff 1 [cj]) (hbCutoff cj) (roles j) bs fs *
        ((scalarProfile kappa B N cj kappa0 fs.prod : ℂ) *
          wordKernel (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) N
            [fs.prod])) =
      occurrenceAtom kappa B N cj kappa0 j bs retainEven cap w z L := by
  rw [sum_factorTuples_rectangle (2*N) (beforeHBCutoff 1 [cj]) (hbCutoff cj)
    (roles j) bs (blockWords_spec _ _ _ hbs).1]
  · unfold occurrenceAtom MellinInsertion20261028.exactDiscrepancy
      MellinInsertion20261028.functional
    apply Finset.sum_congr rfl
    intro n hn
    rw [row_weight]
    simp only [List.prod_ofFn, integerProfile, completeProduct, wordKernel,
      List.prod_cons, List.prod_nil, mul_one]
    ring
  · intro n hn hout
    have hz : scalarProfile kappa B N cj kappa0 (List.ofFn n).prod = 0 := by
      by_contra hp
      have hc := scalarProfile_support kappa hkappa B N cj kappa0 hp
      exact (not_le_of_gt hout) (by simpa only [List.prod_ofFn, completeProduct] using hc)
    simp only [hz, Complex.ofReal_zero, zero_mul]

/-- Expand the independently specified H numeratorAtlas at its genuine
rank one. This retains its original +3, -3, +1 scalars and every block bank. -/
theorem singleton_numerator_expansion (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) :
    normalizedAllGroupAtlas (actualLicence kappa B N) 1 (2*N) N kappa0
      (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) [cj] =
      ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
        ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
          ∑ p ∈ Finset.Icc 1 (2*N), ∑ fs ∈ factorTuples (2*(j+1)) p,
            assignedWeight (beforeHBCutoff 1 [cj]) (hbCutoff cj) (roles j) bs fs *
              ((scalarProfile kappa B N cj kappa0 fs.prod : ℂ) *
                wordKernel (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
                  N [fs.prod]) := by
  unfold normalizedAllGroupAtlas integerWords
  rw [words_sum_cons]
  simp only [words, Finset.sum_singleton]
  have hpwise (p : ℕ) :
      numeratorAtlas ActualEtaPsiOccurrenceBudget.chi (beforeHBCutoff 1 [cj]) [cj] [p]
        (fun rows =>
          (listExtension (normalizedLicence (actualLicence kappa B N)) (originalProducts rows) : ℂ) *
            ((ActualEtaPsiOccurrenceBudget.eta
              (((originalProducts rows).prod : ℝ)/(N : ℝ)^(1-kappa0)) : ℂ) *
              wordKernel (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
                N (originalProducts rows))) =
        ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            ∑ fs ∈ factorTuples (2*(j+1)) p,
              assignedWeight (beforeHBCutoff 1 [cj]) (hbCutoff cj) (roles j) bs fs *
                ((scalarProfile kappa B N cj kappa0 fs.prod : ℂ) *
                  wordKernel (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L)
                    N [fs.prod]) := by
    simp only [numeratorAtlas, originalProducts, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro bs hbs
    apply Finset.sum_congr rfl
    intro fs hfs
    have hprod := (factorTuples_spec (2*(j+1)) p fs hfs).2.1
    rw [← hprod]
    rw [← normalized_singleton_profile kappa B N cj kappa0 fs.prod]
    ring
  simp_rw [hpwise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

/-- The actual normalized H atlas is the finite bank of ordered FULL
right-closed rectangles meeting its smooth profile. No source equation
or rectangular cover is an input to this theorem. -/
theorem normalized_atlas_eq_occurrenceChart (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) :
    normalizedAllGroupAtlas (actualLicence kappa B N) 1 (2*N) N kappa0
      (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) [cj] =
      occurrenceChart kappa B N cj kappa0 retainEven cap w z L := by
  rw [singleton_numerator_expansion]
  unfold occurrenceChart
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  calc
    _ = ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
        occurrenceAtom kappa B N cj kappa0 j bs retainEven cap w z L := by
      apply Finset.sum_congr rfl
      intro bs hbs
      exact actual_row_reindex kappa hkappa B N cj kappa0 j bs hbs retainEven cap w z L
    _ = _ := by
      unfold activeBlocks
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro bs hbs
      by_cases hm : Meets kappa B N cj kappa0 j bs
      · simp only [if_pos hm]
      · simp only [if_neg hm,
          occurrenceAtom_zero_of_not_meets kappa B N cj kappa0 j bs retainEven cap w z L hm]

def lowerOccurrenceAtlas (kappa : ℝ) (B N : ℕ) (kappa0 : ℝ)
    (retainEven : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  trimReserve (actualLicence kappa B N) (2*N) N kappa0
      (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) +
    ∑ js ∈ chartBank (2*N) 1,
      (occurrenceChart kappa B N (js.getD 0 0) kappa0 retainEven cap w z L -
        properPowerReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) js +
        roughPrimeReserve (actualLicence kappa B N) 1 (2*N) N kappa0
          (lowerQ retainEven N cap w z) (lowerRho retainEven N cap w z L) js)

theorem lowerAtlas_eq_occurrences (kappa : ℝ) (hkappa : kappa < 1)
    (B N : ℕ) (kappa0 : ℝ) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) :
    lowerAtlas kappa B N kappa0 retainEven cap w z L =
      lowerOccurrenceAtlas kappa B N kappa0 retainEven cap w z L := by
  unfold lowerAtlas lowerOccurrenceAtlas lowerQ lowerRho
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  have hlen : js.length = 1 := (words_spec _ _ _ hjs).1
  have hs : js = [js.getD 0 0] := by
    cases js with
    | nil => simp at hlen
    | cons cj tail =>
      have ht : tail = [] := List.length_eq_zero.mp (by simpa using hlen)
      subst tail
      rfl
  rw [hs, normalized_atlas_eq_occurrenceChart kappa hkappa]

/-- Independent production prime count, SAME physical signed lower rho,
SAME exact coprime mean, with all five original reserves still present. -/
theorem original_lower_source_occurrences (kappa : ℝ) (hkappa : kappa < 1)
    (B N : ℕ) (kappa0 : ℝ) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 N N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (P5S1SingletonPP.singletonWeight N (fun _ => 1)) : ℂ) =
      lowerOccurrenceAtlas kappa B N kappa0 retainEven cap w z L +
        (lowerReserve kappa B N (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ) +
        (upperReserve kappa B N (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) : ℂ) := by
  rw [original_lower_source_normalized kappa B N kappa0 retainEven cap w z L,
    lowerAtlas_eq_occurrences kappa hkappa B N kappa0 retainEven cap w z L]

theorem actual_lower_smooth_occurrences (kappa : ℝ) (hkappa : kappa < 1)
    (B N : ℕ) (kappa0 : ℝ) (retainEven : List ℕ → Bool)
    (cap : ℕ) (w z L : ℝ) :
    (Part3.primeProductSignedError 1 (2*N) N
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualLowerSmallRoughRho retainEven N cap w z L)
      (fullSmoothWeight kappa B N) : ℂ) =
      lowerOccurrenceAtlas kappa B N kappa0 retainEven cap w z L := by
  rw [actual_lower_smooth_normalized kappa B N kappa0 retainEven cap w z L,
    lowerAtlas_eq_occurrences kappa hkappa B N kappa0 retainEven cap w z L]

theorem activeBlock_dimension (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    {j : ℕ} (hj : j ∈ Finset.range 3) {bs : List Block}
    (hbs : bs ∈ activeBlocks kappa B N cj kappa0 j) :
    bs.length = 2*(j+1) ∧ 2*(j+1) ≤ 6 ∧ Meets kappa B N cj kappa0 j bs := by
  obtain ⟨hb, hm⟩ := Finset.mem_filter.mp hbs
  exact ⟨(blockWords_spec _ _ _ hb).1, by have := Finset.mem_range.mp hj; omega, hm⟩

theorem activeBlock_source_support (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) (j : ℕ) {bs : List Block}
    (hbs : bs ∈ activeBlocks kappa B N cj kappa0 j) :
    ∃ n ∈ rectangle (blockVector (2*(j+1)) bs),
      0 < completeProduct n ∧ completeProduct n ≤ 2*N ∧
        integerProfile kappa B N cj kappa0 n ≠ 0 := by
  obtain ⟨hb, n, hn, hne⟩ := Finset.mem_filter.mp hbs
  refine ⟨n, hn, ?_, scalarProfile_support kappa hkappa B N cj kappa0 hne, hne⟩
  exact Finset.prod_pos (fun a ha => owns_pos ((mem_rectangle _ _).mp hn a))

end
end ImbalancedChen.P5Z.ActualLowerNormalizedAtlasOccurrence
