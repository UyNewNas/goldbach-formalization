import ImbalancedChen.P2GammaRetainedInteriorGeometry
import ImbalancedChen.P2GammaSmallConductorIntervalBridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal original Gamma head has four colours and a [a,f) window.
Here its intersection with (M,2M] is converted to the actual prime-SW
(u,v] carrier.  Ceil(endpoint)-1 preserves every integer endpoint.
The old marked pair, all other word slots, their masks and quotient 1
remain in the unchanged P complete-complement row.

No grid, Abel theorem, positive-carrier cast bridge or distribution
theorem is reproved.  The existing variable-profile supplier is called.
-/

namespace ImbalancedChen.P2GammaHeadWindowDictionary
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory
open Wu2008DoubleSieve P2TwentyOneUnsiftedArithmeticSource
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open P2GammaVariablePrimeProfile P2GammaVariablePrimeSmallConductor
open P2GammaPrimeSmallConductorSum P2GammaSmallConductorIntervalBridge
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalU5SmallPartnerRootPayment (rootQ)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Earlier failed colour tests are retained even without ordered thresholds. -/
def colourLo (a b cc e : ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => max a b
  | 2 => max (max a b) cc
  | _ => max (max (max a b) cc) e

def colourHi (f b cc e : ℝ) : ℕ → ℝ
  | 0 => min f b
  | 1 => min f cc
  | 2 => min f e
  | _ => f

theorem colour_window_iff (a b cc e f : ℝ) (c p : ℕ) (hc : c ≤ 3) :
    (a ≤ (p : ℝ) ∧ (p : ℝ) < f ∧
      secondFunctionalMotherColour b cc e p = c) ↔
      colourLo a b cc e c ≤ p ∧ (p : ℝ) < colourHi f b cc e c := by
  interval_cases c <;>
    simp only [colourLo, colourHi, max_le_iff, lt_min_iff,
      secondFunctionalMotherColour] <;>
    split_ifs <;> simp_all <;> omega

def headLo (N : ℕ) (t : ℕ × ℕ) (c : ℕ) : ℝ :=
  colourLo (cutoff (rootQ N t) (t.1*t.2) (227/50))
    (cutoff (rootQ N t) (t.1*t.2) (353/100))
    (cutoff (rootQ N t) (t.1*t.2) (29/10))
    (cutoff (rootQ N t) (t.1*t.2) (61/25)) c

def headHi (N : ℕ) (t : ℕ × ℕ) (c : ℕ) : ℝ :=
  colourHi (cutoff (rootQ N t) (t.1*t.2) (11/5))
    (cutoff (rootQ N t) (t.1*t.2) (353/100))
    (cutoff (rootQ N t) (t.1*t.2) (29/10))
    (cutoff (rootQ N t) (t.1*t.2) (61/25)) c

theorem mem_headCarrier_iff {N c p : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3) :
    p ∈ headCarrier N t c ↔
      p.Prime ∧ p.Coprime N ∧ headLo N t c ≤ p ∧ (p : ℝ) < headHi N t c := by
  simp only [headCarrier, rootWindow, rootColour, Finset.mem_filter, mem_primeWindow]
  rw [show (p.Prime ∧ p.Coprime N ∧
      cutoff (rootQ N t) (t.1*t.2) (227/50) ≤ (p : ℝ) ∧
      (p : ℝ) < cutoff (rootQ N t) (t.1*t.2) (11/5)) ∧
        secondFunctionalMotherColour
          (cutoff (rootQ N t) (t.1*t.2) (353/100))
          (cutoff (rootQ N t) (t.1*t.2) (29/10))
          (cutoff (rootQ N t) (t.1*t.2) (61/25)) p = c ↔
      p.Prime ∧ p.Coprime N ∧
        (cutoff (rootQ N t) (t.1*t.2) (227/50) ≤ (p : ℝ) ∧
        (p : ℝ) < cutoff (rootQ N t) (t.1*t.2) (11/5) ∧
        secondFunctionalMotherColour
          (cutoff (rootQ N t) (t.1*t.2) (353/100))
          (cutoff (rootQ N t) (t.1*t.2) (29/10))
          (cutoff (rootQ N t) (t.1*t.2) (61/25)) p = c) by tauto]
  rw [colour_window_iff _ _ _ _ _ c p hc]
  rfl

theorem headCarrier_colour_le_three {N c p : ℕ} {t : ℕ × ℕ}
    (hp : p ∈ headCarrier N t c) : c ≤ 3 := by
  have hcolour := (Finset.mem_filter.mp hp).2
  have hcap := secondFunctionalMother_colour_le_three
    (cutoff (rootQ N t) (t.1*t.2) (353/100))
    (cutoff (rootQ N t) (t.1*t.2) (29/10))
    (cutoff (rootQ N t) (t.1*t.2) (61/25)) p
  change secondFunctionalMotherColour _ _ _ p = c at hcolour
  omega

theorem headCarrier_eq_empty_of_three_lt {N c : ℕ} {t : ℕ × ℕ} (hc : 3 < c) :
    headCarrier N t c = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  have hcap := headCarrier_colour_le_three hp
  omega

/-- This row is fixed before q,r,k,characters and moving residues. -/
def source (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (M : ℝ) : Finset ℕ :=
  (headCarrier N t c).filter (fun p => M < (p : ℝ) ∧ (p : ℝ) ≤ 2*M)

def clipLo (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (M : ℝ) : ℝ :=
  max M ((Nat.ceil (headLo N t c) : ℝ)-1)

def clipHi (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (M : ℝ) : ℝ :=
  min (2*M) ((Nat.ceil (headHi N t c) : ℝ)-1)

/-- Exact arithmetic helper, materialized from the inaccessible private
`ceil_window` in P5OriginalSingletonPrimeSource, with the same proof. -/
theorem natural_Ico_iff_Ioc (l h : ℝ) (p : ℕ) :
    l ≤ (p : ℝ) ∧ (p : ℝ) < h ↔
      (Nat.ceil l : ℝ)-1 < p ∧ (p : ℝ) ≤ (Nat.ceil h : ℝ)-1 := by
  rw [← Nat.ceil_le, ← Nat.lt_ceil]
  constructor
  · rintro ⟨hl,hh⟩
    have hl' : (Nat.ceil l : ℝ) ≤ p := by exact_mod_cast hl
    have hh' : (p : ℝ)+1 ≤ Nat.ceil h := by exact_mod_cast hh
    constructor <;> linarith
  · rintro ⟨hl,hh⟩
    have hl' : (Nat.ceil l : ℝ) < (p+1 : ℕ) := by push_cast; linarith
    have hh' : (p : ℝ) < Nat.ceil h := by linarith
    have hl'' : Nat.ceil l < p+1 := by exact_mod_cast hl'
    exact ⟨by omega,by exact_mod_cast hh'⟩

theorem source_nonempty_geometry {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3)
    {M : ℝ} (hs : (source N t c M).Nonempty) :
    M ≤ clipLo N t c M ∧ clipLo N t c M ≤ clipHi N t c M ∧
      clipHi N t c M ≤ 2*M := by
  obtain ⟨p,hp⟩ := hs
  obtain ⟨hp,hu,hv⟩ := Finset.mem_filter.mp hp
  have hf := (mem_headCarrier_iff hc).mp hp
  have hw := (natural_Ico_iff_Ioc (headLo N t c) (headHi N t c) p).mp hf.2.2
  exact ⟨le_max_left _ _,
    (max_lt hu hw.1).le.trans (le_min hv hw.2), min_le_left _ _⟩

theorem source_eq_prime_filter {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3)
    {M : ℝ} (hM : 1 ≤ M) (hs : (source N t c M).Nonempty) :
    source N t c M =
      (primeSWInterval (clipLo N t c M) (clipHi N t c M)).filter
        (fun p => p.Prime ∧ p.Coprime N) := by
  obtain ⟨hul,hlh,hhu⟩ := source_nonempty_geometry hc hs
  have hl0 : 0 ≤ clipLo N t c M := by linarith
  have hh0 : 0 ≤ clipHi N t c M := by linarith
  ext p
  have hfloor : p ∈ primeSWInterval (clipLo N t c M) (clipHi N t c M) ↔
      clipLo N t c M < (p : ℝ) ∧ (p : ℝ) ≤ clipHi N t c M := by
    simp only [primeSWInterval, Finset.mem_Ioc, Nat.floor_lt hl0]
    constructor
    · rintro ⟨hl,hh⟩
      exact ⟨hl,(show (p : ℝ) ≤ (Nat.floor (clipHi N t c M) : ℝ) by
        exact_mod_cast hh).trans (Nat.floor_le hh0)⟩
    · rintro ⟨hl,hh⟩
      exact ⟨hl,Nat.le_floor hh⟩
  simp only [source, Finset.mem_filter, mem_headCarrier_iff hc, hfloor,
    clipLo, clipHi, max_lt_iff, le_min_iff]
  rw [natural_Ico_iff_Ioc]
  tauto

theorem source_weighted_sum_eq_interval {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3)
    {M : ℝ} (hM : 1 ≤ M) (hs : (source N t c M).Nonempty)
    (f : ℝ → ℂ) (F : ℕ → ℂ) :
    (∑ p ∈ source N t c M, f p * F p) =
      ∑ p ∈ primeSWInterval (clipLo N t c M) (clipHi N t c M),
        targetDeleted N (profilePrimeCoefficient f) p * F p := by
  rw [source_eq_prime_filter hc hM hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hcop : p.Coprime N <;>
    simp [targetDeleted, profilePrimeCoefficient, primeSWBeta, hprime, hcop]

/-- Both k-unit gates and the original target deletion survive literally. -/
theorem source_rowTransform_eq_interval {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3)
    {M : ℝ} (hM : 1 ≤ M) (hs : (source N t c M).Nonempty)
    (f : ℝ → ℂ) (k r : ℕ) (psi : DirichletCharacter ℂ r) :
    rowTransform (source N t c M) (fun n => f n) k r psi =
      rowTransform (primeSWInterval (clipLo N t c M) (clipHi N t c M))
        (targetDeleted N (profilePrimeCoefficient f)) k r psi := by
  unfold rowTransform
  rw [source_eq_prime_filter hc hM hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hcop : p.Coprime N <;>
    by_cases hk : p.Coprime k <;>
    simp [targetDeleted, profilePrimeCoefficient, primeSWBeta, hprime, hcop, hk]

theorem source_smallConductorContribution_eq_interval
    {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3) {M : ℝ} (hM : 1 ≤ M)
    (hs : (source N t c M).Nonempty) (f : ℝ → ℂ)
    (R Q : ℕ) (T : Finset ℕ) (b : ℕ → ℂ) :
    smallConductorContribution R Q (source N t c M) T (fun n => f n) b =
      smallConductorContribution R Q
        (primeSWInterval (clipLo N t c M) (clipHi N t c M)) T
        (targetDeleted N (profilePrimeCoefficient f)) b := by
  unfold smallConductorContribution
  simp_rw [source_rowTransform_eq_interval hc hM hs f]

/-- Exact positive-support caps needed by the existing integer bridge. -/
theorem source_subset_Icc {N c : ℕ} {t : ℕ × ℕ} {M : ℝ} (hM : 1 ≤ M) :
    source N t c M ⊆ Finset.Icc 1 (Nat.floor (2*M)) := by
  intro p hp
  obtain ⟨hp,hu,hv⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_Icc.mpr ⟨(headCarrier_prime_and_target_deleted hp).1.pos,
    Nat.le_floor hv⟩

theorem prime_interval_subset_Icc {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3)
    {M : ℝ} (hM : 1 ≤ M) (hs : (source N t c M).Nonempty) :
    primeSWInterval (clipLo N t c M) (clipHi N t c M) ⊆
      Finset.Icc 1 (Nat.floor (2*M)) := by
  obtain ⟨hlo,huv,hhi⟩ := source_nonempty_geometry hc hs
  intro p hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_Ioc.mp hp
  apply Finset.mem_Icc.mpr
  constructor
  · omega
  · exact hp2.trans (Nat.floor_mono hhi)

/-- Calls O's actual variable-profile theorem, after the literal endpoint
dictionary. Constants precede N,t,c,M, all profiles, R,Q and the complement. -/
theorem actual_head_small_conductors
    {eta J A W Ctarget : ℝ} (heta : 0 < eta) (hW : 0 ≤ W)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x M : ℝ, x0 ≤ x → x^eta ≤ M → 1 ≤ M →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ x^Ctarget →
      ∀ t : ℕ × ℕ, ∀ c : ℕ, c ≤ 3 → (source N t c M).Nonempty →
      ∀ f : ℝ → ℂ,
      (∀ y ∈ Icc (clipLo N t c M) (clipHi N t c M), DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc (clipLo N t c M) (clipHi N t c M)) →
      profileAbelNorm f (clipLo N t c M) (clipHi N t c M) ≤ W*Real.log x^J →
      (∀ y ∈ Icc (clipLo N t c M) (clipHi N t c M), ‖f y‖ ≤ W*Real.log x^J) →
      ∀ R Q : ℕ, ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (source N t c M) T (fun n => f n) b ≤
        C*M*rowMass T b*(R : ℝ)^2*(1+Real.log (max 1 (Q : ℝ)))^2/Real.log x^A := by
  obtain ⟨C,hC,x0,hx0,hactual⟩ :=
    variable_profile_small_conductors heta hW hCtarget (A := A) (J := J)
  refine ⟨C,hC,x0,hx0,?_⟩
  intro x M hx hpow hM N hN htarget t c hc hs f hfd hfi hvar hsize R Q T b
  obtain ⟨hlo,huv,hhi⟩ := source_nonempty_geometry hc hs
  rw [source_smallConductorContribution_eq_interval hc hM hs]
  exact hactual x M _ _ hx hpow hM hlo huv hhi f hfd hfi hvar hsize
    N hN htarget R Q T b

/-- Reuse the proved positive natural/integer bridge, with an actual cap;
no second cast proof or residue-count loss is introduced. -/
theorem source_lowConductorTotal_eq_interval
    {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3) {M : ℝ} (hM : 1 ≤ M)
    (hs : (source N t c M).Nonempty) (f : ℝ → ℂ)
    (V Q b0 : ℕ) (T : Finset ℕ) (b : ℕ → ℂ) (hT : T ⊆ Finset.Icc 1 V) :
    P2GammaConductorScaleThreshold.lowConductorTotal
      (paddedRow (source N t c M) (fun n => f n)) (paddedRow T b)
      0 0 (Nat.floor (2*M)) V Q b0 =
    P2GammaConductorScaleThreshold.lowConductorTotal
      (paddedRow (primeSWInterval (clipLo N t c M) (clipHi N t c M))
        (targetDeleted N (profilePrimeCoefficient f))) (paddedRow T b)
      0 0 (Nat.floor (2*M)) V Q b0 := by
  rw [lowConductorTotal_eq_smallConductorContribution _ _ _ _ _ _ _ _
      (source_subset_Icc hM) hT,
    lowConductorTotal_eq_smallConductorContribution _ _ _ _ _ _ _ _
      (prime_interval_subset_Icc hc hM hs) hT]
  exact source_smallConductorContribution_eq_interval hc hM hs f _ _ T b

/-- Weighted support, for every arithmetic test after the fixed head row. -/
theorem head_grid_weighted_sum_eq_source {N c : ℕ} {t : ℕ × ℕ}
    {δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2) (j : ℕ)
    (F : ℕ → ℂ) :
    (∑ p ∈ headCarrier N t c, complexWeight δ j p * F p) =
      ∑ p ∈ source N t c (lower δ j), complexWeight δ j p * F p := by
  unfold source
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : lower δ j < (p : ℝ) ∧ (p : ℝ) ≤ 2*lower δ j
  · simp only [hband, if_true]
  · have hz : complexWeight δ j p = 0 := by
      by_contra hn
      have hw : weight δ j p ≠ 0 := fun h => hn (by simp [complexWeight,h])
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
      obtain ⟨hl,hu⟩ := weight_nonzero_support hδ hp0 j hw
      exact hband ⟨hl,hu.le.trans (upper_le_two_lower hdyadic j)⟩
    simp [hband,hz]

/-- The existing hat support removes the dyadic cut exactly. -/
theorem head_grid_rowTransform_eq_source {N c : ℕ} {t : ℕ × ℕ}
    {δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2) (j k r : ℕ)
    (psi : DirichletCharacter ℂ r) :
    rowTransform (headCarrier N t c) (fun n => complexWeight δ j n) k r psi =
      rowTransform (source N t c (lower δ j))
        (fun n => complexWeight δ j n) k r psi := by
  unfold rowTransform source
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hband : lower δ j < (p : ℝ) ∧ (p : ℝ) ≤ 2*lower δ j
  · simp only [hband, if_true]
  · have hz : complexWeight δ j p = 0 := by
      by_contra hn
      have hw : weight δ j p ≠ 0 := fun h => hn (by simp [complexWeight,h])
      have hp0 : (0 : ℝ) < p := by
        exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
      obtain ⟨hl,hu⟩ := weight_nonzero_support hδ hp0 j hw
      exact hband ⟨hl,hu.le.trans (upper_le_two_lower hdyadic j)⟩
    simp [hband,hz]

theorem head_grid_rowTransform_eq_interval {N c : ℕ} {t : ℕ × ℕ}
    (hc : c ≤ 3) {δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2)
    (j : ℕ) (hM : 1 ≤ lower δ j) (hs : (source N t c (lower δ j)).Nonempty)
    (k r : ℕ) (psi : DirichletCharacter ℂ r) :
    rowTransform (headCarrier N t c) (fun n => complexWeight δ j n) k r psi =
      rowTransform (primeSWInterval (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)))
        (targetDeleted N (profilePrimeCoefficient (complexWeight δ j))) k r psi := by
  rw [head_grid_rowTransform_eq_source hδ hdyadic]
  exact source_rowTransform_eq_interval hc hM hs _ k r psi

theorem head_grid_weighted_sum_eq_interval {N c : ℕ} {t : ℕ × ℕ}
    (hc : c ≤ 3) {δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2)
    (j : ℕ) (hM : 1 ≤ lower δ j) (hs : (source N t c (lower δ j)).Nonempty)
    (F : ℕ → ℂ) :
    (∑ p ∈ headCarrier N t c, complexWeight δ j p * F p) =
      ∑ p ∈ primeSWInterval (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)),
        targetDeleted N (profilePrimeCoefficient (complexWeight δ j)) p * F p := by
  rw [head_grid_weighted_sum_eq_source hδ hdyadic]
  exact source_weighted_sum_eq_interval hc hM hs _ F

theorem head_grid_smallConductorContribution_eq_source
    (N c : ℕ) (t : ℕ × ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hdyadic : 2*δ ≤ Real.log 2) (j R Q : ℕ) (T : Finset ℕ) (b : ℕ → ℂ) :
    smallConductorContribution R Q (headCarrier N t c) T
      (fun n => complexWeight δ j n) b =
      smallConductorContribution R Q (source N t c (lower δ j)) T
        (fun n => complexWeight δ j n) b := by
  unfold smallConductorContribution
  simp_rw [head_grid_rowTransform_eq_source hδ hdyadic]

/-- The P complement is used verbatim: all other prime colours, their
ordering/roughness masks, multiplicities and quotient 1 remain inside beta. -/
theorem retained_cartesian_head_row_eq_interval
    {N c : ℕ} {t : ℕ × ℕ} (hc : c ≤ 3) {M : ℝ} (hM : 1 ≤ M)
    (hs : (source N t c M).Nonempty) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) (F : ℕ → ℂ) :
    (∑ p ∈ source N t c M, ∑ y ∈ rootComplementLabels N t (c::cs),
      (complexWeight δ j p * betaLabel N t H δ j l y) *
        F (product (t.1*t.2) y*p)) =
      ∑ p ∈ primeSWInterval (clipLo N t c M) (clipHi N t c M),
        ∑ y ∈ rootComplementLabels N t (c::cs),
          (targetDeleted N (profilePrimeCoefficient (complexWeight δ j)) p *
            betaLabel N t H δ j l y) * F (product (t.1*t.2) y*p) := by
  simpa only [Finset.mul_sum, mul_assoc] using
    source_weighted_sum_eq_interval hc hM hs (complexWeight δ j)
      (fun p => ∑ y ∈ rootComplementLabels N t (c::cs),
        betaLabel N t H δ j l y * F (product (t.1*t.2) y*p))

/-- Direct attachment to the existing P original retained-row identity.
There is no source identity among the premises, and F remains arbitrary. -/
theorem original_retained_row_eq_prime_interval
    {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N) (hc : c ≤ 3)
    {H δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2)
    (j l : ℕ) (hM : 1 ≤ lower δ j)
    (hs : (source N t c (lower δ j)).Nonempty) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (complexWeight δ j (labelHead x) * betaLabel N t H δ j l (labelComplement x)) *
        F (product (t.1*t.2) x)) =
      ∑ p ∈ primeSWInterval (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)),
        ∑ y ∈ rootComplementLabels N t (c::cs),
          (targetDeleted N (profilePrimeCoefficient (complexWeight δ j)) p *
            betaLabel N t H δ j l y) * F (product (t.1*t.2) y*p) := by
  rw [original_retained_row_eq_cartesian ht c cs hδ j l F]
  have hcut := head_grid_weighted_sum_eq_source (N := N) (c := c) (t := t)
    hδ hdyadic j
    (fun p => ∑ y ∈ rootComplementLabels N t (c::cs),
      betaLabel N t H δ j l y * F (product (t.1*t.2) y*p))
  have hcut' :
      (∑ p ∈ headCarrier N t c, ∑ y ∈ rootComplementLabels N t (c::cs),
        (complexWeight δ j p * betaLabel N t H δ j l y) *
          F (product (t.1*t.2) y*p)) =
      ∑ p ∈ source N t c (lower δ j), ∑ y ∈ rootComplementLabels N t (c::cs),
        (complexWeight δ j p * betaLabel N t H δ j l y) *
          F (product (t.1*t.2) y*p) := by
    simpa only [Finset.mul_sum, mul_assoc] using hcut
  rw [hcut']
  exact retained_cartesian_head_row_eq_interval hc hM hs cs H δ j l F

theorem original_retained_row_eq_zero_of_empty
    {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N)
    {H δ : ℝ} (hδ : 0 < δ) (hdyadic : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hs : source N t c (lower δ j) = ∅) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (complexWeight δ j (labelHead x) * betaLabel N t H δ j l (labelComplement x)) *
        F (product (t.1*t.2) x)) = 0 := by
  rw [original_retained_row_eq_cartesian ht c cs hδ j l F]
  have hcut := head_grid_weighted_sum_eq_source (N := N) (c := c) (t := t)
    hδ hdyadic j
    (fun p => ∑ y ∈ rootComplementLabels N t (c::cs),
      betaLabel N t H δ j l y * F (product (t.1*t.2) y*p))
  simpa only [hs, Finset.sum_empty, Finset.mul_sum, mul_assoc] using hcut

/-- Existing fixed Abel budget + actual variable-profile prime supplier
for the WHOLE original head hat row. Empty clipped rows are zero; their
endpoints are never passed to SW. D,C,x0 precede every varying chart. -/
theorem actual_head_grid_small_conductors
    {eta J A W Ctarget : ℝ} (heta : 0 < eta) (hW : 0 ≤ W)
    (hCtarget : 0 ≤ Ctarget) :
    ∃ D : ℝ, 1 ≤ D ∧ ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x : ℝ, x0 ≤ x → ∀ δ : ℝ, 0 < δ → 2*δ ≤ Real.log 2 →
      ∀ j : ℕ, x^eta ≤ lower δ j → 1 ≤ lower δ j →
      1+2*D/δ ≤ W*Real.log x^J →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ x^Ctarget →
      ∀ t : ℕ × ℕ, ∀ c : ℕ, c ≤ 3 →
      ∀ R Q : ℕ, ∀ T : Finset ℕ, ∀ b : ℕ → ℂ,
      smallConductorContribution R Q (headCarrier N t c) T
        (fun n => complexWeight δ j n) b ≤
      C*lower δ j*rowMass T b*(R : ℝ)^2*
        (1+Real.log (max 1 (Q : ℝ)))^2/Real.log x^A := by
  obtain ⟨D,hD,hbudget⟩ := exists_complexWeight_Abel_budget
  obtain ⟨C,hC,x0,hx0,hactual⟩ := actual_head_small_conductors heta hW hCtarget
    (A := A) (J := J)
  refine ⟨D,hD,C,hC,x0,hx0,?_⟩
  intro x hx δ hδ hdyadic j hpow hM hnorm N hN htarget t c hc R Q T b
  have hlog : 0 < Real.log x := Real.log_pos (hx0.trans_le hx)
  rw [head_grid_smallConductorContribution_eq_source N c t hδ hdyadic]
  by_cases hs : (source N t c (lower δ j)).Nonempty
  · obtain ⟨hlo,huv,hhi⟩ := source_nonempty_geometry hc hs
    have hsub : Icc (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)) ⊆
        Ioi (0 : ℝ) := fun y hy => (lower_pos δ j).trans_le (hlo.trans hy.1)
    have hfd : ∀ y ∈ Icc (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)),
        DifferentiableAt ℝ (complexWeight δ j) y := by
      intro y hy
      exact (complexWeight_hasDerivAt δ j (hsub hy)).differentiableAt
    have hfi : IntegrableOn (deriv (complexWeight δ j))
        (Icc (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j))) :=
      (((complexWeight_contDiffOn δ j).continuousOn_deriv_of_isOpen
        isOpen_Ioi (by norm_num)).mono hsub).integrableOn_Icc
    have hvar : profileAbelNorm (complexWeight δ j)
        (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j)) ≤ W*Real.log x^J :=
      (hbudget δ hδ j (lower δ j) _ _ (lower_pos δ j) hlo huv hhi).trans hnorm
    have h1 : 1 ≤ W*Real.log x^J := by
      have hnonneg : 0 ≤ 2*D/δ :=
        div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hD)) hδ.le
      linarith
    exact hactual x (lower δ j) hx hpow hM N hN htarget t c hc hs
      (complexWeight δ j) hfd hfi hvar
      (fun y _ => (complexWeight_norm_le_one δ j y).trans h1) R Q T b
  · have hempty : source N t c (lower δ j) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hempty, smallConductorContribution, rowTransform, Finset.sum_empty,
      norm_zero, zero_mul, Finset.sum_const_zero, mul_zero]
    have hmass := rowMass_nonneg T b
    have hMpos := lower_pos δ j
    positivity

end
end ImbalancedChen.P2GammaHeadWindowDictionary
