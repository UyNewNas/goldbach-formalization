import ImbalancedChen.P4AOriginalFull87EighthKernelTransport
import ImbalancedChen.P4AOriginalFull87LicensedBoxIntegration

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The real kernel is evaluated at the OWN sixth level actually used by the
new filtered policy, not the old raw maximum or a caller-supplied parent.
The original common-history supplier and canonical new-tree members are
retained. This is a residual-kernel lower estimate with a quantitative
analytic budget. The arithmetic signed-frontier-to-integral bridge, saved
endpoint authentication and the two reserves remain separate obligations.
-/
namespace ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87EighthKernelControl P4AOriginalFull87EighthKernelTransport
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalFull87FiniteParentPolicy (active active_ancestor source_active)
open P4AOriginalFull87LicensedSixthPolicy (level6Exponent)
open P4AOriginalSixthLicensedFilter
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87LicensedBoxIntegration
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length)
open P4AOriginalCompleteSixthChronology (data)
open P5OriginalCommonRefinedConstructor (lambda3)
open P4AOriginalFull87HistoryCore (width width_pos oldHistory)
open P4AOriginalFull87TrimOmission (totalOmitted)
open P4AOriginalSixthCommonMargin (totalSixthOmitted)
open P4AOriginalFourthFifthUniformActionLicense (ArchiveLicenses)
open P4AOriginalFull87SixthMarginIntegration (SixthLicenses)
open P4AOriginalFull87BoxedWinner (SavedSourceSupply)
open P4AOriginalFull87AllRankBoxedProvenance (LowerWinnerSupply)

/-- A projection of the EXISTING policy level, not a substitute parent. -/
def actualParent (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ) : ℝ :=
  level6Exponent n e q om N (rosserAncestor 6 history)

theorem actualParent_eq_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (history : List ℕ) (hlen : history.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 history))
    (hr : RealizedHistory e q om N history c) :
    actualParent n e q om N history = licensedCap n e q om N (rosserAncestor 6 history) := by
  have ha := source_active e q om N history hlen c hs hr
  have ha6 := (active_ancestor e q om N 6 (by decide) history).mpr ha
  simp only [actualParent,level6Exponent,if_pos ha6]

/-- The last-prime residual floor survives the real fifth fallback. It is
proved from H7 at the old third ancestor, not assumed as a kernel licence. -/
theorem actualParent_residual (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (history : List ℕ) (hlen : history.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 history))
    (hr : RealizedHistory e q om N history c) :
    let t := primeHistoryLogCoordinates N 8 history
    t 7 < actualParent n e q om N history - total t ∧
      actualParent n e q om N history ≤ comparison c t := by
  rw [actualParent_eq_licensed n e q om N history hlen c hs hr]
  obtain ⟨_hL,h34,h45,_h56,h6R,_⟩ :=
    parent_bounds_of_history n e q om N history hlen c hs hr
  have h5 : cap5 n e q om N (rosserAncestor 5 history) ≤
      licensedCap n e q om N (rosserAncestor 6 history) := by
    simpa only [rosserAncestor_nested 5 6 (by decide)] using
      fifth_le_licensedCap n e q om N (rosserAncestor 6 history)
  have hL : lambda3 (data e q om) N (rosserAncestor 4 history) ≤
      licensedCap n e q om N (rosserAncestor 6 history) := (h34.trans h45).trans h5
  have h7 := hr.2.2.1 (3 : Fin 4)
  have horder := (source_basic hs).2.2.2 (6 : Fin 7)
  refine ⟨?_,(licensedCap_le_old n e q om N _).trans h6R⟩
  dsimp [oldHistory,P4AOriginalRemainingEighthSources.history] at h7
  norm_num at horder
  dsimp only [total]
  simp only [Fin.sum_univ_succ]
  linarith

/-- In particular this includes the formerly unsafe sixth margin
complement. Only the EXISTING eighth trim and precision are required. -/
theorem actual_eighth_kernel_transport (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om N : ℝ) (history : List ℕ) (hlen : history.length = 8)
    (c : Cell) (ht : primeHistoryLogCoordinates N 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om N history c) :
    let t := primeHistoryLogCoordinates N 8 history
    let P := actualParent n e q om N history
    let M := (finiteCap n c t : ℝ)
    cutoff < t 7 ∧ t 7 < P - total t ∧ P ≤ comparison c t ∧
      comparison c t < M ∧ M - total t < 3 * t 7 ∧
      kernel c t ≤ residual (total t) (product t) P M + roundingConstant * width n := by
  dsimp only
  have hs := trim_subset_source c (width_pos r) ht
  have hpar := actualParent_residual n e q om N history hlen c hs hr
  have hlic := finiteCap_licensed n (width_pos r) hn ht
  have hRM : comparison c (primeHistoryLogCoordinates N 8 history) <
      (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ) := by
    have hd := width_pos r
    linarith [hlic.2.1]
  have hterminal := (finiteCap_upper n hs).2
  have herr := rounded_kernel_loss r n hn ht
  have hmono := residual_parent_mono
    (total (primeHistoryLogCoordinates N 8 history))
    (product (primeHistoryLogCoordinates N 8 history))
    (actualParent n e q om N history)
    (comparison c (primeHistoryLogCoordinates N 8 history))
    (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ)
    (cutoff_pos.trans ((source_coordinate_lower hs 7).trans hpar.1))
    (source_product_lower hs).2 hpar.2 hRM
  refine ⟨source_coordinate_lower hs 7,hpar.1,hpar.2,hRM,?_,?_⟩
  · dsimp [total]; linarith
  · change roundedKernel n c (primeHistoryLogCoordinates N 8 history) ≤ _ at hmono
    linarith [herr.2.2]

/-- Output paired with the existing new-tree membership supplier. This is
an inequality for the actual residual expression, not for a prime count. -/
def ResidualSupply (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) : Prop :=
  ∀ N : ℕ, 1 < (N : ℝ) → ∀ p : Fin 8 → ℕ,
    (∀ i, (p i).Prime) → (∀ i, ¬p i ∣ N) → ∀ c : Cell,
    point (N : ℝ) p ∈ trim c (width r) →
      let t := point (N : ℝ) p
      let P := actualParent n e q om (N : ℝ) (pre p)
      let M := (finiteCap n c t : ℝ)
      cutoff < t 7 ∧ t 7 < P - total t ∧ P ≤ comparison c t ∧
        comparison c t < M ∧ M - total t < 3 * t 7 ∧
        kernel c t ≤ residual (total t) (product t) P M + roundingConstant * width n

theorem residualSupply_of_filtered (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (hn : 4 * width n < width r) (hsource : FilteredSourceSupply s r n e q om) :
    ResidualSupply r n e q om := by
  intro N hN p hp hdelete c ht
  have hr := (hsource N hN p hp hdelete c ht).1
  exact actual_eighth_kernel_transport r n hn e q om (N : ℝ) (pre p) (pre_length p) c ht hr

/-- One common PRE-N source/coarse/rounding/box schedule, now with an
ACTUAL eighth-kernel budget. The source trim returned by the existing
supplier is reused, not replaced by a separately chosen incompatible trim.
The sixth tolerance remains the prior volume tolerance, NOT a new proof
of its signed arithmetic cost. The extra box budget is kernel-weighted. -/
theorem exists_shared_licensed_eighth_kernel_schedule
    (epsilon epsilonSixth : ℝ) (he : 0 < epsilon) (h6 : 0 < epsilonSixth) :
    ∃ s r : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      totalSixthOmitted s (fun _ _ => (1 : ℝ)) < epsilonSixth ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ArchiveLicenses n e q om ∧ SixthLicenses s n e q om ∧
        4 * width n < width r ∧ 0 ≤ totalKernelLoss r n ∧
        ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
          totalKernelLoss r n + licensedBoxOmitted n e q om m kernel < epsilon ∧
          FilteredSourceSupply s r n e q om ∧ CompiledLicensedSupply n m e q om ∧
          SavedSourceSupply r e q om ∧ LowerWinnerSupply n m e q om ∧
          ResidualSupply r n e q om := by
  have hB := kernelBound_pos
  have htol : 0 < epsilon / (4 * kernelBound) := by positivity
  obtain ⟨s,r,e0,he0,hemax,hsixth,hsource,hchoose⟩ :=
    exists_shared_licensed_box_schedule (epsilon / (4 * kernelBound))
      (epsilon / 2) epsilonSixth htol (by positivity) h6
  have hweighted : totalOmitted r kernel < epsilon / 4 := by
    have hmul := mul_lt_mul_of_pos_left hsource kernelBound_pos
    have heq : kernelBound * (epsilon / (4 * kernelBound)) = epsilon / 4 := by
      field_simp [kernelBound_pos.ne']
      <;> ring
    rw [heq] at hmul
    exact (totalOmitted_kernel_le_volume r).trans_lt hmul
  obtain ⟨nLoss,hnLoss⟩ := exists_rounding_budget (epsilon / 4) (by positivity)
  obtain ⟨nCap,hnCap⟩ := exists_uniform_cap_resolution (width r) (width_pos r)
  refine ⟨s,r,e0,he0,hemax,hsixth,?_⟩
  intro e hepos hee
  obtain ⟨q0,hq0,hq⟩ := hchoose e hepos hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨nOld,hnOld⟩ := hq q hqq om hom
  refine ⟨max nOld (max nLoss nCap),?_⟩
  intro n hn
  have hnOther := (le_max_right nOld (max nLoss nCap)).trans hn
  have hcap := hnCap n ((le_max_right nLoss nCap).trans hnOther)
  have hround := hnLoss n ((le_max_left nLoss nCap).trans hnOther)
  have hbudget := totalKernelLoss_budget r n hcap
  have hloss : totalKernelLoss r n < epsilon / 2 := by linarith [hbudget.2]
  obtain ⟨hA,hS,mOld,hmOld⟩ := hnOld n ((le_max_left _ _).trans hn)
  obtain ⟨mKernel,hmKernel⟩ := exists_licensed_L1_mesh n e q om kernel
    integrableOn_kernel (epsilon / 2) (by positivity)
  refine ⟨hA,hS,hcap,hbudget.1,max mOld mKernel,?_⟩
  intro m hm
  obtain ⟨_hOldBox,hfiltered,hcompiled,hsaved,hlower⟩ := hmOld m ((le_max_left _ _).trans hm)
  have hbox := hmKernel m ((le_max_right _ _).trans hm)
  exact ⟨by linarith,hfiltered,hcompiled,hsaved,hlower,
    residualSupply_of_filtered s r n e q om hcap hfiltered⟩

end
end ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
