import ImbalancedChen.P4AOriginalOrderedFifthOwner
import ImbalancedChen.P4AOriginalSavedSixthActualGain

/-! The genuine G4 increment on the corrected whole ordered third: all
raw saved actions require one of the original G4 boxes, and every such
box is a supported old owner on the same mesh at every target. Both
fifth decisions and both saved cap values are compared on their own
admitted carriers. The possibly different decisions elsewhere contribute zero. -/
namespace ImbalancedChen.P4AOriginalOrderedSavedGain
noncomputable section
open Filter
open scoped Classical BigOperators Topology
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root saved accepted eligible prior)
open P4AOriginalOrderedSixthStages (level rawAt finiteAt savedLicensed savedRaw orderedLevel policy orderedFifth)
open P4AOriginalSavedSixthSigned (pre old)
open P4AOriginalSavedSixthArchive (Row Source)
open P4AOriginalSavedSixthHistoricalOwner (actual_owner pre_log bank)
open P4AOriginalSavedSixthSourceGates (source_iff)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalNewFifthCoverage (Schedule)
open P1OriginalFifthGrid400RefinedFullBoxCover
open P5OriginalCommonPositivePresieve (normalize)

theorem fixed_outside (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ)
    (hs : ∀ i : Row,¬Source i (primeHistoryLogCoordinates N 6 h)) :
    level 1 n R d N h=level 0 n R d N h := by
  by_cases hr : R.lower
  · simp only [level,if_pos hr,finiteAt,savedLicensed]
    apply P1OriginalVariableFourthContinuation.finiteMax_eq_seed_of_outside
    intro i _ ha
    exact hs i ha.1.2.1
  · simp only [level,if_neg hr,rawAt,savedRaw]
    apply P1OriginalVariableFourthContinuation.finiteMax_eq_seed_of_outside
    intro i _ ha
    exact hs i ha.2.1

theorem residual_outside (n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (p : Fin 6→ℕ)
    (hs : ∀ i : Row,¬Source i (actualPrimeTupleLog N p)) :
    P4AOriginalOrderedSixthSigned.tupleResidual 0 n d omega N cap p=0 := by
  have he := fixed_outside n (P4AOriginalOrderedThirdFullPolicy.current d omega N (pre p)) d (N:ℝ)
    (pre p) (fun i => by rw [pre_log]; exact hs i)
  simp only [P4AOriginalOrderedSixthSigned.tupleResidual,orderedLevel,Nat.zero_add,he,
    actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div]

theorem residual_on_owner (n : ℕ) (d : OriginalData) {omega : ℝ} {N cap : ℕ}
    (he : 0≤(d.e:ℝ)) (hN : 1≤(N:ℝ)) (hwa : omega≤d.omega) (p : Fin 6→ℕ)
    (hs : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) (pre p)) :
    P4AOriginalOrderedSixthSigned.tupleResidual 0 n d omega N cap p =
    P4AOriginalSavedSixthSigned.tupleResidual n d N cap p := by
  simp only [P4AOriginalOrderedSixthSigned.tupleResidual,Nat.zero_add,
    P4AOriginalOrderedSixthStages.level_on_owner _ n d omega N he hN hwa (pre p) hs,
    P4AOriginalOrderedFifthOwner.prior_zero,P4AOriginalOrderedSixthStages.prior_saved,
    P4AOriginalSavedSixthSigned.tupleResidual]

theorem source_owner {e : ℚ} {q : ℕ} {a : ℝ} (hs : Schedule e q a) {N : ℕ} (hN : 1<N)
    (p : Fin 6→ℕ) (i : Row) (h : Source i (actualPrimeTupleLog N p)) :
    let d := bank e q a
    P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) (pre p) := by
  have ht := ((source_iff i _).mp h).1
  have hp (j : Fin 6) : 0<p j := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    have hl := (P4AOriginalSavedSixthPrimeMean.bounds i ht j).1
    norm_num [actualPrimeTupleLog,hz] at hl
  exact (actual_owner i hs hN p hp ht).active.2

def gain (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) : ℝ :=
  let d := bank e q a
  rawRoot (orderedFifth n d omega (N:ℝ)) N-rawRoot (policy 1 n d omega (N:ℝ)) N

theorem exact_gain (n : ℕ) {e : ℚ} {q : ℕ} {a omega : ℝ} (hs : Schedule e q a)
    (hwa : omega≤a) {N : ℕ} (hN : 1<N) (cap : ℕ) (z : ℝ) :
    normalize N (P4AOriginalVariableFifthPhysicalLedger.raw (orderedFifth n (bank e q a) omega N) N cap 0 z-
      P4AOriginalVariableFifthPhysicalLedger.raw (policy 1 n (bank e q a) omega N) N cap 0 z)=
    normalize N (P4AOriginalVariableFifthPhysicalLedger.raw (P4AOriginalFull87DataPolicy.fifthPolicy n (bank e q a) N) N cap 0 z-
      P4AOriginalVariableFifthPhysicalLedger.raw (P4AOriginalSavedSixthStage.policy n (bank e q a) N) N cap 0 z) := by
  let d := bank e q a
  let A := P4AOriginalOrderedSixthSigned.admitted n d omega N cap z
  let B := P4AOriginalSavedSixthSigned.admitted n d N cap z
  let own := fun p : Fin 6→ℕ => ∃ i : Row,Source i (actualPrimeTupleLog N p)
  let f := fun p : Fin 6→ℕ => (∏ j,weight (p j))*P4AOriginalOrderedSixthSigned.tupleResidual 0 n d omega N cap p
  let g := fun p : Fin 6→ℕ => (∏ j,weight (p j))*P4AOriginalSavedSixthSigned.tupleResidual n d N cap p
  have hNr : 1≤(N:ℝ) := by exact_mod_cast hN.le
  have he : 0≤(d.e:ℝ) := by exact_mod_cast hs.1
  have hz' (p : Fin 6→ℕ) (hn : ¬own p) : f p=0 ∧ g p=0 := by
    have hn' : ∀ i : Row,¬Source i (actualPrimeTupleLog N p) := fun i hi => hn ⟨i,hi⟩
    simp only [f,g,residual_outside n d omega N cap p hn',P4AOriginalSavedSixthOccurrence.off_source n d N cap p hn',mul_zero,and_self]
  have eqset : A.filter own=B.filter own := by
    ext p
    simp only [Finset.mem_filter]
    by_cases hp : own p
    · obtain ⟨i,hi⟩ := hp
      exact and_congr_left (fun _ => P4AOriginalOrderedFifthOwner.admitted_iff_on_owner n d he hNr hwa p
        (source_owner hs hN p i hi))
    · simp [hp]
  have hf : (∑ p∈A.filter own,f p)=∑ p∈A,f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hh : own p <;> simp [hh]
    exact (hz' p hh).1.symm
  have hg : (∑ p∈B.filter own,g p)=∑ p∈B,g p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hh : own p <;> simp [hh]
    exact (hz' p hh).2.symm
  rw [←P4AOriginalOrderedSixthStages.policy_zero n d omega (N:ℝ),
    P4AOriginalOrderedSixthSigned.signed_at_stage 0 n d omega N cap z hNr,
    P4AOriginalSavedSixthSigned.original_raw_difference_eq_admitted n d N cap z hNr]
  change (∑ p∈A,f p)=∑ p∈B,g p
  rw [←hf,←hg,eqset]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hp).2
  simp only [f,g,residual_on_owner n d (cap:=cap) he hNr hwa p (source_owner hs hN p i hi)]

/-- The old G4 arithmetic floor is therefore paid on the corrected policy
for every later physical cutoff below the early activation. -/
theorem exists_original_G4 (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<1/64000 →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a : ℝ,a≤1/800 →
    ∀ᶠ N : ℕ in atTop,Even N → ∀ omega : ℝ,omega≤a →
      currentUpperEighteenGains 3-eps<normalize N (gain n e q a omega N) := by
  obtain ⟨n0,hn⟩ := P4AOriginalSavedSixthActualGain.exists_actual_saved_gain eps heps
  refine ⟨n0,?_⟩
  intro n hnn e he hee
  obtain ⟨qa,hqa,hgain⟩ := hn n hnn e he hee
  obtain ⟨qb,hqb,hstep⟩ := exists_refinement_step_le_half ((e:ℝ)/10) (by positivity)
  refine ⟨max qa qb,hqa.trans_le (le_max_left _ _),?_⟩
  intro q hq a ha
  have hq' := (le_max_right _ _).trans hq
  have hpos := hqb.trans_le hq'
  have hm : logPrimeMeshStep 0 (19/96) (refinedMesh q)≤logPrimeMeshStep 0 (19/96) (refinedMesh qb) := by
    rw [refined_step q hpos,refined_step qb hqb]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast hq') (by norm_num))
  have hs : Schedule e q a := ⟨by exact_mod_cast he.le,by exact_mod_cast hee.le,hpos,
    hm.trans (by linarith only [hstep]),ha⟩
  filter_upwards [hgain q ((le_max_left _ _).trans hq) a ha,eventually_ge_atTop 2] with N h hN
  intro hev omega hwa
  have heq := exact_gain n hs hwa (show 1<N by omega) N (cutoff N)
  change normalize N (gain n e q a omega N)=normalize N (P4AOriginalSavedSixthStage.before n (bank e q a) N) at heq
  rw [heq]
  exact h hev

end
end ImbalancedChen.P4AOriginalOrderedSavedGain
