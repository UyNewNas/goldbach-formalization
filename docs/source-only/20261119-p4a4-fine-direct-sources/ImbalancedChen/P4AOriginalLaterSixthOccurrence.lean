import ImbalancedChen.P4AOriginalLaterSixthPredecessor

/-! One finite resolution and one early mesh cover all later source
pieces. The actual fifth frontier admits their prime words and the
actual sixth bank adopts each own rounded endpoint. -/
namespace ImbalancedChen.P4AOriginalLaterSixthOccurrence
noncomputable section
open Set Filter VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalLaterSixthKernel (Piece action eval lower)
open P2OriginalLaterSixthInnerTests (trim trim_compact trim_region box)
open P4AOriginalLaterSixthMesh (Owner)
open P4AOriginalSavedSixthHistoricalOwner (bank root pre_list pre_len pre_log)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalSixthLaterLiteral (stage)
open P4AOriginalSixthLaterSemantics (comparison endpoint Source)
open P4AOriginalSixthActionBank (selected GeometricSource)
open P4AOriginalFull87HistoryCore (width width_pos)
open P1QuantizedActionLicense (Gate gate LowerLicense rounded_licensed)
open P1GuardFrozenFiniteCapAlgebra (rounded rounded_error)
open P4AOriginalFull87DataPolicy (Accepted)
open P4AOriginalOrderedSixthStages (orderedLevel)
open P4AOriginalOrderedSixthSigned (admitted)
open P4AOriginalFull87RawChronology (cutoff)
open Certificates.P2OriginalSixthElevenLogSemantics (S6 H5)
open P2OriginalSixthSimplexMoments (Point)

theorem gap_continuous (i : Piece) : Continuous (fun t : Point=>endpoint (action i) t-comparison (action i) t) := by
  have hc := P2OriginalLaterSixthSourceIntegral.continuous_eval
    (lower (P4AOriginalLaterSixthPriorGeometry.embed (action i)))
  simp only [P2OriginalLaterSixthKernel.eval_lower,P4AOriginalLaterSixthPriorGeometry.ordinary_embed,
    P4AOriginalLaterSixthPriorGeometry.action_embed,Bool.false_eq_true,if_false] at hc
  exact (P4AOriginalSixthActionBank.endpoint_continuous (.later (action i))).sub hc

theorem resolution {s : ℝ} (hs : 0<s) : ∃ n0 : ℕ,∀ n≥n0,∀ i : Piece,∀ t∈trim i s,
    let c := action i
    LowerLicense (selected (.later c)) t (rounded n (endpoint c t):ℝ) ∧
    (rounded n (endpoint c t):ℝ)+width n≤v (∑ j∈selected (.later c),t j) ∧
    comparison c t<(rounded n (endpoint c t):ℝ) := by
  let I := Piece×Option (Gate 6)
  let gap := fun (u : I) (t : Point)=> match u.2 with
    | none => endpoint (action u.1) t-comparison (action u.1) t
    | some g => endpoint (action u.1) t-gate (selected (.later (action u.1))) t g
  have h (u : I) : ∃ d : ℝ,0<d ∧ ∀ t∈trim u.1 s,d≤gap u t := by
    apply (trim_compact _ _).exists_forall_le'
    · rcases u with ⟨i,_|g⟩
      · exact (gap_continuous i).continuousOn
      · exact ((P4AOriginalSixthActionBank.endpoint_continuous (.later (action i))).sub
          (P4AOriginalSixthActionBank.gate_continuous (.later (action i)) g)).continuousOn
    · intro t ht
      have hsrc := (trim_region hs ht).1.2.1
      have hg := (P4AOriginalLaterSixthHistoryRows.source_margins (action u.1) t hsrc).2.2.2.1
      have hgeo : GeometricSource (.later (action u.1)) t := ⟨hsrc,hg⟩
      cases hu : u.2 with
      | none => simpa only [gap,hu] using sub_pos.mpr hg
      | some g => simpa only [gap,hu] using sub_pos.mpr
          (P4AOriginalSixthActionBank.geometric_lower_license (.later (action u.1)) t hgeo g)
  choose b hb hf using h
  obtain ⟨d,hd,hmin⟩ := P1QuantizedActionLicense.exists_positive_floor
    (Finset.univ : Finset I) (fun _=>True) b (fun j _ _=>hb j)
  obtain ⟨n0,hn⟩ := P1QuantizedActionLicense.exists_resolution d hd
  refine ⟨n0,?_⟩
  intro n hnn i t ht
  let c := action i
  let a := P4AOriginalSixthActionBank.Action.later c
  have hsrc := (trim_region hs ht).1.2.1
  have hg := (P4AOriginalLaterSixthHistoryRows.source_margins c t hsrc).2.2.2.1
  have hgeo : GeometricSource a t := ⟨hsrc,hg⟩
  have hgap : d≤endpoint c t-comparison c t :=
    (hmin (i,none) (Finset.mem_univ _) trivial).trans (hf (i,none) t ht)
  have hgate (g : Gate 6) : gate (selected a) t g+d≤endpoint c t := by
    have hh : d≤endpoint c t-gate (selected a) t g :=
      (hmin (i,some g) (Finset.mem_univ _) trivial).trans (hf (i,some g) t ht)
    linarith
  obtain ⟨h0,hcap⟩ := P4AOriginalLaterSixthPredecessor.endpoint_range c hsrc
  have hw := hn n hnn
  have hlic := rounded_licensed n (selected a) t (endpoint c t) d hd hcap hgate hw
  have hround := rounded_error n _ h0 hcap
  refine ⟨fun g=>by have hg' := hlic.1 g;linarith [width_pos n],
    hlic.2.trans (P4AOriginalSixthActionBank.geometric_upper_license a t hgeo),?_⟩
  linarith only [hgap,hw,hround.1,width_pos n]

def primes (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 6=>P2OriginalSixthMomentRow.cutoff) (fun _=>(1/5:ℝ))

structure Caps (n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) (p : Fin 6→ℕ) (i : Piece) : Prop where
  admitted : p∈P4AOriginalOrderedSixthSigned.admitted n (bank e q a) omega N N (cutoff N)
  previous : orderedLevel (stage (action i)+2) n (bank e q a) omega (N:ℝ) (pre p) ≤
    eval (lower i) (actualPrimeTupleLog N p)
  endpoint_floor : (rounded n (endpoint (action i) (actualPrimeTupleLog N p)):ℝ)≤
    orderedLevel (stage (action i)+3) n (bank e q a) omega (N:ℝ) (pre p)
  strict : eval (lower i) (actualPrimeTupleLog N p)<(rounded n (endpoint (action i) (actualPrimeTupleLog N p)):ℝ)

theorem exists_caps {s : ℝ} (hs : 0<s) : ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧
    ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∀ N : ℕ,1<N → ∀ p∈primes N,∀ i : Piece,actualPrimeTupleLog N p∈trim i s → Caps n e q a omega N p i := by
  obtain ⟨n0,hn0⟩ := resolution hs
  obtain ⟨E,hE,hm⟩ := P4AOriginalLaterSixthMesh.exists_mesh hs
  refine ⟨n0,?_⟩
  intro n hn
  refine ⟨E,hE,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq'⟩ := hm e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa N hN p hp i ht
  let d := bank e q a
  let t := actualPrimeTupleLog N p
  let c := action i
  let h := pre p
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  obtain ⟨hpri,_⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
  have hpos (j) := (hpri j).1.pos
  obtain ⟨hown,hreg⟩ := trim_region hs ht
  have hsrc := hown.2.1
  have ho := hq' q hq a ha N hN p hpos i ht
  obtain ⟨hl,hu,hstrict⟩ := hn0 n hn i t ht
  have hacc : Accepted n d (N:ℝ) h (.later c) :=
    ⟨P4AOriginalLaterSixthPredecessor.eligible hown hreg ho,
      by simpa only [h,pre_log] using hl,by simpa only [h,pre_log] using hu⟩
  have hs5 := (P4AOriginalLaterSixthPredecessor.fifth_bounds n hown ho).1
  have hanti := (P4AOriginalSixthSquareRows.later_source_basic c t hsrc).2.2.2
  have hpa : StrictAnti p := by
    intro j l hjl
    have hh := Real.rpow_lt_rpow_of_exponent_lt hNr (hanti hjl)
    rw [actualPrimeTupleLog_rpow hN p hpos,actualPrimeTupleLog_rpow hN p hpos] at hh
    exact_mod_cast hh
  let L := root d N p
  have hseed : P5OriginalCommonRefinedConstructor.originalSeed d (N:ℝ) [p 2,p 1,p 0]=L := by
    rw [show L=P5OriginalCommonRefinedConstructor.originalSeed d (N:ℝ) h from ho.seed]
    simp [h,pre_list,rosserAncestor,P5OriginalCommonRefinedConstructor.originalSeed,
      P1OriginalVariableFourthContinuation.seedExponent]
  have h5 : L≤P4AOriginalFull87DataPolicy.level5Exponent n d (N:ℝ) [p 4,p 3,p 2,p 1,p 0] := by
    simpa [pre_list,rosserAncestor] using hs5
  have hsel := P4AOriginalSixthTupleReverse.from_own_root n d hN p (fun j=>(hpri j).1) hpa L ho.stop
    hseed ho.initial.le ho.first ho.third ho.fifth h5
  have hcap : cutoff N≤(N:ℝ) := by simpa only [cutoff,Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (19/96:ℝ)≤1)
  have hx := (P4AOriginalSixthSquareRows.later_source_basic c t hsrc).1
  have hold : p∈P4AOriginalSavedSixthSigned.admitted n d N N (cutoff N) := by
    apply (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 6 _ N N 0 _ hcap p).mpr
    refine ⟨hpa,fun j=>⟨(hpri j).1,(hpri j).2,Nat.cast_nonneg _,?_⟩,hsel⟩
    rw [←actualPrimeTupleLog_rpow hN p hpos j]
    apply Real.rpow_lt_rpow_of_exponent_lt hNr
    exact (hanti.antitone (Fin.zero_le j)).trans_lt (hx.trans (by norm_num))
  have her : 0≤(d.e:ℝ) := by exact_mod_cast he.le
  have transfer (k : ℕ) : orderedLevel (k+2) n d omega (N:ℝ) h=P4AOriginalLaterSixthStages.level n d (N:ℝ) h k :=
    (P4AOriginalOrderedSixthStages.level_on_owner _ n d omega _ her hNr.le hwa h ho.supported).trans
      (P4AOriginalOrderedSixthStages.prior_later k n d _ h)
  refine ⟨(P4AOriginalOrderedFifthOwner.admitted_iff_on_owner n d her hNr.le hwa p ho.supported).mpr hold,
    (transfer (stage c)).le.trans (P4AOriginalLaterSixthPredecessor.active_bounds n hown hreg ho _ le_rfl),
    ?_,(P4AOriginalLaterSixthPredecessor.low_le_comparison i hown).trans_lt hstrict⟩
  have had := P4AOriginalLaterSixthStages.active_row n d (N:ℝ) h c ho.active hacc
  rw [show primeHistoryLogCoordinates (N:ℝ) 6 h=t from pre_log N p] at had
  exact had.trans (transfer (stage c+1)).symm.le

end
end ImbalancedChen.P4AOriginalLaterSixthOccurrence
