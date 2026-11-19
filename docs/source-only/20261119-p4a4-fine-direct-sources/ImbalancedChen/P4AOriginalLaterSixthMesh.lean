import ImbalancedChen.P4AOriginalLaterSixthFifthComparison
import ImbalancedChen.P2OriginalLaterSixthInnerTests
import ImbalancedChen.P4AOriginalElevenActualCommonHistory

/-! A single pre-target mesh supplies the actual wholly ordered third
owner on all twenty-one physical trims. The lower estimate uses R0 as
a branch of the envelope. Its upper estimate uses the true six branches,
including W and the first-three tents already compared with the ledger. -/
namespace ImbalancedChen.P4AOriginalLaterSixthMesh
noncomputable section
open Set Filter MeasureTheory VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalLaterSixthKernel (Piece action eval lower)
open P2OriginalLaterSixthInnerTests (trim trim_region trim_compact)
open P2OriginalSixthSimplexMoments (Point)
open P4AOriginalSavedSixthHistoricalOwner (bank pre_list pre_len pre_log triple triple_log firstThree ancestor_three root third_eq_seed)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalFull87GammaApproximation (actual_gamma_sandwich side_widths)
open P2OriginalSaving16HistoricalMesh (mesh_box_width mesh_box_lower_nonneg)
open HistoricalThirdCoarse (box cells mem_cells levelExponent_lt_initial)
open P5OriginalCommonRefinedConstructor (OriginalData originalSeed actualParent5)
open Certificates.P2OriginalSixthElevenLogSemantics (R0 H3 H5 S5 S6)
open P4AOriginalFull87DataPolicy (active)

def slack (t : Point) : Fin 5→ℝ := ![mu-t 0,t 0-t 1,t 1-t 2,R0 t-H3 t,R0 t-H5 t]

theorem slack_pos {i : Piece} {r : ℝ} (hr : 0<r) {t : Point} (ht : t∈trim i r)
    (k : Fin 5) : 0<slack t k := by
  have hs := (trim_region hr ht).1.2.1
  obtain ⟨hx,_,_,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic _ _ hs
  obtain ⟨h3,h5,_⟩ := P4AOriginalLaterSixthHistoryRows.source_margins _ _ hs
  fin_cases k
  · exact sub_pos.mpr hx
  · exact sub_pos.mpr (ho (by decide))
  · exact sub_pos.mpr (ho (by decide))
  · exact sub_pos.mpr h3
  · exact sub_pos.mpr h5

theorem common_margin {r : ℝ} (hr : 0<r) :
    ∃ delta : ℝ,0<delta ∧ ∀ i : Piece,∀ t∈trim i r,∀ k : Fin 5,delta≤slack t k := by
  have h (i : Piece) (k : Fin 5) : ∃ delta : ℝ,0<delta ∧ ∀ t∈trim i r,delta≤slack t k := by
    apply (trim_compact i r).exists_forall_le'
    · fin_cases k <;> dsimp [slack,R0,H3,H5,S5] <;> fun_prop
    · exact fun t ht => slack_pos hr ht k
  choose b hb hbound using h
  obtain ⟨d,hd,hmin⟩ := P1QuantizedActionLicense.exists_positive_floor
    (Finset.univ : Finset (Piece×Fin 5)) (fun _=>True) (fun x=>b x.1 x.2) (fun x _ _=>hb _ _)
  exact ⟨d,hd,fun i t ht k=>(hmin (i,k) (Finset.mem_univ _) trivial).trans (hbound i k t ht)⟩

structure Owner (d : OriginalData) (N : ℕ) (p : Fin 6→ℕ) (i : Piece) : Prop where
  supported : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) (pre p)
  active : active d (N:ℝ) (pre p)
  stop : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0]
  seed : root d N p=originalSeed d (N:ℝ) (pre p)
  initial : root d N p<HistoricalThirdCoarse.initial (d.e:ℝ)
  first : 3*actualPrimeTupleLog N p 0<root d N p
  third : H3 (actualPrimeTupleLog N p)<root d N p
  fifth : H5 (actualPrimeTupleLog N p)<root d N p
  cap : root d N p≤actualParent5 d (N:ℝ) (pre p)
  upper : actualParent5 d (N:ℝ) (pre p)≤eval (lower i) (actualPrimeTupleLog N p)

theorem exists_mesh {r : ℝ} (hr : 0<r) :
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a : ℝ,a≤1/100 → ∀ N : ℕ,1<N → ∀ p : Fin 6→ℕ,(∀ k,0<p k) →
    ∀ i : Piece,actualPrimeTupleLog N p∈trim i r → Owner (bank e q a) N p i := by
  obtain ⟨delta,hd,hslack⟩ := common_margin hr
  refine ⟨min delta (3/256)/20,by positivity,?_⟩
  intro e he he0
  let chi : ℝ := (e:ℝ)/20
  have he' : 0<(e:ℝ) := by exact_mod_cast he
  have hc : 0<chi := by dsimp [chi];positivity
  have hed : 20*(e:ℝ)<delta := by linarith [min_le_left delta (3/256:ℝ)]
  have he3 : 20*(e:ℝ)<3/256 := by linarith [min_le_right delta (3/256:ℝ)]
  obtain ⟨m0,hm0⟩ := eventually_atTop.mp ((tendsto_logPrimeMeshStep 0 (19/96)).eventually (gt_mem_nhds hc))
  refine ⟨m0+1,by omega,?_⟩
  intro q hq a ha N hN p hp i ht
  let d := bank e q a
  let t := actualPrimeTupleLog N p
  have hdm : m0≤d.m := P4AOriginalElevenActualCommonHistory.original_mesh_above m0 q hq e a
  have own := (trim_region hr ht).1
  obtain ⟨hx,hr0,hrlo,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic (action i) t own.2.1
  have hpos (k : Fin 6) : 0<t k := (show (0:ℝ)<53/4608 by norm_num).trans
    (hrlo.trans_le (ho.antitone (Fin.le_last k)))
  have hOrd : Ordered (t 0) (t 1) (t 2) := ⟨(hpos 2).le,(ho (show (1:Fin 6)<2 by decide)).le,
    (ho (show (0:Fin 6)<1 by decide)).le,hx.le⟩
  have hamb : firstThree t∈logPrimeBox (fun _ : Fin 3=>(0:ℝ)) (fun _=>19/96) := by
    apply mem_logPrimeBox.mpr
    intro k
    exact ⟨(hpos _).le,(ho.antitone (Fin.zero_le _)).trans_lt (hx.trans (by norm_num))⟩
  obtain ⟨j,hjt⟩ := exists_logPrimeMeshCell 0 (19/96) d.m hamb
  have hb := HistoricalThirdCoarse.inBox_of_cell hjt
  change (box d.m j).InBox (t 0) (t 1) (t 2) at hb
  have hw : ((box d.m j).width:ℝ)≤chi := by rw [mesh_box_width];exact (hm0 d.m hdm).le
  obtain ⟨wx,wy,wz⟩ := side_widths hw
  have h0 : delta≤mu-t 0 := hslack i t ht 0
  have h01 : delta≤t 0-t 1 := hslack i t ht 1
  have h12 : delta≤t 1-t 2 := hslack i t ht 2
  have h3 : delta≤R0 t-H3 t := hslack i t ht 3
  have h5 : delta≤R0 t-H5 t := hslack i t ht 4
  have hfull : ((box d.m j).ux:ℝ)≤mu-4*(e:ℝ) := by dsimp [chi] at wx;linarith [hb.1]
  have hj : j∈cells (e:ℝ) chi d.m := by
    apply (mem_cells _ _ _ _).mpr
    refine ⟨RationalBox.wellFormed_of_inBox hb,mesh_box_lower_nonneg _ _,?_,?_,?_,hw⟩
    · have h : ((box d.m j).uz:ℝ)≤(box d.m j).ly := by dsimp [chi] at wy wz;linarith [hb.2.2.2.1,hb.2.2.2.2.1]
      exact_mod_cast h
    · have h : ((box d.m j).uy:ℝ)≤(box d.m j).lx := by dsimp [chi] at wx wy;linarith [hb.2.1,hb.2.2.1]
      exact_mod_cast h
    · have h : mu≤extendedFirstStop := by norm_num [mu,extendedFirstStop]
      linarith
  have hg := actual_gamma_sandwich he'.le hOrd hb hw hfull
    (show (e:ℝ)+7*chi≤3/256 by dsimp [chi];linarith)
  have hrough : (N:ℝ)^a≤p 2 := by
    rw [←actualPrimeTupleLog_rpow hN p hp 2]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le)
    have hy := ho.antitone (show (2:Fin 6)≤5 by decide)
    linarith
  have hjt' : primeHistoryLogCoordinates (N:ℝ) 3 (triple p)∈logPrimeMeshCell 0 (19/96) d.m j := by
    simpa only [triple_log] using hjt
  have hs : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega (N:ℝ) (triple p) :=
    (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mpr ⟨hrough,j,hj,hjt'⟩
  have hact : active d (N:ℝ) (pre p) := by rw [active,ancestor_three,triple_log];exact ⟨hx.le,hs⟩
  have hseed := third_eq_seed d N p hx.le
  have heq : root d N p=HistoricalThirdCoarse.levelExponent (e:ℝ) (box d.m j) := by
    rw [hseed,originalSeed,P1OriginalVariableFourthContinuation.seedExponent,ancestor_three,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hs,HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj hjt']
  have hR : R0 t≤six (t 0) (t 1) (t 2) := by
    rw [show R0 t=v (t 0) by rw [v_eq_A hx.le];rfl];exact le_max_left _ _
  have herr : 9/2*chi+2*(e:ℝ)<delta := by dsimp [chi];linarith
  have herr' : 9/2*chi+2*(e:ℝ)<3/256 := by dsimp [chi];linarith
  have hR3 : (3/256:ℝ)≤R0 t-3*t 0 := by dsimp [R0];linarith only [hx]
  have hlow := hg.1
  have hu : root d N p≤eval (lower i) t :=
    heq.le.trans (hg.2.trans (P4AOriginalLaterSixthFifthComparison.six_upper i own))
  have hrootLE : root d N p≤actualParent5 d (N:ℝ) (pre p) :=
    P4AOriginalElevenActualCommonHistory.root_le_actual_fifth d (N:ℝ) (pre p)
  have hh := (mem_cells _ _ _ _).mp hj
  exact ⟨hact.2,hact,HistoricalThirdCoarse.firstStop_of_triple_cell _ _ _ _ _ _ _ j hj hjt',hseed,
    heq.trans_lt (levelExponent_lt_initial _ _ he'.le hh.1 hh.2.1),
    by rw [heq];linarith,by rw [heq];linarith,by rw [heq];linarith,hrootLE,
    P4AOriginalLaterSixthFifthComparison.actual_fifth i d N p he'.le own.1 hu⟩

end
end ImbalancedChen.P4AOriginalLaterSixthMesh
