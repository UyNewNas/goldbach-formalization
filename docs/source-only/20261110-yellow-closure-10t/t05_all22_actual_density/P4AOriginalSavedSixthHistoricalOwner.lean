import ImbalancedChen.P4AOriginalSavedSixthSourceGates
import ImbalancedChen.P4AOriginalSavedSixthSigned
import ImbalancedChen.P4AOriginalHistoricalThirdMajorant
import ImbalancedChen.P4AOriginalNewFifthCoverage

/-! Closed order and the aligned 475q mesh put the first three coordinates
of EVERY actual G4 half-open rectangle in the historical owner. The same
owner gives the first-label stop, effective seed, first/third/fifth cube
slack and the early rough activation on the enriched fifth union. -/
namespace ImbalancedChen.P4AOriginalSavedSixthHistoricalOwner
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthPlanes (box lowerQ upperQ lift)
open P4AOriginalSavedSixthBank (facts lo)
open P4AOriginalSavedSixthPrimeMean (bounds ordered6)
open P4AOriginalSavedSixthIntegral (low)
open P4AOriginalSavedSixthSourceGates (old_margins)
open P1OriginalFifthGrid400RefinedFullBoxCover
open P4AOriginalNewFifthCoverage (Schedule)
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalSavedSixthSigned (pre)
abbrev bank := P4AOriginalNewFifthUnion.data

def firstThree {α : Type*} (t : Fin 6 → α) (j : Fin 3) : α := t (j.castLE (by decide))
def triple (p : Fin 6 → ℕ) := [p 2,p 1,p 0]
def root (d : OriginalData) (N : ℕ) (p : Fin 6 → ℕ) :=
  lambda3 d (N:ℝ) (rosserAncestor 4 (pre p))

theorem pre_list (p : Fin 6 → ℕ) : pre p = [p 5,p 4,p 3,p 2,p 1,p 0] := by
  simp [pre,List.ofFn_succ]
theorem pre_len (p : Fin 6 → ℕ) : (pre p).length=6 := by simp [pre]
theorem pre_log (N : ℕ) (p : Fin 6 → ℕ) :
    primeHistoryLogCoordinates (N:ℝ) 6 (pre p) = actualPrimeTupleLog N p := by
  funext j
  fin_cases j <;> simp [pre_list,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
theorem triple_log (N : ℕ) (p : Fin 6 → ℕ) :
    primeHistoryLogCoordinates (N:ℝ) 3 (triple p) = firstThree (actualPrimeTupleLog N p) := by
  funext j
  fin_cases j <;> simp [triple,firstThree,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
theorem ancestor_three (p : Fin 6 → ℕ) : rosserAncestor 3 (pre p) = triple p := by
  simp [pre_list,triple,rosserAncestor]
theorem ordered (i : Row) {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i) : Ordered (t 0) (t 1) (t 2) :=
  ⟨(by norm_num : (0:ℝ)≤1/50).trans (bounds i ht 2).1,(ordered6 i ht (by decide : (1:Fin 6)<2)).le,
    (ordered6 i ht (by decide : (0:Fin 6)<1)).le,(bounds i ht 0).2.le.trans (by norm_num [mu])⟩

theorem mesh_owner (i : Row) {e : ℚ} {q : ℕ} {a : ℝ} (hs : Schedule e q a)
    {t : Certificates.P2OriginalSixthElevenLogSemantics.Physical} (ht : t∈box i) :
    ∃ j ∈ HistoricalThirdCoarse.cells (e:ℝ) ((e:ℝ)/20) (refinedMesh q),
      firstThree t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j := by
  let m := refinedMesh q
  have hamb : firstThree t ∈ logPrimeBox (fun _ : Fin 3 => (0:ℝ)) (fun _ => (19/96:ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro k
    exact ⟨(by norm_num : (0:ℝ)≤1/50).trans (bounds i ht _).1,(bounds i ht _).2.trans (by norm_num)⟩
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) m hamb
  let b := HistoricalThirdCoarse.box m j
  have hc (k : Fin 3) :
      lowerQ i (k.castLE (by decide : 3≤6)) ≤ qLogPrimeMeshLo 0 (19/96) m j k ∧
      qLogPrimeMeshHi 0 (19/96) m j k ≤ upperQ i (k.castLE (by decide : 3≤6)) := by
    let v := k.castLE (by decide : 3≤6)
    let j5 : RefinedCell q := fun _ => j k
    have hm := mem_logPrimeMeshCell.mp hj k
    have hml := refined_lo q hs.2.2.1 j5 0
    have hmh := refined_hi q hs.2.2.1 j5 0
    change logPrimeMeshLo 0 (19/96) m j k = _ at hml
    change logPrimeMeshHi 0 (19/96) m j k = _ at hmh
    rw [hml,hmh] at hm
    have hr := mem_logPrimeBox.mp ht v
    have hal := aligned_refined_grid400_interval q hs.2.2.1 (lo i v) (j k).val (t v)
      (by simpa [lo,lowerQ,lift] using hr.1) (by simpa [lo,upperQ,lift] using hr.2) hm.1 hm.2
    have hql := refined_qlo q hs.2.2.1 j5 0
    have hqh := refined_qhi q hs.2.2.1 j5 0
    change qLogPrimeMeshLo 0 (19/96) m j k = _ at hql
    change qLogPrimeMeshHi 0 (19/96) m j k = _ at hqh
    rw [hql,hqh]
    exact hal
  have ho (k : Fin 5) : upperQ i k.succ ≤ lowerQ i k.castSucc := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast (facts i).order k) (by norm_num)
  have htop : upperQ i 0 ≤ 39/200 := by
    have h : (lo i 0:ℚ)+1≤78 := by exact_mod_cast (facts i).right
    exact (div_le_iff₀ (by norm_num : (0:ℚ)<400)).mpr (by linarith only [h])
  have huxQ : b.ux≤39/200 := (hc 0).2.trans htop
  have hux : (b.ux:ℝ)≤39/200 := by exact_mod_cast huxQ
  have he : (e:ℝ)≤1/64000 := by exact_mod_cast hs.2.1
  have hstop : (b.ux:ℝ) ≤ extendedFirstStop-4*(e:ℝ) := by dsimp [extendedFirstStop]; linarith
  have hwidth : (b.width:ℝ) ≤ (e:ℝ)/20 := by
    simpa only [b,m,P2OriginalSaving16HistoricalMesh.mesh_box_width] using hs.2.2.2.1
  exact ⟨j,(HistoricalThirdCoarse.mem_cells _ _ _ _).mpr ⟨RationalBox.wellFormed_of_inBox (HistoricalThirdCoarse.inBox_of_cell hj),
    (by norm_num : (0:ℚ)≤1/50).trans ((low i 2).trans (hc 2).1),
    (hc 2).2.trans ((ho 1).trans (hc 1).1),(hc 1).2.trans ((ho 0).trans (hc 0).1),hstop,hwidth⟩,hj⟩

theorem third_eq_seed (d : OriginalData) (N : ℕ) (p : Fin 6 → ℕ)
    (hx : actualPrimeTupleLog N p 0 ≤ mu) : root d N p = originalSeed d (N:ℝ) (pre p) := by
  have hn2 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard (N:ℝ) (rosserAncestor 4 (pre p)) := by
    intro h
    have hc := h.1
    simp [pre_list,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple] at hc
    exact (not_lt_of_ge hx) hc
  have hn3 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard (N:ℝ) (rosserAncestor 4 (pre p)) := by
    intro h
    have hc := h.1
    simp [pre_list,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple] at hc
    exact (not_lt_of_ge hx) hc
  simp only [root,lambda3,fallbackSeed,if_neg hn3,if_neg hn2,max_self,
    P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 4 (by decide)]

structure Owner (d : OriginalData) (N : ℕ) (p : Fin 6 → ℕ) : Prop where
  active : P4AOriginalFull87DataPolicy.active d (N:ℝ) (pre p)
  stop : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0]
  seed : root d N p = originalSeed d (N:ℝ) (pre p)
  initial : root d N p < HistoricalThirdCoarse.initial (d.e:ℝ)
  first : 3*actualPrimeTupleLog N p 0 < root d N p
  third : Certificates.P2OriginalSixthElevenLogSemantics.H3 (actualPrimeTupleLog N p)+1/3200 < root d N p
  fifth : Certificates.P2OriginalSixthElevenLogSemantics.H5 (actualPrimeTupleLog N p)+1/3200 < root d N p
  upper : root d N p ≤ six (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1) (actualPrimeTupleLog N p 2)

theorem actual_owner (i : Row) {e : ℚ} {q : ℕ} {a : ℝ} (hs : Schedule e q a)
    {N : ℕ} (hN : 1<N) (p : Fin 6 → ℕ) (hp : ∀ j,0<p j) (ht : actualPrimeTupleLog N p ∈ box i) :
    Owner (bank e q a) N p := by
  let d := bank e q a
  let t := actualPrimeTupleLog N p
  have ho := ordered i ht
  obtain ⟨j,hj,ht3⟩ := mesh_owner i hs ht
  rw [← triple_log] at ht3
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hrough : (N:ℝ)^a ≤ (p 2:ℝ) := by
    rw [← actualPrimeTupleLog_rpow hN p hp 2]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    linarith only [hs.2.2.2.2,(bounds i ht 2).1]
  have hsup : P1ThirdFallbackSupport.supported (e:ℝ) ((e:ℝ)/20) (refinedMesh q) a (N:ℝ) (triple p) :=
    (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mpr ⟨hrough,j,hj,ht3⟩
  have hact : P4AOriginalFull87DataPolicy.active d (N:ℝ) (pre p) := by
    rw [P4AOriginalFull87DataPolicy.active,ancestor_three,triple_log]
    exact ⟨ho.2.2.2,by simpa only [triple_log] using hsup⟩
  have hsroot := third_eq_seed d N p ho.2.2.2
  have he : 0≤(e:ℝ) := by exact_mod_cast hs.1
  have hb : (e:ℝ)≤1/64000 := by exact_mod_cast hs.2.1
  have heq : root d N p = HistoricalThirdCoarse.levelExponent (e:ℝ) (HistoricalThirdCoarse.box (refinedMesh q) j) := by
    rw [hsroot,originalSeed,P1OriginalVariableFourthContinuation.seedExponent,ancestor_three,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hsup,HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht3]
  have herr := P4AOriginalHistoricalThirdMajorant.cell_error he (by linarith : 0≤(e:ℝ)/20)
    (by linarith) hj ht3
  rw [triple_log] at herr
  have henv : P4AOriginalHistoricalThirdMajorant.envelope (firstThree t) = six (t 0) (t 1) (t 2) := by
    simp only [P4AOriginalHistoricalThirdMajorant.envelope,firstThree,max_eq_right ho.2.2.2]
    have hc : C mu=cap := by norm_num [C,mu,cap]
    rw [hc,min_eq_left (six_le_cap _ _ ho.1)]
  have hnear : six (t 0) (t 1) (t 2) ≤ root d N p + (4*(e:ℝ)+6*((e:ℝ)/20)) := by
    rw [heq]
    have hh := (abs_le.mp herr).1
    rw [henv] at hh; linarith only [hh]
  have hb3 := HistoricalThirdCoarse.inBox_of_cell ht3
  rw [triple_log] at hb3
  have hGam := HistoricalThirdCoarse.gamma_le_endpoint (e:ℝ) (HistoricalThirdCoarse.box (refinedMesh q) j) he hb3 ho.1 ho.2.1 ho.2.2.1
  change _ ≤ HistoricalThirdCoarse.endpoint (t 0) (t 1) (t 2) at hGam
  rw [HistoricalThirdCoarse.endpoint,if_pos ho.2.2.2,original_eq_six ho] at hGam
  have hc := (HistoricalThirdCoarse.mem_cells _ _ _ _).mp hj
  have hA : A (t 0) ≤ six (t 0) (t 1) (t 2) := by rw [←v_eq_A ho.2.2.2]; exact le_max_left _ _
  have hm := old_margins i ht
  refine ⟨hact,HistoricalThirdCoarse.firstStop_of_triple_cell _ _ _ _ _ _ _ j hj ht3,hsroot,?_,?_,?_,?_,?_⟩
  · rw [heq]; exact HistoricalThirdCoarse.levelExponent_lt_initial _ _ he hc.1 hc.2.1
  · dsimp [A] at hA; linarith only [hA,hnear,hb,(bounds i ht 0).2]
  · linarith only [hm.1,hnear,hb]
  · linarith only [hm.2,hnear,hb]
  · rw [heq]; dsimp [HistoricalThirdCoarse.levelExponent]; linarith only [hGam,he]

end
end ImbalancedChen.P4AOriginalSavedSixthHistoricalOwner
