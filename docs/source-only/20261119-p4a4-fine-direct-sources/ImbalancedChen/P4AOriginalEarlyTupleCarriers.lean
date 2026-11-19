import ImbalancedChen.P4AOriginalEarlyTupleLevels
import ImbalancedChen.P1OriginalCoarseFourthArithmeticWall

namespace ImbalancedChen.P4AOriginalEarlyTupleCarriers
noncomputable section
open scoped Classical BigOperators List
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData originalSeed old3)
open P4AOriginalNewFifthUnion (data)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AOriginalOrderedThirdFullPolicy (current prior current_ancestor prior_ancestor Root)
open P4AOriginalFiniteFallbackPolicy (high)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalEarlyFiniteStages (Q3 seed A4 A5)
open P4AOriginalEarlyHistoricalSums (oldLevel3 B4 B5)
open P4AOriginalEarlyTupleLevels (occurs4 occurs5 old_level)
open P1OriginalCoarseFourthArithmeticWall (original_admitted_gap_pos rawTupleGap rawTupleExponent_eq_of_level)
open P1OriginalFourthAllRowsAdmission (originalRows4_geometry)
open P5OriginalFourthFifthSourceInputs (originalRows4)
open P2OriginalFourthCapProducerInterface (ProducerRow)

abbrev hist4 := P1OriginalCoarseFourthResidual.tupleHistory
abbrev hist5 := P1CorrectedFifthCausalTupleDictionary.tupleHistory
abbrev box (k N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin k=>1/400) (fun _=>19/96)
abbrev carrier (N : ℕ) := roughPrimeUniverse N N 0 (cutoff N)
abbrev bank (e : ℚ) (k : ℕ) (a : ℝ) := data e (256*k) a

structure Alignment (e : ℚ) (k : ℕ) (a w : ℝ) : Prop where
  pos : 0<k
  nonneg : 0≤(e:ℝ)
  small : 4*(e:ℝ)+(e:ℝ)/20≤1/3200
  step : logPrimeMeshStep 0 (19/96) (refinedMesh (256*k))≤(e:ℝ)/20
  ceiling : a≤3/200
  lower : w≤a

theorem hist4_list (p : Fin 4→ℕ) : hist4 p=[p 3,p 2,p 1,p 0] := by
  simp [hist4,P1OriginalCoarseFourthResidual.tupleHistory,List.ofFn_succ]

theorem hist5_list (p : Fin 5→ℕ) : hist5 p=[p 4,p 3,p 2,p 1,p 0] := by
  simp [hist5,P1CorrectedFifthCausalTupleDictionary.tupleHistory,List.ofFn_succ]

theorem primes_of_sub {k N : ℕ} {p : Fin k→ℕ} (h : List.ofFn p <+ carrier N) :
    ∀ i,p i∈carrier N := fun i => h.subset (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem in_box {k N : ℕ} (hN : 1<N) {p : Fin k→ℕ} (hc : ∀i,p i∈carrier N)
    (hl : ∀ i,1/400≤actualPrimeTupleLog N p i) : p∈box k N := by
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hp := (mem_roughPrimeUniverse.mp (hc i)).2
  refine ⟨hp.1,hp.2.1,?_,hp.2.2.2⟩
  rw [←actualPrimeTupleLog_rpow hN p (fun j=>(mem_roughPrimeUniverse.mp (hc j)).2.1.pos) i]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) (hl i)

theorem four_owner {e : ℚ} {k : ℕ} {a w : ℝ} (S : Alignment e k a w)
    {N : ℕ} (hN : 1<N) (p : Fin 4→ℕ) (hc : ∀i,p i∈carrier N) (H : occurs4 (bank e k a) N (hist4 p)) :
    let d := bank e k a
    ¬high N (hist4 p) ∧ p∈box 4 N ∧ current d w N (hist4 p)=prior d N (hist4 p) := by
  obtain ⟨r,hr,ht⟩ := H
  have hr' : r∈originalRows4 := hr
  have hbox : actualPrimeTupleLog N p∈r.box := by
    simpa only [P1OriginalCoarseFourthResidual.tupleHistory_log] using ht.2
  have G := originalRows4_geometry r hr'
  have D := r.ordered G _ hbox
  have last : (3/200:ℝ)≤actualPrimeTupleLog N p 3 :=
    (show (3/200:ℝ)≤(r.lower 3:ℝ) by exact_mod_cast G.2.2.2.2.1).trans (hbox.1 3)
  have high_read : high N (hist4 p) ↔ mu<actualPrimeTupleLog N p 0 := by
    rw [hist4_list]; rfl
  refine ⟨fun h=>not_lt_of_ge D.1.2.2.2 (high_read.mp h),in_box hN hc ?_,?_⟩
  · intro i; fin_cases i <;> linarith [D.2.2,D.1.2.1,D.1.2.2.1]
  · rw [hist4_list]
    exact P4AOriginalEarlyFourthAlignedOwner.updated_root_on_fourth S.nonneg S.pos S.ceiling S.lower
      S.small S.step r hr' hN p hc hbox

theorem five_owner {e : ℚ} {k : ℕ} {a w : ℝ} (S : Alignment e k a w)
    {N : ℕ} (hN : 1<N) (p : Fin 5→ℕ) (hc : ∀i,p i∈carrier N) (H : occurs5 (bank e k a) N (hist5 p)) :
    let d := bank e k a
    ¬high N (hist5 p) ∧ p∈box 5 N ∧ primeHistoryLogCoordinates N 5 (hist5 p) 0≤mu ∧
      current d w N (hist5 p)=prior d N (hist5 p) := by
  obtain ⟨r,hr,ht⟩ := H
  have hp : ∀x∈hist5 p,0<x := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
    exact (mem_roughPrimeUniverse.mp (hc i)).2.1.pos
  have O := P4AOriginalEarlyFifthOwner.actual_eligible_owner 0 S.nonneg (256*k) S.lower
    (show 1<(N:ℝ) by exact_mod_cast hN) (hist5 p) (by simp [hist5,P1CorrectedFifthCausalTupleDictionary.tupleHistory])
    hp r hr ht
  have hh : high N (hist5 p) ↔ mu<primeHistoryLogCoordinates N 5 (hist5 p) 0 := by
    rw [hist5_list]; rfl
  exact ⟨fun h=>not_lt_of_ge O.1.le (hh.mp h),in_box hN hc
    (by simpa only [P1CorrectedFifthCausalTupleDictionary.tupleHistory_log] using O.2.1),O.1.le,O.2.2.1⟩

theorem level_three_on_owner {d : OriginalData} {w : ℝ} {N : ℕ} {h : List ℕ}
    (ho : current d w N h=prior d N h) :
    Q3 d w N (rosserAncestor 3 h)=oldLevel3 d N (rosserAncestor 3 h) := by
  rw [old_level]
  exact congrArg (fun x : Root=>(N:ℝ)^x.scalar) ho

/-- First and second have the common initial policy; rank three reads
the displayed capped level, and rank four keeps positive parity. -/
theorem four_reads (d : OriginalData) (w : ℝ) (N i j l m : ℕ)
    (h : Q3 d w N [l,j,i]=oldLevel3 d N [l,j,i]) :
    FirstExitValidSelection (fresh d w N) [] true [i,j,l,m] ↔
      FirstExitValidSelection (old3 d N) [] true [i,j,l,m] := by
  have h1 : fresh d w N false [i]=old3 d N false [i] := rfl
  have h2 : fresh d w N true [j,i]=old3 d N true [j,i] := rfl
  have h3 : fresh d w N false [l,j,i]=old3 d N false [l,j,i] := by
    change ordinaryParityRosserPolicy false (Q3 d w N [l,j,i]) false [l,j,i] =
      ordinaryParityRosserPolicy false (oldLevel3 d N [l,j,i]) false [l,j,i]
    rw [h]
  have h4 : fresh d w N true [m,l,j,i]=old3 d N true [m,l,j,i] := rfl
  simp only [FirstExitValidSelection,Bool.not_true,Bool.not_false,h1,h2,h3,h4]

theorem carrier4_on_owner {d : OriginalData} {w : ℝ} {N : ℕ} {p : Fin 4→ℕ}
    (ho : current d w N (hist4 p)=prior d N (hist4 p)) :
    p∈A4 d w N N (cutoff N) ↔ p∈B4 d N N (cutoff N) := by
  rw [A4,B4,mem_firstExitAdmittedTuples_iff,mem_firstExitAdmittedTuples_iff]
  apply and_congr_right
  intro _
  have H := level_three_on_owner ho
  rw [hist4_list] at H
  simpa [List.ofFn_succ] using four_reads d w N (p 0) (p 1) (p 2) (p 3) H

theorem carrier5_on_owner {d : OriginalData} {w : ℝ} {N : ℕ} {p : Fin 5→ℕ}
    (ho : current d w N (hist5 p)=prior d N (hist5 p)) :
    p∈A5 d w N N (cutoff N) ↔ p∈B5 d N N (cutoff N) := by
  rw [A5,B5,mem_firstExitFrontierTuples_iff,mem_firstExitFrontierTuples_iff]
  apply and_congr_right
  intro _
  have H := level_three_on_owner ho
  rw [hist5_list] at H
  simpa [List.ofFn_succ] using four_reads d w N (p 0) (p 1) (p 2) (p 3) H

theorem legal_four_seed (d : OriginalData) (N : ℕ) (hN : 1<N) (p : Fin 4→ℕ)
    (hp : p∈B4 d N N (cutoff N)) :
    (∑i,actualPrimeTupleLog N p i)+actualPrimeTupleLog N p (Fin.last 3)≤originalSeed d N (hist4 p) := by
  have hc : cutoff N≤(N:ℝ) := P4AOriginalFull87JointPhysicalBudget.cutoff_le_target N (by exact_mod_cast hN.le)
  have h := original_admitted_gap_pos d.e d.chi d.m d.omega N N (19/96) hN hc p hp
  have eq := old_level d N (hist4 p)
  rw [P1OriginalVariableFourthFullSourceActivation.ancestor3_tupleHistory] at eq
  have he := rawTupleExponent_eq_of_level hN p eq
  rw [rawTupleGap,he] at h
  linarith

end
end ImbalancedChen.P4AOriginalEarlyTupleCarriers

