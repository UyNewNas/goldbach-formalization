import ImbalancedChen.P4AOriginalFiniteFallbackCandidate

namespace ImbalancedChen.P4AOriginalFiniteFallbackOwnCubeRows
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackBank (Bank read)
open P4AOriginalFiniteFallbackPolicy (point)
open P4AOriginalFiniteFallbackOccurrence (signedNode onlySecond empty)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third exclusive)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalOrderedThirdFullPolicy (current)
open P5OriginalCommonRefinedConstructor (OriginalData old3)
open P4AOriginalFull87RawChronology (cutoff)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples admittedOrdinary admittedOrdinary_normalized)
open P4AOriginalRankThreeRestorationSource
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open HistoricalThirdCoarse.P1ActualTuple (history history_log)
open P4AOriginalThirdFallbackAdmission (self pre_eq)
open P4AOriginalFiniteFallbackSmallThird (diff)
open VariableEnvelope

def old (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :=
  P4AOriginalOrderedThirdTable.rawExponent (d.e:ℝ) d.m w N (history p)

def pairPoint (N : ℕ) (p : Fin 3 → ℕ) (i : Fin 2) := actualPrimeTupleLog N p (i.castLE (by decide : 2≤3))

theorem points (N : ℕ) (p : Fin 3 → ℕ) :
    point N 2 (history p)=pairPoint N p ∧ point N 3 (history p)=actualPrimeTupleLog N p := by
  constructor
  · funext i
    fin_cases i <;> simp [point,pairPoint,history,rosserAncestor,primeHistoryLogCoordinates,
      primeHistoryTuple,actualPrimeTupleLog]
  · rw [point,self,history_log]

def secondRow (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  match read m (bank m).second (pairPoint N p) with
  | none => 0
  | some c => diff N p (old d w N p) c

def thirdRow (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  match read m (bank m).third (actualPrimeTupleLog N p) with
  | none => 0
  | some c => if ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p)
              then diff N p (old d w N p) c else 0

theorem rows (m : ℕ) (d : OriginalData) (he : 0<(d.e:ℝ)) (hs : (d.e:ℝ)≤1/384)
    (hm : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) (w : ℝ) (hw : w≤5/96)
    (N : ℕ) (hN : 1<N) (s : FirstExitDepthState ℕ) (hf : s∈candidates d N weight (carrier N))
    (p : Fin 3 → ℕ) (hp : s.selectedPrefix=history p) (hc : p∈candidateTuples d N) :
    normalize N (signedNode (empty (bank m)) d w N s-signedNode (onlySecond (bank m)) d w N s)=
        s.mass*secondRow m d w N p ∧
    normalize N (signedNode (onlySecond (bank m)) d w N s-signedNode (bank m) d w N s)=
        s.mass*thirdRow m d w N p := by
  obtain ⟨ha,hbox,_,_⟩ := P4AOriginalFiniteFallbackCandidate.geometry d hN hc
  have hpos (i : Fin 3) := (mem_actualPrimeBoxTuples_iff.mp hbox i).1.pos
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have H (L : ℝ) (hx : (p 0:ℝ)^3<(N:ℝ)^L) :
      normalize N (admittedOrdinary ((N:ℝ)^L) N s)=-s.mass*actualPrimeTupleOwnCubeMinus N N L p :=
    admittedOrdinary_normalized d N s hf p hp (hpos 2) _ hx
  have hfirst : (p 0:ℝ)^3<(N:ℝ)^old d w N p := P4AOriginalFiniteFallbackCandidate.first_cube hN he hs hm w hc
  have hsc : (current d w N s.selectedPrefix).scalar=old d w N p := by rw [hp]; simp [current,self,old]
  have htwo := congrArg (point (N:ℝ) 2) hp
  rw [(points N p).1] at htwo
  have hthree := congrArg (point (N:ℝ) 3) hp
  rw [(points N p).2] at hthree
  have ev (L : ℝ) : (if ordinaryRosserPrefixAdmissible false ((N:ℝ)^L) s.selectedPrefix then
        P1Pair12RetainedSignedSource.signedTest (ordinaryParityRosserPolicy false ((N:ℝ)^L))
          weight (fun _ _ => 1) s.selectedPrefix s.positive s.mass s.remaining else 0)=
        admittedOrdinary ((N:ℝ)^L) N s := rfl
  simp only [signedNode,onlySecond,empty,P4AOriginalFiniteFallbackOccurrence.post,
    P4AOriginalFiniteFallbackPolicy.secondLevel,P4AOriginalFiniteFallbackOccurrence.read_none,
    hsc,htwo,hthree,secondRow,thirdRow,P4AOriginalFiniteFallbackPolicy.choose] 
  cases h3 : read m (bank m).third (actualPrimeTupleLog N p) with
  | none =>
    cases h2 : read m (bank m).second (pairPoint N p) with
    | none => simp [ev,normalize]
    | some c =>
      obtain ⟨_,h1,hc',_⟩ := selected_second h2
      have hf' := first_cube_lt_level_of_exponent (p 0) hn (actualPrimeTupleLog_rpow hN p hpos 0).symm.le
        (h1.trans hc')
      simp only [ev,normalize_sub,H _ hfirst,H _ hf',diff]
      constructor <;> ring
  | some c =>
    have h2 := exclusive h3
    change read m (bank m).second (pairPoint N p)=none at h2
    rw [h2]
    obtain ⟨hR,h1,_,h3c,_⟩ := selected_third h3
    have hz : w≤actualPrimeTupleLog N p 2 := hw.trans hR.2.2.2.2.2.2.2.2.1
    have hupper := P4AOriginalFiniteFallbackCandidate.high_upper hN he.le hc hz hR.1
    have hc' : old d w N p≤(c:ℝ) := hupper.trans h3c.le
    have hmono := ordinaryRosserPrefixAdmissible_mono false s.selectedPrefix
      (Real.rpow_le_rpow_of_exponent_le hn.le hc')
    have hcf := hfirst.trans_le (Real.rpow_le_rpow_of_exponent_le hn.le hc')
    by_cases had : ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) s.selectedPrefix
    · have ha' : ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p) := hp ▸ had
      have hid (L : ℝ) (haL : ordinaryRosserPrefixAdmissible false ((N:ℝ)^L) s.selectedPrefix) :
          P1Pair12RetainedSignedSource.signedTest (ordinaryParityRosserPolicy false ((N:ℝ)^L))
            weight (fun _ _ => 1) s.selectedPrefix s.positive s.mass s.remaining=admittedOrdinary ((N:ℝ)^L) N s :=
        (if_pos haL).symm
      simp only [if_pos had,if_pos ha',hid _ had,hid _ (hmono had),normalize_sub,H _ hfirst,H _ hcf,diff]
      constructor <;> ring
    · have ha' : ¬ordinaryRosserPrefixAdmissible false ((N:ℝ)^old d w N p) (history p) := by rwa [←hp]
      simp [had,ha',normalize]

end
end ImbalancedChen.P4AOriginalFiniteFallbackOwnCubeRows
