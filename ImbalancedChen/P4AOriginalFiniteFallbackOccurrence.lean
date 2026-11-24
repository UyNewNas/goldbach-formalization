import ImbalancedChen.P4AOriginalFiniteFallbackCanonical
import ImbalancedChen.P4AOriginalFiniteFallbackSignedSectors
import ImbalancedChen.P4AOriginalThirdFallbackActualGain

namespace ImbalancedChen.P4AOriginalFiniteFallbackOccurrence
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackBank (Bank read)
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFiniteFallbackSignedSectors (signed_split)
open P5OriginalCommonRefinedConstructor (OriginalData old3)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples admittedOrdinary)
open P4AOriginalRankThreeRestorationSource
open P1Pair12RetainedSignedSource
open P5OriginalCommonFourthSourceLedger (signedTest_one_eq_polynomial)
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open HistoricalThirdCoarse.P1ActualTuple (history)

def onlySecond (B : Bank) : Bank := {B with third := fun _ => none}
def empty (B : Bank) : Bank := {B with second := fun _ => none,third := fun _ => none}
def post (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) : ℝ :=
  choose (read B.mesh B.third (point N 3 p)) (secondLevel B d w N p)

theorem read_none {k : ℕ} (m : ℕ) (t : Fin k → ℝ) :
    read m (fun _ => none) t=none := by
  unfold read
  split <;> rfl

theorem empty_eq (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) :
    upper (empty B) d w N=fresh d w N := by
  funext pos p
  simp [upper,level,post,secondLevel,empty,read_none,choose,fresh,P4AOriginalOrderedThirdTable.policy,
    thirdCappedUpperPolicy,firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,
    P4AOriginalOrderedThirdFullPolicy.current]

theorem positive (B : Bank) (d : OriginalData) (w N : ℝ) (p : List ℕ) : upper B d w N true p=true := by
  simp [upper,HistoricalThirdCoarse.initialPolicy,ordinaryParityRosserPolicy,oddFirstExitPolicy]

theorem point_cons {k : ℕ} {p : List ℕ} (N : ℝ) (q : ℕ) (hk : k≤p.length) :
    point N k (q::p)=point N k p := by rw [point,point,rosserAncestor_cons k q p hk]

theorem post_cons (B : Bank) (d : OriginalData) (w N : ℝ) (q : ℕ) (p : List ℕ) (hp : 3≤p.length) :
    post B d w N (q::p)=post B d w N p := by
  simp only [post,secondLevel,point_cons N q hp,point_cons N q (show 2≤p.length by omega),
    P4AOriginalOrderedThirdFullPolicy.current,rosserAncestor_cons 3 q p hp]

theorem continuation (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (p : List ℕ)
    (hp : 3≤p.length) (pos : Bool) (mass : ℝ) (xs : List ℕ) :
    signedTest (upper B d w N) weight (fun _ _ => 1) p pos mass xs=
      signedTest (ordinaryParityRosserPolicy false ((N:ℝ)^post B d w N p)) weight
        (fun _ _ => 1) p pos mass xs := by
  induction xs generalizing p pos mass with
  | nil => rfl
  | cons q qs ih =>
    have hq : 3<(q::p).length := by simp; omega
    have hn : upper B d w N (!pos) (q::p)=
        ordinaryParityRosserPolicy false ((N:ℝ)^post B d w N p) (!pos) (q::p) := by
      change (if (q::p).length≤2 then _ else _) = _
      rw [if_neg (by omega : ¬(q::p).length≤2)]
      rw [level,if_neg (not_le.mpr hq)]
      exact congrArg (fun a : ℝ => ordinaryParityRosserPolicy false ((N:ℝ)^a) (!pos) (q::p))
        (post_cons B d w N q p hp)
    simp only [signedTest,hn,ih p hp pos mass,ih (q::p) hq.le (!pos) (mass*weight q),post_cons B d w N q p hp]

def signedNode (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (s : FirstExitDepthState ℕ) : ℝ :=
  if ordinaryRosserPrefixAdmissible false ((N:ℝ)^secondLevel B d w N s.selectedPrefix) s.selectedPrefix then
    signedTest (ordinaryParityRosserPolicy false ((N:ℝ)^post B d w N s.selectedPrefix))
      weight (fun _ _ => 1) s.selectedPrefix s.positive s.mass s.remaining else 0

theorem node (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (s : FirstExitDepthState ℕ)
    (hs : s∈candidates d N weight (carrier N)) :
    admittedTest (upper B d w N) weight (fun _ _ => 1) s=signedNode B d w N s := by
  obtain ⟨hl,_,_,_,_,hb,_⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N:ℝ))) N N (cutoff N) s hs
  have hfalse : s.positive=false := by
    have h := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1:ℝ)
    cases H : evenListLength s.selectedPrefix
    · exact hb.trans H
    · rw [H,hl] at h; norm_num [signedTreeCoefficient] at h
  rw [admittedTest,signedNode,hfalse,rank_three B d w N _ hl,decide_eq_true_eq]
  split
  · exact continuation B d w N _ hl.ge false s.mass s.remaining
  · rfl

/-- The signed source is on the same unrestricted before-third candidate
list for both banks. The rank-three test always reads rank two, while
the retained third continuation receives its own distinct level. -/
theorem difference (B C : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) :
    rawRoot (upper B d w N) N-rawRoot (upper C d w N) N=
      ((candidates d N weight (carrier N)).map (fun s => signedNode B d w N s-signedNode C d w N s)).sum := by
  have hroot (T : Bank) :
      signedTest (upper T d w N) weight (fun _ _ => 1) [] true 1 (carrier N)=rawRoot (upper T d w N) N := by
    rw [signedTest_one_eq_polynomial]
    exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _ (positive _ _ _ _) _ _ _ _
  have thru (T : Bank) (b : Bool) (p : List ℕ) (h : p.length≤2) :
      upper T d w N b p=old3 d N b p := by
    rw [upper,if_pos h,old3,HistoricalThirdCoarse.policy_through_two _ _ _ _ _ b p h]
  rw [←hroot B,←hroot C,signed_difference_before_third (old3 d N) (upper C d w N) (upper B d w N)
    (thru C) (thru B) weight (fun _ _ => 1) [] (by simp) true 1 (carrier N)]
  congr 1
  apply List.map_congr_left
  intro s hs
  rw [node B d w N s hs,node C d w N s hs]

theorem two_node (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (s : FirstExitDepthState ℕ)
    (hb : s.positive=false) :
    signedNode (onlySecond B) d w N s=admittedOrdinary ((N:ℝ)^secondLevel B d w N s.selectedPrefix) N s := by
  simp [signedNode,onlySecond,secondLevel,post,read_none,choose,admittedOrdinary,hb,
    ordinaryParityRosserPolicy,oddFirstExitPolicy]

end
end ImbalancedChen.P4AOriginalFiniteFallbackOccurrence
