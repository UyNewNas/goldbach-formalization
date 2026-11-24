import ImbalancedChen.P4AOriginalFiniteFallbackSignedSource

namespace ImbalancedChen.P4AOriginalFiniteFallbackFullTree
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackBank (Bank read)
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFiniteFallbackOccurrence (onlySecond empty read_none empty_eq positive)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third)
open P4AOriginalFiniteFallbackSignedSource (sum)
open P4AOriginalFiniteFallbackOwnCubeRows (secondRow thirdRow)
open P4AFallbackCanonicalBanks (bank)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87RawChronology (rawRoot)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)

theorem coord_zero {k : ℕ} (N : ℝ) (p : List ℕ) (h : k+1≤p.length) :
    point N (k+1) p 0=point N 1 p 0 := by
  have hl : (rosserAncestor (k+1) p).length=k+1 := by simp [Nat.min_eq_left h]
  have H := primeHistoryLogCoordinates_ancestor N hl (by omega : 1≤k+1) (0:Fin 1)
  rw [rosserAncestor_nested 1 (k+1) (by omega)] at H
  exact H.symm

theorem off (m : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (p : List ℕ) (pos : Bool) (hl : ¬high N p) :
    upper (bank m) d w N pos p=fresh d w N pos p ∧
    upper (onlySecond (bank m)) d w N pos p=fresh d w N pos p := by
  rw [← empty_eq (bank m) d w N]
  by_cases h : p.length≤2
  · simp [upper,h]
  · have hn2 : read m (bank m).second (point N 2 p)=none := by
      cases h2 : read m (bank m).second (point N 2 p) with
      | none => rfl
      | some c =>
        have hx := (selected_second h2).1.1
        rw [coord_zero N p (by omega)] at hx
        exact (hl hx).elim
    have hn3 : read m (bank m).third (point N 3 p)=none := by
      cases h3 : read m (bank m).third (point N 3 p) with
      | none => rfl
      | some c =>
        have hx := (selected_third h3).1.1
        rw [coord_zero N p (by omega)] at hx
        exact (hl hx).elim
    simp [upper,level,secondLevel,empty,onlySecond,read_none,hn2,hn3,choose]

def withLower (B : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (L : Rule) := dispatch N (upper B d w N) L

/-- The unchanged lower sector can already contain all licensed rows,
including corrected chronological stages. Completed upper increments on
the actual whole raw node are identical to the arithmetic candidate sums. -/
theorem actual_two_three (m : ℕ) (d : OriginalData) (he : 0<(d.e:ℝ)) (hs : (d.e:ℝ)≤1/384)
    (hm : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) (w : ℝ) (hw : w≤5/96)
    (N : ℕ) (hN : 1<N) (L : Rule) (hL : ∀ p,L true p=true) :
    let B := bank m
    normalize N (rawRoot (withLower (empty B) d w N L) N-rawRoot (withLower (onlySecond B) d w N L) N)=
        sum d N (secondRow m d w N) ∧
    normalize N (rawRoot (withLower (onlySecond B) d w N L) N-rawRoot (withLower B d w N L) N)=
        sum d N (thirdRow m d w N) := by
  let B := bank m
  let R := fresh d w N
  have hp (p : List ℕ) : R true p=true := by rw [show R=upper (empty B) d w N from (empty_eq B d w N).symm]; exact positive _ _ _ _ _
  have hi (T : Bank) (h : ∀ pos p,¬high N p → upper T d w N pos p=R pos p) :
      dispatch N (upper T d w N) R=upper T d w N := by
    funext pos p
    by_cases hh : high N p
    · simp [dispatch,hh]
    · simp [dispatch,hh,h pos p hh]
  have h0 := hi (empty B) (fun pos p _ => congrFun (congrFun (empty_eq B d w N) pos) p)
  have h2 := hi (onlySecond B) (fun pos p hh => (off m d w N p pos hh).2)
  have h3 := hi B (fun pos p hh => (off m d w N p pos hh).1)
  have a := P4AOriginalFiniteFallbackSignedSectors.original_root (empty B) (onlySecond B) d w N L R hL hp
  have b := P4AOriginalFiniteFallbackSignedSectors.original_root (onlySecond B) B d w N L R hL hp
  rw [h0,h2,empty_eq] at a
  rw [h2,h3] at b
  obtain ⟨ha,hb⟩ := P4AOriginalFiniteFallbackSignedSource.two_and_three m d he hs hm w hw N hN
  exact ⟨(congrArg (normalize N) a).trans ha,(congrArg (normalize N) b).trans hb⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackFullTree
