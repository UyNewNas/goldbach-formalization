import ImbalancedChen.P4AOriginalFiniteFallbackAtoms
import ImbalancedChen.P4AOriginalFiniteFallbackFullTree
import ImbalancedChen.ActualDwellSelectedRemainder

namespace ImbalancedChen.P4AOriginalFiniteFallbackSelectedTail
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackPolicy (Rule F upper policy high point)
open P4AOriginalFiniteFallbackBank (Bank read)
open P4AOriginalFiniteFallbackOccurrence (post post_cons positive)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackCanonical (selected_second selected_third exclusive)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler (rawSupport universe)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AOriginalFiniteFallbackSignedSectors (high_cons)
open P5Z.PresievedRoughSlotAffineGates (original_upper_prefix_iff_log cube prefix)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondMask thirdMask)
open Part3.ActualCompactAllRankSupport (upper_set_dwell_support)

theorem ordinary_tail (B : Bank) (d : OriginalData) (delta : ℝ) (n : ℕ) (w : ℝ) (N : ℕ)
    (xs pre : List ℕ) (pos : Bool) (hpre : 3≤pre.length) (hhigh : high N pre)
    (hp : ∀ p∈xs,p.Prime) (hs : (xs.reverse++pre).Pairwise (·<·)) (hpos : pos=evenListLength pre)
    (hv : FirstExitValidSelection (oddFirstExitPolicy (F B delta n d w N)) pre pos xs)
    (ha : ordinaryRosserPrefixAdmissible false ((N:ℝ)^post B d w N pre) pre) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^post B d w N pre) (xs.reverse++pre) := by
  induction xs generalizing pre pos with
  | nil => simpa using ha
  | cons q qs ih =>
    have hsort : (qs.reverse++(q::pre)).Pairwise (·<·) := by simpa [List.append_assoc] using hs
    have hqsort := (List.pairwise_append.mp hsort).2.1
    have hh : high N (q::pre) := (high_cons N q (by intro H; simp [H] at hpre)).mpr hhigh
    have hq : (q::pre).length>3 := by simp; omega
    have hret : ordinaryParityRosserPolicy false ((N:ℝ)^post B d w N pre) (!pos) (q::pre)=true := by
      rw [←post_cons B d w N q pre hpre]
      have h := hv.1
      cases pos <;> simpa [F,policy,P4AOriginalFiniteFallbackPolicy.dispatch,hh,upper,
        P4AOriginalFiniteFallbackPolicy.level,post,show ¬(q::pre).length≤2 by omega,
        not_le.mpr hq,ordinaryParityRosserPolicy,oddFirstExitPolicy] using h
    rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false _ pre pos q ha hpos (hp q (by simp))
      (by simp) hqsort] at hret
    have hnext : ordinaryRosserPrefixAdmissible false ((N:ℝ)^post B d w N (q::pre)) (q::pre) := by
      rw [post_cons B d w N q pre hpre]
      exact of_decide_eq_true hret
    have H := ih (q::pre) (!pos) hq.le hh (fun p hp' => hp p (by simp [hp'])) hsort
      (by rw [hpos]; rfl) hv.2 hnext
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,post_cons B d w N q pre hpre] using H

theorem post_dwell (m : ℕ) (d : OriginalData) (delta : ℝ) (n : ℕ) (w : ℝ) {N cap u : ℕ} {z : ℝ}
    (hu : u∈rawSupport (F (bank m) delta n d w N) N cap ((N:ℝ)^w) z)
    (a b c : ℕ) (tail : List ℕ) (ht : u.primeFactorsList.reverse=a::b::c::tail)
    (hh : high N [c,b,a])
    (h3 : ordinaryRosserPrefixAdmissible false ((N:ℝ)^post (bank m) d w N [c,b,a]) [c,b,a]) :
    actualDwellSupport ((N:ℝ)^post (bank m) d w N [c,b,a]) (a::b::c::tail) := by
  obtain ⟨hU,hv⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hu
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap _ _ hU).1
  rw [ht] at hsub hv
  have prime (p : ℕ) (hp : p∈a::b::c::tail) := mem_roughPrimeUniverse_prime (hsub.subset hp)
  have hsort := (roughPrimeUniverse_pairwise_gt N cap ((N:ℝ)^w) z).sublist hsub
  have hlist : (a::b::c::tail).reverse=tail.reverse++[c,b,a] := by simp [List.append_assoc]
  have hs : (tail.reverse++[c,b,a]).Pairwise (·<·) := by
    rw [←hlist,List.pairwise_reverse]
    exact hsort
  have ha := ordinary_tail (bank m) d delta n w N tail [c,b,a] false (by simp) hh
    (fun p hp => prime p (by simp [hp])) hs rfl hv.2.2.2 h3
  rw [←hlist] at ha
  apply upper_set_dwell_support _ prime hsort
  simpa only [Bool.false_eq_true,if_false,List.toFinset_reverse] using ha.2

end
end ImbalancedChen.P4AOriginalFiniteFallbackSelectedTail
