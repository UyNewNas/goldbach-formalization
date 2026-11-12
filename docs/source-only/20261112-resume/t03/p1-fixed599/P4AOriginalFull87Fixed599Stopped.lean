import ImbalancedChen.P4AOriginalFull87Fixed599Charges
import ImbalancedChen.P4AOriginalFull87UnilateralStoppedLevel

/-! Below depth eight the two roots agree through their shared fourth
frontier. At the smaller cutoff every admitted fifth take contributes zero,
on either side, by its own cube and the two available suffix positions. -/
namespace ImbalancedChen.P4AOriginalFull87Fixed599Stopped
noncomputable section
open scoped Classical BigOperators List
open P4AOriginalCompleteSixthChronology (data)
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87UnilateralStoppedLevel (eventPolicy admitted_fifth_cube stopped_extension prod_le_pow)
open P4AOriginalFull87StoppedTerminalPopulation (nonzero_stopped_has_actual_ancestor_highq_witness)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour actual_stopped_difference_eq_shared_four_suffix)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

private theorem admitted_fifth_zero (side : Bool) (delta : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (om : ℝ) (N cap : ℕ) (w epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ))
    (hN : 1 < (N : ℝ)) (heps : epsilon ≤ 1/1000)
    (X : ℕ) (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ)) (F : ℕ → ℝ)
    (pre : List ℕ) (p : ℕ) (ps : List ℕ) (mass : ℝ) (h4 : pre.length=4)
    (hp : 0<p) (hord : (p::pre).Pairwise (· < ·)) (hs : ∀ y∈ps, y ≤ p)
    (hg : eventPolicy side delta n e q om N false (p::pre)=true) :
    stoppedTest 8 (eventPolicy side delta n e q om N) (fun _ => 1)
      (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)) (p::pre) false mass ps = 0 := by
  by_contra hn
  obtain ⟨t,ht,hd,_,a,_,hhigh,hbeta,_⟩ :=
    nonzero_stopped_has_actual_ancestor_highq_witness _ (fun _ => 1)
      N cap w ((N : ℝ)^epsilon) X F (p::pre) false mass ps hn
  obtain ⟨xs,hword,hxs⟩ := stopped_extension p (p::pre) false mass ps hs t ht
  rw [hword,List.length_append,List.length_cons,h4] at hd
  have hlen : xs.length ≤ 2 := by omega
  have hprod : (xs.prod : ℝ) ≤ (p : ℝ)^2 := by
    exact_mod_cast (prod_le_pow p xs hxs).trans (Nat.pow_le_pow_right hp hlen)
  have hcube := admitted_fifth_cube side delta n e q om N p pre he hN h4 hord hg
  have hrough : (t.selected.prod : ℝ) < (N : ℝ)^(299/500 : ℝ) := by
    rw [hword,List.prod_append,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg _)).trans_lt
      (by simpa only [mul_comm] using hcube)
  exact (Nat.not_lt_of_ge (P4AOriginalFull87Fixed599Charges.nat_le_cut
    (P4AOriginalFull87Fixed599Charges.actual_live_product_lt_599 N cap w epsilon
      hN heps t.positive a t.selected.prod hbeta hrough) hX)) hhigh

private theorem fourth_suffix_eq (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (heps : epsilon ≤ 1/1000) (X : ℕ)
    (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ)) (F : ℕ → ℝ)
    (pre : List ℕ) (mass : ℝ) (h4 : pre.length=4) (ho : pre.Pairwise (· < ·))
    (rest : List ℕ) (hs : rest.Pairwise (· > ·)) (hp : ∀ y∈rest, 0<y)
    (hx : ∀ x∈pre, ∀ y∈rest, y<x) :
    stoppedTest 8 (eventPolicy true delta n e q om N) (fun _ => 1)
      (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)) pre true mass rest =
    stoppedTest 8 (eventPolicy false delta n e q om N) (fun _ => 1)
      (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)) pre true mass rest := by
  let T := attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F)
  have hk : ¬8 ≤ pre.length := by omega
  induction rest with
  | nil => rfl
  | cons p ps ih =>
      have hparts := List.pairwise_cons.mp hs
      have ht := ih hparts.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))
        (fun x h y hy => hx x h y (List.mem_cons_of_mem _ hy))
      have htake (side : Bool) :
          (if eventPolicy side delta n e q om N false (p::pre)=true then
            stoppedTest 8 (eventPolicy side delta n e q om N) (fun _ => 1) T
              (p::pre) false (mass*1) ps else 0) = 0 := by
        split_ifs with hg
        · exact admitted_fifth_zero side delta n e q om N cap w epsilon he hN heps X hX F
            pre p ps _ h4 (hp p (by simp))
            (List.pairwise_cons.mpr ⟨fun x h => hx x h p (by simp),ho⟩)
            (fun y hy => (hparts.1 y hy).le) hg
        · rfl
      change stoppedTest 8 (eventPolicy true delta n e q om N) (fun _ => 1) T pre true mass (p::ps) =
        stoppedTest 8 (eventPolicy false delta n e q om N) (fun _ => 1) T pre true mass (p::ps)
      simp only [stoppedTest,if_neg hk,Bool.not_true,htake,add_zero]
      exact ht

theorem actual_stopped_599 (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (heps : epsilon ≤ 1/1000) (X : ℕ) (hX : (N : ℝ)^(599/1000 : ℝ) ≤ ((X+1 : ℕ) : ℝ))
    (F : ℕ → ℝ) :
    rawStopped e q om N cap w z ((N : ℝ)^epsilon) X F -
      licensedStopped delta n e q om N cap w z ((N : ℝ)^epsilon) X F = 0 := by
  rw [actual_stopped_difference_eq_shared_four_suffix]
  let R := eventPolicy true delta n e q om N
  let C := roughPrimeUniverse N cap w z
  have hall (u : FirstExitDepthState ℕ) (hu : u∈sharedRankFour e q om N cap w z) :
      stoppedTest 8 R (fun _ => 1) (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F))
          u.selectedPrefix u.positive u.mass u.remaining -
        stoppedTest 8 (eventPolicy false delta n e q om N) (fun _ => 1)
          (attachedLeafTest N cap 1 w ((N : ℝ)^epsilon) (highQTest X F))
          u.selectedPrefix u.positive u.mass u.remaining = 0 := by
    have h4 := firstExitDepthFrontier_selected_length 4 R (fun _ => (1 : ℝ)) [] C true 1 (by simp) u hu
    have hpos := mem_firstExitDepthFrontier_positive_eq_evenListLength 4 R (fun _ => (1 : ℝ)) C u hu
    have parity (xs : List ℕ) : evenListLength xs = decide (Even xs.length) := by
      induction xs with
      | nil => simp [evenListLength]
      | cons x xs ih => simp only [evenListLength,ih,List.length_cons,Nat.even_add_one,decide_not]
    have htrue : u.positive = true := by rw [hpos,parity,h4] <;> decide
    have hsub : u.selectedPrefix.reverse ++ u.remaining <+ C := by
      simpa only [List.reverse_nil,List.nil_append] using
        firstExitDepthFrontier_selected_remaining_sublist 4 R (fun _ => (1 : ℝ)) [] C true 1 u hu
    have hw := List.pairwise_append.mp ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
    rw [htrue,sub_eq_zero]
    exact fourth_suffix_eq delta n e q om N cap w epsilon he hN heps X hX F u.selectedPrefix
      u.mass h4 (by simpa only [List.pairwise_reverse] using hw.1) u.remaining hw.2.1
      (fun y hy => (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_append_right _ hy))).pos)
      (fun x hx y hy => hw.2.2 x (List.mem_reverse.mpr hx) y hy)
  have sumZero {α : Type*} (xs : List α) (f : α → ℝ)
      (hz : ∀ x∈xs, f x=0) : (xs.map f).sum=0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,hz x (by simp),
        ih (fun y hy => hz y (List.mem_cons_of_mem _ hy)),zero_add]
  exact sumZero _ _ hall

end
end ImbalancedChen.P4AOriginalFull87Fixed599Stopped
