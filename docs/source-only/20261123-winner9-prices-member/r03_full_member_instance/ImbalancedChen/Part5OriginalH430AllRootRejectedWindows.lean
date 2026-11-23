import ImbalancedChen.Part5OriginalH430AllOriginalReceiptIncidence
import ImbalancedChen.Part5OriginalH430FixedRejectedWindows
import ImbalancedChen.Part5OriginalH430EnhancedPhysicalGrid

/-! Actual counts on both tagged roots.  At every fixed/retained
occurrence the rejected set has exactly the directed least-prime window
from its physical cutoff to the original roughness cutoff. Enhanced
purely retained positions have an empty window, including their origin. -/
namespace ImbalancedChen.Part5OriginalH430AllRootRejectedWindows
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount frozen_selected_buchstab)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34 (tailCutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430RootSourceDictionary
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedOriginalRowFreeze
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430MonotoneSieveHeight
open Part5OriginalH430ZeroFreshReceiverPayment Part5OriginalH430ClassicalRejectedShell
open Part5OriginalH430RetainedRejectedPayment Part5OriginalH430AllOriginalReceiptIncidence
open Part5OriginalH430FixedRejectedWindows (firstWindow)
open Part5OriginalH430EnhancedPhysicalGrid

/-- The single quota of 57/112 is preserved by every later cumulative
grid at either enhanced root. -/
theorem enhanced_level_floor {n : ℕ} {k : Root} {t x : ℝ} (hn : 111≤n)
    (ht : 0≤t) (hu : t≤1/12) (hb : x∈rootBand k) (he : rootSource k x=.enhanced) :
    57/112 ≤ frozenLevel n (VariableEnvelope.v x) := by
  have hx := enhanced_root_coordinate he hb
  have hlo := (rootBand_subset k hb).1
  have ht' := root_total_bounds ht hu hb
  rw [enhanced_root_total (tau:=t) he] at ht'
  apply grid_persists hn ht'
  rw [VariableEnvelope.v_eq_min]
  apply le_min <;> dsimp [VariableEnvelope.A,VariableEnvelope.C] <;>
    dsimp [a] at hlo <;> dsimp [tailCutoff] at hx <;> linarith

/-- Pure retention at an enhanced root never changes the original
arithmetic cutoff. A common right-query approximation is not used. -/
theorem enhanced_retained_cutoff {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (he : rootSource k (physicalPrime N p)=.enhanced) (hr : o.path.all retainedEdge=true) :
    memberCutoff (cellQ N n c.1) o = (N:ℝ)^a := by
  have hband := (Finset.mem_filter.mp hp).1
  have hb := original_band_geometry hN hband
  have hw := zeroFresh_original_word ho (retained_path_zeroFresh _ hr)
  have hh := (retained_replay_state (rootRequest N n k t p) o.path hr).2
  rw [←(history_facts ho).2.2] at hh
  have hroot := frozen_root_sameQ_cutoff_power N n p k t hN (original_band_prime hband).1.pos ht hu hb
    (precision_error hn)
  have hlevel := enhanced_level_floor hn ht hu hb he
  have hcoord := enhanced_root_coordinate he hb
  have cut : a ≤ residual (frozenRoot n k t (physicalPrime N p)).physical / 2 := by
    rw [frozenRoot_residual,enhanced_root_total (tau:=t) he]
    dsimp only [a]
    dsimp only [tailCutoff] at hcoord
    linarith only [hlevel,hcoord]
  rw [memberCutoff,hw,hh,(original_fibre_geometry hN ht hu (precision_error hn) hp).1]
  simpa only [parentProduct,List.prod_cons,List.prod_nil,mul_one,cutoff,rootRequest,min_eq_left cut] using hroot

private theorem rough_at_root {N p : ℕ} {k : Root} (hp : p∈originalBand N k) :
    ChenPrimeRough ((N:ℝ)^a) p := by
  have hpa : (N:ℝ)^a ≤ (p:ℝ) := by cases k <;> exact (Finset.mem_filter.mp hp).2.1
  intro r hr hd
  rw [(Nat.prime_dvd_prime_iff_eq hr (original_band_prime hp).1).mp hd]
  exact hpa

/-- Exact directed window and compatible count at EVERY actual
zero-fresh position on both roots. Any stable far part of this window
keeps its original additive-prime and moduli. -/
theorem zeroFresh_window {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (hf : o.path.all zeroFreshEdge=true) :
    let z := memberCutoff (cellQ N n c.1) o
    inheritedChild N (parentProduct o.current.old) (tailProduct o) z = originalReceiver N p ∧
    rejectedAt N (cellQ N n c.1) o = firstWindow N p z ((N:ℝ)^a) ∧
    (frozenCount N p (receiver N) z:ℝ) = ((originalReceiver N p).card:ℝ)+firstWindow N p z ((N:ℝ)^a) := by
  dsimp only
  let z := memberCutoff (cellQ N n c.1) o
  have hb := (Finset.mem_filter.mp hp).1
  have hw := zeroFresh_original_word ho hf
  have hz := member_cutoff_le_original hN ht hu hn hb ho
  rw [←(original_fibre_geometry hN ht hu hn hp).1] at hz
  have hr := rough_at_root hb
  have hsplit := unit_frozen_split (fun r hr' hd => hz.trans (hr r hr' hd)) hz
  have hsharp := frozenCount_eq_original_count N p ((N:ℝ)^a) hr
  have H : (frozenCount N p (receiver N) z:ℝ) =
      (frozenCount N p (receiver N) ((N:ℝ)^a):ℝ)+firstWindow N p z ((N:ℝ)^a) := by
    unfold firstWindow
    exact_mod_cast frozen_selected_buchstab N p (receiver N) hz
  have hs : (frozenCount N p (receiver N) ((N:ℝ)^a):ℝ) = ((originalReceiver N p).card:ℝ) := by
    exact_mod_cast hsharp
  rw [hs] at H
  have heq : rejectedAt N (cellQ N n c.1) o = ((rejectedChild N p 1 z).card:ℝ) := by
    simp only [rejectedAt,tailProduct,hw,parentProduct,List.tail_cons,List.prod_nil,List.prod_cons,mul_one,z]
  refine ⟨?_,heq.trans (by linarith only [hsplit,H]),H⟩
  simpa only [hw,parentProduct,tailProduct,List.tail_cons,List.prod_nil,List.prod_cons,mul_one] using
    (unit_inherited_eq_original N p hz)

/-- No price at all is required for rejected quotients on the entire
enhanced retained subtree, even when arbitrary additive-prime masks are used. -/
theorem enhanced_retained_rejected_empty {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t c) (ho : o∈rootHistory N n k t p)
    (he : rootSource k (physicalPrime N p)=.enhanced) (hr : o.path.all retainedEdge=true) :
    rejectedChild N (parentProduct o.current.old) (tailProduct o) (memberCutoff (cellQ N n c.1) o) = ∅ := by
  have cut := enhanced_retained_cutoff hN hn ht hu hp ho he hr
  have hw := zeroFresh_original_word ho (retained_path_zeroFresh _ hr)
  rw [rejectedChild,cut,tailProduct,hw,parentProduct]
  simp only [List.prod_cons,List.prod_nil,mul_one,List.tail_cons,unit_inherited_eq_original N p le_rfl,
    originalReceiver,Finset.sdiff_self]

/-- For any preassigned selection of actual occurrences, with any real
signed test, all rejected counts on either root reduce to two explicit
finite arithmetic quantities on those same occurrences. -/
theorem selected_rejected_balance {N n m p : ℕ} {k : Root} {t : ℝ} {c : RootKey n m}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈rootFibre N n m k t c) (weight : Occurrence N→ℝ) (select : Occurrence N→Bool) :
    let H := (rootHistory N n k t p).filter select
    let z := fun o : Occurrence N => memberCutoff (cellQ N n c.1) o
    (H.map (fun o => weight o * rejectedAt N (cellQ N n c.1) o)).sum =
      (H.map (fun o => weight o * (if o.path.all zeroFreshEdge then firstWindow N p (z o) ((N:ℝ)^a)
        else ((chenSiftedQuotientPrimeSource N (parentProduct o.current.old) (z o)).card:ℝ)))).sum := by
  dsimp only
  apply congrArg List.sum
  apply List.map_congr_left
  intro o ho
  have hpos := (List.mem_filter.mp ho).1
  by_cases hf : o.path.all zeroFreshEdge=true
  · rw [if_pos hf,(zeroFresh_window hN ht hu hn hp hpos hf).2.1]
  · rw [if_neg hf,rejectedAt,
      (fresh_rejection_exact hN ht hu hn (Finset.mem_filter.mp hp).1 hpos hf _).2.2]

end
end ImbalancedChen.Part5OriginalH430AllRootRejectedWindows
