import ImbalancedChen.Part5OriginalH430OwnedRootCounts

/-! Exact original-receipt pullback on a chosen U3/U4 Member.
The root quotient is D*x, not the descendant quotient x or the
additive prime. The prefix and residual roughness tests are independent.
No count estimate, admissibility licence or common level is an input. -/
namespace ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts

private theorem mem_source_iff {N b x : ℕ} (hb : 0 < b) :
    x ∈ chenQuotientPrimeSource N b ↔
      ∃ ell ∈ chenAdditivePrimeCarrier N, N-ell = b*x := by
  constructor
  · intro hx
    obtain ⟨ell,hell,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨he,hd⟩ := mem_chenQuotientPrimeCarrier.mp hell
    exact ⟨ell,he,(Nat.mul_div_cancel' hd).symm⟩
  · rintro ⟨ell,he,hm⟩
    exact Finset.mem_image.mpr ⟨ell,
      mem_chenQuotientPrimeCarrier.mpr ⟨he,⟨x,hm⟩⟩,
      by rw [hm, Nat.mul_div_cancel_left _ hb]⟩

/-- Same additive prime on BOTH sides, before any sieve gates.
The root quotient can have repeated factors, including p. -/
theorem receipt_multiplier_iff {N p D x : ℕ} (hp : 0 < p) (hD : 0 < D) :
    D*x ∈ chenQuotientPrimeSource N p ↔ x ∈ chenQuotientPrimeSource N (p*D) := by
  rw [mem_source_iff hp, mem_source_iff (Nat.mul_pos hp hD), Nat.mul_assoc]

private theorem rough_mul_iff (A : ℝ) (D x : ℕ) :
    ChenPrimeRough A (D*x) ↔ ChenPrimeRough A D ∧ ChenPrimeRough A x := by
  constructor
  · intro h
    exact ⟨fun q hq hd => h q hq (hd.trans (dvd_mul_right D x)),
      fun q hq hx => h q hq (hx.trans (dvd_mul_left x D))⟩
  · rintro ⟨hD,hx⟩ q hq hm
    exact (hq.dvd_mul.mp hm).elim (hD q hq) (hx q hq)

/-- Independently filtered ORIGINAL root receipts, in original quotient labels. -/
def originalReceiptLane (N p D : ℕ) (z : ℝ) : Finset ℕ :=
  (originalReceiver N p).filter (fun r => D ∣ r ∧ ChenPrimeRough z (r/D))

/-- Literal descendant source, at its own physical cutoff, with exactly the
two nonredundant tests obtained by pulling back ORIGINAL root sifting. -/
def inheritedChild (N B D : ℕ) (z : ℝ) : Finset ℕ :=
  (chenSiftedQuotientPrimeSource N B z).filter (fun x =>
    ChenPrimeRough ((N:ℝ)^a) D ∧ ChenPrimeRough ((N:ℝ)^a) x)

theorem originalReceiptLane_image {N p D : ℕ} (hp : 0 < p) (hD : 0 < D) (z : ℝ) :
    originalReceiptLane N p D z = (inheritedChild N (p*D) D z).image (fun x => D*x) := by
  ext r
  constructor
  · intro hr
    obtain ⟨hr,hd,hz⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr,hA⟩ := Finset.mem_filter.mp hr
    have hm : D*(r/D) = r := Nat.mul_div_cancel' hd
    rw [← hm] at hr hA
    exact Finset.mem_image.mpr ⟨r/D,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨(receipt_multiplier_iff hp hD).mp hr,hz⟩,
        (rough_mul_iff _ _ _).mp hA⟩,hm⟩
  · intro hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hx,hA⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx,hz⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(receipt_multiplier_iff hp hD).mpr hx,(rough_mul_iff _ _ _).mpr hA⟩,
      dvd_mul_right D x,by simpa only [Nat.mul_div_cancel_left _ hD] using hz⟩

theorem originalReceiptLane_test {N p D : ℕ} (hp : 0 < p) (hD : 0 < D)
    (z : ℝ) (f : ℕ → ℝ) :
    (∑ r ∈ originalReceiptLane N p D z, f r) =
      ∑ x ∈ inheritedChild N (p*D) D z, f (D*x) := by
  rw [originalReceiptLane_image hp hD]
  exact Finset.sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hD he)

/-- A small appended factor excludes the whole intersection, even if the
unrestricted emitted child has positive count or positive Theta. -/
theorem originalReceiptLane_empty_of_small {N p D q : ℕ} (z : ℝ)
    (hq : q.Prime) (hd : q ∣ D) (hs : (q:ℝ) < (N:ℝ)^a) :
    originalReceiptLane N p D z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hm,hrD,_⟩ := Finset.mem_filter.mp hr
  exact (not_le_of_gt hs) ((Finset.mem_filter.mp hm).2 q hq (hd.trans hrD))

/-- Exact residual/new shell of the FROZEN child that has no compatible
original root receipt; it is not an estimated error term. -/
def rejectedChild (N B D : ℕ) (z : ℝ) : Finset ℕ :=
  chenSiftedQuotientPrimeSource N B z \ inheritedChild N B D z

def tailProduct {N : ℕ} (o : Occurrence N) : ℕ := o.current.old.tail.prod
def memberCutoff {N : ℕ} (Q : ℝ) (o : Occurrence N) : ℝ :=
  cutoff Q (parentProduct o.current.old) o.current.node.physical.argument

theorem member_product {N n p : ℕ} {k : Root} {t : ℝ} {o : Occurrence N}
    (ho : o ∈ rootHistory N n k t p) : parentProduct o.current.old = p*tailProduct o := by
  have hw := (rootHistory_realization 0 ho).2
  obtain ⟨xs,hxs⟩ := integerWord_prefix [p] (pathCode 0 o.path) (pathPrimes o.path)
  change integerWord o.path.length [p] (pathCode 0 o.path) (pathPrimes o.path) =
    o.current.old at hw
  have hword : o.current.old = p::xs := hw.symm.trans hxs
  simp only [parentProduct,tailProduct,hword,List.prod_cons,List.tail_cons]

/-- Reindex the original receipts on a real history Member, with its
physical Q forced by the root key. The test can distinguish every receipt. -/
theorem owned_member_receipt_pullback {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k t c)
    (ho : o ∈ rootHistory N n k t p) (f : ℕ → ℝ) :
    (∑ r ∈ originalReceiptLane N p (tailProduct o) (memberCutoff (cellQ N n c.1) o), f r) =
      ∑ x ∈ inheritedChild N (parentProduct o.current.old) (tailProduct o)
        (memberCutoff (rootQ N n k t p) o), f (tailProduct o*x) := by
  have hp' := (Finset.mem_filter.mp hp).1
  have hpr := original_band_prime hp'
  have hpos := (rootHistory_support (by omega : 1<N) ht hu hn hpr
    (original_band_geometry hN hp') ho).1.2.1
  rw [member_product ho] at hpos
  have hD : 0 < tailProduct o := (Nat.pos_of_mul_pos_left hpos)
  rw [(original_fibre_geometry hN ht hu hn hp).1,member_product ho]
  exact originalReceiptLane_test hpr.1.pos hD _ f

/-- Predicate of the *original additive prime* ell; the old receiver
coprimality is kept and the ORIGINAL root quotient is tested at N^a. -/
def rootMask (N p ell : ℕ) : Prop :=
  receiver N ell ∧ ChenPrimeRough ((N:ℝ)^a) ((N-ell)/p)

/-- Generic specialization for a fresh singleton or pair with an actual
word product and a verified physical rough-prefix gate. -/
theorem rootMasked_count {N p B D : ℕ} {z : ℝ} (hp : 0 < p)
    (hB : B=p*D) (hr : ChenPrimeRough z B) :
    (frozenCount N B (rootMask N p) z : ℝ) =
      ((inheritedChild N B D z).card : ℝ) := by
  classical
  let A := (N:ℝ)^a
  have filtered :
      P2FrozenReceiverCountActions.frozenCarrier N B (rootMask N p) z =
      (P2FrozenReceiverCountActions.frozenCarrier N B (receiver N) z).filter
        (fun ell => ChenPrimeRough A ((N-ell)/p)) := by
    ext ell
    simp only [P2FrozenReceiverCountActions.frozenCarrier,rootMask,Finset.mem_filter,A,
      and_assoc]
  have hsrc : inheritedChild N B D z = (chenQuotientPrimeSource N B).filter
       (fun x => ChenPrimeRough z x ∧ ChenPrimeRough A D ∧ ChenPrimeRough A x) := by
    ext x
    simp only [inheritedChild,chenSiftedQuotientPrimeSource,Finset.mem_filter,A,and_assoc]
  have hsets :
      ((chenAdditivePrimeCarrier N).filter
        (fun ell => B ∣ N-ell ∧ ChenPrimeRough z ((N-ell)/B))).filter
          (fun ell => ChenPrimeRough A ((N-ell)/p)) =
      (chenAdditivePrimeCarrier N).filter (fun ell => B ∣ N-ell ∧
        ChenPrimeRough z ((N-ell)/B) ∧ ChenPrimeRough A D ∧
        ChenPrimeRough A ((N-ell)/B)) := by
    ext ell
    by_cases hd : B ∣ N-ell
    · have he : (N-ell)/p = D*((N-ell)/B) := by
        apply Nat.eq_of_mul_eq_mul_left hp
        have hpB : p ∣ B := by rw [hB]; exact dvd_mul_right p D
        have hpdiv : p ∣ N-ell := hpB.trans hd
        rw [Nat.mul_div_cancel' hpdiv,← Nat.mul_assoc,← hB,Nat.mul_div_cancel' hd]
      simp only [Finset.mem_filter,hd,true_and,he,rough_mul_iff,and_assoc]
    · simp [Finset.mem_filter,hd]
  rw [frozenCount,filtered,P5OriginalU5FrozenSource.frozenCarrier_eq_original_labels _ _ _ hr,
    hsets,hsrc,chenQuotientPrimeSource_filter_card] <;> simp only [Int.cast_natCast]

/-- The inherited source is an actual frozen count with a predicate on
the original additive prime, not a new abstract count assumption. -/
theorem owned_member_masked_count {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k t c)
    (ho : o ∈ rootHistory N n k t p) :
    let Q := cellQ N n c.1
    let z := memberCutoff Q o
    (frozenCount N (parentProduct o.current.old) (rootMask N p) z : ℝ) =
      ((originalReceiptLane N p (tailProduct o) z).card : ℝ) := by
  dsimp only
  have hband := (Finset.mem_filter.mp hp).1
  have hQ := (original_fibre_geometry hN ht hu hn hp).1
  have hr := (history_integer_roughness hN ht hu hn hband ho).1
  change ChenPrimeRough (memberCutoff (rootQ N n k t p) o) _ at hr
  rw [← hQ] at hr
  have hh := owned_member_receipt_pullback hN ht hu hn hp ho (fun _ => 1)
  rw [← hQ] at hh
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  exact (rootMasked_count (original_band_prime hband).1.pos (member_product ho) hr).trans hh.symm

private theorem unit_lane {N p : ℕ} {z : ℝ} (hz : z ≤ (N:ℝ)^a) :
    originalReceiptLane N p 1 z = originalReceiver N p := by
  ext r
  constructor
  · exact fun hr => (Finset.mem_filter.mp hr).1
  · intro hr
    refine Finset.mem_filter.mpr ⟨hr,one_dvd _,?_⟩
    rw [Nat.div_one]
    intro q hq hd
    exact hz.trans ((Finset.mem_filter.mp hr).2 q hq hd)

/-- At the actual origin the original root mask keeps exactly the original
quotients despite the physical clamp. This connects the masked history
count to the literal U3/U4 (all q, both tags) before any selected action. -/
theorem original_U34_masked_origins (N n m : ℕ) (t : ℝ) (hN : 2 ≤ N)
    (ht : 0 ≤ t) (hu : t ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    let count := fun (k : Root) =>
      ∑ c : RootKey n m, ∑ p ∈ rootFibre N n m k t c,
        (frozenCount N p (rootMask N p)
          (memberCutoff (cellQ N n c.1)
            (origin (N := N) 430 (rootRequest N n k t p))) : ℝ)
    currentChenUpsilon3 N + currentChenUpsilon4 N = count .U3 + count .U4 := by
  dsimp only
  rw [original_U34_eq_tagged_card,original_tagged_card,Nat.cast_add]
  simp only [Nat.cast_sum]
  have trans (k : Root) :
      (∑ c : RootKey n m, ∑ p ∈ rootFibre N n m k t c,
        (frozenCount N p (rootMask N p) (memberCutoff (cellQ N n c.1)
          (origin (N := N) 430 (rootRequest N n k t p))) : ℝ)) =
      ∑ p ∈ originalBand N k, ((originalReceiver N p).card : ℝ) := by
    calc
      _ = ∑ c : RootKey n m, ∑ p ∈ rootFibre N n m k t c, ((originalReceiver N p).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).1
        let o : Occurrence N := origin 430 (rootRequest N n k t p)
        have ho : o ∈ rootHistory N n k t p := List.mem_cons_self
        have hB : parentProduct o.current.old = p := by simp [o,origin,rootRequest,parentProduct]
        have hD : tailProduct o = 1 := rfl
        have hQ := (original_fibre_geometry hN ht hu hn hp).1
        have hz : memberCutoff (cellQ N n c.1) o ≤ (N:ℝ)^a := by
          rw [memberCutoff,hB,hQ,cutoff]
          change (rootQ N n k t p/(p:ℝ))^(1/
            (frozenRoot n k t (physicalPrime N p)).physical.argument) ≤ (N:ℝ)^a
          rw [Part5OriginalH430RequestedOriginalRowFreeze.frozen_root_sameQ_cutoff_power
            N n p k t hN (original_band_prime hp').1.pos ht hu (original_band_geometry hN hp') hn]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
            (min_le_left _ _)
        have hh := owned_member_masked_count hN ht hu hn hp ho
        dsimp only at hh
        rw [hB,hD,unit_lane hz] at hh
        exact hh
      _ = _ := Finset.sum_fiberwise_of_maps_to (s := originalBand N k)
        (t := Finset.univ) (g := keyAt N n m k t) (fun _ _ => Finset.mem_univ _)
        (fun p => ((originalReceiver N p).card : ℝ))
  exact congrArg₂ (· + ·) (trans .U3).symm (trans .U4).symm

/-- Every emitted TRUE quotient is charged exactly once, as a compatible
root receipt or a named incompatible value. This is positionwise;
no occurrence/path injectivity or sign claim about a later estimate. -/
theorem actual_member_count_split {N n m p : ℕ} {k : Root} {t : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k t c)
    (ho : o ∈ rootHistory N n k t p) :
    let Q := cellQ N n c.1
    let B := parentProduct o.current.old
    let D := tailProduct o
    let z := memberCutoff Q o
    (frozenCount N B (receiver N) z : ℝ) =
      ((originalReceiptLane N p D z).card : ℝ) + ((rejectedChild N B D z).card : ℝ) := by
  dsimp only
  have hc := owned_member_receipt_pullback hN ht hu hn hp ho (fun _ => 1)
  have hQ := (original_fibre_geometry hN ht hu hn hp).1
  rw [← hQ] at hc
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hf := history_frozen_count_eq_true_quotient hN ht hu hn (Finset.mem_filter.mp hp).1 ho
  change (frozenCount N _ (receiver N) (memberCutoff (rootQ N n k t p) o) : ℝ) = _ at hf
  rw [← hQ] at hf
  rw [hf,hc]
  let B := parentProduct o.current.old
  let D := tailProduct o
  let z := memberCutoff (cellQ N n c.1) o
  have sub : inheritedChild N B D z ⊆ chenSiftedQuotientPrimeSource N B z :=
    Finset.filter_subset _ _
  change ((chenSiftedQuotientPrimeSource N B z).card : ℝ) =
    ((inheritedChild N B D z).card : ℝ) +
    (((chenSiftedQuotientPrimeSource N B z \ inheritedChild N B D z).card : ℕ) : ℝ)
  exact_mod_cast (by simpa only [Nat.add_comm] using
    (Finset.card_sdiff_add_card_eq_card sub).symm :
      (chenSiftedQuotientPrimeSource N B z).card =
        (inheritedChild N B D z).card +
          (chenSiftedQuotientPrimeSource N B z \ inheritedChild N B D z).card)

end
end ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback
