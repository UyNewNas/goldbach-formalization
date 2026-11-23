import ImbalancedChen.Part5OriginalH430MaskedSievePlateau

/-! Strict physical child carriers and same-mother switched words on the
original masked receipts, independent of any archived numerical bank price. -/
namespace ImbalancedChen.Part5OriginalH430ActualMaskedBankWindows
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedLowerPhysicalNode (residual)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430BankSlotTargets
open Part5OriginalH430SeedHistoryMass Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430ReceiptFourBand
open Part5OriginalH430MonotoneSieveHeight Part5OriginalH430MaskedSievePlateau
open P2FrozenReceiverCountActions (quotientCount)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount)
open scoped Classical BigOperators

variable {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}

private theorem inherited_empty {B D q : ℕ} (z : ℝ) (hq : q.Prime) (hd : q∣D)
    (hs : (q:ℝ)<(N:ℝ)^a) : inheritedChild N B D z=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_lt_of_ge ((mem_filter.mp hx).2.1 q hq hd)) hs

private theorem selected_prime_lt (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (l : Index N n k t p g) (A : Original106Action) (hl : l∈selectedLevel N n k t p g A)
    {q : ℕ} (hq : q.Prime)
    (hr : relativePrime (rootQ N n k t p) (oldWord l) q < 1/actionTarget A) : (q:ℝ)<(N:ℝ)^a := by
  have ho := (levelOccurrence_source l).1
  have hg := selected_geometry hN ht hu hn hp A l hl
  have h := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) ho
  have hL := (parentWindow_logs hg.1).2.2
  have hx := mul_lt_mul_of_pos_left hr hL
  rw [relativePrime_physical hg.1,mul_one_div] at hx
  have hbound := div_le_div_of_nonneg_left hL.le (zero_lt_one.trans_le h.2.2.2.1.1) hg.2.1
  have hheight := rootHistory_height_le hN ht hu hn hp ho
  unfold height at hheight
  rw [h.2.1] at hheight
  have hpq : (N:ℝ)^physicalPrime N q = q :=
    actualPrimeTupleLog_rpow (by omega : 1<N) (fun _ : Fin 1 => q) (fun _ => hq.pos) 0
  rw [←hpq]
  exact (strictMono_rpow_of_base_gt_one (by exact_mod_cast (show 1<N by omega)))
    (hx.trans_le (hbound.trans hheight))

/-- Each accepted bank singleton has empty intersection with the original
root even if its requested rough cutoff is moved. -/
theorem strict_single_carrier_empty (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (b : Lane) (hl : l∈selectedLevel N n k t p g (owner b)) {q : Fin (N+1)}
    (hq : q∈singleChildren (rule b) N (rootQ N n k t p) (oldWord l) (ceilingAt l)) (z : ℝ) :
    inheritedChild N (wordProduct l*q.val) (tailProduct (levelOccurrence l)*q.val) z=∅ := by
  have h := mem_singleChildren.mp hq
  have htop : relativePrime (rootQ N n k t p) (oldWord l) q.val < 1/actionTarget (owner b) := by
    rcases b with ⟨i,j⟩ | ⟨j,s⟩
    · exact h.2.2.1.2
    · exact singleton_below_target j s h.2.2.1
  exact inherited_empty z h.1.1 (dvd_mul_left _ _)
    (selected_prime_lt hN ht hu hn hp l (owner b) hl h.1.1 htop)

/-- The smaller fresh prime excludes the root receipt at the original
larger,smaller appended word in each of the four W2 lanes. -/
theorem strict_pair_carrier_empty (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (j : Fin 36) (s : Fin 4) (hl : l∈selectedLevel N n k t p g (.inr j))
    {v : Fin (N+1) × Fin (N+1)} (hv : v∈pairChildren j s N (rootQ N n k t p) (oldWord l) (ceilingAt l))
    (z : ℝ) : inheritedChild N (wordProduct l*v.1.val*v.2.val)
      (tailProduct (levelOccurrence l)*v.2.val*v.1.val) z=∅ := by
  have h := mem_pairChildren.mp hv
  have hs := pair_below_target j s h.2.2.2.1
  exact inherited_empty z h.1.1.1 (dvd_mul_left _ _)
    (selected_prime_lt hN ht hu hn hp l (.inr j) hl h.1.1.1 hs)

theorem selected_cutoff_le (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k) (l : Index N n k t p g)
    (A : Original106Action) (hl : l∈selectedLevel N n k t p g A) {s : ℝ} (hs : actionTarget A≤s) :
    cutoff (rootQ N n k t p) (wordProduct l) s ≤ (N:ℝ)^a := by
  have ho := (levelOccurrence_source l).1
  have hg := selected_geometry hN ht hu hn hp A l hl
  have hr := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp)
    (original_band_geometry hN hp) ho
  have hle : cutoff (rootQ N n k t p) (wordProduct l) s ≤
      memberCutoff (rootQ N n k t p) (levelOccurrence l) :=
    rpow_le_rpow_of_exponent_le (parentWindow_logs hg.1).2.1.le
      (one_div_le_one_div_of_le (zero_lt_one.trans_le hr.2.2.2.1.1) (hg.2.1.trans hs))
  exact hle.trans (member_cutoff_le_original hN ht hu hn hp ho)

private theorem empty_positive_labels (χ : ℕ → ℕ) : positiveLabels ∅ χ=0 := by
  norm_num [positiveLabels,fourthRowMotherLowPairs,fourthRowMotherCrossPairs,
    secondFunctionalMotherPrefixIndices,secondFunctionalMotherGammaLabels,secondFunctionalMotherGammaWords,
    fourthRowMotherColoured,fourthRowMotherPrefixes]

/-- W2's actual switched label mass includes every original Gamma word,
with its own multiplicity, prior to any upper relaxation of the mask. -/
theorem root_positive_mass_zero {N p B D : ℕ} (hp : 0<p) (hB : B=p*D)
    (u b c e f : ℝ) (hf : f≤(N:ℝ)^a) : positiveMass N B (rootMask N p) u b c e f=0 := by
  unfold positiveMass
  apply sum_eq_zero
  intro ell he
  rw [small_divisor_labels_empty hp hB (fun _ h => h) hf he,empty_positive_labels]

/-- The first prime alone excludes every actual raw switched triple,
including its historical middle-prime cutoff and exemption modulus. -/
theorem root_raw_triple_zero {N p B D M : ℕ} (hp : 0<p) (hB : B=p*D)
    (z w : ℝ) (hw : w≤(N:ℝ)^a) : rawTripleCount N B M (rootMask N p) z w=0 := by
  unfold rawTripleCount
  apply sum_eq_zero
  intro v hv
  have hq := mem_primeWindow.mp (mem_product.mp (mem_filter.mp hv).1).1
  let K := v.1*v.2.1*v.2.2
  have hK : v.1∣K := (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hx : (sieveCarrier N (B*K) (M*v.1) (v.2.1:ℝ)).filter (rootMask N p) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ell he
    obtain ⟨hcar,hmask⟩ := mem_filter.mp he
    have hdiv := (mem_filter.mp hcar).2.2.1
    have hBD : B*K=p*(D*K) := by rw [hB,Nat.mul_assoc]
    have hm : v.1 ∣ (N-ell)/p := by
      rw [quotient_on_root hp hBD hdiv]
      exact ((hK.trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _))
    exact (not_lt_of_ge (hmask.2 v.1 hq.1 hm)) (hq.2.2.2.trans_le hw)
  change (((sieveCarrier N (B*K) (M*v.1) (v.2.1:ℝ)).filter (rootMask N p)).card:ℤ)=0
  rw [hx,card_empty,Nat.cast_zero]

/-- Both signed mothers on every actual bank position, before relaxation
to the entire full prime-positive packet. -/
theorem selected_masked_switched_zero {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}
    (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈originalBand N k) (l : Index N n k t p g) (A : Original106Action)
    (hl : l∈selectedLevel N n k t p g A) :
    let d := wordProduct l
    let z := cutoff (rootQ N n k t p) d
    match A with
    | .inl (i,j) => rawTripleCount N d (d*N) (rootMask N p) (z (W1Anchor j)) (z (W1Target i))=0
    | .inr j => let b := originalW2At j
                positiveMass N d (rootMask N p) (z b.s0) (z b.phi1) (z b.phi2) (z b.phi3) (z b.s)=0 := by
  have hB := member_product (levelOccurrence_source l).1
  have htop := selected_cutoff_le hN ht hu hn hp l A hl le_rfl
  rcases A with ⟨i,j⟩ | j
  · exact root_raw_triple_zero (original_band_prime hp).1.pos hB _ _ htop
  · exact root_positive_mass_zero (original_band_prime hp).1.pos hB _ _ _ _ _ htop

end
end ImbalancedChen.Part5OriginalH430ActualMaskedBankWindows
