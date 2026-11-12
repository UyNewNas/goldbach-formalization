import ImbalancedChen.Part5OriginalH430SelectedFreshWindows
import ImbalancedChen.Part5OriginalH430BankAfterW1PrimeRestriction
import ImbalancedChen.P2EnhancedCollisionThetaPayment

/-! All 106 selected rows on their original marked positions. Remove the
three restored windows and the labelled collision cost from the W2 base.
Keep the rejected pairs, longer positive words, ordinary base difference,
W1 prime restriction, and the signed predecessor discrepancies explicitly. -/
namespace ImbalancedChen.Part5OriginalH430FreshBankBudget
noncomputable section
open Real Set Filter Finset Wu2008DoubleSieve
open MathlibNt.SieveTheory.SingularSeries
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalPositiveSameQMassLift P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedCollisionWeightedBudget P2EnhancedCollisionThetaPayment
open P2EnhancedThetaReciprocalMass (Theta_lower)
open P2EnhancedTwentyOneQuotientFinite (collisionSwitched)
open P2EnhancedPrefixMaskDefect (SelectedCollision collisionCarrier)
open P2FrozenReceiverCountActions (frozenCount)
open P5OriginalU5FrozenSource (receiver)
open P2OriginalW2CountTupleReindex P2OriginalW2MotherOccurrenceReindex
open P2OriginalHalfOpenProfileCarrier P2OriginalProfileThetaNormalization P2OriginalCompactThetaMass
open P2OriginalBankOldProfilePassage P2OriginalW2ComplementAction
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger (selectedBankRoundingLoss)
open Part5OriginalH430ActualSelectedRowBudget (actualBankTheta)
open Part5OriginalH430AllBankSignedCounts (physicalDefect)
open Part5OriginalH430BankAfterW1PrimeRestriction (cleanDebt finalDebt full_bank_after_W1_prime_restriction)
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430FixedReadDictionary (baseValue)
open Part5OriginalH430OrdinaryPairCounts (childDiscrepancy)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows
open scoped Classical BigOperators Topology

variable {N n p : ℕ} {rt : Root} {t : ℝ} {g : Fin 430}

def collision (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  let a := originalW2At j
  collisionSwitched N d N (cutoff Q d a.s0) (cutoff Q d a.phi1)
    (cutoff Q d a.phi2) (cutoff Q d a.phi3) (cutoff Q d a.s)

/-- Length-two switched words have no exempt selected position. -/
theorem pair_collision_empty (N d q r : ℕ) : collisionCarrier N d [q,r]=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ell he
  obtain ⟨b,hb,hd,_,_⟩ := (mem_filter.mp he).2
  exact hb.not_dvd_one (by simpa using hd)

/-- In every actual selected long word, even a receiver with a selected
square has a word disjoint from the old prefix. All the word's letters,
including the collision prime if present, lie below the target. -/
theorem collision_word_no_old_repeat (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (j : Fin 36) (hl : l∈selectedLevel N n rt t p g (.inr j))
    (r : ℕ) (w : List ℕ)
    (hw : w∈secondFunctionalMotherTuples
      (primeWindow N (cutoff (rootQ N n rt t p) (wordProduct l) (originalW2At j).s0)
        (cutoff (rootQ N n rt t p) (wordProduct l) (originalW2At j).s)) r) :
    (collisionCarrier N (wordProduct l) w).filter
      (fun _ => ∃ q∈w, q∣wordProduct l) = ∅ := by
  have hrough := (selected_geometry hN ht hu hn hp _ l hl).2.2.2
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ell he
  obtain ⟨q,hq,hd⟩ := (mem_filter.mp he).2
  have hwin := mem_primeWindow.mp (((secondFunctionalMother_tuple_mem _ _ _).mp hw).2.2 q hq)
  exact (not_lt_of_ge (hrough q hwin.1 hd)) hwin.2.2.2

private theorem restored_three_zero (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (j : Fin 36) (hl : l∈selectedLevel N n rt t p g (.inr j)) :
    let Q := rootQ N n rt t p
    let d := wordProduct l
    let a := originalW2At j
    let A := cutoff Q d a.s0
    fourthRowMotherBadPrime N d A (cutoff Q d a.s) = 0 ∧
    fourthRowMotherBadPrime N d A (cutoff Q d a.phi2) = 0 ∧
    fourthRowMotherBadPrime N d A (cutoff Q d a.phi3) = 0 := by
  have h := selected_geometry hN ht hu hn hp _ l hl
  have hb := P2AllW2SameQRawCountAction.bank_cutoff_order (Q:=rootQ N n rt t p)
    (d:=wordProduct l) j (parentWindow_logs h.1).2.1.le
  have hz {u : ℝ} (hfit : u≤cutoff (rootQ N n rt t p) (wordProduct l) (originalW2At j).s) :
      fourthRowMotherBadPrime N (wordProduct l)
        (cutoff (rootQ N n rt t p) (wordProduct l) (originalW2At j).s0) u=0 := by
    unfold fourthRowMotherBadPrime
    rw [restored_zero hfit h.2.2.2,sum_empty]
  exact ⟨hz le_rfl,hz (hb.2.2.1.trans hb.2.2.2),hz hb.2.2.2⟩

/-- The original all-word collision majorant has free endpoints. The
published relative seed bound hardcodes 227/50, so here the actual bank
anchor is bounded using the residual floor and s0≤5. -/
theorem all36_collision_on_history {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (n : ℕ) (rt : Root) (t : ℝ) (p dep : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N rt →
      ∀ (l : LevelIndex N n rt t p dep) (j : Fin 36),
        collision N (rootQ N n rt t p) (wordProduct l) j ≤
          ε*thetaAtom N (rootQ N n rt t p) (wordProduct l) := by
  let η := frozenLeafCutoffFloor
  have hη : 0<η := frozenLeafCutoffFloor_pos
  have hU := liuUniversalProduct_pos
  obtain ⟨T1,hT1,hpay⟩ := ninth_power_log_error_budget 6 (C:=1408/η)
    (α:=η) (ε:=2*liuUniversalProduct*ε) (by positivity) hη (by positivity)
  have hlog : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hN hEven n rt t p dep ht hu hn hp l j
  have h4 : 4≤N := by omega
  have hN2 : 2≤N := by omega
  have h1 : 1<N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  let Q := rootQ N n rt t p
  let d := wordProduct l
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN2 ht hu hn hp l
  have hrs := rootHistory_support h1 ht hu hn (original_band_prime hp)
    (original_band_geometry hN2 hp) (levelOccurrence_source l).1
  have hR := (parentWindow_logs hrs.1).2.1
  have hR' := residual_level_le_N hd hrs.1.2.2.2.1
  have hold := (history_integer_roughness hN2 ht hu hn hp (levelOccurrence_source l).1).2.2.1
  obtain ⟨hs,h3,h2,hp1,h0,h5⟩ := P2AllW2SameQRawCountAction.original_W2_order _ (originalW2At_mem j)
  have hz : (N:ℝ)^η≤cutoff Q d (originalW2At j).s0 := by
    rw [cutoff_eq_physical_power hd hQ]
    apply rpow_le_rpow_of_exponent_le hNr
    change frozenResidualFloor/6≤wordLevel l/(originalW2At j).s0
    exact (div_le_div_of_nonneg_right hL.1 (by norm_num : (0:ℝ)≤6)).trans
      (div_le_div_of_nonneg_left (frozenResidualFloor_pos.trans_le hL.1).le
        (by linarith) (by linarith))
  have hf : cutoff Q d (originalW2At j).s≤(N:ℝ) := by
    unfold cutoff
    have hh : 1/(originalW2At j).s≤1 := by
      apply (div_le_iff₀ (by linarith : 0<(originalW2At j).s)).mpr
      linarith
    exact (show (Q/(d:ℝ))^(1/(originalW2At j).s)≤Q/d by
      simpa using rpow_le_rpow_of_exponent_le hR.le hh).trans hR'
  have hc : collision N Q d j≤collisionScale N d η*(22*(1+log N)^6) :=
    collisionSwitched_le h4 hEven hd hη hold hz hf
  have hcoef := (collision_coefficient_le hη (hT2 N ((le_max_right _ _).trans hN))).trans
    (hpay N ((le_max_left _ _).trans hN))
  have hθ := Theta_lower h4 Q {d} (fun _ => (1:ℝ)) (by simpa using hd)
    (by simp) (by simpa using And.intro hR hR')
  simp only [Theta_eq_sum_atoms,sum_singleton,one_mul] at hθ
  calc
    _ ≤ collisionScale N d η*(22*(1+log N)^6) := hc
    _ = (22*(1+log N)^6*(1/η)*(N:ℝ)/(N:ℝ)^η)*(1/(d:ℝ)) := by
      simp only [collisionScale,div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ((2*liuUniversalProduct*ε)*(N:ℝ)/log N^2)*(1/(d:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ε*((2*liuUniversalProduct*(N:ℝ)/log N^2)*(1/(d:ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hθ he.le

def strictSingle (l : Index N n rt t p g) (a : Lane) : ℝ :=
  let Q := rootQ N n rt t p
  let d := wordProduct l
  ∑ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
    thetaAtom N Q (d*q.val)*(P5CanonicalUpperCancellation.lowerBar (argument N Q d q.val a)+
      tableFunction true (precedingh g) (argument N Q d q.val a)) -
      (frozenCount N (d*q.val) (receiver N) (cutoff Q d (anchor a)):ℝ)

def pairDifference (N : ℕ) (Q L : ℝ) (d : ℕ) (j : Fin 36) (k : Fin 4)
    (g : Fin 430) (x : Fin 2 → ℕ) : ℝ :=
  let a := originalW2At j
  let b := d*x 0*x 1
  let s := pairProfile a k (normalizedLog N L x)
  (frozenCount N b (receiver N) (occurrenceCutoff Q d a k (x 0) (x 1)):ℝ) -
    thetaAtom N Q b*(P5CanonicalUpperCancellation.upperA s-tableFunction false (precedingH g) s)

def strictPair (l : Index N n rt t p g) (j : Fin 36) (k : Fin 4) : ℝ :=
  let Q := rootQ N n rt t p
  ∑ v∈pairChildren j k N Q (oldWord l) (ceilingAt l),
    pairDifference N Q (wordLevel l) (wordProduct l) j k g
      (P2OriginalPairChildWindowDictionary.pairTuple v)

private theorem pair_debt_exact (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (j : Fin 36) (k : Fin 4)
    (hl : l∈selectedLevel N n rt t p g (.inr j)) :
    childDiscrepancy N (rootQ N n rt t p) (wordLevel l) (actualState N) (wordProduct l) j k g =
      strictPair l j k := by
  let Q := rootQ N n rt t p
  let L := wordLevel l
  let d := wordProduct l
  let F := fun (a b : ℕ) => pairDifference N Q L d j k g ![a,b]
  have hvec (x : Fin 2 → ℕ) : ![x 0,x 1]=x := by funext i; fin_cases i <;> rfl
  obtain ⟨hd,hL,hQ,_,_⟩ := scale_and_alpha hN ht hu hn hp l
  have hsum := all_four_window_occurrences_reindex (by omega : 1<N) hd
    (frozenResidualFloor_pos.trans_le hL.1) hQ (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k F
  have hh : windowOccurrence N Q L d (originalW2At j) k F =
      childDiscrepancy N Q L (actualState N) d j k g := by
    simpa only [F,hvec,pairDifference,childDiscrepancy,actualState] using hsum
  exact hh.symm.trans (pair_W2 hN ht hu hn hp j k l hl F)

def remainingPositive (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  let a := originalW2At j
  (∑ k : Fin 4,sourceRejectedOccurrence N Q d a k) +
    higherPaidSwitched N Q (actualState N) d (cutoff Q d a.s0) (cutoff Q d a.phi1)
      (cutoff Q d a.phi2) (cutoff Q d a.phi3) (cutoff Q d a.s)

def strictDebt (l : Index N n rt t p g) : Original106Action → ℝ
  | .inl (i,j) =>
    let Q := rootQ N n rt t p
    let d := wordProduct l
    Part5OriginalH430W1SignedOrdinaryBase.fixedDebt N Q d i j g +
      strictSingle l (.inl (i,j))/2 + cleanDebt N Q d i j
  | .inr j =>
    let Q := rootQ N n rt t p
    let d := wordProduct l
    Part5OriginalH430W2SignedOrdinaryBase.fixedDebt N Q d j g +
      (∑ s : Fin 3, strictSingle l (.inr (j,s)))/5 +
      (∑ s : Fin 4, strictPair l j s)/5 +
      (remainingPositive N Q d j/5 -
        (Part5OriginalH430W2SignedOrdinaryBase.ordinaryBase j - baseValue (.inr j))*thetaAtom N Q d)

theorem selected_debt_exact (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N rt)
    (l : Index N n rt t p g) (a : Original106Action)
    (hl : l∈selectedLevel N n rt t p g a) :
    let Q := rootQ N n rt t p
    let d := wordProduct l
    finalDebt N Q (wordLevel l) d g a = strictDebt l a +
      (match a with | .inl _ => 0 | .inr j => collision N Q d j/5) := by
  let Q := rootQ N n rt t p
  let d := wordProduct l
  dsimp only
  rcases a with ⟨i,j⟩ | j
  · have hsing : Part5OriginalH430W1SignedOrdinaryBase.lowerDebt N Q (wordLevel l) d i j g =
        strictSingle l (.inl (i,j)) :=
      selected_single_sum hN ht hu hn hp (.inl (i,j)) l hl _
    change _ + Part5OriginalH430W1SignedOrdinaryBase.lowerDebt N Q (wordLevel l) d i j g/2 +
      cleanDebt N Q d i j = (_ + strictSingle l (.inl (i,j))/2 + cleanDebt N Q d i j) + 0
    rw [hsing,add_zero]
  · have hsing (s : Fin 3) :
        Part5OriginalH430W2SignedSingletons.lowerDebt N Q (wordLevel l) d j s g =
          strictSingle l (.inr (j,s)) := selected_single_sum hN ht hu hn hp (.inr (j,s)) l hl _
    have hpairs := pair_debt_exact hN ht hu hn hp l j
    obtain ⟨hZ,hC,hD⟩ := restored_three_zero hN ht hu hn hp l j hl
    change Part5OriginalH430W2SignedOrdinaryBase.rowDebt N Q (wordLevel l) d j g =
      strictDebt l (.inr j) + collision N Q d j/5
    unfold Part5OriginalH430W2SignedOrdinaryBase.rowDebt
      Part5OriginalH430W2SignedOrdinaryBase.switchedDebt Part5OriginalH430W2SignedOrdinaryBase.positive
    have hk (s : Fin 4) := hpairs s hl
    simp_rw [hsing,hk]
    dsimp only [strictDebt,remainingPositive,collision,Q,d] at *
    rw [hZ,hC,hD]
    ring

/-- One threshold for the actual selected positions in all 106 rows.
The error is proportional to the sum of the parent's original marked
atoms; no division by the family's total mass occurs. -/
theorem full_bank_strict_after_exceptions {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (rt : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N rt →
      ∀ g : Fin 430,
        (∑ a : Original106Action,∑ l∈selectedLevel N n rt t p g a,
          levelMark l*physicalDefect l)+selectedBankRoundingLoss N n rt t p g ≤
        (∑ a : Original106Action,∑ l∈selectedLevel N n rt t p g a,levelMark l*strictDebt l a)+
          ε*actualBankTheta N n rt t p g := by
  obtain ⟨Ta,ha4,ha⟩ := full_bank_after_W1_prime_restriction (half_pos he)
  obtain ⟨Tb,hb4,hb⟩ := all36_collision_on_history (show 0<5*(ε/2) by positivity)
  refine ⟨max Ta Tb,ha4.trans (le_max_left _ _),?_⟩
  intro N hN hEven n rt t p ht hu hn hp g
  have hNa := (le_max_left Ta Tb).trans hN
  have hNb := (le_max_right Ta Tb).trans hN
  have h4 := ha4.trans hNa
  have h2 : 2≤N := by omega
  let Q := rootQ N n rt t p
  let S := selectedLevel N n rt t p g
  have hbase := ha N hNa hEven n rt t p ht hu hn hp g
  have hr : (∑ a : Original106Action,∑ l∈S a,
        levelMark l*finalDebt N Q (wordLevel l) (wordProduct l) g a) ≤
      (∑ a : Original106Action,∑ l∈S a,levelMark l*strictDebt l a) +
        ε/2*actualBankTheta N n rt t p g := by
    unfold actualBankTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro a _
    unfold levelTheta
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro l hl
    have hm := (mark_pos (levelOccurrence l)).le
    have h := selected_debt_exact h2 ht hu hn hp l a hl
    change levelMark l*finalDebt N Q (wordLevel l) (wordProduct l) g a ≤
      levelMark l*strictDebt l a+(ε/2)*(levelMark l*thetaAtom N Q (wordProduct l))
    rw [h]
    rcases a with ⟨i,j⟩ | j
    · have hs := (selected_geometry h2 ht hu hn hp _ l hl).1
      have hθ := thetaAtom_nonneg h4 hs.2.1 (parentWindow_logs hs).2.1
      simpa only [add_zero] using le_add_of_nonneg_right (a:=levelMark l*strictDebt l (.inl (i,j)))
        (mul_nonneg (half_pos he).le (mul_nonneg hm hθ))
    · have hc := hb N hNb hEven n rt t p (g.val+1) ht hu hn hp l j
      have hh : collision N Q (wordProduct l) j/5 ≤ (ε/2)*thetaAtom N Q (wordProduct l) := by
        linarith only [hc]
      dsimp only
      nlinarith only [mul_le_mul_of_nonneg_left hh hm]
  dsimp only [S,Q] at hr
  linarith only [hbase,hr]

end
end ImbalancedChen.Part5OriginalH430FreshBankBudget
