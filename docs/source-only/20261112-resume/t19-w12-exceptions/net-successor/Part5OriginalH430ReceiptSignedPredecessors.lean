import ImbalancedChen.Part5OriginalH430OwnedReceiptNet

/-! The change of ordinary receiver inside the archived signed ledger.
The switch price and all predecessor profiles stay at their own Q,
argument, and multiplicity. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptSignedPredecessors
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers P2OriginalHalfOpenProfileCarrier (normalizedLog)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalW2CountTupleReindex (occurrenceCutoff)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P5CanonicalUpperCancellation (upperA lowerBar)
open P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430BankOrdinarySingletons
open Part5OriginalH430SelectedFreshWindows Part5OriginalH430FreshBankBudget (strictDebt)
open Part5OriginalH430FreshReceiptCounts (receiptSingle receiptPair strict_receipt_rows)
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430ReceiptFourBand (count)
open Part5OriginalH430ReceiptDirections (outsideReceipt receiver_count_split)
open Part5OriginalH430OwnedReceiptNet
open Part5OriginalH430ImmutableBankProfiles (precedingH precedingh)
open Part5OriginalH430FixedReadDictionary (fixedValue baseValue)
open Part5OriginalH430W1OriginalBaseEnclosure (currentK)
open Part5OriginalH430W1PhysicalRoughDictionary (integerMass)
open scoped Classical BigOperators

variable {N n p : ℕ} {k : Root} {t : ℝ} {g : Fin 430}

def lowerPrice (l : Index N n k t p g) (a : Lane) : ℝ :=
  let Q := rootQ N n k t p
  let d := wordProduct l
  ∑ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
    let u := argument N Q d q.val a
    thetaAtom N Q (d*q.val)*(lowerBar u+tableFunction true (precedingh g) u)

def lowerShell (l : Index N n k t p g) (a : Lane) : ℝ :=
  let Q := rootQ N n k t p
  let d := wordProduct l
  ∑ q∈singleChildren (rule a) N Q (oldWord l) (ceilingAt l),
    ((rejectedChild N (d*q.val) (tailProduct (levelOccurrence l)*q.val)
      (cutoff Q d (anchor a))).card:ℝ)

def upperPrice (l : Index N n k t p g) (j : Fin 36) (s : Fin 4) : ℝ :=
  let Q := rootQ N n k t p
  let d := wordProduct l
  ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
    let u := pairProfile (originalW2At j) s (normalizedLog N (wordLevel l)
      (P2OriginalPairChildWindowDictionary.pairTuple v))
    thetaAtom N Q (d*v.1.val*v.2.val)*(upperA u-tableFunction false (precedingH g) u)

def upperShell (l : Index N n k t p g) (j : Fin 36) (s : Fin 4) : ℝ :=
  let Q := rootQ N n k t p
  let d := wordProduct l
  ∑ v∈pairChildren j s N Q (oldWord l) (ceilingAt l),
    ((rejectedChild N (d*v.1.val*v.2.val) (tailProduct (levelOccurrence l)*v.2.val*v.1.val)
      (occurrenceCutoff Q d (originalW2At j) s v.1.val v.2.val)).card:ℝ)

def fixedPrice (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (i,j) => thetaAtom N (rootQ N n k t p) (wordProduct l)*
      (upperA (W1Anchor j)-fixedValue (precedingH g) (.inl (i,j)))
  | .inr j => let a := originalW2At j
    thetaAtom N (rootQ N n k t p) (wordProduct l)*
      ((4*upperA a.s0+upperA a.phi1)/5-fixedValue (precedingH g) (.inr j))

def anchorShell (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (_,j) => count N (wordProduct l) (outsideReceipt N p)
      (cutoff (rootQ N n k t p) (wordProduct l) (W1Anchor j))
  | .inr j => let d := wordProduct l
    let z := cutoff (rootQ N n k t p) d
    let a := originalW2At j
    (4*count N d (outsideReceipt N p) (z a.s0)+count N d (outsideReceipt N p) (z a.phi1))/5

def switchPrice (l : Index N n k t p g) : Original106Action → ℝ
  | .inl (i,j) => (currentK:ℝ)/4*(thetaConversion N (wordProduct l)*
      integerMass N (rootQ N n k t p) (wordProduct l) i j)/2
  | .inr j => (Part5OriginalH430W2SignedOrdinaryBase.ordinaryBase j-baseValue (.inr j))*
      thetaAtom N (rootQ N n k t p) (wordProduct l)

def modelRow (l : Index N n k t p g) (a : Original106Action) : ℝ :=
  fixedPrice l a + (match a with
    | .inl (i,j) => -lowerPrice l (.inl (i,j))/2
    | .inr j => -(∑ s : Fin 3,lowerPrice l (.inr (j,s)))/5 + (∑ s : Fin 4,upperPrice l j s)/5) +
    switchPrice l a

def correction (l : Index N n k t p g) (a : Original106Action) : ℝ :=
  -anchorShell l a + match a with
    | .inl (i,j) => lowerShell l (.inl (i,j))/2
    | .inr j => (∑ s : Fin 3,lowerShell l (.inr (j,s)))/5 - (∑ s : Fin 4,upperShell l j s)/5

/-- None of the three outside-receipt counts is set to zero. Inserting
the sharp source instead of relaxing all ordinary outputs removes the
positive pair shell and has the opposite effect on singleton deficits. -/
theorem signed_price_identity (hN : 2≤N) (ht : 0≤t) (hu : t≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈originalBand N k)
    (l : Index N n k t p g) (a : Original106Action) :
    row l a-parentModel l =
      strictDebt l a+correction l a+(modelRow l a-parentModel l) := by
  obtain ⟨h1,h2⟩ := strict_receipt_rows hN ht hu hn hp l
  have hs (b : Lane) : Part5OriginalH430FreshBankBudget.strictSingle l b =
      lowerPrice l b-Part5OriginalH430SelectedReceiptMother.strictSingle l b-lowerShell l b := by
    rw [h1]
    simp only [receiptSingle,lowerPrice,Part5OriginalH430SelectedReceiptMother.strictSingle,
      lowerShell,sum_sub_distrib]
  have hpair (j : Fin 36) (s : Fin 4) : Part5OriginalH430FreshBankBudget.strictPair l j s =
      pairCount l j s+upperShell l j s-upperPrice l j s := by
    rw [h2]
    simp only [receiptPair,pairCount,upperShell,upperPrice,sum_sub_distrib,sum_add_distrib]
  let Q := rootQ N n k t p
  let d := wordProduct l
  have hfix (u : ℝ) : (P2FrozenReceiverCountActions.frozenCount N d (receiver N) u:ℝ) =
      count N d (rootMask N p) u+count N d (outsideReceipt N p) u := receiver_count_split N p d u
  rcases a with ⟨i,j⟩|j
  · simp only [row,anchors,negatives,positives,switched,strictDebt,
      Part5OriginalH430W1SignedOrdinaryBase.fixedDebt,
      Part5OriginalH430BankAfterW1PrimeRestriction.cleanDebt,hs,correction,anchorShell,modelRow,
      fixedPrice,switchPrice]
    rw [hfix]
    ring
  · simp only [row,anchors,negatives,positives,switched,strictDebt,
      Part5OriginalH430W2SignedOrdinaryBase.fixedDebt,Part5OriginalH430SelectedOrdinaryPairCounts.actualState,
      hs,hpair,correction,anchorShell,modelRow,fixedPrice,switchPrice,sum_add_distrib,sum_sub_distrib]
    rw [hfix,hfix]
    ring

end
end ImbalancedChen.Part5OriginalH430ReceiptSignedPredecessors
