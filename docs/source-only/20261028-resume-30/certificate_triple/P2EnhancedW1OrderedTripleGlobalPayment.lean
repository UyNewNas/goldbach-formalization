import ImbalancedChen.P2EnhancedW1OrderedPositiveTripleWord

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The PhaseB4 ordered positive triple is a single SAME-parent source word,
not three feedback edges. This file sums its actual repeated-label fibres
first over the original old-mask receivers and then over the actual finite
marked B support. No fibre multiplicity is assumed: it follows from the
eligible-prime product divisibility at the exact quotient (N-ell)/B.

The unchanged sigma(B), E(B,ell), Q and B are retained throughout. The
fixed-power cutoff is a physical admissibility condition. PhaseB4's
graph_w1_fixed_power caller supplies it from the finite graph; no final
positive-product or K estimate is postulated here. The resulting threshold
precedes N, Q, the marked support, actions and weights.

Original anchors: manuscript-body.tex 790--817, 819--875;
same-new-level-double-sieve-route.tex 93--105,147--165.
-/

namespace ImbalancedChen.P2EnhancedW1OrderedTripleGlobalPayment

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedW1OrderedPositiveTripleWord
  (repeatedTripleWords repeatedTripleWords_mem_squareEvent
   repeatedTripleWords_card_le_cube)
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes)
open P2EnhancedW1FixedPowerLabelMultiplicity
  (eligiblePrimes_card_le_inv_fixed_power)
open P2EnhancedW1SquareExceptionPower
  (squareEvent weightedSquareEvent weightedSquareEvent_theta_payment)
open P2EnhancedLowerPrimeChildCarriers (parentWindow)
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P5OriginalActionMassBound (W1Anchor)

/-- All actual old-mask receivers, with every distinct strictly ordered
triple counted once. There is no division by 3! and no identification of
prime labels which merely have the same product. -/
def repeatedTripleMass (N : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) : ℝ :=
  ∑ ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)),
    ((repeatedTripleWords N ell Q old i j E).card : ℝ)

/-- The repeated triple has empty fibre off the same physical square
exception. This establishes the summation support, rather than assuming
that the exceptional positive word has a unique receiver. -/
theorem repeatedTripleWords_empty_off_squareEvent
    {N ell : ℕ} {Q eta : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {E : ℕ → ℕ → Prop}
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j))
    (hell : ell ∉ squareEvent N old.prod E
      (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)) :
    repeatedTripleWords N ell Q old i j E = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro t ht
  exact hell (repeatedTripleWords_mem_squareEvent ht hcut)

/-- The genuine integer product bound pays all three selected labels.
The constant (1/eta)^3 comes from the actual eligible-prime fibre and is
independent of N, B and the receiver. -/
theorem repeatedTripleMass_le_squareEvent
    {N : ℕ} {Q chi eta : ℝ} {old : List ℕ}
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop)
    (hw : parentWindow N Q old chi) (heta : 0 < eta)
    (hcut : (N : ℝ)^eta ≤ cutoff Q old.prod (W1Anchor j)) :
    repeatedTripleMass N Q old i j E ≤
      (1/eta)^3 *
        ((squareEvent N old.prod E
          (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)).card : ℝ) := by
  let C := historyCarrier N old.prod E (cutoff Q old.prod (W1Anchor j))
  let S := squareEvent N old.prod E
    (cutoff Q old.prod (W1Anchor j)) ((N : ℝ)^eta)
  have hSC : S ⊆ C := by
    intro ell hell
    exact (Finset.mem_filter.mp hell).1
  have hsum : repeatedTripleMass N Q old i j E =
      ∑ ell ∈ S, ((repeatedTripleWords N ell Q old i j E).card : ℝ) := by
    unfold repeatedTripleMass
    symm
    apply Finset.sum_subset hSC
    intro ell hell hnot
    have hempty := repeatedTripleWords_empty_off_squareEvent
      (i := i) (j := j) hcut hnot
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
  rw [hsum]
  calc
    (∑ ell ∈ S, ((repeatedTripleWords N ell Q old i j E).card : ℝ)) ≤
        ∑ _ell ∈ S, (1/eta)^3 := by
      apply Finset.sum_le_sum
      intro ell hell
      have hdata := Finset.mem_filter.mp hell
      have hfibre : ((eligiblePrimes N ell Q old i j).card : ℝ) ≤
          1/eta :=
        eligiblePrimes_card_le_inv_fixed_power hw
          (Nat.sub_pos_of_lt hdata.2.1) hdata.1 heta hcut
      calc
        ((repeatedTripleWords N ell Q old i j E).card : ℝ) ≤
            ((eligiblePrimes N ell Q old i j).card : ℝ)^3 := by
          exact_mod_cast repeatedTripleWords_card_le_cube N ell Q old i j E
        _ ≤ (1/eta)^3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hfibre 3
    _ = (1/eta)^3 * (S.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- A real finite-graph parent supplies the fixed cutoff. Its old
integer word and unchanged Q are checked against that realized parent;
there is no independently supplied exponent bound in this caller. -/
theorem graph_repeatedTripleMass_le_squareEvent
    {N mesh depth : ℕ} {Q chi gamma lo hi : ℝ}
    {old : List ℕ} (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop)
    {root : P2EnhancedLowerFinitePhysicalGraph.TypedNode}
    {code : P2EnhancedLowerFinitePhysicalGraph.Program mesh depth}
    {z : P2EnhancedLowerFinitePhysicalGraph.Coordinates depth}
    (hmember : P2EnhancedLowerFinitePhysicalGraph.Member
      lo hi depth root code z)
    (hroot : gamma ≤ P2EnhancedLowerPhysicalNode.residual root.physical)
    (hgamma : 0 < gamma)
    (hw : parentWindow N Q old chi)
    (hprime : ∀ p ∈ old, p.Prime)
    (hword : P2EnhancedLowerPhysicalNode.word
      (P2EnhancedLowerFinitePhysicalGraph.realize depth root code z).physical =
        old.map (P2EnhancedLowerPrimeChildCarriers.physicalPrime N))
    (htotal :
      (P2EnhancedLowerFinitePhysicalGraph.realize depth root code z).physical.total =
        Real.log Q / Real.log (N : ℝ)) :
    repeatedTripleMass N Q old i j E ≤
      (1 / ((gamma/(101:ℝ)^depth)/5))^3 *
        ((squareEvent N old.prod E (cutoff Q old.prod (W1Anchor j))
          ((N : ℝ)^((gamma/(101:ℝ)^depth)/5))).card : ℝ) := by
  have hcoord :=
    P2EnhancedW1RepeatedLabelClassification.physical_level_eq_parent_residual
      hw hprime hword htotal
  have hcut := P2EnhancedW1RepeatedLabelClassification.graph_w1_fixed_power
    hmember hroot hgamma hw hcoord j
  have heta : 0 < (gamma/(101:ℝ)^depth)/5 := by positivity
  exact repeatedTripleMass_le_squareEvent i j E hw heta hcut

/-- Finite marked support indexed by its literal old product. An old
word and action are allowed to depend on B; they cannot change between
the exceptional triple count and its square-event payment. -/
def weightedRepeatedTripleMass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop) (old : ℕ → List ℕ)
    (i : ℕ → Fin 7) (j : ℕ → Fin 10) : ℝ :=
  ∑ B ∈ D, sigma B * repeatedTripleMass N Q (old B) (i B) (j B) E

/-- All B at once, with the exact same sigma(B) and unchanged physical
cutoffs. No disjointness of different B receiver sets is needed: the
original marked sum, including its multiplicity across B, is retained. -/
theorem weightedRepeatedTripleMass_le_squareEvent
    {N : ℕ} {Q chi eta : ℝ} (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop) (old : ℕ → List ℕ)
    (i : ℕ → Fin 7) (j : ℕ → Fin 10)
    (heta : 0 < eta)
    (hprod : ∀ B ∈ D, (old B).prod = B)
    (hw : ∀ B ∈ D, parentWindow N Q (old B) chi)
    (hsigma : ∀ B ∈ D, 0 ≤ sigma B)
    (hcut : ∀ B ∈ D,
      (N : ℝ)^eta ≤ cutoff Q B (W1Anchor (j B))) :
    weightedRepeatedTripleMass N Q D sigma E old i j ≤
      (1/eta)^3 * weightedSquareEvent N D sigma E
        (fun B => cutoff Q B (W1Anchor (j B))) ((N : ℝ)^eta) := by
  unfold weightedRepeatedTripleMass weightedSquareEvent
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hcutB : (N : ℝ)^eta ≤
      cutoff Q (old B).prod (W1Anchor (j B)) := by
    simpa only [hprod B hB] using hcut B hB
  have hlocal := repeatedTripleMass_le_squareEvent
    (i B) (j B) E (hw B hB) heta hcutB
  rw [hprod B hB] at hlocal
  have hweighted := mul_le_mul_of_nonneg_left hlocal (hsigma B hB)
  convert hweighted using 1 <;> ring

/-- Actual repeated ordered triple labels have the same-Q power-saving
payment. The threshold depends only on eta and epsilon, before every
finite marked support, actual old-word map, action map and nonnegative
weight. The positive K supplier is not an assumption of this theorem. -/
theorem weightedRepeatedTripleMass_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q chi : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
        (E : ℕ → ℕ → Prop) (old : ℕ → List ℕ)
        (i : ℕ → Fin 7) (j : ℕ → Fin 10),
      (∀ B ∈ D, (old B).prod = B) →
      (∀ B ∈ D, parentWindow N Q (old B) chi) →
      (∀ B ∈ D, 0 ≤ sigma B) →
      (∀ B ∈ D, (N : ℝ)^eta ≤ cutoff Q B (W1Anchor (j B))) →
      (∀ B ∈ D, 1 < Q / (B : ℝ) ∧ Q / (B : ℝ) ≤ (N : ℝ)) →
      weightedRepeatedTripleMass N Q D sigma E old i j ≤
        epsilon * Theta N Q D sigma := by
  let C : ℝ := (1/eta)^3
  have hC : 0 < C := by dsimp [C]; positivity
  have heps : 0 < epsilon / C := div_pos hepsilon hC
  obtain ⟨T,hT,hpay⟩ := weightedSquareEvent_theta_payment heta heps
  refine ⟨T,hT,?_⟩
  intro N hNT Q chi D sigma E old i j hprod hw hsigma hcut hR
  have hd : ∀ B ∈ D, 0 < B := by
    intro B hB
    rw [← hprod B hB]
    exact (hw B hB).2.1
  have hfirst := weightedRepeatedTripleMass_le_squareEvent
    D sigma E old i j heta hprod hw hsigma hcut
  have hsecond := hpay N hNT Q D sigma E
    (fun B => cutoff Q B (W1Anchor (j B))) hd hsigma hR
  calc
    weightedRepeatedTripleMass N Q D sigma E old i j ≤
        C * weightedSquareEvent N D sigma E
          (fun B => cutoff Q B (W1Anchor (j B))) ((N : ℝ)^eta) := hfirst
    _ ≤ C * ((epsilon/C) * Theta N Q D sigma) :=
      mul_le_mul_of_nonneg_left hsecond hC.le
    _ = epsilon * Theta N Q D sigma := by
      field_simp [ne_of_gt hC] <;> ring

end
end ImbalancedChen.P2EnhancedW1OrderedTripleGlobalPayment
