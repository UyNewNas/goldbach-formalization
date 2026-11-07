import ImbalancedChen.P5TwoFineUnrestrictedOwnerAtoms
import ImbalancedChen.P5OriginalJointPresievedCompiler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A finite same-coefficient bridge for manuscript eq:current-PP.  The original
all16 ordinary mark set (including W) is unchanged.  Its physical small/rough
carrier is pulled back by the proved unique small/rough factorization.  Each
RETAINED rough divisor is then expanded in the actual unrestricted two-fine
owner atoms at its own prime-factor rank.  The common beta pair, rough sign,
upper gate and M_res/k! interleaving scalar are all retained exactly once.

This is an identity for arbitrary signed tests F on the COMPLETE modulus.
It therefore applies simultaneously to the independent labelled count and
exact coprime reciprocal-totient mean.  It does not identify marked t with
test u.  No Mobius factor mu(q*product(u)) is introduced.

The owner family below is still indexed by the physical retained d.  The
converse from the unrestricted all-k squarefree raw family to this retained
family, regrouping owner words into sorted blocks, and the absolute repeated
rough collision bounds remain separate obligations.  No PP estimate follows
from this finite identity alone.
-/

namespace ImbalancedChen.P5Z.All16PhysicalOwnerDiscrepancy
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalJointPresievedCompiler OriginalPresievedRoughPrimeSlots
open ActualAll16UnrestrictedResidualConvolution
open TwoFineUnrestrictedOwnerAtoms All16CanonicalFineWordNoZGuard

/-- The precise physical row carriers, with the original per-mark cutoff. -/
def rowSmall (n N : ℕ) (eta : ℚ) (w : ℝ) (t : Four) : Finset ℕ :=
  actualSmallRosserSupport N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w

def rowRough (n N : ℕ) (eta : ℚ) (w : ℝ) (t : Four) : Finset ℕ :=
  fixedRoughSupport
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)

/-- All actually occurring owner words at the retained divisor's rank.
No sorted-block quotient or squarefree deletion is made in this box. -/
def rowOwners (n N : ℕ) (eta : ℚ) (w : ℝ) (t : Four) (d : ℕ) :
    Finset (List ℕ) :=
  ownerWords N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    d.primeFactors.card w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)

/-- One literal owner summand.  Its only factorial is the residual
interleaving scalar M_res/k!; the physical marked prefix stays outside. -/
def ownerRowWeight (N cap k : ℕ) (w Z L B : ℝ) (e d : ℕ)
    (J : List ℕ) : ℝ :=
  (if rawUpperGate L d then (-1 : ℝ) ^ k else 0) *
    rawBetaWeight N cap k w B e *
    ((ownerMres J : ℝ) / (k.factorial : ℝ)) *
    ownerAtomRawFibre N cap w Z J d

def physicalOwnerWeight (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (t : Four) (e d : ℕ) (J : List ℕ) : ℝ :=
  ownerRowWeight N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    d.primeFactors.card w
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B e d J

/-- The raw signed row is an actual sum of owner atoms; the gate, beta
and sign distribute over that finite sum, rather than being new premises. -/
theorem raw_row_eq_sum_owner_weights {N cap k e d : ℕ} {w Z L B : ℝ}
    (hN : 1 < N) (hZN : Z ≤ (N : ℝ)) :
    rawResidualRowWeight N cap k w Z L B e d =
      ∑ J ∈ ownerWords N cap k w Z,
        ownerRowWeight N cap k w Z L B e d J := by
  rw [raw_signed_row_by_owner hN hZN]
  by_cases hg : rawUpperGate L d
  · simp only [ownerRowWeight, if_pos hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J hJ
    ring
  · simp [ownerRowWeight, hg]

/-- Each actual physical row, including zero rows and the W policy,
has its own proved owner expansion.  Z<=N comes from the physical compiler;
there is no caller-supplied coefficient identity or extra cutoff guard. -/
theorem physical_row_eq_owner_weights {n N e d : ℕ} {eta : ℚ}
    {w B : ℝ} {E : ℕ × ℕ → Prop}
    (hN : 1 < N) (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (he : e ∈ rowSmall n N eta w t)
    (hd : d ∈ rowRough n N eta w t) :
    rowCoefficient n N eta w B t (e * d) =
      ∑ J ∈ rowOwners n N eta w t d,
        physicalOwnerWeight n N eta w B t e d J := by
  rw [← physical_joint_row_raw_value hN heta ht he hd]
  exact raw_row_eq_sum_owner_weights hN
    (all16_physical_Z_le_N (by omega) heta ht)

/-- Pull back the multiplicity-free physical residual carrier to the
unique original small/rough pair.  This is independent of the arithmetic
test and does not assume any distribution bound. -/
theorem physical_row_pullback (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (t : Four) (F : ℕ → ℝ) :
    (∑ r ∈ rowSupport n N eta w t,
      rowCoefficient n N eta w B t r * F (fullPrefix t * r)) =
      ∑ e ∈ rowSmall n N eta w t,
        ∑ d ∈ rowRough n N eta w t,
          rowCoefficient n N eta w B t (e * d) * F (fullPrefix t * (e * d)) := by
  have hpull := sum_smallRoughModuli
    (small := rowSmall n N eta w t) (rough := rowRough n N eta w t)
    (w := w)
    (fun e he => actualSmallRosserSupport_smallPrimeSupportedAt N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w he)
    (fun d hd => fixedRoughSupport_roughPrimeSupportedAt
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd)
    (fun r => rowCoefficient n N eta w B t r * F (fullPrefix t * r))
  simpa only [rowSupport, actualSmallRoughModuli, rowSmall, rowRough,
    smallRoughPairs, Finset.sum_product] using hpull

/-- The full unchanged all16 physical mark family, expanded by its own
small/rough factors and owner words.  The independent test F sees only q. -/
def physicalOwnerLinear (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
    ∑ e ∈ rowSmall n N eta w t,
      ∑ d ∈ rowRough n N eta w t,
        ∑ J ∈ rowOwners n N eta w t d,
          physicalOwnerWeight n N eta w B t e d J * F (fullPrefix t * (e * d))

/-- Main exact identity: the actual jointPresievedSigma used for the
physical count is also the coefficient of EVERY signed test in this owner
family.  No absolute values, count/mean estimates, or coefficient-equality
hypotheses enter the proof. -/
theorem joint_linear_eq_owner_linear {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ q ∈ jointSupport n N eta w E,
      jointPresievedSigma n N eta w B E q * F q) =
        physicalOwnerLinear n N eta w B E F := by
  rw [← joint_exact_pushforward n N eta w B E F]
  unfold physicalOwnerLinear
  apply Finset.sum_congr rfl
  intro t ht
  rw [physical_row_pullback]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro d hd
  rw [physical_row_eq_owner_weights hN heta ht he hd, Finset.sum_mul]

/-- Pointwise coefficient equality, not just agreement for one selected
arithmetic test.  The indicator is used only to read off a finite fibre. -/
def physicalOwnerSigma (n N : ℕ) (eta : ℚ) (w B : ℝ)
    (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  physicalOwnerLinear n N eta w B E (fun x => if x = q then 1 else 0)

theorem physical_owner_sigma_eq_joint {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta)
    (E : ℕ × ℕ → Prop) (q : ℕ) :
    physicalOwnerSigma n N eta w B E q =
      jointPresievedSigma n N eta w B E q := by
  unfold physicalOwnerSigma
  rw [← joint_linear_eq_owner_linear hN heta]
  by_cases hq : q ∈ jointSupport n N eta w E
  · simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single q]
    · simp
    · intro b hb hne
      simp [hne]
    · intro hn
      exact (hn hq).elim
  · rw [jointSigma_zero_off_support n N eta w B E hq]
    apply Finset.sum_eq_zero
    intro x hx
    have hne : x ≠ q := by
      intro heq
      exact hq (heq ▸ hx)
    simp [hne]

/-- Exact original count and exact coprime mean are expanded using ONE
physical coefficient and ONE owner family.  The test word u is independent
of the four-prime mark t and residual owner word J. -/
theorem joint_signed_PP_owner_expansion {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (u P T : ℕ) (W : (Fin u → Fin (P + 1)) → ℝ) :
    (∑ q ∈ jointSupport n N eta w E,
      jointPresievedSigma n N eta w B E q *
        (labelledCountTest u P T W q - labelledExactCoprimeMeanTest u P W q)) =
      ∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
        ∑ e ∈ rowSmall n N eta w t,
          ∑ d ∈ rowRough n N eta w t,
            ∑ J ∈ rowOwners n N eta w t d,
              physicalOwnerWeight n N eta w B t e d J *
                (labelledCountTest u P T W (fullPrefix t * (e * d)) -
                  labelledExactCoprimeMeanTest u P W (fullPrefix t * (e * d))) := by
  exact joint_linear_eq_owner_linear hN heta E _

end
end ImbalancedChen.P5Z.All16PhysicalOwnerDiscrepancy
