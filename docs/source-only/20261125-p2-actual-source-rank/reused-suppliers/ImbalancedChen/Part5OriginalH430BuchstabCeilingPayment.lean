import ImbalancedChen.Part5OriginalH430BuchstabCeilingDictionary
import ImbalancedChen.P2OriginalPositiveSameQMassLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The retained finite ceiling fibre is paid in the SAME arithmetic Theta,
not in native Lebesgue measure. At most one prime occurs. On the actual
Buchstab local domain, its residual ratio is <= 1/2 and its size is at
least N^(physicalLevel/6). For any 4 <= A below that floor, its total
child Theta is <= (4/A)*parent Theta. No division by parent Theta occurs.

This is the ceiling correction, not the interior prime-to-integral limit,
not the full Member estimate, and not an h34 or 441-level realization.
-/

namespace ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment

noncomputable section
open Set Classical
open scoped BigOperators
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430BuchstabCeilingDictionary
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift

/-- No repeated-prefix multiplier is replaced by the fresh multiplier. -/
theorem localPrimeFactor_le_two_div {d q : ℕ} (hq : (4 : ℝ) ≤ q) :
    localPrimeFactor d q ≤ 2/(q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by linarith
  unfold localPrimeFactor
  split_ifs
  · exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hq0.le
  · apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ)-2) hq0).mpr
    linarith

theorem relativePrime_le_half {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} {q : Fin (N+1)}
    (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hq : q ∈ closedChildren up N old p) : relativePrime Q old q.val ≤ 1/2 := by
  have hsquare := (local_geometry (mem_closedChildren.mp hq).2).2.2.1
  rw [hL] at hsquare
  have heq := relativePrime_physical (p := q.val) hw
  have hpos := (parentWindow_logs hw).2.2
  apply (mul_le_mul_left hpos).mp
  nlinarith only [hsquare, heq]

theorem childTheta_nonneg {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode} {q : Fin (N+1)}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hq : q ∈ closedChildren up N old p) :
    0 ≤ thetaAtom N Q (parentProduct old*q.val) := by
  have hprime := (mem_closedChildren.mp hq).1.1
  have hd : 0 < parentProduct old*q.val := mul_pos hw.2.1 hprime.pos
  have hdR : (0 : ℝ) < (parentProduct old*q.val : ℕ) := by exact_mod_cast hd
  apply thetaAtom_nonneg hN hd
  apply (lt_div_iff₀ hdR).mpr
  simpa only [one_mul] using local_product_lt hw hL hq

/-- An actual child, including a ceiling child, with the exact singular factor. -/
theorem childTheta_le {up : Bool} {N : ℕ} {Q chi A : ℝ}
    {old : List ℕ} {p : PhysicalNode} {q : Fin (N+1)}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hq : q ∈ closedChildren up N old p) (hA : 4 ≤ A) (hAq : A ≤ (q.val : ℝ)) :
    thetaAtom N Q (parentProduct old*q.val) ≤
      (4/A)*thetaAtom N Q (parentProduct old) := by
  have hprime := (mem_closedChildren.mp hq).1
  have hq4 : (4 : ℝ) ≤ q.val := hA.trans hAq
  have hq0 : (0 : ℝ) < q.val := by linarith
  have hA0 : 0 < A := by linarith
  have hq2 : 2 < q.val := by exact_mod_cast (show (2 : ℝ) < q.val by linarith)
  have hpN : q.val.Coprime N := (Nat.coprime_mul_iff_right.mp hprime.2).1
  have hR := (parentWindow_logs hw).2.1
  have htheta : 0 ≤ thetaAtom N Q (parentProduct old) := thetaAtom_nonneg hN hw.2.1 hR
  have hr := relativePrime_le_half hw hL hq
  have hden : 0 < 1-relativePrime Q old q.val := by linarith
  have hratio : localPrimeFactor (parentProduct old) q.val /
      (1-relativePrime Q old q.val) ≤ 4/(q.val : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    calc
      localPrimeFactor (parentProduct old) q.val ≤ 2/(q.val : ℝ) :=
        localPrimeFactor_le_two_div hq4
      _ = (4/(q.val : ℝ))*(1/2) := by ring
      _ ≤ (4/(q.val : ℝ))*(1-relativePrime Q old q.val) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (by norm_num) hq0.le)
  have hdiv : 4/(q.val : ℝ) ≤ 4/A := by
    apply (div_le_div_iff₀ hq0 hA0).mpr
    linarith
  rw [thetaAtom_single (by omega) hw.2.1 hprime.1 hq2 hpN hR]
  change thetaAtom N Q (parentProduct old) *
    (localPrimeFactor (parentProduct old) q.val/(1-relativePrime Q old q.val)) ≤ _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hratio.trans hdiv) htheta

/-- Literal sum of the finite exceptional arithmetic weights. -/
def ceilingMass (up : Bool) (N : ℕ) (Q : ℝ) (old : List ℕ) (p : PhysicalNode) : ℝ :=
  ∑ q ∈ ceilingChildren up N old p, thetaAtom N Q (parentProduct old*q.val)

theorem ceilingMass_nonneg {up : Bool} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) : 0 ≤ ceilingMass up N Q old p := by
  apply Finset.sum_nonneg
  intro q hq
  exact childTheta_nonneg hN hw hL (mem_ceilingChildren.mp hq).1

/-- Uniform in the parent label, ceiling and both Buchstab directions. -/
theorem ceilingMass_le {up : Bool} {N : ℕ} {Q chi A : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old)
    (hA : 4 ≤ A) (hfloor : A ≤ primeFloor N Q old) :
    ceilingMass up N Q old p ≤ (4/A)*thetaAtom N Q (parentProduct old) := by
  have htheta : 0 ≤ thetaAtom N Q (parentProduct old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hc : (0 : ℝ) ≤ (4/A)*thetaAtom N Q (parentProduct old) :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) htheta
  have hcard : ((ceilingChildren up N old p).card : ℝ) ≤ 1 := by
    exact_mod_cast ceilingChildren_card_le_one (up := up) (old := old) (p := p) hw.1
  calc
    ceilingMass up N Q old p ≤
        ∑ _q ∈ ceilingChildren up N old p, (4/A)*thetaAtom N Q (parentProduct old) := by
      apply Finset.sum_le_sum
      intro q hq
      have hclosed := (mem_ceilingChildren.mp hq).1
      exact childTheta_le hN hw hL hclosed hA (hfloor.trans (primeFloor_le hw hL hclosed))
    _ = ((ceilingChildren up N old p).card : ℝ) *
        ((4/A)*thetaAtom N Q (parentProduct old)) := by simp
    _ ≤ 1*((4/A)*thetaAtom N Q (parentProduct old)) := mul_le_mul_of_nonneg_right hcard hc
    _ = _ := one_mul _

/-- A common threshold for the ACTUAL residual floor, chosen before Q,
old words, ceilings, directions or labelled families. The positive
residual lower bound is still a geometric obligation of the full graph. -/
theorem exists_uniform_primeFloor {Lmin A : ℝ}
    (hmin : 0 < Lmin) (hA : 4 ≤ A) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 4 ≤ N ∧
      ∀ Q : ℝ, ∀ old : List ℕ,
        Lmin ≤ physicalLevel N Q old → A ≤ primeFloor N Q old := by
  obtain ⟨T, hT⟩ := exists_nat_ge (A ^ (6/Lmin))
  refine ⟨max 4 T, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := by omega
  refine ⟨hN4, ?_⟩
  intro Q old hL
  have hA0 : 0 ≤ A := by linarith
  have hbase : A ^ (6/Lmin) ≤ (N : ℝ) :=
    hT.trans (by exact_mod_cast (show T ≤ N by omega))
  have hcancel : (A ^ (6/Lmin)) ^ (Lmin/6) = A := by
    rw [← Real.rpow_mul hA0]
    have he : (6/Lmin)*(Lmin/6) = (1 : ℝ) := by
      field_simp [hmin.ne'] <;> ring
    rw [he, Real.rpow_one]
  calc
    A = (A ^ (6/Lmin)) ^ (Lmin/6) := hcancel.symm
    _ ≤ (N : ℝ) ^ (Lmin/6) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hbase (by positivity)
    _ ≤ primeFloor N Q old := by
      apply (Real.rpow_le_rpow_left_iff (by exact_mod_cast (show 1 < N by omega))).mpr
      exact div_le_div_of_nonneg_right hL (by norm_num)

/-- The finite signed error is paid before any cancellation in its test. -/
theorem signed_ceiling_error_le {up : Bool} {N : ℕ} {Q chi A B : ℝ}
    {old : List ℕ} {p : PhysicalNode}
    (hN : 4 ≤ N) (hw : parentWindow N Q old chi)
    (hL : residual p = physicalLevel N Q old) (hC : p.ceiling = chi)
    (hs : 1 ≤ p.argument) (hA : 4 ≤ A) (hfloor : A ≤ primeFloor N Q old)
    (hB : 0 ≤ B) (F : Fin (N+1) → ℝ)
    (hF : ∀ q ∈ ceilingChildren up N old p, |F q| ≤ B) :
    |(∑ q ∈ closedChildren up N old p, thetaAtom N Q (parentProduct old*q.val)*F q) -
      (∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        thetaAtom N Q (parentProduct old*q.val)*F q)| ≤
      B*((4/A)*thetaAtom N Q (parentProduct old)) := by
  have he := closedChildren_sum hw hL hC hs
    (fun q => thetaAtom N Q (parentProduct old*q.val)*F q)
  have heq : (∑ q ∈ closedChildren up N old p, thetaAtom N Q (parentProduct old*q.val)*F q) -
      (∑ q ∈ singleChildren (.buchstab up p.argument) N Q old chi,
        thetaAtom N Q (parentProduct old*q.val)*F q) =
      ∑ q ∈ ceilingChildren up N old p, thetaAtom N Q (parentProduct old*q.val)*F q := by
    linarith only [he]
  rw [heq]
  calc
    _ ≤ ∑ q ∈ ceilingChildren up N old p,
        |thetaAtom N Q (parentProduct old*q.val)*F q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ ceilingChildren up N old p,
        thetaAtom N Q (parentProduct old*q.val)*B := by
      apply Finset.sum_le_sum
      intro q hq
      have hnonneg := childTheta_nonneg hN hw hL (mem_ceilingChildren.mp hq).1
      rw [abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (hF q hq) hnonneg
    _ = B*ceilingMass up N Q old p := by
      unfold ceilingMass
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ceilingMass_le hN hw hL hA hfloor) hB

end
end ImbalancedChen.Part5OriginalH430BuchstabCeilingPayment
