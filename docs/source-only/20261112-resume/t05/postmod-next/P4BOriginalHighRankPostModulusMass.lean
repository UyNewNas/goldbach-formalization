import ImbalancedChen.P4BOriginalHighRankLocalLevel
import ImbalancedChen.P4BArbitraryWidthUpperPostModulusTail

/-! Positive complete-modulus moments for the actual rectangular coefficient
on the original two-group HB row. The zero coefficient and q=1 retain their
native conventions, and the equality of the complete product to N has its
own divisor payment. -/
namespace ImbalancedChen.P4BOriginalHighRankPostModulusMass
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open P5Z.ActualHBPostModulusLogCutoff
open P5Z.ActualCompleteModulusFourierTail
open P5Z.CompleteProductTailDivisorBudgets
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle)
open P5Z.ActualRoughHeathBrownWords (Role)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale scaleFactor)
open P4BUpperPairOrderedRowGeometry (pairOwner integerProfile)
open P4BOuterRampRoughness (baseline)

def active (S : Finset ℕ) (c : ℕ→ℝ) := S.filter (fun d => c d≠0)

theorem discrepancy_active {ι : Type*} (I : Finset ι) (S : Finset ℕ) (c : ℕ→ℝ)
    (prod : ι→ℕ) (N : ℕ) (w : ι→ℂ) :
    MellinInsertion20261028.exactDiscrepancy I S (fun d => (c d:ℂ)) prod N w=
    MellinInsertion20261028.exactDiscrepancy I (active S c) (fun d => (c d:ℂ)) prod N w := by
  unfold MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  rw [active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : c d=0 <;> simp [hz]

theorem block_rect {w : ℕ} {bs : Fin w→Block} {z : Fin w→ℕ} (hz : z∈rectangle bs) :
    z∈P4BArbitraryWidthUpperBlockGeometry.rectangle bs := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have ho := (mem_rectangle bs z).mp hz j
  cases hbj : bs j <;> simpa [P4BArbitraryWidthUpperBlockGeometry.blockIntegers,
    P5Z.HBRightClosedDyadicRoles.Owns,hbj] using ho

theorem exponent_le {w : ℕ} (hw : w≤12) : paymentExponent w 0≤paymentExponent 12 0 := by
  have ha : 2^(2*w)≤(2:ℕ)^(2*12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : 2^w≤(2:ℕ)^12 := Nat.pow_le_pow_right (by norm_num) hw
  unfold paymentExponent
  omega

/-- One constant for every subset of the complete physical modulus set and
every occupied original subrow, including arbitrary complementary fibres. -/
theorem exists_complete_mass :
    ∃ C : ℝ,0≤C ∧ ∀ {u v N : ℕ} {b kap s kap0 : ℝ},0<N → 0<b → 0<kap →
    0<s → 2*s≤baseline b kap-19/96 → u+v≤12 → ∀ (cj ck : ℕ) (bs : Fin (u+v)→Block)
      (I : Finset (Fin (u+v)→ℕ)),I⊆rectangle bs →
    (∃ y∈I,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) →
    ∀ (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
      (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),
    S⊆Q omega N →
    let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
    (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
    fullTailMass I (hbSlots Z ys rs) completeProduct (active S c) (fun d => (c d:ℂ)) N 0 1≤
      C*(N:ℝ)*logScale (countingScale N)^(paymentExponent 12 0) := by
  obtain ⟨C,hC,hcollision⟩ := exists_uniform_exact_product_payment 2 modulusExponent
    (by norm_num [modulusExponent])
  refine ⟨massConstant 0*scaleFactor+C,by dsimp [massConstant,scaleFactor]; positivity,?_⟩
  intro u v N b kap s kap0 hN hb hk hs hg hm cj ck bs I hI hnz Z ys rs m r n e q a omega k ell S hS
  dsimp only
  intro hsup
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let D := Nat.floor ((N:ℝ)^modulusExponent)
  let X := countingScale N
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hp : 1≤(N:ℝ)^modulusExponent := Real.one_le_rpow hn (by norm_num [modulusExponent])
  have hd1 : 1≤D := Nat.le_floor (by simpa only [Nat.cast_one] using hp)
  have hD : (D:ℝ)≤(N:ℝ)^modulusExponent := Nat.floor_le (by linarith)
  have hDN : (D:ℝ)≤N := hD.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hn (show modulusExponent≤1 by norm_num [modulusExponent]))
  have hX := countingScale_one_le hN
  have hNX := target_le_countingScale N
  have hsq (d : ℕ) (hd : d∈effectiveModuli (active S c)) : Squarefree d :=
    P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ (hS (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).1)
  have hclass : effectiveModuli (active S c)⊆Finset.Icc 1 D := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hsq d hd).ne_zero,
      Nat.le_floor (hsup d (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).2).le⟩
  obtain ⟨y,hy,hyz⟩ := hnz
  have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have hprod (z : Fin (u+v)→ℕ) (hz : z∈I) :
      (∀ j,0<z j) ∧ (completeProduct z:ℝ)≤6*X := by
    obtain ⟨hpos,hp⟩ := P4BArbitraryWidthUpperBlockGeometry.rectangle_counting_scale hb hk
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs hG (pairOwner u v) bs
      (![P5Z.ExactOriginalSmoothDyadicPartition.R cj,P5Z.ExactOriginalSmoothDyadicPartition.R ck]) kap0
      hm ⟨y,block_rect (hI hy),hyz⟩ (block_rect (hI hz))
    exact ⟨hpos,by change (completeProduct z:ℝ)≤6*countingScale N; linarith⟩
  have H := actual_hb_mass_polylog I Z ys rs hX N D 0 hN hNX hd1 (by linarith) hprod
    (active S c) (fun d => (c d:ℂ)) hclass hsq 1 (by norm_num)
    (fun d _ => by simpa only [Complex.norm_real,Real.norm_eq_abs,pow_zero,mul_one] using
      P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d)
  have he := hcollision (u+v) N D (by omega) hN hD
  have hlead : massConstant 0*X+(D:ℝ)*tau N^(u+v)≤(massConstant 0*scaleFactor+C)*N := by
    dsimp only [X,countingScale]
    linarith only [he]
  have hL := logScale_one_le hX
  apply H.trans
  rw [one_mul]
  exact mul_le_mul hlead (pow_le_pow_right₀ hL (exponent_le hm)) (pow_nonneg (by linarith) _)
    (by dsimp [massConstant,scaleFactor]; positivity)

end
end ImbalancedChen.P4BOriginalHighRankPostModulusMass
