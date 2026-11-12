import ImbalancedChen.P4BOriginalHighRankPostModulusMass

/-! Retained Fourier cube for each genuine mother or fixed complementary
fibre. Its logarithmic exponent is fixed before the targets and all
frequencies. The complete signed modulus sum is formed before taking the tail. -/
namespace ImbalancedChen.P4BOriginalHighRankPostModulusRow
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open P5Z.ActualHBPostModulusLogCutoff
open P5Z.ActualCompleteModulusFourierTail (discrepancy_tail_le effectiveModuli)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.ActualEuclideanPhysicalFourier
open P5Z.AllRankCauchyCubeTail
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le exists_actual_upper_cube_tail)
open P4BUpperPairOrderedRowGeometry (integerProfile pairOwner rowChart rowChart_integer blockScales)
open P4BUpperPairOrderedRowModes (amplitude amplitude_mode_integrable)
open P4BOriginalHighRankPostModulusMass (active discrepancy_active exists_complete_mass)
open P4BOriginalHighRankScheduledCount (resolution outerWidth)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)

def H (N A : ℕ) := selectedCutoff (countingScale N) (A+15) 24 (paymentExponent 12 0)

def bandwidthOrder (A : ℕ) := A+15+24+paymentExponent 12 0+3

/-- The individual twist bound in the complete local scale.  Its exponent
is fixed before N, x, rho and every retained mode. -/
theorem eventually_local_twists (A : ℕ) {kappa : ℝ} (hk : kappa≤1) :
    ∀ᶠ N : ℕ in atTop,∀ x : ℝ,1<x → (N:ℝ)≤x^(1+kappa) →
    ∀ (d : ℕ) (xi : Fin d→ℝ),xi∈(outsideCube d (H N A))ᶜ →
    ∀ i,|xi i|≤(Real.log x)^(bandwidthOrder A+1) := by
  have tend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [P4BOriginalHighRankScheduledCount.eventually_width 1 (by norm_num),
    tend.eventually_ge_atTop (2*(4:ℝ)^bandwidthOrder A)] with N hN hbig
  intro x hx hNx d xi hxi i
  have hNx' := Real.log_le_log (show (0:ℝ)<N by exact_mod_cast (show 0<N by linarith only [hN.1])) hNx
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hNx'
  have hL := hN.2.2.2.2
  have hx0 := (Real.log_pos hx).le
  have hNt : Real.log (N:ℝ)≤2*Real.log x := hNx'.trans
    (mul_le_mul_of_nonneg_right (by linarith) hx0)
  have hlim : (4:ℝ)^bandwidthOrder A≤Real.log x := by linarith
  have hs : 1≤logScale (countingScale N) := logScale_one_le (countingScale_one_le (by linarith only [hN.1]))
  have hband : |xi i|≤H N A := le_of_not_gt (fun h => hxi ⟨i,h⟩)
  calc
    _≤H N A := hband
    _≤(4*Real.log x)^bandwidthOrder A := pow_le_pow_left₀ (by linarith) (by linarith) _
    _≤(Real.log x)^(bandwidthOrder A+1) := by
      rw [mul_pow,pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlim (pow_nonneg hx0 (bandwidthOrder A))

variable {u v : ℕ}

def original (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (I : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) :=
  MellinInsertion20261028.exactDiscrepancy I S (fun d => (c d:ℂ)) completeProduct N
    (fun y => hbSlots Z ys rs y*(integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y:ℂ))

def truncated (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block)
    (I : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) (B : ℝ) :=
  MellinInsertion20261028.exactDiscrepancy I S (fun d => (c d:ℂ)) completeProduct N
    (fun y => hbSlots Z ys rs y*truncatedPhysical (u+v) (rowChart b kap s N kap0 cj ck bs) B
      (WithLp.toLp 2 (logOccurrence (blockScales bs) y)))

def retained (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block)
    (I : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) (A : ℕ) :=
  if ∃ y∈I,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0
  then truncated b kap s N kap0 cj ck bs I Z ys rs S c (H N A) else 0

theorem original_dead (b kap s : ℝ) (N : ℕ) (kap0 : ℝ) (cj ck : ℕ)
    (I : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (S : Finset ℕ) (c : ℕ→ℝ) (hz : ¬∃ y∈I,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) :
    original b kap s N kap0 cj ck I Z ys rs S c=0 := by
  unfold original MellinInsertion20261028.exactDiscrepancy MellinInsertion20261028.functional
  apply Finset.sum_eq_zero
  intro y hy
  have h : integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y=0 := by
    by_contra h; exact hz ⟨y,hy,h⟩
  simp only [h,Complex.ofReal_zero,mul_zero,zero_mul]

/-- Literal finite-frequency integral on the same full modulus/coprime row. -/
theorem truncated_eq_band {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N : ℕ) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block) (I : Finset (Fin (u+v)→ℕ))
    (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) (S : Finset ℕ) (c : ℕ→ℝ) (B : ℝ) :
    truncated b kap s N kap0 cj ck bs I Z ys rs S c B=
      ∫ xi in (outsideCube (u+v) B)ᶜ,amplitude b kap s N kap0 cj ck bs xi*
        MellinInsertion20261028.exactDiscrepancy I S (fun d => (c d:ℂ)) completeProduct N
          (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi) := by
  let kernel := fun y : Fin (u+v)→ℕ => ∑ d∈S,(c d:ℂ)*MellinInsertion20261028.residueKernel d N (completeProduct y)
  let A := amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs
  have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have hint (y : Fin (u+v)→ℕ) : Integrable (fun xi =>
      A xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) := by
    have hi := (amplitude_mode_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
      hs hG N kap0 cj ck bs y).const_mul (hbSlots Z ys rs y)
    exact hi.congr (Eventually.of_forall (fun xi => by dsimp [A]; ring))
  have rep (y : Fin (u+v)→ℕ) :
      hbSlots Z ys rs y*truncatedPhysical (u+v) (rowChart b kap s N kap0 cj ck bs) B
        (WithLp.toLp 2 (logOccurrence (blockScales bs) y))=
      ∫ xi in (outsideCube (u+v) B)ᶜ,A xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi) := by
    unfold truncatedPhysical
    rw [←integral_smul,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun xi => by rw [physicalPhase_occurrenceMode]; simp only [A,amplitude,smul_eq_mul]; ring)
  change MellinInsertion20261028.functional I kernel _=_
  simp_rw [rep]
  rw [MellinInsertion20261028.functional_integral I kernel _ (fun y _ => (hint y).integrableOn)]
  simp_rw [MellinInsertion20261028.functional_mul]
  rfl

/-- Per actual integer subrow with its complete Q-arithmetic. Fifteen powers
remain in reserve for the original fourteen label/order powers and one
genuine complementary fibre power. Width costs twenty-four powers. -/
theorem exists_row_payment :
    ∃ C : ℝ,0≤C ∧ ∀ {N u v : ℕ} {b kap : ℝ},0<N → 0<b → b≤1 → 0<kap →
    2*outerWidth N≤baseline b kap-19/96 →
    (resolution N+1:ℝ)≤logScale (countingScale N) → u+v≤12 →
    ∀ (kap0 : ℝ) (A cj ck : ℕ) (bs : Fin (u+v)→Block) (I : Finset (Fin (u+v)→ℕ)),I⊆rectangle bs →
    ∀ (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
      (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),
    S⊆Q omega N → let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
    (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
    ‖original (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck I Z ys rs S c-
      retained b kap (outerWidth N) N kap0 cj ck bs I Z ys rs S c A‖≤
      C*(N:ℝ)/logScale (countingScale N)^(A+15+3) := by
  obtain ⟨Cd,hCd,hFour⟩ := exists_actual_upper_cube_tail
  obtain ⟨Cm,hCm,hMass⟩ := exists_complete_mass
  refine ⟨12*Cd*Cm,by positivity,?_⟩
  intro N u v b kap hN hb hb1 hk hg hres hm kap0 A cj ck bs I hI Z ys rs m r n e q a omega k ell S hS
  dsimp only
  intro hsup
  let s := outerWidth N
  let X := countingScale N
  let L := logScale X
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let B := H N A
  have hX := countingScale_one_le hN
  have hL := logScale_one_le hX
  have hL0 : 0≤L := zero_le_one.trans hL
  have hB : 0<B := zero_lt_one.trans_le (selectedCutoff_one_le hX _ _ _)
  have hs : 0<s := one_div_pos.mpr (by positivity)
  by_cases hLive : ∃ y∈I,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0
  · have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
    have hmass := hMass hN hb hk hs hg hm cj ck bs I hI hLive Z ys rs m r n e q a omega k ell S hS hsup
    have ht := hFour b kap 1 (19/96) s hb hb1 hk (by norm_num) (by norm_num) hs hG N (u+v)
      (pairOwner u v) bs (![R cj,R ck]) kap0 B hN (by intro i; fin_cases i <;> exact R_pos _) hm hB
    let f := fun y => (integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y:ℂ)
    let g := fun y => truncatedPhysical (u+v) (rowChart b kap s N kap0 cj ck bs) B
      (WithLp.toLp 2 (logOccurrence (blockScales bs) y))
    have hwidth : Cd/s^24≤Cd*L^24 := by
      dsimp [s,outerWidth]
      rw [one_div,inv_pow,div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hres _) hCd
    have hdim : (u+v:ℕ)≤12 := hm
    have hdimR : ((u+v:ℕ):ℝ)≤12 := by exact_mod_cast hdim
    have herr (y : Fin (u+v)→ℕ) (hy : y∈I) : ‖f y-g y‖≤(12*Cd*L^24)/B := by
      dsimp only [f,g]
      rw [←rowChart_integer b kap s N kap0 cj ck bs (hI hy)]
      apply (ht _).trans
      apply div_le_div_of_nonneg_right _ hB.le
      calc
        _=((u+v:ℕ):ℝ)*(Cd/s^24) := by ring
        _≤12*(Cd*L^24) := mul_le_mul hdimR hwidth (div_nonneg hCd (pow_nonneg hs.le _)) (by norm_num)
        _=_ := by ring
    have hnorm (d : ℕ) (_ : d∈effectiveModuli (active S c)) :
        ‖(c d:ℂ)‖≤(1:ℝ)*P5Z.ActualCompleteModulusFourierTail.tau d^0 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,pow_zero,mul_one] using
        P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d
    have hrow := discrepancy_tail_le I (hbSlots Z ys rs) completeProduct (active S c)
      (fun d => (c d:ℂ)) N 0 1 (12*Cd*L^24/B) (by norm_num) (by positivity) hnorm f g herr
    unfold retained
    rw [if_pos hLive]
    unfold original truncated
    rw [discrepancy_active I S c,discrepancy_active I S c]
    apply hrow.trans
    calc
      _≤(12*Cd*L^24/B)*(Cm*N*L^paymentExponent 12 0) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _=(Cm*N)*((12*Cd*L^24/B)*L^paymentExponent 12 0) := by ring
      _=_ := by
        rw [show (12*Cd*L^24/B)*L^paymentExponent 12 0=(12*Cd)/L^(A+15+3) from
          selected_cutoff_payment hX (A+15) 24 (paymentExponent 12 0) (12*Cd)]
        ring
  · rw [retained,if_neg hLive,original_dead _ _ _ _ _ _ _ _ _ _ _ _ _ hLive,sub_zero,norm_zero]
    positivity

end
end ImbalancedChen.P4BOriginalHighRankPostModulusRow
