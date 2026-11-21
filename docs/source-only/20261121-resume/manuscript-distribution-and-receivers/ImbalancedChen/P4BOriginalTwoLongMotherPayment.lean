import ImbalancedChen.P4BOriginalTwoLongMotherBank
import ImbalancedChen.P5zElevenErrorTransport

/-! SOURCE ONLY / UNCOMPILED. Payment of the actual two-long mother
subbank on the already chosen outer schedule. The true amplitude/HB
budget is log^38, independent of inner endpoint smoothing. Choose the
outer width and band first, local accuracy A+40 next, inner smoothing
through the local theorem next, and the common N threshold last. -/
namespace ImbalancedChen.P4BOriginalTwoLongMotherPayment
noncomputable section
open Classical Filter
open P4BOriginalTwoLongMotherBank
open P4BOriginalNativeTargetPayment (localConstant localConstant_nonneg)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width exists_scheduled_mass)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale)
open P5Z.CompleteProductTailDivisorBudgets (logScale)
open P4BOuterRampRoughness (baseline)

theorem fixed_scalar_log_payment (C : ℝ) (hC : 0≤C) (A N : ℕ)
    (hlog : 1≤Real.log (N:ℝ)) (hlarge : C≤Real.log (N:ℝ)) :
    C*N/(Real.log (N:ℝ))^(A+2)≤(N:ℝ)/(Real.log (N:ℝ))^(A+1) := by
  have hl0 : 0<Real.log (N:ℝ) := zero_lt_one.trans_le hlog
  calc
    _=(C/Real.log (N:ℝ))*((N:ℝ)/(Real.log (N:ℝ))^(A+1)) := by
      rw [show A+2=(A+1)+1 by omega,pow_succ]; field_simp [hl0.ne']; ring
    _≤1*((N:ℝ)/(Real.log (N:ℝ))^(A+1)) := mul_le_mul_of_nonneg_right
      ((div_le_one hl0).mpr hlarge) (by positivity)
    _=_ := one_mul _

/-- The actual no-medium two-mother HB subbank, with both original group
logs, all ordered labels/scalars, normalized Fourier amplitudes, complete
signed modulus sum and exact coprime mean. Other source branches and any
later H_N/compiler reconstruction are outside this theorem. -/
theorem eventually_actual_twoLong_mother_paid (K A : ℕ)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgate : 19/96<baseline b kap) :
    ∀ᶠ N : ℕ in atTop,∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      ‖originalBank zeta b kap (outerWidth N) N K kap0 S
        (coefficient m r n e q a omega k N ((N:ℝ)^ell))‖≤(N:ℝ)/(Real.log (N:ℝ))^A := by
  let P := A+40
  obtain ⟨CM,hCM,hMass⟩ := exists_scheduled_mass
  obtain ⟨CT,hCT,hTail⟩ := exists_branch_bank_tail
  have hLocal := eventually_retained_bank_le K A P hz hz1 hk hkz ht ht1
  have tend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hLocal,hMass hb hb1 hkap hgate,hTail hb hb1 hkap hgate,
    eventually_width _ (half_pos (sub_pos.mpr hgate)),
    tend.eventually_ge_atTop (max 2 (max (CM*localConstant P) CT))]
    with N hRows hM hT hw hlarge
  obtain ⟨hN,hs,hs',hres,hLtop⟩ := hw
  have hN0 : 0<N := by omega
  have hNpos : (0:ℝ)<N := by exact_mod_cast hN0
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith
  have hl2 : 2≤Real.log (N:ℝ) := (le_max_left _ _).trans hlarge
  have hl1 : 1≤Real.log (N:ℝ) := by linarith
  have hl0 : 0<Real.log (N:ℝ) := by linarith
  have hcM : CM*localConstant P≤Real.log (N:ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hcT : CT≤Real.log (N:ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hL : Real.log (N:ℝ)≤logScale (countingScale N) := by
    have hNX := target_le_countingScale N
    have HH := Real.log_le_log hNpos (show (N:ℝ)≤7*countingScale N by linarith)
    unfold logScale
    linarith
  intro m r n e q a omega k ell hRange S hS
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let full := originalBank zeta b kap (outerWidth N) N K kap0 S c
  let band := retainedBank zeta b kap (outerWidth N) N K A kap0 S c
  have hE : 0≤localConstant P*N/(Real.log (N:ℝ))^P := by
    have h := localConstant_nonneg P
    positivity
  have hb0 := hRows hb hkap hs hg m r n e q a omega k ell hRange S hS
  have hb1' : ‖band‖≤(CM*localConstant P)*N/(Real.log (N:ℝ))^(A+2) := by
    apply hb0.trans
    apply (mul_le_mul_of_nonneg_right (hM kap0) hE).trans_eq
    dsimp [P]
    rw [show A+40=(A+2)+38 by omega,pow_add]
    field_simp [hl0.ne']
    ring
  have hband : ‖band‖≤(N:ℝ)/(Real.log (N:ℝ))^(A+1) :=
    hb1'.trans (fixed_scalar_log_payment (CM*localConstant P)
      (mul_nonneg hCM (localConstant_nonneg P)) A N hl1 hcM)
  have ht0 := hT K A kap0 zeta m r n e q a omega k ell S hS hRange
  have ht2 : ‖full-band‖≤CT*N/(Real.log (N:ℝ))^(A+2) := by
    apply ht0.trans
    apply (div_le_div_of_nonneg_left (mul_nonneg hCT (Nat.cast_nonneg N))
      (pow_pos hl0 (A+4)) (pow_le_pow_left₀ hl0.le hL (A+4))).trans
    exact div_le_div_of_nonneg_left (mul_nonneg hCT (Nat.cast_nonneg N)) (pow_pos hl0 (A+2))
      (pow_le_pow_right₀ hl1 (by omega))
  have htail : ‖full-band‖≤(N:ℝ)/(Real.log (N:ℝ))^(A+1) :=
    ht2.trans (fixed_scalar_log_payment CT hCT A N hl1 hcT)
  change ‖full‖≤_
  calc
    _=‖(full-band)+band‖ := by rw [sub_add_cancel]
    _≤‖full-band‖+‖band‖ := norm_add_le _ _
    _≤2*N/(Real.log (N:ℝ))^(A+1) := by linarith
    _=(2/Real.log (N:ℝ))*((N:ℝ)/(Real.log (N:ℝ))^A) := by
      rw [pow_succ]; field_simp [hl0.ne']; ring
    _≤1*((N:ℝ)/(Real.log (N:ℝ))^A) := mul_le_mul_of_nonneg_right
      ((div_le_one hl0).mpr hl2) (by positivity)
    _=_ := one_mul _

/-- Original H_N error scale for this paid subbank only. The literal
singularNormalization and its existing positive-series transport are used;
this is not the remaining full H_N source or an hUpper conclusion. -/
theorem eventually_actual_twoLong_mother_le_singular (K : ℕ)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgate : 19/96<baseline b kap)
    (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      ‖originalBank zeta b kap (outerWidth N) N K kap0 S
        (coefficient m r n e q a omega k N ((N:ℝ)^ell))‖≤eta*singularNormalization N := by
  filter_upwards [eventually_actual_twoLong_mother_paid K 3 hz hz1 hk hkz ht ht1 hb hb1 hkap hgate,
    p5z_eventually_logCube_le_singularNormalization 1 eta heta] with N hbank hnorm
  intro m r n e q a omega k ell hRange S hS
  exact (hbank m r n e q a omega k ell hRange S hS).trans (by simpa only [one_mul] using hnorm)

end
end ImbalancedChen.P4BOriginalTwoLongMotherPayment
