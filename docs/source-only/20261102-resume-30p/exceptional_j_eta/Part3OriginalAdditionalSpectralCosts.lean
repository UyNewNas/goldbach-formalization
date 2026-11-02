import ImbalancedChen.Part3ActualExceptionalJSelectableEta
import ImbalancedChen.Part3OriginalCommonPoissonLanes
import ImbalancedChen.Part3ActualCommonIntervalPhysicalLogBudget
import ImbalancedChen.Part3ZExceptionalSpectralPolynomial
import ImbalancedChen.Part3MediumActualRestorationPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original-parameter adaptations of genuine extra cost suppliers. No spectral
PacketData association or estimate of completedEnergy is assumed or proved.
The actual Poisson block scale is treated before any such association.
All finite orders entering selectable power fees must be fixed before eta.
The omitted-frequency tail and its order choice remain separate obligations;
no tail estimate is claimed by the cutoff bookkeeping theorem below.
-/

namespace ImbalancedChen.Part3.OriginalAdditionalSpectralCosts20261102

noncomputable section
open Classical Finset Filter
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3ActualWeightedSpectralBudgetSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualCommonMaskSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualCommonIntervalCompletionSourceOnly
open ActualCommonIntervalCompletionNormSourceOnly
open ActualCommonIntervalPhysicalLogBudgetSourceOnly
open ActualExceptionalJSelectableEta20261102
open OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102
open OriginalMaskedOuterEnergy20261102
open MediumGlobalDyadicOwnership20261028
open MediumActualRestorationPayment20261028
open OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding

variable {ι : Type*}

/-- The actual original rough dyadic S is always at least one. -/
theorem scaleS_one_le (k : Key) : 1 ≤ scaleS k := by
  have hp : 0 < (2 : ℕ)^k.u := pow_pos (by norm_num) _
  have hh : 1 ≤ (2 : ℕ)^k.u := hp
  change (1 : ℝ) ≤ ((2 : ℕ)^k.u : ℝ)
  exact_mod_cast hh

/-- The actual ceil cutoff enlarges the natural nonempty m-block scale
by at most two. The integer is extracted from that original block. -/
theorem commonMBlock_scale_le_twice_cutoff (D : OriginalData) {x epsilon : ℝ}
    (hx : 1 ≤ x) (hepsilon : 0 ≤ epsilon) (j : ℕ)
    (hne : (commonMBlock (globalCutoff D x epsilon) j).Nonempty) :
    ((2 : ℕ)^j : ℝ) ≤ 2*x^epsilon*D.cScale/D.bScale := by
  have hratio : D.cScale/D.bScale = scaleS D.key := by
    unfold OriginalData.cScale
    field_simp [D.bScale_pos.ne'] <;> ring
  have hS := scaleS_one_le D.key
  have hT : 1 ≤ (D.cScale/D.bScale)*x^epsilon := by
    rw [hratio]
    simpa only [one_mul] using
      mul_le_mul hS (Real.one_le_rpow hx hepsilon)
        zero_le_one (zero_le_one.trans hS)
  have hceil : (globalCutoff D x epsilon : ℝ) ≤
      2*((D.cScale/D.bScale)*x^epsilon) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (D.cScale/D.bScale)*x^epsilon by
      have := D.bScale_pos; have := D.cScale_pos; positivity)
    change (Nat.ceil ((D.cScale/D.bScale)*x^epsilon) : ℝ) ≤ _
    linarith
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hp
  have hpJ : p ≤ globalCutoff D x epsilon := by
    have hh := (lt_min_iff.mp hhi).2
    omega
  have hVJ : ((2 : ℕ)^j : ℝ) ≤ (globalCutoff D x epsilon : ℝ) := by
    exact_mod_cast hlo.trans hpJ
  exact (hVJ.trans hceil).trans_eq (by ring)

/-- The ceil enlargement is paid at a threshold chosen BEFORE OriginalData
or a dyadic block. The original cutoff is narrowed to eta/2, so the caller
can use its literal eta without silently dropping an endpoint factor two. -/
theorem exists_globalCutoff_common_scale_threshold {eta : ℝ} (heta : 0 < eta) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (D : OriginalData) (x : ℝ), X ≤ x →
      ∀ j : ℕ, (commonMBlock (globalCutoff D x (eta/2)) j).Nonempty →
        ((2 : ℕ)^j : ℝ) ≤ x^eta*D.cScale/D.bScale := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < eta/2 by positivity)).eventually_ge_atTop 2)
  refine ⟨max 1 X,le_max_left _ _,?_⟩
  intro D x hx j hne
  have hx1 : 1 ≤ x := (le_max_left 1 X).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hhalf : (2 : ℝ) ≤ x^(eta/2) := hX x ((le_max_right 1 X).trans hx)
  have hraw := commonMBlock_scale_le_twice_cutoff D hx1 (by positivity : 0 ≤ eta/2) j hne
  have hpowers : x^(eta/2)*x^(eta/2) = x^eta := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  calc
    _ ≤ 2*((D.cScale/D.bScale)*x^(eta/2)) := hraw.trans_eq (by ring)
    _ ≤ (x^(eta/2)*x^(eta/2))*(D.cScale/D.bScale) := by
      have hh := mul_le_mul_of_nonneg_right hhalf
        (show 0 ≤ (D.cScale/D.bScale)*x^(eta/2) by
          have := D.bScale_pos; have := D.cScale_pos; positivity)
      nlinarith only [hh]
    _ = x^eta*D.cScale/D.bScale := by rw [hpowers]; ring

/-- All six original smooth pieces have M<=2*bScale and N>=cScale.
With the SAME eta/2 cutoff, a single stronger threshold pays both the
ceil factor two and the physical six-piece ratio factor two. No spectral
packet or identification is a premise. -/
theorem exists_globalCutoff_six_rho_threshold {eta : ℝ} (heta : 0 < eta) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (D : OriginalData) (x : ℝ), X ≤ x →
      ∀ (j : ℕ) (M N : ℝ), 0 < M → 0 < N →
        M ≤ 2*D.bScale → D.cScale ≤ N →
        (commonMBlock (globalCutoff D x (eta/2)) j).Nonempty →
        (((2 : ℕ)^j : ℝ)*M/N) ≤ x^eta := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < eta/2 by positivity)).eventually_ge_atTop 4)
  refine ⟨max 1 X,le_max_left _ _,?_⟩
  intro D x hx j M N hM hN hMB hCN hne
  have hx1 : 1 ≤ x := (le_max_left 1 X).trans hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hhalf : (4 : ℝ) ≤ x^(eta/2) := hX x ((le_max_right 1 X).trans hx)
  have hraw := commonMBlock_scale_le_twice_cutoff D hx1 (by positivity : 0 ≤ eta/2) j hne
  have hraw0 : 0 ≤ 2*x^(eta/2)*D.cScale/D.bScale := by
    have := D.bScale_pos; have := D.cScale_pos; positivity
  have hVM : ((2 : ℕ)^j : ℝ)*M ≤ 4*x^(eta/2)*D.cScale := by
    have hh := mul_le_mul hraw hMB hM.le hraw0
    apply hh.trans_eq
    field_simp [D.bScale_pos.ne'] <;> ring
  have hrho : (((2 : ℕ)^j : ℝ)*M/N) ≤ 4*x^(eta/2) := by
    apply (div_le_iff₀ hN).mpr
    exact hVM.trans (mul_le_mul_of_nonneg_left hCN (by positivity))
  calc
    _ ≤ 4*x^(eta/2) := hrho
    _ ≤ x^(eta/2)*x^(eta/2) :=
      mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hx0.le _)
    _ = x^eta := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring

/-- Production already proves the ordinary x^(2 eta) return. This is the
missing matching specialization of the actual exceptional expression. -/
theorem exceptional_return_le_rpow_cutoff {A U C D V Z theta x eta : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (htheta : 0 ≤ theta) (htheta' : theta ≤ 1/2)
    (hx : 1 ≤ x) (heta : 0 ≤ eta) (hcut : V ≤ x^eta*C/D) :
    ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalReturn A U C D V Z theta ≤
      x^(2*eta)*
        ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial U C D Z theta := by
  have hh := ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptional_return_le_inflated_cutoff
    hA hU hC hD hV hZ htheta htheta' (Real.one_le_rpow hx heta) hcut
  have hp : (x^eta)^2 = x^(2*eta) := by
    simpa using rpow_nat_power x eta (zero_le_one.trans hx) 2
  simpa only [hp] using hh

/-- If a later valid mode estimate leaves an unweighted coefficient mass,
that mass is NOT free. This invokes its actual supplier at order zero and
pays it together with the proved degree-two cutoff. It is not an estimate
of completedEnergy or of any automorphic quadratic form. -/
theorem exists_unweighted_mass_and_cutoff_constant :
    ∃ K : ℝ, 0 < K ∧ ∀ x eta rho sign : ℝ,
      1 ≤ x → 0 ≤ eta → 0 ≤ rho → rho ≤ x^eta → |sign| ≤ 1 →
      x^(2*eta)*actualW rho sign 0 ≤ K*x^(14*eta) := by
  obtain ⟨K,hK,hbudget⟩ := actual_uniform_xeta_weighted_budget 0
  refine ⟨K,hK,?_⟩
  intro x eta rho sign hx heta hrho hcut hsign
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hw : actualW rho sign 0 ≤ K*x^(12*eta) := by
    simpa using (hbudget x hx eta heta rho hrho hcut sign hsign).2.1
  calc
    _ ≤ x^(2*eta)*(K*x^(12*eta)) :=
      mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hx0.le _)
    _ = K*(x^(2*eta)*x^(12*eta)) := by ring
    _ = K*x^(14*eta) := by
      rw [← Real.rpow_add hx0]
      congr 2
      ring

/-- The original C=NRS,D=NR cutoff has polynomial V even if eta is
subsequently narrowed. These are the printed physical length variables. -/
theorem literal_cutoff_V_le_sq {N R S V x eta : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hS : S ≤ x) (hx : 1 ≤ x)
    (heta : eta ≤ 1) (hcut : V ≤ x^eta*(N*R*S)/(N*R)) : V ≤ x^2 := by
  have hratio : x^eta*(N*R*S)/(N*R) = x^eta*S := by
    field_simp [hN.ne',hR.ne'] <;> ring
  have hxeta : x^eta ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx heta
  rw [hratio] at hcut
  calc
    V ≤ x^eta*S := hcut
    _ ≤ x^eta*x := mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg (zero_le_one.trans hx) _)
    _ ≤ x*x := mul_le_mul_of_nonneg_right hxeta (zero_le_one.trans hx)
    _ = x^2 := by ring

/-- The actual common-mask completion, including the empty m branch,
has a single pre-packet threshold at the original polynomial scale.
Its maximum is ONE common frequency maximum, exactly as in production. -/
theorem exists_original_mask_log_threshold {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K X : ℝ, 0 < K ∧ ∀ (P : PacketData ι) (x : ℝ),
      1 ≤ x → X ≤ x → P.V ≤ x^2 → ∀ (a b : ℕ) (k : D4 → ℤ),
      ‖completedPacketSum (restrictM P a b) k‖^2 ≤
        K*x^delta*maxShiftedPacketNormSq P k (physicalPeriod P) := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (one_add_log_sq_eventually hdelta)
  let L : ℝ := Real.log 3+2
  have hL : 0 < L := by
    dsimp [L]
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]
  refine ⟨4*physicalCompletionConstant^2*L^2,X,by
    have := physicalCompletionConstant_pos; positivity,?_⟩
  intro P x hx hxX hV a b k
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlogx := Real.log_nonneg hx
  have hlogV : Real.log (2+P.V) ≤ L*(1+Real.log x) := by
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
    have hb : 2+P.V ≤ 3*x^2 := by linarith
    have hh := Real.log_le_log (show 0 < 2+P.V by linarith [P.V_pos]) hb
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    have hp := mul_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)) hlogx
    dsimp [L]
    nlinarith
  have hlog0 : 0 ≤ Real.log (2+P.V) :=
    Real.log_nonneg (by linarith [P.V_pos])
  have hs := pow_le_pow_left₀ hlog0 hlogV 2
  have hl := hX x hxX
  have hlogSq : (Real.log (2+P.V))^2 ≤ 4*L^2*x^delta := by
    have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg L)
    nlinarith only [hs,hh]
  have hmax : 0 ≤ maxShiftedPacketNormSq P k (physicalPeriod P) := by
    rw [← maxShiftedPacketNorm_sq]
    exact sq_nonneg _
  calc
    _ ≤ physicalCompletionConstant^2*(Real.log (2+P.V))^2*
        maxShiftedPacketNormSq P k (physicalPeriod P) :=
      actual_same_mask_physical_norm_sq P a b k
    _ ≤ physicalCompletionConstant^2*(4*L^2*x^delta)*
        maxShiftedPacketNormSq P k (physicalPeriod P) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogSq (sq_nonneg _)) hmax
    _ = _ := by ring

/-- ONE extra preliminary D on every occupied original dyadic key is
paid by an arbitrarily small power. No hypothesis asserting that payment
is used. The real threshold precedes the atom, receiver and occupied key. -/
theorem exists_occupied_keyD_subpower_threshold {delta : ℝ} (hdelta : 0 < delta) :
    ∃ X : ℝ, ∀ (atom : MediumAtom) (x receiver : ℝ) (k : Key),
      1 ≤ x → X ≤ x → k ∈ keyBank atom receiver (roughY x) → keyD k ≤ x^delta := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (2/delta))
  refine ⟨X,?_⟩
  intro atom x receiver k hx hxX hk
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hll : 2/delta ≤ Real.log (Real.log x) := hX x hxX
  have hll0 : 0 < Real.log (Real.log x) := (div_pos (by norm_num) hdelta).trans_le hll
  have he : 2/Real.log (Real.log x) ≤ delta := by
    apply (div_le_iff₀ hll0).mpr
    have hh := mul_le_mul_of_nonneg_left hll hdelta.le
    have hc : delta*(2/delta) = (2 : ℝ) := by field_simp [hdelta.ne'] <;> ring
    rw [hc] at hh
    linarith
  have hy : 0 < roughY x := Real.rpow_pos_of_pos hx0 _
  calc
    keyD k ≤ roughY x^2 := occupied_keyD_le_trim_sq hy.le hk
    _ = x^(2/Real.log (Real.log x)) := by
      unfold roughY
      rw [← Real.rpow_mul_natCast hx0.le]
      congr 1 <;> ring
    _ ≤ x^delta := Real.rpow_le_rpow_of_exponent_le hx he

end
end ImbalancedChen.Part3.OriginalAdditionalSpectralCosts20261102
