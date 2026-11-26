import ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData
import ImbalancedChen.P1Full87TrueDUnitBound
import ImbalancedChen.P4BOriginalSquarefreeP2
import ImbalancedChen.Part3TwoLongBrunSupport
import ImbalancedChen.Part3TwoLongActualHBShortMass
import ImbalancedChen.DivisorMomentBudget

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original historical true-d coefficient supplies the squarefree physical
modulus, target coprimality and unit norm needed by the existing internal P2.
The literal Brun pairs and signed ordered short pushforward are retained.
Their masses and the physical modulus moment are proved by existing suppliers.
No P2, Weil, short-mass, moment or discrepancy estimate is a premise.

This is the finite expanded-core invoice of the frozen 1106 coefficient
appendix, equations core-summed and two-rough-error. It does not identify
the rough source with its Brun polynomial, pay E1/E3 or endpoint strips,
perform Fourier reconstruction, or close the two-long/P1.5 terminal.
The free product carrier is not asserted squarefree.
-/

namespace ImbalancedChen.P1OriginalHistoricalTwoLongP2
noncomputable section
open Classical
open scoped BigOperators
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P1Full87TrueDPolicyDelta
  (trueDDeltaSupport trueDDeltaRho trueDDeltaSupport_squarefree
    trueDDeltaSupport_coprime_target)
open Part3.TwoLongHBMellinBrunProfiles
open Part3.TwoLongActualHBShortMass
open Part3.TwoLongActualLowerBrunMoment
  (brunSupport brunSupport_bounds brunPairCoefficient brunPair_mass)
open Part3.TwoLongActualThreeBrunP2Receiver
  (modulusBudget tau modulusBudget_nonneg)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualRoughHeathBrownWords (Role)

/-- Exactly the original remaining physical modulus carrier. -/
abbrev historicalModuli (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  remainingModuli B N (trueDDeltaSupport old fresh N cap w z)

/-- The unchanged signed historical difference, embedded into ℂ. -/
abbrev historicalRho (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℂ :=
  (trueDDeltaRho old fresh N cap w z L q : ℂ)

def momentBudget (D : ℕ) : ℝ :=
  ((D : ℝ) * Real.sqrt D + 1) *
    (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16

theorem momentBudget_nonneg (D : ℕ) : 0 ≤ momentBudget D := by
  unfold momentBudget
  positivity

/-- These arithmetic properties come from the actual historical support,
not from an extra modulus-class assumption on the desired conclusion. -/
theorem historical_modulus_class (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : q ∈ historicalModuli B old fresh N cap w z) :
    0 < q ∧ Nat.Coprime N q ∧ Squarefree q ∧
      ‖historicalRho old fresh N cap w z L q‖ ≤ 1 := by
  have hsource := (Finset.mem_filter.mp hq).1
  have hsf := trueDDeltaSupport_squarefree old fresh N cap w z hsource
  refine ⟨Nat.pos_of_ne_zero hsf.ne_zero,
    (trueDDeltaSupport_coprime_target old fresh N cap w z hsource).symm, hsf, ?_⟩
  simpa only [historicalRho, Complex.norm_real, Real.norm_eq_abs] using
    P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap q w z L

theorem historical_modulus_floor (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ historicalModuli B old fresh N cap w z) :
    q ≤ ⌊(N : ℝ) ^ (599 / 1000 : ℝ)⌋₊ := by
  exact Nat.le_floor (Finset.mem_filter.mp hq).2.2.le

/-- A geometric finite upper endpoint is enough: the moment itself is
derived from the existing fourth-divisor moment theorem. All original
signed coefficients remain inside their actual modulus carrier. -/
theorem historical_modulus_moment (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D) :
    (∑ q ∈ historicalModuli B old fresh N cap w z,
      ‖historicalRho old fresh N cap w z L q‖ * modulusBudget q) ≤
      momentBudget D := by
  let S := historicalModuli B old fresh N cap w z
  have hS : S ⊆ Finset.Icc 1 D := by
    intro q hq
    exact Finset.mem_Icc.mpr
      ⟨(historical_modulus_class B old fresh N cap w z L hq).1, hlevel q hq⟩
  have hsf : ∀ q ∈ S, Squarefree q := fun q hq =>
    (historical_modulus_class B old fresh N cap w z L hq).2.2.1
  have hpoint (q : ℕ) (hq : q ∈ S) :
      ‖historicalRho old fresh N cap w z L q‖ * modulusBudget q ≤
      ((D : ℝ) * Real.sqrt D + 1) *
        ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := by
    obtain ⟨hqpos, hqD⟩ := Finset.mem_Icc.mp (hS hq)
    have hphi : 0 < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hphiD : (Nat.totient q : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (Nat.totient_le q).trans hqD
    have htau : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
      have hm : 1 ∈ q.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, Nat.ne_of_gt hqpos⟩
      exact_mod_cast Finset.card_pos.mpr ⟨1, hm⟩
    have htau1 : (q.divisors.card : ℝ) ≤ (q.divisors.card : ℝ)^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ htau (by norm_num : (1 : ℕ) ≤ 4)
    have htau2 : (q.divisors.card : ℝ)^2 ≤ (q.divisors.card : ℝ)^4 :=
      pow_le_pow_right₀ htau (by norm_num)
    have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (D : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hqD)
    have hfirst : Real.sqrt (q : ℝ) * (q.divisors.card : ℝ) ≤
        ((D : ℝ) * Real.sqrt D) * ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hphi).2
      calc
        _ ≤ Real.sqrt (D : ℝ) * (q.divisors.card : ℝ)^4 * (D : ℝ) := by gcongr
        _ = _ := by ring
    have hsecond : (q.divisors.card : ℝ)^2 / (Nat.totient q : ℝ) ≤
        (q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ) :=
      div_le_div_of_nonneg_right htau2 hphi.le
    calc
      _ ≤ modulusBudget q := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (historical_modulus_class B old fresh N cap w z L hq).2.2.2
          (modulusBudget_nonneg q)
      _ ≤ _ := by
        unfold modulusBudget tau
        nlinarith [hfirst, hsecond]
  calc
    _ ≤ ∑ q ∈ S, ((D : ℝ) * Real.sqrt D + 1) *
        ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := Finset.sum_le_sum hpoint
    _ = ((D : ℝ) * Real.sqrt D + 1) *
        ∑ q ∈ S, (q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_divisor_fourth_moment_le_log S D hS hsf) (by positivity)

/-- The two real Brun supports, original pair signs and original target N.
The inner core is the existing count minus its exact coprime mean. -/
def historicalBrunCore (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L Z : ℝ) (j : ℕ) (b₁ b₂ : Bool)
    (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (short : ℕ) : ℂ :=
  ∑ q ∈ historicalModuli B old fresh N cap w z,
    historicalRho old fresh N cap w z L q *
      ∑ d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)),
        brunPairCoefficient Z j b₁ b₂ d *
          mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N q

theorem historical_Brun_P2 (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {Z delta U V H t₁ t₂ : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (short : ℕ) :
    ‖historicalBrunCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ alpha short‖ ≤
      pairCost delta U V H * ((Z^(2*j+1))^2 * ‖alpha‖) * momentBudget D := by
  let c := historicalRho old fresh N cap w z L
  let Q := historicalModuli B old fresh N cap w z
  let R := (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1))
  have hpoint (q : ℕ) (hq : q ∈ Q) (d : ℕ × ℕ) (hdr : d ∈ R) :
      ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N q‖ ≤
        pairCost delta U V H * ‖alpha‖ * modulusBudget q := by
    obtain ⟨hqpos, hcop, hsf, _⟩ := historical_modulus_class B old fresh N cap w z L hq
    exact P4BOriginalSquarefreeP2.mellinBrunCore_internalP2 hsf hd hs hU hV hH ht₁ ht₂
      label log₁ log₂ alpha short d.1 d.2 N
      (brunSupport_bounds hZ _ (Finset.mem_product.mp hdr).1).1
      (brunSupport_bounds hZ _ (Finset.mem_product.mp hdr).2).1 hqpos hcop
  have hfinite : ‖historicalBrunCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ alpha short‖ ≤
      pairCost delta U V H * (∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ * ‖alpha‖) *
        (∑ q ∈ Q, ‖c q‖ * modulusBudget q) := by
    unfold historicalBrunCore
    calc
      _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ *
          ‖mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha short d.1 d.2 N q‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
      _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ d ∈ R, ‖brunPairCoefficient Z j b₁ b₂ d‖ *
          (pairCost delta U V H * ‖alpha‖ * modulusBudget q) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum
        intro d hdr
        exact mul_le_mul_of_nonneg_left (hpoint q hq d hdr) (norm_nonneg _)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro d hdr
        ring
  exact hfinite.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (brunPair_mass hZ j b₁ b₂ alpha) (pairCost_nonneg _ _ _ _))
    (historical_modulus_moment B old fresh N cap D w z L hlevel)
    (Finset.sum_nonneg (fun q hq => mul_nonneg (norm_nonneg _) (modulusBudget_nonneg _)))
    (mul_nonneg (pairCost_nonneg _ _ _ _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original signed short pushforward, including collisions between
ordered tuples, inserted into the same historical coefficient and target. -/
def historicalRowCore (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L Z : ℝ) (j : ℕ) (b₁ b₂ : Bool)
    (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role) : ℂ :=
  ∑ short ∈ shortSupport bs,
    historicalBrunCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ (shortSequence bs Z y xi rs short) short

theorem historical_rowCore_bound (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {Z X delta U V H t₁ t₂ : ℝ} (hZ : 1 ≤ Z) (hX : 1 ≤ X)
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ i, 2 * (lower (bs i) : ℝ) ≤ X) :
    ‖historicalRowCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        momentBudget D * (1 + Real.log X)^Fintype.card ι := by
  have hm := shortSequence_mass bs Z y xi rs hX hcap
  unfold historicalRowCore
  calc
    _ ≤ ∑ short ∈ shortSupport bs,
        pairCost delta U V H * ((Z^(2*j+1))^2 * ‖shortSequence bs Z y xi rs short‖) *
          momentBudget D := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun short _ => historical_Brun_P2 B old fresh N cap D w z L
        hlevel hZ hd hs hU hV hH ht₁ ht₂ j b₁ b₂ label log₁ log₂ _ short)
    _ = (pairCost delta U V H * (Z^(2*j+1))^2 * momentBudget D) *
        ∑ short ∈ shortSupport bs, ‖shortSequence bs Z y xi rs short‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro short hshort
      ring
    _ ≤ (pairCost delta U V H * (Z^(2*j+1))^2 * momentBudget D) *
        ((shortScale bs : ℝ) * (1 + Real.log X)^Fintype.card ι) :=
      mul_le_mul_of_nonneg_left hm
        (mul_nonneg (mul_nonneg (pairCost_nonneg _ _ _ _) (sq_nonneg _))
          (momentBudget_nonneg D))
    _ = _ := by ring

/-- At the original physical endpoint there is no remaining level premise:
the strict .599 cutoff in remainingModuli supplies the natural floor. -/
theorem historical_rowCore_bound_at_physical_level (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ)
    {Z X delta U V H t₁ t₂ : ℝ} (hZ : 1 ≤ Z) (hX : 1 ≤ X)
    (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ i, 2 * (lower (bs i) : ℝ) ≤ X) :
    ‖historicalRowCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z^(2*j+1))^2) *
        momentBudget ⌊(N : ℝ) ^ (599 / 1000 : ℝ)⌋₊ *
          (1 + Real.log X)^Fintype.card ι := by
  exact historical_rowCore_bound B old fresh N cap _ w z L
    (fun q hq => historical_modulus_floor B old fresh N cap w z hq)
    hZ hX hd hs hU hV hH ht₁ ht₂ j b₁ b₂ label log₁ log₂ bs y xi rs hcap

end
end ImbalancedChen.P1OriginalHistoricalTwoLongP2
