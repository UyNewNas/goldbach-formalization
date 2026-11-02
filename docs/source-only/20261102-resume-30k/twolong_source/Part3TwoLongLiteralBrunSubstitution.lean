import ImbalancedChen.Part3TwoLongRetainedRowReindex
import ImbalancedChen.Part3TwoLongActualLowerCorePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal smooth upper/gap Brun tuple expansion, including the original
divisibility tests, is identified with J's paid rowCore. Divisor changes
the fixed short integer to m*d1*d2 and the evaluation scales to U/d1,V/d2;
the profiles still contain log U,log V and therefore log(d1*u),log(d2*v).
This proves no equality between the rough row and the upper polynomial:
that comparison requires the still-open E1/E3 and strip suppliers.
-/
namespace ImbalancedChen.Part3.TwoLongLiteralBrunSubstitution
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open TwoLongActualHBShortMass TwoLongActualLowerBrunMoment
open TwoLongActualLowerCorePayment TwoLongHBMellinBrunProfiles
open TwoLongLiteralMellinModes TwoLongFixedMRectangularCore
open TwoLongRetainedRowReindex
open ImbalancedChen.P5Z.HBRightClosedDyadicRoles
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail (lowerQ lowerRho)
open ImbalancedChen.OriginalOneLongLiteralBrunDictionary
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b (smallPrimes)
open ImbalancedChen.PrimeProducts

/-- The long original one/log occurrence agrees pointwise with the
actual transition profile times its SAME rough mask. After substitution
the log is log(d*u); no log d term is discarded. -/
theorem owned_left_profile_source {b : Block} {d u : ℕ}
    (hd : 0 < d) (hOwn : Owns b (d*u)) (Z y delta t : ℝ)
    (label : Fin 3) (role : Role) (hrole : role = .one ∨ role = .logarithm) :
    leftMellin delta (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b) t label
      (decide (role = .logarithm))
      ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) *
        ImbalancedChen.Part3.roughOneSlot Z (d*u) =
      TwoLongActualThreeBrunP2Receiver.leftProfile delta label
        ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d)) *
        (actual Z y role (d*u) *
          ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b.phase t
            ((u : ℝ)/((ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower b : ℝ)/d))) := by
  rw [leftMellin_exact, owned_long_role_profile hd hOwn Z y t role hrole]
  ring

def divisorIndicator (d n : ℕ) : ℂ := if d ∣ n then 1 else 0

theorem brun_ratio {U : ℝ} (hU : 0 < U) {d : ℕ} (hd : 0 < d) (u : ℕ) :
    ((d*u : ℕ) : ℝ)/U = (u : ℝ)/(U/d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp [hU.ne', hdR] <;> ring

/-- Actual divisor substitution on the full smooth cover. Zero values
at the extra ceil endpoints are removed by the proved profile support,
not by identifying two generally unequal integer windows. -/
theorem sum_divisor_substitution {U : ℝ} (hU : 0 < U) {d : ℕ} (hd : 0 < d)
    (f : ℝ → ℂ) (hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2)) (H : ℕ → ℂ) :
    (∑ n ∈ wideWindow U, f ((n : ℝ)/U) * divisorIndicator d n * H n) =
      ∑ u ∈ wideWindow (U/d), f ((u : ℝ)/(U/d)) * H (d*u) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let A := (wideWindow U).filter (fun n => d ∣ n ∧ f ((n : ℝ)/U) ≠ 0)
  let B := (wideWindow (U/d)).filter (fun u => f ((u : ℝ)/(U/d)) ≠ 0)
  have ha : (∑ n ∈ wideWindow U, f ((n : ℝ)/U) * divisorIndicator d n * H n) =
      ∑ n ∈ A, f ((n : ℝ)/U) * H n := by
    dsimp [A]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hdn : d ∣ n <;> by_cases hfn : f ((n : ℝ)/U) = 0 <;>
      simp [divisorIndicator, hdn, hfn]
  have hb : (∑ u ∈ wideWindow (U/d), f ((u : ℝ)/(U/d)) * H (d*u)) =
      ∑ u ∈ B, f ((u : ℝ)/(U/d)) * H (d*u) := by
    dsimp [B]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hfu : f ((u : ℝ)/(U/d)) = 0 <;> simp [hfu]
  rw [ha, hb]
  refine Finset.sum_bij (fun n _ => n/d) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnW, hdn, hfn⟩ := Finset.mem_filter.mp hn
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hr : (n : ℝ)/U = ((n/d : ℕ) : ℝ)/(U/d) := by
      simpa only [he] using brun_ratio hU hd (n/d)
    have hnon : f (((n/d : ℕ) : ℝ)/(U/d)) ≠ 0 := by rwa [← hr]
    exact Finset.mem_filter.mpr
      ⟨nonzero_mem_wideWindow (div_pos hU hdR) hf hnon, hnon⟩
  · intro n hn n' hn' he
    have hd1 := (Finset.mem_filter.mp hn).2.1
    have hd2 := (Finset.mem_filter.mp hn').2.1
    calc
      n = d*(n/d) := (Nat.mul_div_cancel' hd1).symm
      _ = d*(n'/d) := by rw [he]
      _ = n' := Nat.mul_div_cancel' hd2
  · intro u hu
    obtain ⟨huW, hfu⟩ := Finset.mem_filter.mp hu
    have hr := brun_ratio hU hd u
    have hnon : f (((d*u : ℕ) : ℝ)/U) ≠ 0 := by rwa [hr]
    refine ⟨d*u, Finset.mem_filter.mpr
      ⟨nonzero_mem_wideWindow hU hf hnon, dvd_mul_right d u, hnon⟩, ?_⟩
    exact Nat.mul_div_cancel_left u hd
  · intro n hn
    have hdn := (Finset.mem_filter.mp hn).2.1
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    rw [← brun_ratio hU hd (n/d), he]

/-- Both independent long substitutions preserve the complete integer
in the residue test and in the coprimality test, even for nonprimitive m. -/
theorem pair_divisor_substitution {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (f g : ℝ → ℂ)
    (hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2))
    (hg : Function.support g ⊆ Icc (1/2 : ℝ) (5/2))
    (alpha : ℂ) (m : ℕ) (K : ℕ → ℂ) :
    (∑ n ∈ wideWindow U, ∑ k ∈ wideWindow V,
      alpha*f ((n : ℝ)/U)*g ((k : ℝ)/V)*divisorIndicator d₁ n*
        divisorIndicator d₂ k*K (m*n*k)) =
      ∑ u ∈ wideWindow (U/d₁), ∑ v ∈ wideWindow (V/d₂),
        alpha*f ((u : ℝ)/(U/d₁))*g ((v : ℝ)/(V/d₂))*
          K ((m*d₁*d₂)*u*v) := by
  calc
    _ = ∑ n ∈ wideWindow U, f ((n : ℝ)/U)*divisorIndicator d₁ n*
        (∑ k ∈ wideWindow V,
          g ((k : ℝ)/V)*divisorIndicator d₂ k*(alpha*K (m*n*k))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ u ∈ wideWindow (U/d₁), f ((u : ℝ)/(U/d₁))*
        (∑ k ∈ wideWindow V,
          g ((k : ℝ)/V)*divisorIndicator d₂ k*(alpha*K (m*(d₁*u)*k))) :=
      sum_divisor_substitution hU hd₁ f hf _
    _ = ∑ u ∈ wideWindow (U/d₁), f ((u : ℝ)/(U/d₁))*
        (∑ v ∈ wideWindow (V/d₂),
          g ((v : ℝ)/(V/d₂))*(alpha*K (m*(d₁*u)*(d₂*v)))) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [sum_divisor_substitution hV hd₂ g hg]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [show m*(d₁*u)*(d₂*v) = (m*d₁*d₂)*u*v by ring]
      ring

theorem fixedMCore_eq_kernel (I J : Finset ℕ) (m N q : ℕ)
    (alpha : ℂ) (f g : ℝ → ℂ) (U V : ℝ) :
    fixedMCore I J m N q alpha f g U V =
      ∑ u ∈ I, ∑ v ∈ J, alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V)*
        MellinInsertion20261028.residueKernel q N (m*u*v) := by
  rw [fixedMCore_exact]
  have hp (u v : ℕ) : alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V)*
      MellinInsertion20261028.residueKernel q N (m*u*v) =
      (if m*u*v % q = N % q then alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V) else 0) -
      (((Nat.totient q : ℝ)⁻¹ : ℂ) *
        (if Nat.Coprime (m*u*v) q then alpha*f ((u : ℝ)/U)*g ((v : ℝ)/V) else 0)) := by
    by_cases ha : m*u*v % q = N % q <;> by_cases hc : Nat.Coprime (m*u*v) q <;>
      simp [MellinInsertion20261028.residueKernel, ha, hc, div_eq_mul_inv,
        Complex.ofReal_inv] <;> ring
  simp_rw [hp, Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]

def brunCoefficient (Z : ℝ) (h : ℕ) (gap : Bool) (d : ℕ) : ℂ :=
  ((if gap then gapCoefficient (smallPrimes Z) (2*h+1) d
    else upperCoefficient (smallPrimes Z) (2*h) d) : ℂ)

/-- Exactly the original upper or upper-minus-lower polynomial on the
inclusive p<=Z alphabet. These can be complex multiplied without ever
asserting positivity of the lower Brun polynomial. -/
def brunPolynomial (Z : ℝ) (h : ℕ) (gap : Bool) (n : ℕ) : ℂ :=
  ∑ d ∈ brunSupport Z (2*h+1), brunCoefficient Z h gap d * divisorIndicator d n

theorem brunPolynomial_eq_literal (Z : ℝ) (h : ℕ) (gap : Bool) (n : ℕ) :
    brunPolynomial Z h gap n =
      ((ImbalancedChen.OriginalOneLongFiniteBrun.polynomial
        (divisorSupport (smallPrimes Z) (2*h+1))
        ImbalancedChen.OriginalOneLongFiniteBrun.divisorMask
        (fun d => if gap then gapCoefficient (smallPrimes Z) (2*h+1) d
          else upperCoefficient (smallPrimes Z) (2*h) d) n : ℝ) : ℂ) := by
  cases gap <;>
    simp [brunPolynomial, brunSupport, brunCoefficient, divisorIndicator,
      ImbalancedChen.OriginalOneLongFiniteBrun.polynomial,
      ImbalancedChen.OriginalOneLongFiniteBrun.divisorMask,
      Complex.ofReal_sum, Complex.ofReal_mul]

theorem polynomial_pair (Z : ℝ) (h : ℕ) (b₁ b₂ : Bool) (n k : ℕ) :
    brunPolynomial Z h b₁ n * brunPolynomial Z h b₂ k =
      ∑ d ∈ (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1)),
        brunPairCoefficient Z h b₁ b₂ d * divisorIndicator d.1 n * divisorIndicator d.2 k := by
  simp only [brunPolynomial, Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  unfold brunPairCoefficient brunCoefficient
  ring

/-- Source is the literal long-integer double sum with divisibility
polynomials, not a sum of P2 cores by definition. -/
def smoothBrunTupleCore (Z : ℝ) (h : ℕ) (b₁ b₂ : Bool)
    (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m N q : ℕ) : ℂ :=
  ∑ n ∈ wideWindow U, ∑ k ∈ wideWindow V,
    alpha * leftMellin delta U t₁ label log₁ ((n : ℝ)/U) *
      rightMellin delta V t₂ label log₂ ((k : ℝ)/V) *
      (brunPolynomial Z h b₁ n * brunPolynomial Z h b₂ k) *
      MellinInsertion20261028.residueKernel q N (m*n*k)

theorem smoothBrunTupleCore_eq_expansion {Z delta U V : ℝ}
    (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (h : ℕ) (b₁ b₂ : Bool) (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (alpha : ℂ) (m N q : ℕ) :
    smoothBrunTupleCore Z h b₁ b₂ delta U V t₁ t₂ label log₁ log₂ alpha m N q =
      ∑ d ∈ (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1)),
        brunPairCoefficient Z h b₁ b₂ d *
          mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d.1 d.2 N q := by
  let I := (wideWindow U) ×ˢ (wideWindow V)
  let R := (brunSupport Z (2*h+1)) ×ˢ (brunSupport Z (2*h+1))
  let f := leftMellin delta U t₁ label log₁
  let g := rightMellin delta V t₂ label log₂
  have hf : Function.support f ⊆ Icc (1/2 : ℝ) (5/2) :=
    TwoLongTransitionMellinN2.profile_support _ _ hd hs U t₁
  have hg : Function.support g ⊆ Icc (1/2 : ℝ) (5/2) :=
    TwoLongTransitionMellinN2.profile_support _ _ hd hs V t₂
  calc
    _ = ∑ a ∈ I, ∑ d ∈ R, brunPairCoefficient Z h b₁ b₂ d *
        (alpha*f ((a.1 : ℝ)/U)*g ((a.2 : ℝ)/V)*
          divisorIndicator d.1 a.1*divisorIndicator d.2 a.2*
            MellinInsertion20261028.residueKernel q N (m*a.1*a.2)) := by
      unfold smoothBrunTupleCore
      simp_rw [polynomial_pair]
      simp only [I, R, Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro d₁ hd₁
      apply Finset.sum_congr rfl
      intro d₂ hd₂
      dsimp [f, g]
      ring
    _ = ∑ d ∈ R, brunPairCoefficient Z h b₁ b₂ d *
        ∑ a ∈ I, alpha*f ((a.1 : ℝ)/U)*g ((a.2 : ℝ)/V)*
          divisorIndicator d.1 a.1*divisorIndicator d.2 a.2*
            MellinInsertion20261028.residueKernel q N (m*a.1*a.2) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdr
      congr 1
      obtain ⟨hd₁, hd₂⟩ := Finset.mem_product.mp hdr
      have hp₁ := (brunSupport_bounds hZ _ hd₁).1
      have hp₂ := (brunSupport_bounds hZ _ hd₂).1
      simp only [I, Finset.sum_product]
      rw [pair_divisor_substitution hU hV hp₁ hp₂ f g hf hg alpha m]
      exact (fixedMCore_eq_kernel _ _ _ _ _ _ _ _ _ _).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Original ordered short tuples are still present in this source.
The same target and same physical signed lower coefficient multiply
the entire exact count-minus-coprime-mean kernel. -/
def actualExpandedTupleSource (policy : List ℕ → Bool) (N cap : ℕ) (w z L Z : ℝ)
    (h : ℕ) (b₁ b₂ : Bool) (delta U V t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role) : ℂ :=
  ∑ s ∈ shortRectangle bs, ∑ q ∈ lowerQ policy N cap w z,
    lowerRho policy N cap w z L q *
      smoothBrunTupleCore Z h b₁ b₂ delta U V t₁ t₂ label log₁ log₂
        (shortWeight bs Z y xi rs s) (shortProduct s) N q

/-- This is the missing source equality to J's arithmetic consumer.
Neither source identity, short L1, modulus moment, P2 nor E4 is a premise. -/
theorem actualExpandedTupleSource_eq_rowCore (policy : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) {Z delta U V : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta)
    (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (h : ℕ) (b₁ b₂ : Bool) (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role) :
    actualExpandedTupleSource policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ bs y xi rs =
      rowCore policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂ label log₁ log₂ bs y xi rs := by
  have hlin (alpha : ℂ) (m : ℕ) :
      lowerBrunCoreSum policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
        label log₁ log₂ alpha m =
      alpha * lowerBrunCoreSum policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
        label log₁ log₂ 1 m := by
    unfold lowerBrunCoreSum mellinBrunCore
    simp only [fixedMCore_eq_kernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro d hdr
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  unfold actualExpandedTupleSource
  simp_rw [smoothBrunTupleCore_eq_expansion hZ hd hs hU hV]
  change (∑ s ∈ shortRectangle bs,
    lowerBrunCoreSum policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ (shortWeight bs Z y xi rs s) (shortProduct s)) = _
  calc
    _ = ∑ s ∈ shortRectangle bs, shortWeight bs Z y xi rs s *
        lowerBrunCoreSum policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
          label log₁ log₂ 1 (shortProduct s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hlin _ _
    _ = ∑ m ∈ shortSupport bs, shortSequence bs Z y xi rs m *
        lowerBrunCoreSum policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
          label log₁ log₂ 1 m := (shortSequence_pushforward bs Z y xi rs _).symm
    _ = _ := by
      unfold rowCore
      apply Finset.sum_congr rfl
      intro m hm
      exact (hlin _ _).symm

/-- The actual ordered Brun tuple source now consumes the proved J
short mass and same-rho moment. All remaining inputs are elementary
source geometry or H's unchanged precise composite Weil input. -/
theorem actualExpandedTupleSource_bound (hWeil : TwoLongInternalP2Modes.CompositeWeilInput)
    (policy : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ) {Z X : ℝ}
    (hZ : 1 ≤ Z) (hX : 1 ≤ X)
    (hlevel : ∀ q ∈ lowerQ policy N cap w z,
      lowerRho policy N cap w z L q ≠ 0 → q ≤ D)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (h : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ a, 2 * (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower (bs a) : ℝ) ≤ X) :
    ‖actualExpandedTupleSource policy N cap w z L Z h b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z^(2*h+1))^2) *
        (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16) *
          (1 + Real.log X)^Fintype.card ι := by
  rw [actualExpandedTupleSource_eq_rowCore policy N cap w z L hZ hd hs hU hV]
  exact rowCore_bound hWeil policy N cap D w z L hZ hX hlevel hd hs
    hU hV hH ht₁ ht₂ h b₁ b₂ label log₁ log₂ bs y xi rs hcap

/-- Uniform payment is now a conclusion about the literal ordered
Brun tuple source. Its threshold and all original power/support gates
are exactly J's; no assumed source equality occurs among the inputs. -/
theorem eventually_actual_expanded_tuple_paid
    (hWeil : TwoLongInternalP2Modes.CompositeWeilInput)
    (B K A : ℕ) (hB : 1 ≤ B) (c : ℝ) (hc : 0 < c)
    (zeta theta epsilon : ℝ) (hepsilon : 0 < epsilon) (htheta : theta ≤ 1)
    (hmargin : 40*zeta+2*epsilon+3*theta/2 < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (policy : List ℕ → Bool) (N cap D : ℕ)
      (w z L Z U V t₁ t₂ : ℝ) (h : ℕ) (b₁ b₂ : Bool) (label : Fin 3)
      (log₁ log₂ : Bool) (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role),
      Fintype.card ι ≤ 6 → 1 ≤ D → 1 ≤ Z →
      (∀ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q ≠ 0 → q ≤ D) →
      (D : ℝ) ≤ x^theta → (shortScale bs : ℝ) ≤ x^(40*zeta) → Z^(2*h+1) ≤ x^epsilon →
      (∀ a, 2 * (ImbalancedChen.P5Z.ActualHBDyadicProductWindow.lower (bs a) : ℝ) ≤ x) →
      1 ≤ U → 1 ≤ V → U ≤ c*x → V ≤ c*x →
      |t₁| ≤ (Real.log x)^K → |t₂| ≤ (Real.log x)^K →
      ‖actualExpandedTupleSource policy N cap w z L Z h b₁ b₂ ((Real.log x)^B)⁻¹
        U V t₁ t₂ label log₁ log₂ bs y xi rs‖ ≤ x/(Real.log x)^A := by
  filter_upwards [eventually_actual_lower_core_paid hWeil B K A hB c hc
    zeta theta epsilon hepsilon htheta hmargin, TwoLongMellinLogBudget.eventually_schedule B hB]
    with x hpay hsched
  intro ι instF instD policy N cap D w z L Z U V t₁ t₂ h b₁ b₂ label log₁ log₂ bs y xi rs
    hrank hD hZ hlevel hDx hMx hyx hcap hU hV hUx hVx ht₁ ht₂
  rw [actualExpandedTupleSource_eq_rowCore policy N cap w z L hZ hsched.2.1 hsched.2.2
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)]
  exact hpay ι policy N cap D w z L Z U V t₁ t₂ h b₁ b₂ label log₁ log₂ bs y xi rs
    hrank hD hZ hlevel hDx hMx hyx hcap hU hV hUx hVx ht₁ ht₂

end
end ImbalancedChen.Part3.TwoLongLiteralBrunSubstitution
