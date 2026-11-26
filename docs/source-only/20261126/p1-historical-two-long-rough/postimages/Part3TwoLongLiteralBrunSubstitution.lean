import ImbalancedChen.Part3TwoLongRetainedRowReindex
import ImbalancedChen.Part3TwoLongActualLowerCorePayment
import ImbalancedChen.P1HistoricalTwoLongBrunSubstitutionData

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
