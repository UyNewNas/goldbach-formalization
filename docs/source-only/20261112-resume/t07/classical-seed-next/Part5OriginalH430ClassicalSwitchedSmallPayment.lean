import ImbalancedChen.Part5OriginalH430ClassicalSmallSwitchedIntegers
import ImbalancedChen.Part5OriginalH430SeedSameCarrierPP

/-! Pay the two actual small-product carriers against each history's own
true-li atom. The estimate is uniform over every original marked subfamily;
there is no division by a possibly zero marked mass. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSwitchedSmallPayment
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open MathlibNt.SieveTheory.SingularSeries (liuUniversalProduct liuUniversalProduct_pos)
open P2EnhancedSwitchedTrueNormalization (thetaConversion rawMainAtom rawMainAtom_to_thetaAtom)
open P2EnhancedUnitSourceMass (thetaConversion_nonneg)
open P2EnhancedThetaReciprocalMass (Theta_lower)
open P2EnhancedCollisionThetaPayment (residual_level_le_N)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2OriginalPositiveSameQMassLift (thetaAtom_nonneg)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open Part5OriginalH430OriginalRootQBound (original_root_Q_le_target)
open Part5OriginalH430ClassicalCausalSeedScale
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open scoped Classical Topology BigOperators

/-- Both estimates use the same product split, with the literal converted
K/4 in the second inequality. Only the first carrier tests N-Dm for primality. -/
theorem small_both_atoms {κ ε : ℝ} (hk : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q : ℝ) (d : ℕ),0<d → Q≤(N:ℝ) →
      (N:ℝ)^frozenResidualFloor≤Q/d →
      let X := smallProduct N κ
      allSmall true N Q d X≤ε*thetaAtom N Q d ∧
        (K/4)*thetaConversion N d*allSmall false N Q d X≤ε*thetaAtom N Q d := by
  let C : ℝ := 20*5^6
  let δ := min (2*liuUniversalProduct*ε) (ε/(K/4))
  have hK : 0<K/4 := by norm_num [K]
  have hδ : 0<δ := lt_min (mul_pos (mul_pos (by norm_num) liuUniversalProduct_pos) he) (div_pos he hK)
  obtain ⟨Ta,h4,ha⟩ := all_small_integer_budget frozenResidualFloor_pos
  obtain ⟨Tb,_,hb⟩ := ninth_power_log_error_budget 0 (C:=C) (α:=κ) (ε:=δ) (by norm_num [C]) hk hδ
  obtain ⟨Tc,hc⟩ := eventually_atTop.mp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨max Ta (max Tb Tc),h4.trans (le_max_left _ _),?_⟩
  intro N hN Q d hd hQ hscale
  let X := smallProduct N κ
  let Z := (N:ℝ)/((d:ℝ)*log (N:ℝ)^2)
  have haN := (le_max_left Ta (max Tb Tc)).trans hN
  have hbN := (le_max_left Tb Tc).trans ((le_max_right Ta (max Tb Tc)).trans hN)
  have hcN := (le_max_right Tb Tc).trans ((le_max_right Ta (max Tb Tc)).trans hN)
  have hN4 := h4.trans haN
  have hN0 : 0<N := by omega
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN0
  have hdr : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hR := (one_lt_rpow (by exact_mod_cast (show 1<N by omega)) frozenResidualFloor_pos).trans_le hscale
  have hRN := residual_level_le_N hd hQ
  have hc0 := thetaConversion_nonneg hN4 hd hR
  have hlog := hc N hcN
  have hlog0 : 0<log (N:ℝ) := zero_lt_one.trans_le hlog
  have hZ : 0≤Z := div_nonneg hNr.le (mul_nonneg hdr.le (sq_nonneg _))
  have hx : X=(N:ℝ)/(N:ℝ)^κ := by rw [show X=(N:ℝ)^(1-κ) from rfl,rpow_sub hNr,rpow_one]
  have hl : C*(N:ℝ)/(N:ℝ)^κ≤δ*N/log N^2 := by simpa only [pow_zero,mul_one] using hb N hbN
  have hall : allSmall false N Q d X≤δ*Z := by
    have hf := ha N haN Q d hd hscale X (rpow_nonneg hNr.le _)
    calc
      _ ≤ C*X/d := hf
      _ = (C*N/(N:ℝ)^κ)/d := by rw [hx]; ring
      _ ≤ (δ*N/log N^2)/d := div_le_div_of_nonneg_right hl hdr.le
      _ = _ := by dsimp only [Z]; ring
  have htheta : (2*liuUniversalProduct)*Z≤thetaAtom N Q d := by
    have h := Theta_lower hN4 Q ({d}:Finset ℕ) (fun _ => (1:ℝ))
      (fun x hx => (mem_singleton.mp hx).symm ▸ hd) (fun _ _ => zero_le_one)
      (fun x hx => (mem_singleton.mp hx).symm ▸ ⟨hR,hRN⟩)
    rw [Theta_eq_sum_atoms] at h
    simp only [sum_singleton,one_mul] at h
    convert h using 1 <;> dsimp only [Z] <;> ring
  have hraw : thetaConversion N d*Z≤thetaAtom N Q d := by
    have hlogR := log_pos hR
    have hlogRN := log_le_log (zero_lt_one.trans hR) hRN
    have h2 : log (Q/d)≤log (N:ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_left hlog hlog0.le
      nlinarith only [hlogRN,hh]
    have hz : Z≤(N:ℝ)/((d:ℝ)*log (Q/d)) := div_le_div_of_nonneg_left hNr.le
      (mul_pos hdr hlogR) (mul_le_mul_of_nonneg_left h2 hdr.le)
    have h := rawMainAtom_to_thetaAtom hN0 hd Q hR (fun _ => 1)
    simp only [rawMainAtom,mul_one] at h
    exact (mul_le_mul_of_nonneg_left hz hc0).trans_eq h
  refine ⟨(small_order N Q d X).trans (hall.trans ?_),?_⟩
  · calc
      δ*Z ≤ (2*liuUniversalProduct*ε)*Z := mul_le_mul_of_nonneg_right (min_le_left _ _) hZ
      _ = ε*((2*liuUniversalProduct)*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htheta he.le
  · have hcoeff : (K/4)*δ≤ε := by
      have h := (le_div_iff₀ hK).mp (show δ≤ε/(K/4) from min_le_right _ _)
      simpa only [mul_comm δ] using h
    calc
      _ ≤ (K/4)*thetaConversion N d*(δ*Z) :=
        mul_le_mul_of_nonneg_left hall (mul_nonneg hK.le hc0)
      _ = ((K/4)*δ)*(thetaConversion N d*Z) := by ring
      _ ≤ ε*(thetaConversion N d*Z) := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hc0 hZ)
      _ ≤ _ := mul_le_mul_of_nonneg_left hraw he.le

theorem all_marked_small_products {κ ε : ℝ} (hk : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (τ : ℝ) (p dep : ℕ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈classicalBand N →
      ∀ B : Finset (LevelIndex N n .U3 τ p dep),
      let Q := rootQ N n .U3 τ p; let X := smallProduct N κ
      (∑ l∈B,levelMark l*allSmall true N Q (wordProduct l) X)≤ε*markedTheta B ∧
      (∑ l∈B,levelMark l*((K/4)*thetaConversion N (wordProduct l)*allSmall false N Q (wordProduct l) X))
        ≤ε*markedTheta B := by
  obtain ⟨T,h4,ha⟩ := small_both_atoms hk he
  refine ⟨T,h4,?_⟩
  intro N hN n τ p dep ht ht' hn hp B
  let Q := rootQ N n .U3 τ p
  let X := smallProduct N κ
  have h2 : 2≤N := by omega
  have hQ := original_root_Q_le_target N n .U3 τ p h2 ht ht' (mem_filter.mp hp).1
  have h (l : LevelIndex N n .U3 τ p dep) := by
    have hh := actual_cubic_residual h2 ht ht' hn hp l
    exact ha N hN Q (wordProduct l) hh.1 hQ hh.2.2.1
  dsimp only
  unfold markedTheta
  simp only [mul_sum]
  constructor
  · apply sum_le_sum
    intro l _
    calc
      _ ≤ levelMark l*(ε*thetaAtom N Q (wordProduct l)) :=
        mul_le_mul_of_nonneg_left (h l).1 (mark_pos _).le
      _ = _ := by ring
  · apply sum_le_sum
    intro l _
    calc
      _ ≤ levelMark l*(ε*thetaAtom N Q (wordProduct l)) :=
        mul_le_mul_of_nonneg_left (h l).2 (mark_pos _).le
      _ = _ := by ring

end
end ImbalancedChen.Part5OriginalH430ClassicalSwitchedSmallPayment
