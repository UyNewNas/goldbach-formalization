import ImbalancedChen.Part3OriginalNativeCriticalInduction
import ImbalancedChen.Part3OriginalNativeJInitialRegion

/-! Original T08 Theorem J range from the critical induction and its
single outstanding positive half-order support premise. -/
namespace ImbalancedChen.Part3.OriginalNativeJFromHalfSupport20261113
noncomputable section
open Finset Real
open scoped BigOperators Classical
open OriginalNativeCriticalTransport20261113 (positiveHalfSupport)
open OriginalNativeCriticalInduction20261113 (critical)
open OriginalNativeCriticalPrices20261113 (height benchmark normPrice)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy full_window)
open OriginalSwitchedTwistedBaseline20261113 (zero_frequency)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalSwitchedMellinRows20261113 (nativeRow)
open OriginalExceptionalJNativeCompletion20261110 (pascadiJ exceptional tau classicalLevels)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)

theorem original_range_of_half_support (coeff : positiveHalfSupport) {ε : ℝ} (ep : 0<ε)
    (A : ℝ) (ap : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset ℕ+) (j : ℕ) (Q X ω : ℝ),0<Q → 0<X →
    S⊆classicalLevels Q → X≤A*max (classicalMScale j) (Q^2/classicalMScale j) →
    pascadiJ S X j ω≤C*((1+Q)*(1+classicalMScale j))^ε*(Q+classicalMScale j)*classicalMScale j := by
  obtain ⟨P,pp,F⟩ := critical coeff ep
  let K := (max 1 A)^(3/4:ℝ)
  have kpos : 0<K := Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left 1 A)) _
  refine ⟨K*P,mul_pos kpos pp,fun S j Q X ω qp xp sub xmax => ?_⟩
  let M := classicalMScale j
  let W := benchmark M Q
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have wh : height M≤W := le_max_left _ _
  have wp : 0<W := (zero_lt_one.trans_le (le_max_left 1 M)).trans_le wh
  have w : max M (Q^2/M)≤W := max_le ((le_max_right 1 M).trans wh) (le_max_right _ _)
  have xw : X/W≤A := (div_le_iff₀ wp).mpr (xmax.trans (mul_le_mul_of_nonneg_left w ap))
  have scale : (max 1 (X/W))^(3/4:ℝ)≤K := Real.rpow_le_rpow
    (zero_le_one.trans (le_max_left _ _)) (max_le_max_left 1 xw) (by norm_num)
  have ap₀ : 0<(2:ℕ)^j := pow_pos (by norm_num) _
  have ab : (2:ℕ)^j≤2^(j+1) := by rw [pow_succ];omega
  have init := F j (2^j) (2^(j+1)) le_rfl ab le_rfl Q ω qp
  let L := classicalLevels Q
  have hi := OriginalFullPositiveInitialMean20261113.transport L wp xp ω ap₀ (2^(j+1)) 0
  simp only [full_window,zero_frequency] at init hi
  have sq (Y : ℝ) (yp : 0≤Y) (q : ℕ+) : 0≤∑ i : ↥(exceptional q),Y^(tau q i.val)*
    ‖∑ m∈dyadicWindow j,nativeRow q i.val ω m‖^2 :=
    sum_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg yp _) (sq_nonneg _)
  have pos : 0≤pascadiJ L W j ω := sum_nonneg fun q _ => sq W wp.le q
  have small : pascadiJ S X j ω≤pascadiJ L X j ω :=
    sum_le_sum_of_subset_of_nonneg sub (fun q _ _ => sq X xp.le q)
  have a := (mul_le_mul_of_nonneg_right scale pos).trans (mul_le_mul_of_nonneg_left init kpos.le)
  have qh : max 1 Q≤1+Q := max_le (by linarith only [qp]) (by linarith)
  have mh : height M≤1+M := max_le (by linarith only [mp]) (by linarith)
  have cap := mul_le_mul qh mh (zero_le_one.trans (le_max_left 1 M)) (by linarith only [qp])
  have mov := Real.rpow_le_rpow (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left 1 M))) cap ep.le
  apply small.trans (hi.trans (a.trans ?_))
  change K*(P*((max 1 Q*height M)^ε*(Q+M)*M))≤(K*P)*((1+Q)*(1+M))^ε*(Q+M)*M
  have z := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left mov (mul_nonneg kpos.le pp.le)) (add_nonneg qp.le mp.le)) mp.le
  nlinarith only [z]

end
end ImbalancedChen.Part3.OriginalNativeJFromHalfSupport20261113

