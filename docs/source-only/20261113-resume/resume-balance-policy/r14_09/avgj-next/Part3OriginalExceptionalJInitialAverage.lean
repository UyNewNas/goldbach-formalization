import ImbalancedChen.Part3OriginalFixedLevelExceptionalSieve
import ImbalancedChen.Part3OriginalExceptionalJNativeCompletion
import Batteries.Tactic.OpenPrivate

/-! The fixed-level estimate in the native finite exceptional indexing,
and the initial level average on the literal positive-frequency block. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalJInitialAverage20261113
open Finset
open scoped BigOperators MatrixGroups Classical
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisWhittakerCoefficients20261102 ActualContinuousPoincarePairing20261110
open OriginalExceptionalJNativeCompletion20261110 OriginalFixedLevelExceptionalSieve20261113
open OriginalUnitStripPacketMass20261113 OriginalClassicalSpectralSupports20261102
open MediumGlobalDyadicOwnership20261028 ActualIntervalGeometricSumSourceOnly
open private phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

/-- Reindex the published signed estimate by the source's natural frequencies.
The sign applies to the Fourier index and the coefficient is chosen once per row. -/
theorem signed_row (z : ℕ+) (one : Bool) {L X A : ℝ} (hL : 0 < L) (hX : 0 < X)
    (range : X ≤ A * max 1 ((z.val : ℝ)/L)) (S : Finset ℕ) (w : ℕ → ℂ)
    (s : ℤ) (hs : s = 1 ∨ s = -1) (band : ∀ n ∈ S, L < (n : ℝ) ∧ (n : ℝ) ≤ 2*L) :
    (∑ i : ↥(exceptional z), X ^ tau z i.val *
      ‖∑ n ∈ S, w n * basisR z z.property i.val (originalFrame one) (s*(n : ℤ))‖^2) ≤
        (sieveConstant*(1+max 1 A))*(1+L/(z.val : ℝ)) * ∑ n ∈ S, ‖w n‖^2 := by
  classical
  let f (n : ℕ) : ℤ := s*(n : ℤ)
  have abs_f (n : ℕ) : (f n).natAbs = n := by
    rcases hs with h | h <;> simp [f,h]
  have abs_real (n : ℕ) : |((f n : ℤ) : ℝ)| = (n : ℝ) := by
    rcases hs with h | h <;> simp [f,h]
  have hinj : Function.Injective f := by
    intro n n' he
    simpa only [abs_f] using congrArg Int.natAbs he
  let a (m : ℤ) := w m.natAbs
  have hband (m) (hm : m ∈ S.image f) : L < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2*L := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    simpa only [abs_real] using band n hn
  obtain ⟨summ,price⟩ := manuscript_range z.val one hL hX range (S.image f) a hband
  have hmass : coeffMass (S.image f) a = ∑ n ∈ S, ‖w n‖^2 := by
    rw [coeffMass, Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simp only [a,abs_f]
  have hfunc (i : actualCuspBasisIndex z z.property) :
      functional z.val one (S.image f) a i =
        ∑ n ∈ S, w n * basisR z z.property i (originalFrame one) (f n) := by
    rw [functional, Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simp only [a,abs_f]
  have hpart := summ.sum_le_tsum (exceptional z) (fun i _ => by
    unfold term
    split <;> positivity)
  rw [hmass] at price
  refine (le_of_eq ?_).trans (hpart.trans price)
  rw [Finset.univ_eq_attach, Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro i hi
  have hex : ActualUnitBandSpectralMass20261112.exceptional z.val i :=
    ((mem_exceptional z i).mp hi).2
  rw [term, if_pos hex,hfunc] <;> rfl

private theorem card_levels {Q : ℝ} (hQ : 0 < Q) : ((classicalLevels Q).card : ℝ) ≤ 2*Q := by
  have hcard : (classicalLevels Q).card ≤ (Finset.Ioc 0 ⌊2*Q⌋₊).card :=
    Finset.card_le_card_of_injOn (fun z : ℕ+ => z.val)
      (fun z hz => Finset.mem_Ioc.mpr ⟨z.property,Nat.le_floor ((mem_classicalLevels Q z).mp hz).2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
  have hnat : (classicalLevels Q).card ≤ ⌊2*Q⌋₊ := by
    simpa only [Nat.card_Ioc,Nat.sub_zero] using hcard
  exact (show ((classicalLevels Q).card : ℝ) ≤ (⌊2*Q⌋₊ : ℝ) by exact_mod_cast hnat).trans
    (Nat.floor_le (by linarith))

/-- Initial bound for the level-average induction in §10(vii). The entire
printed dyadic energy, including its factor four, has the target size
at weights up to max(1,Q/M). A fixed implied range constant is explicit. -/
theorem initial_average {Q X A : ℝ} (hQ : 1/2 ≤ Q) (hX : 0 < X) (hA : 0 ≤ A)
    (j : ℕ) (ω : ℝ) (range : X ≤ A * max 1 (Q/classicalMScale j)) :
    pascadiJ (classicalLevels Q) X j ω ≤
      16*(sieveConstant*(1+max 1 A))*(Q+classicalMScale j)*classicalMScale j := by
  let M := classicalMScale j
  let C := sieveConstant*(1+max 1 A)
  have qpos : 0 < Q := by linarith
  have mpos : 0 < M := lt_of_lt_of_le (by norm_num) (classicalMScale_bounds j).1
  have cn : 0 ≤ C := mul_nonneg sieveConstant_pos.le (by
    have h := le_max_left (1:ℝ) A
    linarith)
  have card : ((dyadicWindow j).card : ℝ) ≤ 2*M := by
    have he : (dyadicWindow j).card = 2^j := by
      change (Finset.Ico (2^j) (2^(j+1)) : Finset ℕ).card = 2^j
      rw [Nat.card_Ico,pow_succ]
      omega
    rw [he]
    linarith only [(classicalMScale_bounds j).2.1]
  have phaseMass : (∑ n ∈ dyadicWindow j, ‖phaseAt ω n‖^2) = ((dyadicWindow j).card : ℝ) := by
    simp [phaseAt_norm]
  have base (z : ℕ+) (hz : z ∈ classicalLevels Q) :
      (∑ i : ↥(exceptional z), X ^ tau z i.val * ‖fullM j ω z i.val‖^2) ≤
        C * (1+M/Q) * (2*M) := by
    have qz := ((mem_classicalLevels Q z).mp hz).1.le
    have bound : X ≤ A*max 1 ((z.val : ℝ)/M) := range.trans
      (mul_le_mul_of_nonneg_left (max_le_max_left _ (div_le_div_of_nonneg_right qz mpos.le)) hA)
    have h := signed_row z false mpos hX bound (dyadicWindow j) (phaseAt ω)
      1 (Or.inl rfl) (fun n hn => (mem_full_classical_block j n).mp hn)
    simp only [one_mul,originalFrame,Bool.false_eq_true,if_false,phaseMass] at h
    have hratio : M/(z.val : ℝ) ≤ M/Q := div_le_div_of_nonneg_left mpos.le qpos qz
    exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_left hratio 1) cn) card
      (Nat.cast_nonneg _) (mul_nonneg cn (by positivity)))
  rw [pascadiJ_eq_four_mul]
  have sumBound : fullJ (classicalLevels Q) X j ω ≤
      ((classicalLevels Q).card : ℝ)*(C*(1+M/Q)*(2*M)) := by
    unfold fullJ
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      (Finset.sum_le_sum (fun z hz => base z hz))
  have bnon : 0 ≤ C*(1+M/Q)*(2*M) := by positivity
  have hh := sumBound.trans (mul_le_mul_of_nonneg_right (card_levels qpos) bnon)
  calc
    _ ≤ 4 * (2*Q * (C*(1+M/Q)*(2*M))) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by change _ = 16*C*(Q+M)*M; field_simp [qpos.ne'] <;> ring

end ImbalancedChen.Part3.OriginalExceptionalJInitialAverage20261113
end
