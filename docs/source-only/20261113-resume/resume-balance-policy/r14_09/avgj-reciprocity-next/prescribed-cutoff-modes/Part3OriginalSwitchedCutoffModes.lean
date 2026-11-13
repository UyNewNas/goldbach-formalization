import ImbalancedChen.Part3OriginalSwitchedCutoffFamily
import ImbalancedChen.Part3OriginalSwitchedExceptionalTransform

/-! Uniformly summable physical period-64 modes for both cutoffs in
the same-infinity trace. No level-dependent frequency sequence is introduced. -/
namespace ImbalancedChen.Part3.OriginalSwitchedCutoffModes20261113
noncomputable section
open Set Complex AddCircle
open scoped BigOperators ContDiff
open OriginalSwitchedCutoffFamily20261113
open P3CompactCoordinateSourceOnly (coeff64 norm_coeff64_iterated_le norm_coeff64_le)
open P3TwoLogMixed22SourceOnly (decay summable_decay basis hasSum_coeff64)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (chi e chi_eq_one chi_tsupport_subset spectralMode spectralTest)
open CommonSmoothCutoff (dyadicCutoff)

def coefficient (s : Bool) (L : ℝ) (n : ℤ) := coeff64 (profile s L) n
def mode (n : ℤ) (i : D4) : ℤ := if i=0 then n else 0

private theorem in_cell (s : Bool) (L : ℝ) :
    tsupport (profile s L) ⊆ Ioo (-32:ℝ) 32 := fun x h => by
  obtain ⟨lo,hi⟩ := support s L h
  exact ⟨by linarith,by linarith⟩

theorem rapid (j : ℕ) : ∃ C : ℝ,0<C ∧ ∀ (s : Bool) (L : ℝ) (n : ℤ),
    (1+|(n:ℝ)|)^j*‖coefficient s L n‖ ≤ C := by
  obtain ⟨A,ap,ha⟩ := uniform_jet j
  obtain ⟨B,bp,hb⟩ := uniform_jet 0
  let T := (64/Real.pi)^j*A
  refine ⟨B+T,by dsimp [T];positivity,?_⟩
  intro s L n
  by_cases z : n=0
  · subst n
    simp only [Int.cast_zero,abs_zero,add_zero,one_pow,one_mul]
    apply (norm_coeff64_le _ 0 B (fun x h => by simpa using hb s L x h)).trans
    exact le_add_of_nonneg_right (by dsimp [T];positivity)
  · have one : (1:ℝ)≤|(n:ℝ)| := by
      rw [←Int.cast_one,←Int.cast_abs,Int.cast_le]
      exact Int.one_le_abs z
    have nz : 0<|(n:ℝ)| := by linarith
    have h := norm_coeff64_iterated_le (profile s L) j ((profile_smooth s L).of_le (by simp))
      (in_cell s L) n z A (ha s L)
    have bound : (1+|(n:ℝ)|)*(64/(2*Real.pi*|(n:ℝ)|)) ≤ 64/Real.pi := by
      calc
        _ ≤ (2*|(n:ℝ)|)*(64/(2*Real.pi*|(n:ℝ)|)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by field_simp [Real.pi_ne_zero,nz.ne'] <;> ring
    calc
      _ ≤ (1+|(n:ℝ)|)^j*((64/(2*Real.pi*|(n:ℝ)|))^j*A) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((1+|(n:ℝ)|)*(64/(2*Real.pi*|(n:ℝ)|)))^j*A := by ring
      _ ≤ T := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) bound j) ap.le
      _ ≤ _ := le_add_of_nonneg_left bp.le

/-- Every prescribed polynomial seminorm of the mode weights has a
single finite price chosen before L, Y, the modulus or the two marks. -/
theorem mode_budget (r : ℕ) : ∃ A : ℝ,0<A ∧ ∀ (s : Bool) (L : ℝ),
    Summable (fun n : ℤ => (1+|(n:ℝ)|)^r*‖coefficient s L n‖) ∧
    (∑' n : ℤ, (1+|(n:ℝ)|)^r*‖coefficient s L n‖) ≤ A := by
  obtain ⟨C,cp,h⟩ := rapid (r+2)
  let D := ∑' n : ℤ,decay n
  have d0 : 0≤D := tsum_nonneg (fun n => by dsimp [decay];positivity)
  refine ⟨1+C*D,by positivity,?_⟩
  intro s L
  let F (n : ℤ) := (1+|(n:ℝ)|)^r*‖coefficient s L n‖
  have bound (n : ℤ) : F n ≤ C*decay n := by
    change F n ≤ C*(1/(1+|(n:ℝ)|)^2)
    rw [mul_one_div,le_div_iff₀ (by positivity)]
    simpa only [F,pow_add,mul_assoc,mul_left_comm,mul_comm] using h s L n
  have M := summable_decay.mul_left C
  have S := M.of_nonneg_of_le (fun n => by dsimp [F];positivity) bound
  refine ⟨S,(S.tsum_le_tsum bound M).trans ?_⟩
  rw [tsum_mul_left]
  dsimp [D]
  linarith

private theorem single_basis (n : ℤ) (x : ℝ) : basis n x=e ((n:ℝ)/64*x) := by
  rw [basis,fourier_coe_apply]
  dsimp [e]
  push_cast
  congr 1
  ring

private theorem profile_window (s : Bool) (L x : ℝ) :
    (chi x : ℂ)*profile s L x=profile s L x := by
  by_cases z : profile s L x=0
  · rw [z,mul_zero]
  · have h := support s L (subset_tsupport _ z)
    rw [chi_eq_one (show x∈Icc (1/8:ℝ) 8 from ⟨by linarith [h.1],by linarith [h.2]⟩),
      Complex.ofReal_one,one_mul]

/-- The expansion holds at every physical q, also outside the period
cell. The very same spectralTest used in the existing positive trace is
evaluated at scale Y⁻¹; its outer χ suppresses all other period copies. -/
theorem prescribed_modes (s : Bool) (L Y q : ℝ) (yp : 0<Y) :
    HasSum (fun n : ℤ => coefficient s L n*spectralTest (mode n) Y⁻¹ q) (profile s L (Y*q)) := by
  let x := Y*q
  have z (u : ℝ) (h : u∉Ioo (-32:ℝ) 32) : profile s L u=0 := by
    by_contra nn
    exact h (in_cell s L (subset_tsupport _ nn))
  have sp (n : ℤ) : spectralTest (mode n) Y⁻¹ q=(chi x:ℂ)*basis n x := by
    simp only [spectralTest,spectralMode,mode,ite_true,single_basis,div_inv_eq_mul]
    simp [x,mul_comm q Y]
  by_cases cell : x∈Ioo (-32:ℝ) 32
  · obtain ⟨_,_,h⟩ := mode_budget 0
    have summ : Summable (coeff64 (profile s L)) :=
      (show Summable (fun n : ℤ => ‖coefficient s L n‖) by simpa using (h s L).1).of_norm
    have H := (hasSum_coeff64 (profile s L) (profile_smooth s L).continuous.continuousOn
      (by rw [z (-32) (by simp),z 32 (by simp)]) summ x ⟨cell.1,cell.2.le⟩).mul_left (chi x:ℂ)
    rw [profile_window] at H
    exact H.congr_fun (fun n => by rw [sp]; dsimp only [coefficient];ring)
  · have cz : chi x=0 := P3Period64NativeReconstructionSourceOnly.chi_zero_of_notMem cell
    change HasSum _ (profile s L x)
    simpa only [sp,cz,Complex.ofReal_zero,zero_mul,mul_zero,z x cell] using
      (hasSum_zero : HasSum (fun _ : ℤ => (0:ℂ)) 0)

theorem initial_test (Y q : ℝ) (yp : 0<Y) :
    HasSum (fun n : ℤ => coefficient false 0 n*spectralTest (mode n) Y⁻¹ q) (dyadicCutoff (Y*q):ℂ) := by
  simpa [profile] using prescribed_modes false 0 Y q yp

theorem switched_test (Y D a q : ℝ) (yp : 0<Y) (dp : 0<D) (qp : 0<q) :
    HasSum (fun n : ℤ => coefficient true (Y*a/D) n*spectralTest (mode n) Y⁻¹ q)
      ((dyadicCutoff (Y*q):ℂ)*(dyadicCutoff (a/(D*q)):ℂ)) := by
  have eq : (Y*a/D)/(Y*q)=a/(D*q) := by field_simp [yp.ne',dp.ne',qp.ne'] <;> ring
  simpa only [profile,ite_true,eq] using prescribed_modes true (Y*a/D) Y q yp

/-- Literal kernel of native_weighted_row, with the original physical
argument and the divisor d used as the new spectral level. -/
theorem native_switched_test (d : ℕ+) (m n : ℕ) (Y Q x : ℝ) (yp : 0<Y) (Qp : 0<Q) (xp : 0<x) :
    HasSum (fun k : ℤ =>
      coefficient true (Y*(4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ)))/((d.val:ℝ)*Q)) k*
        spectralTest (mode k) Y⁻¹ x)
      (OriginalSwitchedExceptionalTransform20261113.switchedTest Y ((d.val:ℝ)*Q) m n x) := by
  exact switched_test Y ((d.val:ℝ)*Q) _ x yp (mul_pos (by exact_mod_cast d.property) Qp) xp

end
end ImbalancedChen.Part3.OriginalSwitchedCutoffModes20261113
