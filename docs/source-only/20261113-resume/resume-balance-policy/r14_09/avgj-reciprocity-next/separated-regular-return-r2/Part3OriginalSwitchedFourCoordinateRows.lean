import ImbalancedChen.Part3OriginalSwitchedFourCoordinateSymbol
import ImbalancedChen.Part3OriginalSwitchedCutoffModes

/-! Separate all four coordinates, with an independent factor for
each mark and the switched level. The output weights are the actual
spectral tests at the original inverse scale. -/
namespace ImbalancedChen.Part3.OriginalSwitchedFourCoordinateRows20261113
noncomputable section
open Set Complex
open scoped BigOperators
open OriginalSwitchedFourCoordinateSymbol20261113 (symbol coefficient smooth_symbol compact_symbol support_cell lattice_budget)
open P3NativePeriod64SamplingSourceOnly (D4 E4 inside64)
open P3Period64NativeReconstructionSourceOnly (point4 phase4 e chi chi_eq_one chi_zero_of_notMem
  compact_pointwise_hasSum spectralTest spectralMode norm_e)
open OriginalSwitchedCutoffModes20261113 (mode)
open OriginalSwitchedPhysicalWindows20261113 (returnScale switched_level_window)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalExceptionalJNativeCompletion20261110 (mem_full_classical_block)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_eq_one)
open ActualNormalizedSmoothF (cutoff_nonzero_bounds)

def phase (k : D4→ℤ) (v w ζ : ℝ) := e ((k 1:ℝ)/64*v)*(e ((k 2:ℝ)/64*w)*e ((k 3:ℝ)/64*ζ))

theorem norm_phase (k : D4→ℤ) (v w ζ : ℝ) : ‖phase k v w ζ‖=1 := by simp only [phase,norm_mul,norm_e,mul_one]

theorem normalized_weights {Y v w ζ : ℝ} (yp : 0<Y) (V : v∈Icc 1 2) (W : w∈Icc 1 2)
    (Z : ζ∈Icc (1/8:ℝ) 8) (x : ℝ) :
    HasSum (fun k : D4→ℤ => (coefficient k*phase k v w ζ)*spectralTest (mode (k 0)) Y⁻¹ x)
      ((dyadicCutoff (Y*x):ℂ)*(dyadicCutoff (Real.sqrt (v*w)/(ζ*(Y*x))):ℂ)) := by
  let u := Y*x
  let p := point4 u v w ζ
  have se : symbol p=(dyadicCutoff u:ℂ)*(dyadicCutoff (Real.sqrt (v*w)/(ζ*u)):ℂ) := by
    change ((dyadicCutoff u*dyadicCutoff v*dyadicCutoff w*chi ζ*dyadicCutoff (Real.sqrt (v*w)/(ζ*u)):ℝ):ℂ)=_
    rw [dyadicCutoff_eq_one V,dyadicCutoff_eq_one W,chi_eq_one Z]
    push_cast;ring
  have win : (chi u:ℂ)*symbol p=symbol p := by
    by_cases hi : dyadicCutoff u=0
    · simp [se,hi]
    · have h := cutoff_nonzero_bounds hi
      rw [chi_eq_one (show u∈Icc (1/8:ℝ) 8 from ⟨by linarith [h.1],by linarith [h.2]⟩)]
      simp
  have row (k : D4→ℤ) : spectralTest (mode (k 0)) Y⁻¹ x=
      (chi u:ℂ)*e ((k 0:ℝ)/64*u) := by
    simp only [spectralTest,spectralMode,mode,ite_true,div_inv_eq_mul,u,mul_comm x Y]
  by_cases cell : u∈Ioo (-32:ℝ) 32
  · have pc : p∈inside64 := by
      intro i
      fin_cases i
      · exact cell
      · exact ⟨by linarith [V.1],by linarith [V.2]⟩
      · exact ⟨by linarith [W.1],by linarith [W.2]⟩
      · exact ⟨by linarith [Z.1],by linarith [Z.2]⟩
    have H := (compact_pointwise_hasSum symbol 0 (smooth_symbol.of_le (by simp)) compact_symbol support_cell p pc).mul_left (chi u:ℂ)
    rw [win,se] at H
    apply H.congr_fun
    intro k
    rw [row]
    change _=(chi u:ℂ)*(coefficient k*(e ((k 0:ℝ)/64*u)*phase k v w ζ))
    ring
  · have z : dyadicCutoff u=0 := by
      by_contra n
      have h := cutoff_nonzero_bounds n
      exact cell ⟨by linarith [h.1],by linarith [h.2]⟩
    have c := chi_zero_of_notMem cell
    change HasSum _ ((dyadicCutoff u:ℂ)*_)
    rw [z,Complex.ofReal_zero,zero_mul]
    simpa only [row,c,Complex.ofReal_zero,zero_mul,mul_zero] using
      (hasSum_zero : HasSum (fun _ : D4→ℤ => (0:ℂ)) 0)

def ratio {j : ℕ} (Y Q : ℝ) (d : ℕ+) := (d.val:ℝ)/(4*returnScale j Y Q)

private theorem reflected_ratio {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (x : ℝ) :
    Real.sqrt (((m:ℝ)/classicalMScale j)*((n:ℝ)/classicalMScale j))/
      (ratio (j:=j) Y Q d*(Y*x))=
    4*Real.pi*Real.sqrt ((m:ℝ)*(n:ℝ))/(((d.val:ℝ)*Q)*x) := by
  let M := classicalMScale j
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have r : Real.sqrt (((m:ℝ)/M)*((n:ℝ)/M))=Real.sqrt ((m:ℝ)*(n:ℝ))/M := by
    rw [show ((m:ℝ)/M)*((n:ℝ)/M)=((m:ℝ)*(n:ℝ))/(M^2) by
      rw [sq,div_mul_div_comm],
      Real.sqrt_div (by positivity),Real.sqrt_sq mp.le]
  change Real.sqrt (((m:ℝ)/M)*((n:ℝ)/M))/(((d.val:ℝ)/(4*(Real.pi*M*Y/Q)))*(Y*x))=_
  rw [r]
  by_cases z : x=0
  · simp [z]
  · field_simp [yp.ne',qp.ne',mp.ne',Real.pi_ne_zero,show (d.val:ℝ)≠0 by exact_mod_cast d.property.ne',z] <;> ring

theorem physical_weights {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (x : ℝ) :
    let M := classicalMScale j
    let ζ := ratio (j:=j) Y Q d
    HasSum (fun k : D4→ℤ =>
      (if ζ∈Icc (1/8:ℝ) 8 then coefficient k*phase k ((m:ℝ)/M) ((n:ℝ)/M) ζ else 0)*
        spectralTest (mode (k 0)) Y⁻¹ x) (switchedTest Y ((d.val:ℝ)*Q) m n x) := by
  classical
  let M := classicalMScale j
  let C := returnScale j Y Q
  let ζ := ratio (j:=j) Y Q d
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have cp : 0<C := div_pos (mul_pos (mul_pos Real.pi_pos mp) yp) qp
  have band (a : ℕ) (ha : a∈dyadicWindow j) : (a:ℝ)/M∈Icc 1 2 := by
    have h := (mem_full_classical_block j a).mp ha
    exact ⟨(le_div_iff₀ mp).mpr (by simpa only [one_mul] using h.1.le),(div_le_iff₀ mp).mpr h.2⟩
  by_cases h : ζ∈Icc (1/8:ℝ) 8
  · simp only [if_pos h]
    have E := normalized_weights yp (band m hm) (band n hn) h x
    rw [reflected_ratio hm hn yp qp d] at E
    exact E
  · have z : switchedTest Y ((d.val:ℝ)*Q) m n x=0 := by
      by_contra nz
      have p := switched_level_window hm hn yp qp d nz
      apply h
      change (1/8:ℝ)≤(d.val:ℝ)/(4*C) ∧ (d.val:ℝ)/(4*C)≤8
      exact ⟨(le_div_iff₀ (by positivity)).mpr (by linarith only [p.1,cp]),
        (div_le_iff₀ (by positivity)).mpr (by linarith only [p.2])⟩
    simp only [if_neg h,zero_mul,z,hasSum_zero]

end
end ImbalancedChen.Part3.OriginalSwitchedFourCoordinateRows20261113
