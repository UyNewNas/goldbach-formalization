import ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds

/-! Every true factor on a logarithmic dyadic chart of the whole marked
word. Centres can vary freely. Uniform bounds use the original fixed gate
widths and one factor-two physical prime cutoff at every genuine position. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerProfile
noncomputable section
open Finset Set Filter Real Wu2008DoubleSieve
open P4B
open P2SeedOmegaLiteralFibre (a0 b)
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothSharpGates (code)
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothEulerBounds (E BoundedDerivatives)
open scoped Classical Topology BigOperators ContDiff

abbrev Param (k : ℕ) := {N : ℕ // 2≤N} × E k
def split {s r : ℕ} (v : E (rank s r)) : Point s r := (first v,qVec v,rVec v)
def coord {k : ℕ} (i : Fin k) : E k →L[ℝ] ℝ := ContinuousLinearMap.proj i

def row {s r : ℕ} : Gate s r → E (rank s r) →L[ℝ] ℝ
  | .outerLo => coord 0
  | .outerHi => -coord 0
  | .primeLo i => a0 • coord 0+coord (qi i)
  | .primeHi i => -(b • coord 0+coord (qi i))
  | .colourLo i j => colourPower j • coord 0+coord (qi i)
  | .colourHi i j => -(colourPower j • coord 0+coord (qi i))
  | .primeOrder i j => coord (qi j)-coord (qi i)
  | .tailOrder i j => coord (ri j)-coord (ri i)
  | .penultimate i j => coord (ri j)-coord (qi i)

def logCoords {s r : ℕ} (a : Param (rank s r)) (u : E (rank s r)) : Point s r :=
  split (fun i => (a.2 i+u i)/log (a.1.val:ℝ))
def ratios {s r : ℕ} (a : Param (rank s r)) (u : E (rank s r)) : Point s r :=
  split (fun i => exp (a.2 i+u i-(1/90)*log (a.1.val:ℝ)))
def radial {k : ℕ} (a : Param k) (u : E k) := exp ((∑ i,a.2 i+u i)-log (a.1.val:ℝ))
def bump (v : ℝ) := smoothGateUpperStep 1 (v/log 2)-smoothGateUpperStep 1 (v/log 2-1)

def chart {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) (a : Param (rank s r)) (u : E (rank s r)) :=
  (∏ i,bump (u i))*outerWeight C ν δ h c (logCoords a u) (ratios a u) (radial a u)

theorem margin_on_chart {s r : ℕ} (g : Gate s r) (a : Param (rank s r)) (u : E (rank s r)) (ν : ℝ) :
    margin ν (logCoords a u) g=margin ν (logCoords a 0) g+
      (1/log (a.1.val:ℝ))*(row g u) := by
  cases g <;> simp [margin,powerMargin,logCoords,split,row,coord,first,qVec,rVec,
    smul_eq_mul,add_div,div_eq_mul_inv] <;> ring

theorem gate_budget {s r : ℕ} (C : Fin s → ℕ) (ν : ℝ) {δ : ℝ} (hd : 0<δ) :
    BoundedDerivatives (fun (a : Param (rank s r)) u => weight C ν δ (logCoords a u)) := by
  unfold weight
  apply Part5OriginalH430ClassicalSmoothEulerBounds.prod
  intro g
  simp_rw [margin_on_chart]
  apply Part5OriginalH430ClassicalSmoothEulerBounds.affine
    (Part5OriginalH430ClassicalSmoothEulerBounds.step_bound hd) _ _ _ (R:=1/log 2)
    (one_div_pos.mpr (log_pos (by norm_num : (1:ℝ)<2))).le
  intro a
  have hN : (2:ℝ)≤a.1.val := by exact_mod_cast a.1.property
  have hL := log_le_log (by norm_num : (0:ℝ)<2) hN
  have hpos := log_pos (by norm_num : (1:ℝ)<2)
  rw [abs_of_nonneg (one_div_nonneg.mpr (hpos.le.trans hL))]
  exact one_div_le_one_div_of_le hpos hL

theorem floor_budget {s r : ℕ} :
    BoundedDerivatives (fun (a : Param (rank s r)) u => allFloors (ratios a u)) := by
  have H (i : Fin (rank s r)) : BoundedDerivatives (fun (a : Param (rank s r)) u =>
      floorGate (exp (a.2 i+u i-(1/90)*log (a.1.val:ℝ)))) := by
    have hh := Part5OriginalH430ClassicalSmoothEulerBounds.affine
      Part5OriginalH430ClassicalSmoothEulerBounds.log_floor_bound
      (fun a : Param (rank s r) => a.2 i-(1/90)*log (a.1.val:ℝ)) (fun _ => (1:ℝ))
      (coord i) zero_le_one (fun _ => by norm_num)
    convert hh using 1
    funext a u
    dsimp only [coord,ContinuousLinearMap.proj_apply,one_mul]
    apply congrArg floorGate
    apply congrArg Real.exp
    ring
  exact Part5OriginalH430ClassicalSmoothEulerBounds.mul
    (Part5OriginalH430ClassicalSmoothEulerBounds.mul (H 0)
      (Part5OriginalH430ClassicalSmoothEulerBounds.prod univ _ (fun i : Fin s => H (qi i))))
    (Part5OriginalH430ClassicalSmoothEulerBounds.prod univ _ (fun i : Fin r => H (ri i)))

private theorem radial_budget {k : ℕ} {f : ℝ → ℝ}
    (hf : Part5OriginalH430ClassicalSmoothEulerBounds.ScalarBound (fun v => f (exp v))) :
    BoundedDerivatives (fun (a : Param k) u => f (radial a u)) := by
  let L : E k →L[ℝ] ℝ := ∑ i : Fin k,coord i
  have hh := Part5OriginalH430ClassicalSmoothEulerBounds.affine hf
    (fun a : Param k => (∑ i,a.2 i)-log (a.1.val:ℝ)) (fun _ => (1:ℝ))
    L zero_le_one (fun _ => by norm_num)
  have he (a : Param k) (u : E k) :
      exp (((∑ i,a.2 i)-log (a.1.val:ℝ))+1*L u)=radial a u := by
    unfold radial
    apply congrArg Real.exp
    simp [L,ContinuousLinearMap.sum_apply,coord,sum_add_distrib] <;> ring
  simpa only [he] using hh

theorem chart_budget {s r : ℕ} (C : Fin s → ℕ) (ν : ℝ) {δ h c : ℝ}
    (hd : 0<δ) (hh : 0<h) (hc : 0<c) :
    BoundedDerivatives (fun (a : Param (rank s r)) u => chart C ν δ h c a u) := by
  have hB := radial_budget (k:=rank s r) (Part5OriginalH430ClassicalSmoothEulerBounds.log_thin_bound hc)
  have hA := radial_budget (k:=rank s r) (Part5OriginalH430ClassicalSmoothEulerBounds.log_radial_bound hh)
  have hX := Part5OriginalH430ClassicalSmoothEulerBounds.mul (floor_budget (s:=s) (r:=r))
    (Part5OriginalH430ClassicalSmoothEulerBounds.add hB (Part5OriginalH430ClassicalSmoothEulerBounds.mul
      (Part5OriginalH430ClassicalSmoothEulerBounds.sub Part5OriginalH430ClassicalSmoothEulerBounds.one hB)
      (Part5OriginalH430ClassicalSmoothEulerBounds.mul hA (gate_budget C ν hd))))
  apply Part5OriginalH430ClassicalSmoothEulerBounds.mul _ hX
  apply Part5OriginalH430ClassicalSmoothEulerBounds.prod
  intro i
  have H (off : ℝ) := Part5OriginalH430ClassicalSmoothEulerBounds.affine
    (Part5OriginalH430ClassicalSmoothEulerBounds.step_bound (by norm_num : (0:ℝ)<1))
    (fun _ : Param (rank s r) => off) (fun _ => (1:ℝ)) ((1/log 2) • coord i)
    zero_le_one (fun _ => by norm_num)
  have h0 := H 0
  have h1 := H (-1)
  convert Part5OriginalH430ClassicalSmoothEulerBounds.sub h0 h1 using 1
  funext a u
  simp [bump,coord,smul_eq_mul,div_eq_mul_inv]
  <;> congr 1 <;> ring

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerProfile

