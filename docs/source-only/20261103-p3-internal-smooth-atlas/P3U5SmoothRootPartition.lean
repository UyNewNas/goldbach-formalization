import ImbalancedChen.P3U5RootAtlas
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import ImbalancedChen.AffinePrimeGates

/-!
Manuscript-internal / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
A genuine C-infinity partition for the entire original four-owner atlas.
The same physical level and coefficient are never averaged or replaced.
All boundary values remain in exact finite error identities. The common
wall majorant is smooth; its later harmonic payment is a separate module.
-/
namespace ImbalancedChen.P3U5SmoothRootPartition
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
open P3U5RootAtlas P2GammaU5PlateauGeometry

abbrev Point := Fin 2 → ℝ

def wallForm : Fin 4 → (Point →L[ℝ] ℝ) :=
  ![ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1,
    (1/2 : ℝ) • ContinuousLinearMap.proj 1,
    (-3/2 : ℝ) • (ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1),
    (3/2 : ℝ) • ContinuousLinearMap.proj 0 + (2 : ℝ) • ContinuousLinearMap.proj 1]

def wallOffset : Fin 4 → ℝ :=
  ![VariableEnvelope.mu, plateauLevel-1/2, plateauLevel-57/64, 25/64]

def margin (j : Fin 4) (x : Point) : ℝ := wallOffset j - wallForm j x

theorem margins_original (x : Point) :
    margin 0 x = VariableEnvelope.mu-(x 1+x 0) ∧
    margin 1 x = plateauLevel-VariableEnvelope.A (x 1) ∧
    margin 2 x = plateauLevel-VariableEnvelope.C (x 1+x 0) ∧
    margin 3 x = VariableEnvelope.C (x 1+x 0)-VariableEnvelope.A (x 1) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [margin,wallForm,wallOffset] <;> ring
  · simp [margin,wallForm,wallOffset,VariableEnvelope.A] <;> ring
  · simp [margin,wallForm,wallOffset,VariableEnvelope.C] <;> ring
  · simp [margin,wallForm,wallOffset,VariableEnvelope.A,VariableEnvelope.C] <;> ring

theorem wallForm_ne_zero (j : Fin 4) : wallForm j ≠ 0 := by
  intro heq
  have h := congrArg (fun L : Point →L[ℝ] ℝ => L ![1,1]) heq
  fin_cases j <;> norm_num [wallForm] at h

/-- Boolean values include equality, matching the old owner convention. -/
def bit (z : ℝ) : ℝ := if 0 ≤ z then 1 else 0

def circuit (l : Lane) (v : Fin 4 → ℝ) : ℝ :=
  match l with
  | .rise => v 0
  | .plateau => (1-v 0)*(v 1*v 2)
  | .fall => (1-v 0)*(1-v 1*v 2)*v 3
  | .head => (1-v 0)*(1-v 1*v 2)*(1-v 3)

theorem sum_lanes_eval (f : Lane → ℝ) :
    (∑ l : Lane,f l) = f .rise+f .plateau+f .fall+f .head := by
  have hu : (Finset.univ : Finset Lane) = {.rise,.plateau,.fall,.head} := by
    ext l
    cases l <;> simp
  rw [hu]
  simp [add_assoc]

theorem circuit_sum (v : Fin 4 → ℝ) : (∑ l : Lane,circuit l v) = 1 := by
  rw [sum_lanes_eval]
  simp only [circuit]
  ring

private theorem unit_mul {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    0 ≤ a*b ∧ a*b ≤ 1 :=
  ⟨mul_nonneg ha.1 hb.1,(mul_le_mul ha.2 hb.2 hb.1 zero_le_one).trans_eq (by norm_num)⟩

private theorem unit_compl {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) :
    0 ≤ 1-a ∧ 1-a ≤ 1 := by constructor <;> linarith

theorem circuit_range (l : Lane) (v : Fin 4 → ℝ)
    (hv : ∀ j,0 ≤ v j ∧ v j ≤ 1) : 0 ≤ circuit l v ∧ circuit l v ≤ 1 := by
  have hp := unit_mul (hv 1) (hv 2)
  cases l with
  | rise => exact hv 0
  | plateau => exact unit_mul (unit_compl (hv 0)) hp
  | fall => exact unit_mul (unit_mul (unit_compl (hv 0)) (unit_compl hp)) (hv 3)
  | head => exact unit_mul (unit_mul (unit_compl (hv 0)) (unit_compl hp)) (unit_compl (hv 3))

theorem circuit_bits_original (l : Lane) (x : Point) :
    circuit l (fun j => bit (margin j x)) =
      if owner (x 0) (x 1) = l then 1 else 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := margins_original x
  by_cases hs : x 1+x 0 ≤ VariableEnvelope.mu <;>
    by_cases ha : VariableEnvelope.A (x 1) ≤ plateauLevel <;>
    by_cases hc : VariableEnvelope.C (x 1+x 0) ≤ plateauLevel <;>
    by_cases hd : VariableEnvelope.A (x 1) ≤ VariableEnvelope.C (x 1+x 0) <;>
    cases l <;> simp [circuit,bit,h0,h1,h2,h3,sub_nonneg,owner,hs,ha,hc,hd]

/-- A smooth one-sided step; it does NOT reproduce the sharp equality face. -/
def gate (m : ℕ) (j : Fin 4) (x : Point) : ℝ :=
  Real.smoothTransition ((m+1 : ℝ)*margin j x)

def smoothWeight (m : ℕ) (l : Lane) (x : Point) : ℝ :=
  circuit l (fun j => gate m j x)

/-- The equality face has edge=1, rather than being deleted. -/
def edge (z : ℝ) : ℝ := 1-Real.smoothTransition z-Real.smoothTransition (-z)

def wallBudget (m : ℕ) (x : Point) : ℝ :=
  ∑ j : Fin 4,edge ((m+1 : ℝ)*margin j x)

theorem edge_range (z : ℝ) : 0 ≤ edge z ∧ edge z ≤ 1 := by
  by_cases hz : 0 ≤ z
  · rw [edge,Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hz),sub_zero]
    constructor <;> linarith [Real.smoothTransition.nonneg z,Real.smoothTransition.le_one z]
  · have hzn : z ≤ 0 := le_of_not_ge hz
    rw [edge,Real.smoothTransition.zero_of_nonpos hzn,sub_zero]
    constructor <;> linarith [Real.smoothTransition.nonneg (-z),Real.smoothTransition.le_one (-z)]

theorem edge_zero : edge 0 = 1 := by
  simp [edge,Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]

theorem edge_eq_zero_of_abs_ge_one {z : ℝ} (hz : 1 ≤ |z|) : edge z = 0 := by
  rcases le_total 0 z with hp | hn
  · rw [abs_of_nonneg hp] at hz
    rw [edge,Real.smoothTransition.one_of_one_le hz,
      Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hp)]
    ring
  · rw [abs_of_nonpos hn] at hz
    rw [edge,Real.smoothTransition.zero_of_nonpos hn,Real.smoothTransition.one_of_one_le hz]
    ring

theorem gate_range (m : ℕ) (j : Fin 4) (x : Point) :
    0 ≤ gate m j x ∧ gate m j x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem smoothWeight_range (m : ℕ) (l : Lane) (x : Point) :
    0 ≤ smoothWeight m l x ∧ smoothWeight m l x ≤ 1 :=
  circuit_range l _ (fun j => gate_range m j x)

theorem smoothWeight_sum (m : ℕ) (x : Point) : (∑ l : Lane,smoothWeight m l x) = 1 :=
  circuit_sum _

theorem wallBudget_range (m : ℕ) (x : Point) :
    0 ≤ wallBudget m x ∧ wallBudget m x ≤ 4 := by
  refine ⟨Finset.sum_nonneg (fun j _ => (edge_range _).1),?_⟩
  calc
    _ ≤ ∑ _j : Fin 4,(1 : ℝ) := Finset.sum_le_sum (fun j _ => (edge_range _).2)
    _ = 4 := by simp

theorem gate_contDiff (m : ℕ) (j : Fin 4) : ContDiff ℝ ∞ (gate m j) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub (wallForm j).contDiff))

theorem smoothWeight_contDiff (m : ℕ) (l : Lane) : ContDiff ℝ ∞ (smoothWeight m l) := by
  have h0 := gate_contDiff m 0
  have h1 := gate_contDiff m 1
  have h2 := gate_contDiff m 2
  have h3 := gate_contDiff m 3
  cases l with
  | rise => exact h0
  | plateau => exact (contDiff_const.sub h0).mul (h1.mul h2)
  | fall => exact ((contDiff_const.sub h0).mul (contDiff_const.sub (h1.mul h2))).mul h3
  | head => exact ((contDiff_const.sub h0).mul (contDiff_const.sub (h1.mul h2))).mul
      (contDiff_const.sub h3)

theorem wallBudget_contDiff (m : ℕ) : ContDiff ℝ ∞ (wallBudget m) := by
  have he (j : Fin 4) : ContDiff ℝ ∞ (fun x : Point => edge ((m+1 : ℝ)*margin j x)) :=
    (contDiff_const.sub (gate_contDiff m j)).sub
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul (contDiff_const.sub (wallForm j).contDiff)).neg)
  have hs : wallBudget m = fun x : Point =>
      edge ((m+1 : ℝ)*margin 0 x)+(edge ((m+1 : ℝ)*margin 1 x)+
      (edge ((m+1 : ℝ)*margin 2 x)+edge ((m+1 : ℝ)*margin 3 x))) := by
    funext x
    simp [wallBudget,Fin.sum_univ_succ]
  rw [hs]
  exact (he 0).add ((he 1).add ((he 2).add (he 3)))

private theorem abs_compl_sub (a b : ℝ) : |(1-a)-(1-b)| = |a-b| := by
  rw [show (1-a)-(1-b)=-(a-b) by ring,abs_neg]

private theorem product_error {a b c d : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add _ _
    _ = a*|b-d|+|a-c|*d := by rw [abs_mul,abs_mul,abs_of_nonneg ha.1,abs_of_nonneg hd.1]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_right ha.2 (abs_nonneg (b-d))
      have hc := mul_le_mul_of_nonneg_left hd.2 (abs_nonneg (a-c))
      nlinarith

/-- A fixed four-input circuit bound; no arithmetic threshold or count occurs. -/
theorem circuit_error (l : Lane) (v w : Fin 4 → ℝ)
    (hv : ∀ j,0 ≤ v j ∧ v j ≤ 1) (hw : ∀ j,0 ≤ w j ∧ w j ≤ 1) :
    |circuit l v-circuit l w| ≤ ∑ j : Fin 4,|v j-w j| := by
  have hpv := unit_mul (hv 1) (hv 2)
  have hpw := unit_mul (hw 1) (hw 2)
  have hp := product_error (a:=v 1) (b:=v 2) (c:=w 1) (d:=w 2) (hv 1) (hw 2)
  have hleft := product_error (a:=1-v 0) (b:=1-v 1*v 2)
    (c:=1-w 0) (d:=1-w 1*w 2) (unit_compl (hv 0)) (unit_compl hpw)
  rw [abs_compl_sub,abs_compl_sub] at hleft
  have hbasev := unit_mul (unit_compl (hv 0)) (unit_compl hpv)
  have hs : (∑ j : Fin 4,|v j-w j|) =
      |v 0-w 0|+(|v 1-w 1|+(|v 2-w 2|+|v 3-w 3|)) := by
    simp [Fin.sum_univ_succ]
  rw [hs]
  cases l with
  | rise => dsimp [circuit]; linarith [abs_nonneg (v 1-w 1),abs_nonneg (v 2-w 2),abs_nonneg (v 3-w 3)]
  | plateau =>
      have ht := product_error (a:=1-v 0) (b:=v 1*v 2) (c:=1-w 0) (d:=w 1*w 2)
        (unit_compl (hv 0)) hpw
      rw [abs_compl_sub] at ht
      dsimp [circuit]
      linarith [abs_nonneg (v 3-w 3)]
  | fall =>
      have ht := product_error (a:=(1-v 0)*(1-v 1*v 2)) (b:=v 3)
        (c:=(1-w 0)*(1-w 1*w 2)) (d:=w 3) hbasev (hw 3)
      dsimp [circuit]
      linarith
  | head =>
      have ht := product_error (a:=(1-v 0)*(1-v 1*v 2)) (b:=1-v 3)
        (c:=(1-w 0)*(1-w 1*w 2)) (d:=1-w 3) hbasev (unit_compl (hw 3))
      rw [abs_compl_sub] at ht
      dsimp [circuit]
      linarith

theorem bit_gate_error (m : ℕ) (z : ℝ) :
    |bit z-Real.smoothTransition ((m+1 : ℝ)*z)| ≤ edge ((m+1 : ℝ)*z) := by
  by_cases hz : 0 ≤ z
  · have hpos : 0 ≤ (m+1 : ℝ)*z := mul_nonneg (by positivity) hz
    simp only [bit,if_pos hz,edge,
      Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hpos),sub_zero,
      abs_of_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _)),le_refl]
  · have hneg : (m+1 : ℝ)*z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hz)
    rw [bit,if_neg hz,Real.smoothTransition.zero_of_nonpos hneg,sub_zero,abs_zero]
    exact (edge_range _).1

/-- The old equality owners are kept; boundary points cost a genuine edge term. -/
theorem smooth_owner_error (m : ℕ) (l : Lane) (x : Point) :
    |(if owner (x 0) (x 1)=l then (1 : ℝ) else 0)-smoothWeight m l x| ≤ wallBudget m x := by
  rw [← circuit_bits_original l x]
  apply (circuit_error l (fun j => bit (margin j x)) (fun j => gate m j x)
    (by intro j; unfold bit; split_ifs <;> norm_num) (fun j => gate_range m j x)).trans
  exact Finset.sum_le_sum (fun j _ => bit_gate_error m (margin j x))

/-- Away from the four explicit transition strips, the smoothed chart
is exactly its old owner. No branch-specific licence is asserted inside them. -/
theorem smoothWeight_eq_owner_off_strips (m : ℕ) (l : Lane) (x : Point)
    (hclear : ∀ j : Fin 4,1 ≤ |(m+1 : ℝ)*margin j x|) :
    smoothWeight m l x = if owner (x 0) (x 1)=l then 1 else 0 := by
  have hb : wallBudget m x=0 :=
    Finset.sum_eq_zero (fun j _ => edge_eq_zero_of_abs_ge_one (hclear j))
  have he := smooth_owner_error m l x
  rw [hb] at he
  have hz := abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
  exact (sub_eq_zero.mp hz).symm

/-- A proper affine wall is small only after integration, not pointwise. -/
theorem wallBudget_ge_one_on_wall (m : ℕ) (x : Point) (j : Fin 4)
    (hj : margin j x=0) : 1 ≤ wallBudget m x := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => (edge_range ((m+1 : ℝ)*margin i x)).1)
    (Finset.mem_univ j)
  simpa only [hj,mul_zero,edge_zero] using h

/-- An explicit eventual constant plateau, avoiding a rate claim at a wall. -/
theorem tendsto_edge_scaled {z : ℝ} (hz : z ≠ 0) :
    Tendsto (fun m : ℕ => edge ((m+1 : ℝ)*z)) atTop (𝓝 0) := by
  have hp : 0 < |z| := abs_pos.mpr hz
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (Nat.ceil (1/|z|))] with m hm
  have hmR : 1/|z| ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hmul : 1 ≤ (m+1 : ℝ)*|z| := by
    have h := (div_le_iff₀ hp).mp hmR
    nlinarith
  exact (edge_eq_zero_of_abs_ge_one (by
    simpa only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ m+1 by positivity)] using hmul)).symm

theorem tendsto_wallBudget {x : Point} (hx : ∀ j,margin j x ≠ 0) :
    Tendsto (fun m : ℕ => wallBudget m x) atTop (𝓝 0) := by
  simpa only [wallBudget,Finset.sum_const_zero] using
    tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun j _ => tendsto_edge_scaled (hx j))

end
end ImbalancedChen.P3U5SmoothRootPartition
