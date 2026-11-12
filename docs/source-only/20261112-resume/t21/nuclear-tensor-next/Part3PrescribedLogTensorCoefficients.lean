import ImbalancedChen.Part3PrescribedLogTensorWindows
import ImbalancedChen.Part3ProductConvolutionSecondDerivatives

/-! Apply the pre-existing two-coordinate period-64 coefficient theorem
to unit translates of the logarithmic Abel lift. The first coordinate of
the old C2 operator is y; this matches the order of the lift's mixed jets. -/
namespace ImbalancedChen.Part3.PrescribedLogTensorCoefficients20261112
noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Classical ContDiff Topology
open PrescribedLogTensorWindows20261112 P3TwoLogMixed22SourceOnly
open ProductConvolutionSecondDerivatives20261026a

abbrev Modes := (ℤ × ℤ) × (ℤ × ℤ)
def cellKernel (H : ℝ → ℝ → ℂ) (i j : ℤ) (u v : ℝ) : ℂ :=
  rho v * (rho u * H ((i:ℝ)+v) ((j:ℝ)+u))
def coefficient (H : ℝ → ℝ → ℂ) (q : Modes) : ℂ :=
  C2 (cellKernel H q.1.1 q.1.2) q.2.2 q.2.1
def jet (H : ℝ → ℝ → ℂ) (r s : ℕ) (x y : ℝ) : ℂ :=
  iteratedDeriv r (fun X => iteratedDeriv s (H X) y) x
def tail (A : ℝ) (i j : ℤ) := Real.exp (-A*(|(i:ℝ)|+|(j:ℝ)|))

private theorem yjet_smooth (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H)) (s : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv s (H p.1) p.2) := by
  induction s with
  | zero => simpa only [iteratedDeriv_zero] using hH
  | succ s ih =>
    have he : (fun p : ℝ × ℝ => iteratedDeriv (s+1) (H p.1) p.2) =
        directional yDirection (fun p : ℝ × ℝ => iteratedDeriv s (H p.1) p.2) := by
      funext p
      simpa only [iteratedDeriv_succ] using (directional_y_eq_slice ih p).symm
    rw [he]
    exact directional_cinfty ih yDirection

private theorem cell_smooth (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H)) (i j : ℤ) :
    ContDiff ℝ ∞ (Function.uncurry (cellKernel H i j)) :=
  (rho_smooth.comp contDiff_snd).mul ((rho_smooth.comp contDiff_fst).mul
    (hH.comp ((contDiff_const.add contDiff_snd).prodMk (contDiff_const.add contDiff_fst))))

theorem cell_regularity (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H)) (i j : ℤ) :
    MixedC2 (cellKernel H i j) := by
  let G := cellKernel H i j
  have hg := cell_smooth H hH i j
  have h₂ : ContDiff ℝ ∞ (Function.uncurry (dx2 G)) := by
    have he : Function.uncurry (dx2 G) =
        directional xDirection (directional xDirection (Function.uncurry G)) := by
      funext p
      simpa only [dx2,Function.uncurry,iteratedDeriv_succ,iteratedDeriv_zero] using (second_x_eq_slice hg p).symm
    rw [he]; exact directional_cinfty (directional_cinfty hg _) _
  exact ⟨hg.continuous,fun _ => (hg.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp),
    fun _ => (hg.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp),h₂.continuous,
    fun _ => (h₂.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)⟩

theorem cell_support (H : ℝ → ℝ → ℂ) (i j : ℤ) : InBox (cellKernel H i j) := by
  intro p hp
  have h := mul_ne_zero_iff.mp (show rho p.2*(rho p.1*H _ _) ≠ 0 from hp)
  obtain ⟨hu₁,hu₂⟩ := rho_nonzero (mul_ne_zero_iff.mp h.2).1
  obtain ⟨hv₁,hv₂⟩ := rho_nonzero h.1
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

private def bin (n a : ℕ) (t : ℝ) : ℂ := (n.choose a : ℂ)*iteratedDeriv a rho t

/-- Formula for u derivatives on the translated tile. -/
private theorem jet_u (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (i j : ℤ) (s : ℕ) (u v : ℝ) :
    iteratedDeriv s (fun a => cellKernel H i j a v) u =
      ∑ b ∈ Finset.range (s+1), bin s b u *
        (rho v * iteratedDeriv (s-b) (H ((i:ℝ)+v)) ((j:ℝ)+u)) := by
  have hz : ContDiff ℝ ∞ (H ((i:ℝ)+v)) := hH.comp (contDiff_const.prodMk contDiff_id)
  unfold cellKernel
  rw [iteratedDeriv_const_mul_field]
  rw [show iteratedDeriv s (fun a => rho a*H ((i:ℝ)+v) ((j:ℝ)+a)) u =
      ∑ b ∈ Finset.range (s+1), (s.choose b : ℂ)*iteratedDeriv b rho u*
        iteratedDeriv (s-b) (fun a => H ((i:ℝ)+v) ((j:ℝ)+a)) u from
      iteratedDeriv_mul (rho_smooth.of_le (by simp)).contDiffAt
        ((hz.comp (contDiff_const.add contDiff_id)).of_le (by simp)).contDiffAt]
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
  rw [iteratedDeriv_comp_const_add]; unfold bin; ring

theorem cell_jet (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (i j : ℤ) (r s : ℕ) (u v : ℝ) :
    iteratedDeriv r (fun t => iteratedDeriv s (fun a => cellKernel H i j a t) u) v =
      ∑ b ∈ Finset.range (s+1), ∑ a ∈ Finset.range (r+1),
        bin s b u * bin r a v * jet H (r-a) (s-b) ((i:ℝ)+v) ((j:ℝ)+u) := by
  have reg (b : ℕ) : ContDiff ℝ ∞ (fun t => iteratedDeriv (s-b) (H ((i:ℝ)+t)) ((j:ℝ)+u)) :=
    (yjet_smooth H hH (s-b)).comp ((contDiff_const.add contDiff_id).prodMk contDiff_const)
  simp_rw [jet_u H hH]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl; intro b _
    rw [iteratedDeriv_const_mul_field]
    rw [show iteratedDeriv r (fun t => rho t*iteratedDeriv (s-b) (H ((i:ℝ)+t)) ((j:ℝ)+u)) v =
      ∑ a ∈ Finset.range (r+1), (r.choose a:ℂ)*iteratedDeriv a rho v*
        iteratedDeriv (r-a) (fun t => iteratedDeriv (s-b) (H ((i:ℝ)+t)) ((j:ℝ)+u)) v from
      iteratedDeriv_mul (rho_smooth.of_le (by simp)).contDiffAt ((reg b).of_le (by simp)).contDiffAt]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
    simp only [bin,jet,iteratedDeriv_comp_const_add]; ring
  · intro b _
    exact ((contDiff_const.mul (rho_smooth.mul (reg b))).of_le (by simp)).contDiffAt

private theorem rho_jet_bound (a : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ t ∈ Icc (-32:ℝ) 32, ‖iteratedDeriv a rho t‖ ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-32:ℝ) 32)).exists_bound_of_continuousOn
    ((rho_smooth.of_le (by simp) : ContDiff ℝ a rho).continuous_iteratedDeriv a le_rfl).continuousOn
  exact ⟨max 0 B,le_max_left _ _,fun t ht => (hB t ht).trans (le_max_right _ _)⟩

private theorem shift_tail {A u v : ℝ} (hA : 0 ≤ A) (hu : u ∈ Icc (-32:ℝ) 32)
    (hv : v ∈ Icc (-32:ℝ) 32) (i j : ℤ) :
    Real.exp (-A*(|((i:ℝ)+v)|+|((j:ℝ)+u)|)) ≤ Real.exp (64*A)*tail A i j := by
  rw [tail,← Real.exp_add,Real.exp_le_exp]
  have hi := abs_sub ((i:ℝ)+v) v
  have hj := abs_sub ((j:ℝ)+u) u
  simp only [add_sub_cancel_right] at hi hj
  have h := add_le_add hi hj
  have h1 : |u| ≤ 32 := abs_le.mpr hu
  have h2 : |v| ≤ 32 := abs_le.mpr hv
  nlinarith [mul_nonneg hA (show 0 ≤ |(i:ℝ)+v|+|(j:ℝ)+u|+64-(|(i:ℝ)|+|(j:ℝ)|) by linarith)]

def JetDecay (H : ℝ → ℝ → ℂ) (A : ℝ) : Prop :=
  ∀ r s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖jet H r s x y‖ ≤ C*Real.exp (-A*(|x|+|y|))

private theorem tile_jet_budget (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    {A : ℝ} (hA : 0 ≤ A) (dec : JetDecay H A) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : ℤ, ∀ u ∈ Icc (-32:ℝ) 32, ∀ v ∈ Icc (-32:ℝ) 32,
      ‖iteratedDeriv r (fun t => iteratedDeriv s (fun a => cellKernel H i j a t) u) v‖ ≤ C*tail A i j := by
  choose B hB hB' using rho_jet_bound
  choose D hD hD' using dec
  let K (b a : ℕ) := ((s.choose b:ℝ)*B b)*((r.choose a:ℝ)*B a)*(D (r-a) (s-b)*Real.exp (64*A))
  refine ⟨∑ b ∈ Finset.range (s+1), ∑ a ∈ Finset.range (r+1), K b a,
    Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun a _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB b))
        (mul_nonneg (Nat.cast_nonneg _) (hB a))) (mul_nonneg (hD _ _) (Real.exp_pos _).le))),?_⟩
  intro i j u hu v hv
  rw [cell_jet H hH,Finset.sum_mul]
  apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro b _
  rw [Finset.sum_mul]; apply (norm_sum_le _ _).trans; apply Finset.sum_le_sum; intro a _
  have hbin (n a : ℕ) (x : ℝ) (hx : x ∈ Icc (-32:ℝ) 32) :
      ‖bin n a x‖ ≤ (n.choose a:ℝ)*B a := by
    rw [bin,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hB' a x hx) (Nat.cast_nonneg _)
  have hg := (hD' (r-a) (s-b) ((i:ℝ)+v) ((j:ℝ)+u)).trans
    (mul_le_mul_of_nonneg_left (shift_tail hA hu hv i j) (hD _ _))
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (((s.choose b:ℝ)*B b)*((r.choose a:ℝ)*B a)) *
        (D (r-a) (s-b)*(Real.exp (64*A)*tail A i j)) :=
      mul_le_mul (mul_le_mul (hbin _ _ u hu) (hbin _ _ v hv) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hB b))) hg (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB b)) (mul_nonneg (Nat.cast_nonneg _) (hB a)))
    _ = K b a*tail A i j := by dsimp [K]; ring

theorem cell_budget (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    {A : ℝ} (hA : 0 ≤ A) (dec : JetDecay H A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : ℤ, MixedBounds (cellKernel H i j) (C*tail A i j) := by
  choose B hp hb using tile_jet_budget H hH hA dec
  let C := B 0 0 + B 0 2 + B 2 0 + B 2 2
  have h0 : 0 ≤ C := by dsimp [C]; linarith [hp 0 0,hp 0 2,hp 2 0,hp 2 2]
  refine ⟨C,h0,?_⟩; intro i j
  have h (r s : ℕ) (hrs : B r s ≤ C) (u : ℝ) (hu : u ∈ Icc (-32:ℝ) 32)
      (v : ℝ) (hv : v ∈ Icc (-32:ℝ) 32) :=
    (hb r s i j u hu v hv).trans (mul_le_mul_of_nonneg_right hrs (Real.exp_pos _).le)
  have h' (r s : ℕ) (a : B r s ≤ C) := h r s a
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [iteratedDeriv_zero] using h' 0 0 (by dsimp [C]; linarith [hp 0 2,hp 2 0,hp 2 2])
  · simpa only [dx2,iteratedDeriv_zero] using h' 0 2 (by dsimp [C]; linarith [hp 0 0,hp 2 0,hp 2 2])
  · simpa only [dy2,iteratedDeriv_zero] using h' 2 0 (by dsimp [C]; linarith [hp 0 0,hp 0 2,hp 2 2])
  · exact h' 2 2 (by dsimp [C]; linarith [hp 0 0,hp 0 2,hp 2 0])

theorem coeff_decay (H : ℝ → ℝ → ℂ) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    {A : ℝ} (hA : 0 ≤ A) (dec : JetDecay H A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Modes, ‖coefficient H q‖ ≤
      C*tail A q.1.1 q.1.2*decay q.2.1*decay q.2.2 := by
  obtain ⟨C,hC,hb⟩ := cell_budget H hH hA dec
  refine ⟨fixedCost^2*C,by positivity,?_⟩
  rintro ⟨⟨i,j⟩,⟨k,l⟩⟩
  have h := C2_product_decay (cellKernel H i j) (cell_regularity H hH i j) (cell_support H i j)
    (C*tail A i j) (mul_nonneg hC (Real.exp_pos _).le) (hb i j) l k
  simpa only [coefficient,mul_comm,mul_assoc,mul_left_comm] using h

end
end ImbalancedChen.Part3.PrescribedLogTensorCoefficients20261112
