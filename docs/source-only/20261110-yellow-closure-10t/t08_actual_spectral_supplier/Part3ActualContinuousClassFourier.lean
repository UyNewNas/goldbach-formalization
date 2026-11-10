import ImbalancedChen.Part3ActualOrdinaryContinuousModes

/-! The normalized Fourier coefficient in both original observing frames
for every orthogonal Young channel and every ordinary native cusp. Each
coefficient is extracted as a physical integral times its radial term. -/
namespace ImbalancedChen.Part3.ActualContinuousClassFourier20261110

noncomputable section
open Complex Set Matrix UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualYoungCriticalProjection20261110 ActualYoungFormalClass20261110
open ActualCriticalCuspEvaluation20261110 ActualYoungCriticalD20261110
open ActualYoungCriticalCusps20261110 ActualYoungDilationInverse20261110
open ActualCuspDenominatorClasses20261110 ActualOrdinaryContinuousModes20261110
open ActualEisensteinFourierInterchange20261025a FrickeNormalizer
open ActualCharacterCuspExpansion20261110 ActualFrickeCuspPhase20261025a
open PowerSeedFourierLaplaceFubini

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
local instance conductorNe {N : ℕ} [NeZero N] (i : CharacterSlots N) : NeZero i.2.conductor :=
  ⟨i.2.conductor_ne_zero⟩

structure Slot {N : ℕ} [NeZero N] (i : CharacterSlots N) where
  L : ℕ
  pos : 0 < L
  j : Div L
  level : i.2.conductor^2*L = N
  denominator : i.2.conductor*j.1 = i.1.1
  realized : ∀ s z, channelFunction i.1 i.2 s z = criticalD i.2.primitiveCharacter pos j s z

def originalSlot {N : ℕ} [NeZero N] (i : CharacterSlots N) : Slot i := Classical.choice (by
  obtain ⟨L,hL,j,hN,hf,he⟩ := channel_slot i.1 i.2
  exact ⟨⟨L,hL,j,hN,hf,he⟩⟩)

theorem legal {N : ℕ} [NeZero N] {i : CharacterSlots N} (S : Slot i) (b : Div S.L) :
    i.2.conductor^2*(dilation S.pos b : ℕ) ∣ N := S.level ▸ level_at_dilation b

def observing (N : ℕ) (hN : 0 < N) (one : Bool) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℍ :=
  if one then frickeSL N hN • horizontalPoint y hy x else horizontalPoint y hy x

theorem section_finite {ι : Type*} [Fintype ι] (N : ℕ) (hN : 0 < N) (one : Bool)
    (c : ι → ℂ) (F : ι → ℍ → ℂ) (n : ℤ) (y : ℝ) (hy : 0 < y)
    (hc : ∀ b, Continuous (fun x => F b (observing N hN one y hy x))) :
    sectionMode N hN one (fun z => ∑ b : ι,c b*F b z) n y hy =
      ∑ b : ι,c b*sectionMode N hN one (F b) n y hy := by
  classical
  let O := observing N hN one y hy
  have hI : (∫ x in (0 : ℝ)..1, fourierPhase n x*(∑ b : ι,c b*F b (O x))) =
      ∑ b : ι,c b*(∫ x in (0 : ℝ)..1, fourierPhase n x*F b (O x)) := by
    let K := fun b (x : ℝ) => c b*(fourierPhase n x*F b (O x))
    have HK (x : ℝ) : fourierPhase n x*(∑ b : ι,c b*F b (O x)) = ∑ b : ι,K b x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      unfold K
      ring
    simp_rw [HK]
    rw [intervalIntegral.integral_finsetSum (fun b _ =>
      (continuous_const.mul ((show Continuous (fourierPhase n) by unfold fourierPhase; fun_prop).mul (hc b))).intervalIntegrable 0 1)]
    apply Finset.sum_congr rfl
    intro b _
    exact intervalIntegral.integral_const_mul _ _
  cases one
  · simpa only [sectionMode,observing,O,Bool.false_eq_true,if_false] using hI
  · simp only [sectionMode,if_true]
    simp only [O,observing,if_true] at hI
    rw [hI,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

theorem incoming_observer_cont {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (N : ℕ) (hN : 0 < N) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N)
    (one : Bool) (t y : ℝ) (hy : 0 < y) :
    Continuous (fun x => incoming χ d t (observing N hN one y hy x)) := by
  cases one
  · exact incoming_horizontal_continuous χ d t y hy
  · simp only [observing,if_true,incoming_fricke χ hχ N hN d hle]
    exact continuous_const.mul (incoming_horizontal_continuous χ _ t y hy)

theorem original_expansion {N : ℕ} [NeZero N] (i : CharacterSlots N) (t : ℝ) :
    channelFunction i.1 i.2 (criticalPoint t) =
      fun z => ∑ b : Div (originalSlot i).L,
        dilationCoefficient i.2.primitiveCharacter (criticalPoint t) (originalSlot i).j b *
          incoming i.2.primitiveCharacter (dilation (originalSlot i).pos b) t z := by
  funext z
  rw [(originalSlot i).realized,D_as_dilations]
  rfl

theorem channel_invariant {N : ℕ} [NeZero N] (i : CharacterSlots N) (t : ℝ) (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    channelFunction i.1 i.2 (criticalPoint t) (g • z) = channelFunction i.1 i.2 (criticalPoint t) z := by
  rw [original_expansion]
  simp only [incoming_invariant i.2.primitiveCharacter i.2.primitiveCharacter_isPrimitive N (NeZero.pos N) _
    (legal (originalSlot i) _) t g hg z]

theorem channel_continuous {N : ℕ} [NeZero N] (i : CharacterSlots N)
    (one : Bool) (t y : ℝ) (hy : 0 < y) :
    Continuous (fun x => channelFunction i.1 i.2 (criticalPoint t) (observing N (NeZero.pos N) one y hy x)) := by
  rw [original_expansion]
  apply continuous_finsetSum
  intro b _
  exact continuous_const.mul (incoming_observer_cont _ i.2.primitiveCharacter_isPrimitive N (NeZero.pos N) _
    (legal (originalSlot i) b) one t y hy)

def channelR {N : ℕ} [NeZero N] (i : CharacterSlots N) (one : Bool) (n : ℤ) (t : ℝ) : ℂ :=
  ∑ b : Div (originalSlot i).L,dilationCoefficient i.2.primitiveCharacter (criticalPoint t) (originalSlot i).j b*
    dilationR i.2.primitiveCharacter N (NeZero.pos N) (dilation (originalSlot i).pos b)
      (legal (originalSlot i) b) one n t

/-- The R in the trace numerator is precisely sqrt(|n|) rho_W. Its
physical Fourier coefficient is 2sqrt(y)K times this same scalar in
both observing frames. The proof never divides by an observed K value. -/
theorem channel_mode {N : ℕ} [NeZero N] (i : CharacterSlots N) (one : Bool)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    sectionMode N (NeZero.pos N) one (channelFunction i.1 i.2 (criticalPoint t)) n y hy =
      radial n t y*channelR i one n t := by
  rw [original_expansion,section_finite N (NeZero.pos N) one _ _ n y hy (fun b =>
    incoming_observer_cont _ i.2.primitiveCharacter_isPrimitive N (NeZero.pos N) _
      (legal (originalSlot i) b) one t y hy)]
  simp_rw [incoming_mode _ i.2.primitiveCharacter_isPrimitive N (NeZero.pos N) _ (legal (originalSlot i) _) one n hn t y hy]
  rw [channelR,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem channel_sigmaOne {N : ℕ} [NeZero N] (i : CharacterSlots N)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    fourierCoeff (sigmaOneSection N (NeZero.pos N) (channelFunction i.1 i.2 (criticalPoint t))
      (channel_invariant i t) y hy) n = radial n t y*channelR i true n t := by
  rw [← sectionMode_cuspOne]
  exact channel_mode i true n hn t y hy

def inverseWeight {N : ℕ} [NeZero N] (f : Div N) (u : (ZMod (band N f.1))ˣ)
    (ξ : DirichletCharacter ℂ (band N f.1)) : ℂ :=
  ((band N f.1).totient : ℂ)⁻¹*star (ξ (-(u : ZMod (band N f.1))))

def nativeR {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool) (n : ℤ) (t : ℝ) : ℂ :=
  ∑ ξ : DirichletCharacter ℂ (band N a.1.1), inverseWeight a.1 a.2 ξ*channelR ⟨a.1,ξ⟩ one n t

private theorem native_expansion {N : ℕ} [NeZero N] (a : Parameters N) (t : ℝ) :
    physicalFamily N t a = fun z => ∑ ξ : DirichletCharacter ℂ (band N a.1.1),
      inverseWeight a.1 a.2 ξ*channelFunction a.1 ξ (criticalPoint t) z := by
  funext z
  rw [physicalFamily,inverse_cusp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  unfold inverseWeight
  ring

theorem native_mode {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    sectionMode N (NeZero.pos N) one (cuspFamily N ((youngCuspEquiv N) a) (criticalPoint t)) n y hy =
      radial n t y*nativeR a one n t := by
  simp only [cuspFamily,Equiv.symm_apply_apply]
  change sectionMode N (NeZero.pos N) one (physicalFamily N t a) n y hy = _
  rw [native_expansion,section_finite N (NeZero.pos N) one _ _ n y hy
    (fun ξ => channel_continuous (⟨a.1,ξ⟩ : CharacterSlots N) one t y hy)]
  simp_rw [channel_mode (⟨a.1,_⟩ : CharacterSlots N) one n hn t y hy]
  rw [nativeR,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  ring

theorem native_invariant {N : ℕ} [NeZero N] (a : Parameters N) (t : ℝ)
    (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    physicalFamily N t a (g • z) = physicalFamily N t a z := by
  rw [native_expansion]
  simp only [channel_invariant (⟨a.1,_⟩ : CharacterSlots N) t g hg z]

theorem native_sigmaOne {N : ℕ} [NeZero N] (a : Parameters N)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    fourierCoeff (sigmaOneSection N (NeZero.pos N) (physicalFamily N t a)
      (native_invariant a t) y hy) n = radial n t y*nativeR a true n t := by
  rw [← sectionMode_cuspOne]
  simpa only [cuspFamily,Equiv.symm_apply_apply,physicalFamily] using native_mode a true n hn t y hy

end
end ImbalancedChen.Part3.ActualContinuousClassFourier20261110

