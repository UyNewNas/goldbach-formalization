import ImbalancedChen.Part3OriginalContinuousClassRemoval

/-! Original first-conjugated m/n covariance and the complete native
cusp-summed continuous n energy, with the genuine relative inverse
norms, original signs, and the same marked coefficient at every height. -/
namespace ImbalancedChen.Part3.OriginalContinuousCuspGram20261110

noncomputable section
open Complex Set Finset MeasureTheory
open scoped BigOperators MatrixGroups
open OriginalContinuousClassRemoval20261110 ActualYoungFormalClass20261110
open ActualContinuousClassFourier20261110 ActualYoungCriticalProjection20261110
open ActualOrdinaryContinuousModes20261110 ActualCriticalCuspEvaluation20261110
open ActualCuspDenominatorClasses20261110 ActualYoungDilationInverse20261110
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open P3NativePeriod64SamplingSourceOnly (D4)

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

private def inverseSum {N : ℕ} [NeZero N] (f : Div N) (X : DirichletCharacter ℂ (band N f.1) → ℂ)
    (u : (ZMod (band N f.1))ˣ) : ℂ := ∑ ξ, inverseWeight f u ξ*X ξ

private theorem recover {N : ℕ} [NeZero N] (f : Div N) (X : DirichletCharacter ℂ (band N f.1) → ℂ)
    (χ : DirichletCharacter ℂ (band N f.1)) :
    (∑ u : (ZMod (band N f.1))ˣ, χ (-(u : ZMod (band N f.1)))*inverseSum f X u) = X χ := by
  classical
  let H := band N f.1
  let V := fun (η : DirichletCharacter ℂ H) (u : (ZMod H)ˣ) => η (-(u : ZMod H))
  have hφ : (H.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne H))).ne'
  have hu (u : (ZMod H)ˣ) : V χ u*inverseSum f X u =
      (H.totient : ℂ)⁻¹ * ∑ η : DirichletCharacter ℂ H,(V χ u*star (V η u))*X η := by
    simp only [inverseSum,inverseWeight,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    unfold V
    ring
  change (∑ u : (ZMod H)ˣ,V χ u*inverseSum f X u) = _
  simp_rw [hu]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,show ∀ η : DirichletCharacter ℂ H,
    (∑ u : (ZMod H)ˣ,V χ u*star (V η u)) = if χ = η then (H.totient : ℂ) else 0 from unit_orthogonality χ,
    ite_mul,zero_mul]
  simp [hφ]

def classProduct (N : ℕ) [NeZero N] (X Y : CharacterSlots N → ℂ) : ℂ :=
  ∑ f : Div N, ∑ ξ : DirichletCharacter ℂ (band N f.1),
    star (X ⟨f,ξ⟩)*Y ⟨f,ξ⟩/(4*(Real.pi : ℂ)*((band N f.1).totient : ℂ))

def nativeProduct (N : ℕ) [NeZero N] (X Y : Parameters N → ℂ) : ℂ :=
  ∑ a : Parameters N, star (X a)*Y a/(4*(Real.pi : ℂ))

private theorem inverse_gram (N : ℕ) [NeZero N] (X Y : CharacterSlots N → ℂ) :
    classProduct N X Y =
      nativeProduct N (fun a => inverseSum a.1 (fun ξ => X ⟨a.1,ξ⟩) a.2)
        (fun a => inverseSum a.1 (fun ξ => Y ⟨a.1,ξ⟩) a.2) := by
  classical
  rw [classProduct,nativeProduct,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro f _
  let A := inverseSum f (fun ξ => X ⟨f,ξ⟩)
  let B := inverseSum f (fun ξ => Y ⟨f,ξ⟩)
  have H := local_projection A B
  simp only [A,B,recover] at H
  have hφ : ((band N f.1).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (band N f.1)))).ne'
  rw [← Finset.sum_div,← Finset.sum_div,H]
  field_simp [hφ,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

/-- This applies in particular to the true shared common-M interval,
indices with residue and Poisson signs, and the ABL-reduced indices. -/
theorem marked_covariance (N : ℕ) [NeZero N] (t : ℝ) (left right : Bool)
    (S T : Finset ℕ) (c d : ℕ → ℂ) (p n : ℕ → ℤ) :
    classProduct N
      (fun i => markedRow S c p (fun a => channelR i left a t))
      (fun i => markedRow T d n (fun a => channelR i right a t)) =
    nativeProduct N
      (fun a => markedRow S c p (fun b => nativeR a left b t))
      (fun a => markedRow T d n (fun b => nativeR a right b t)) := by
  rw [inverse_gram]
  have he (a : Parameters N) (one : Bool) (U : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ) :
      markedRow U w ind (fun b => nativeR a one b t) =
        inverseSum a.1 (fun ξ => markedRow U w ind (fun b => channelR (⟨a.1,ξ⟩ : CharacterSlots N) one b t)) a.2 :=
    markedRow_sum U w ind _ _
  simp only [he]

/-- The actual physical first-input weights are conjugated inside M.
The outer conjugation restores precisely the original common weight. -/
theorem original_projected_product (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    classProduct z.val (fun i => M J j ell (fun n => channelR i false n t))
      (fun i => source D r k z upper negativeM ell (fun n => channelR i true n t)) =
    nativeProduct z.val (fun a => M J j ell (fun n => nativeR a false n t))
      (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  exact marked_covariance z.val t false true _ _ _ _ _ _

def nativeMass (N : ℕ) [NeZero N] (X : Parameters N → ℂ) : ℝ :=
  ∑ a : Parameters N,‖X a‖^2/(4*Real.pi)

private theorem squared_re (x : ℂ) (d : ℝ) : (star x*x/(d : ℂ)).re = ‖x‖^2/d := by
  rw [Complex.div_ofReal_re,Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

private theorem class_self_re (N : ℕ) [NeZero N] (X : CharacterSlots N → ℂ) :
    (classProduct N X X).re = continuousMass N X := by
  simp only [classProduct,continuousMass,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro ξ _
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast] using
    squared_re (X ⟨f,ξ⟩) (4*Real.pi*((band N f.1).totient : ℝ))

private theorem native_self_re (N : ℕ) [NeZero N] (X : Parameters N → ℂ) :
    (nativeProduct N X X).re = nativeMass N X := by
  simp only [nativeProduct,nativeMass,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using squared_re (X a) (4*Real.pi)

theorem native_mass_eq (N : ℕ) [NeZero N] (t : ℝ) (one : Bool)
    (S : Finset ℕ) (w : ℕ → ℂ) (ind : ℕ → ℤ) :
    nativeMass N (fun a => markedRow S w ind (fun n => nativeR a one n t)) =
      continuousMass N (fun i => markedRow S w ind (fun n => channelR i one n t)) := by
  rw [← native_self_re,← class_self_re]
  exact congrArg Complex.re (marked_covariance N t one one S S w w ind ind).symm

/-- The completed native cusp-summed continuous quadratic form obeys
the manuscript's t-independent divisor loss on the literal marked row. -/
theorem original_native_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ) (t : ℝ) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    nativeMass z.val (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t)) ≤
      ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2*
      nativeMass z.val (fun a => reduced D r k z upper negativeM ell (fun n => nativeR a true n t)) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  unfold source reduced
  rw [native_mass_eq,native_mass_eq]
  exact full_continuous_removal D r k z upper negativeM ell t

end
end ImbalancedChen.Part3.OriginalContinuousCuspGram20261110

