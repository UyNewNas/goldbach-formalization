import ImbalancedChen.Part3Gamma0ActualSmoothCoreSymmetry
import ImbalancedChen.Part3Gamma0SmoothTensorSpanRendering

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Every actual smooth quotient-core vector is represented by ONE literal
finite smooth compact-tensor Poincare family, and its actual Maass output
is the corresponding genuine finite-family Laplacian Poincare L2 vector.
The actual effective-group periodization is proved additive and complex
linear: compact-hit finiteness supplies summability before tsum laws are
used. Scalars are absorbed into genuine horizontal factors; addition uses
the existing real Fin(n+m) concatenation constructor.

This is stronger than existence of an arbitrary C-infinity representative.
It permits whole-core energy to be deduced from a true arbitrary finite-
family identity, including all cross terms. Positivity on individual seed
generators is neither assumed nor incorrectly extended by span induction.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothCoreFinitePoincareRepresentation20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0SmoothTensorSpanRendering20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothCoreSymmetry20261025a

/-- Genuine summability of each actual effective-group seed series,
derived from proper-action compact hits, not supplied as a tsum premise. -/
theorem compact_seed_summable (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (z : UpperHalfPlane) : Summable (fun q : effectiveGamma0 N => f (effectiveMatrixAction N q z)) := by
  obtain ⟨U,hU,S,hS⟩ := compact_seed_locally_finite N f hK hsupp z
  exact summable_of_ne_finset_zero (s := S) (fun q hq => hS z (mem_of_mem_nhds hU) q hq)

theorem finite_seed_summable (N : ℕ) {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (z : UpperHalfPlane) :
    Summable (fun q : effectiveGamma0 N => finiteCoreFunction s T (effectiveMatrixAction N q z)) :=
  compact_seed_summable N _ (finiteCompactTensorSupportK_isCompact s T)
    (finiteCoreFunction_support_subset s T) z

theorem finite_seed_append {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor) :
    finiteCoreFunction Finset.univ (fun i => (appendSmoothTensors T U i).toCompactTensor) =
      finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor) +
        finiteCoreFunction Finset.univ (fun i => (U i).toCompactTensor) := by
  funext z
  simpa only [finiteCoreFunction_eq_smoothChartFinite,Pi.add_apply] using
    congrFun (smoothChartFinite_append T U) (z.re,z.im)

theorem finite_seed_scale {n : ℕ} (c : ℂ) (T : Fin n → SmoothCompactTensor) :
    finiteCoreFunction Finset.univ (fun i => (scaleSmoothTensor c (T i)).toCompactTensor) =
      c • finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor) := by
  funext z
  simpa only [finiteCoreFunction_eq_smoothChartFinite,Pi.smul_apply] using
    congrFun (smoothChartFinite_scale c T) (z.re,z.im)

/-- Addition of actual Poincare series is licensed by the compact-hit
summability theorem for BOTH original families. -/
theorem smoothPoincare_append (N : ℕ) {n m : ℕ} (T : Fin n → SmoothCompactTensor)
    (U : Fin m → SmoothCompactTensor) :
    smoothFinitePoincare N Finset.univ (appendSmoothTensors T U) =
      smoothFinitePoincare N Finset.univ T + smoothFinitePoincare N Finset.univ U := by
  funext z
  change (∑' q : effectiveGamma0 N,
    finiteCoreFunction Finset.univ (fun i => (appendSmoothTensors T U i).toCompactTensor)
      (effectiveMatrixAction N q z)) = _
  rw [finite_seed_append]
  exact (finite_seed_summable N Finset.univ (fun i => (T i).toCompactTensor) z).tsum_add
    (finite_seed_summable N Finset.univ (fun i => (U i).toCompactTensor) z)

theorem smoothPoincare_scale (N : ℕ) {n : ℕ} (c : ℂ) (T : Fin n → SmoothCompactTensor) :
    smoothFinitePoincare N Finset.univ (fun i => scaleSmoothTensor c (T i)) =
      c • smoothFinitePoincare N Finset.univ T := by
  funext z
  change (∑' q : effectiveGamma0 N,
    finiteCoreFunction Finset.univ (fun i => (scaleSmoothTensor c (T i)).toCompactTensor)
      (effectiveMatrixAction N q z)) = _
  rw [finite_seed_scale]
  exact (finite_seed_summable N Finset.univ (fun i => (T i).toCompactTensor) z).tsum_const_smul c

/-- Equality is in the original canonical quotient L2 space. -/
theorem smoothQuotientL2_append (N : ℕ) [NeZero N] {n m : ℕ}
    (T : Fin n → SmoothCompactTensor) (U : Fin m → SmoothCompactTensor) :
    smoothQuotientPoincareL2 N Finset.univ (appendSmoothTensors T U) =
      smoothQuotientPoincareL2 N Finset.univ T + smoothQuotientPoincareL2 N Finset.univ U := by
  have hQ : quotientTensorPoincare N Finset.univ
      (fun i => (appendSmoothTensors T U i).toCompactTensor) =
      quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) +
        quotientTensorPoincare N Finset.univ (fun i => (U i).toCompactTensor) := by
    funext q
    exact Quotient.inductionOn q (fun z => congrFun (smoothPoincare_append N T U) z)
  apply Lp.ext
  filter_upwards [
    (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i => (appendSmoothTensors T U i).toCompactTensor)).coeFn_toLp,
    (quotientTensorPoincare_memLp_two N Finset.univ (fun i => (T i).toCompactTensor)).coeFn_toLp,
    (quotientTensorPoincare_memLp_two N Finset.univ (fun i => (U i).toCompactTensor)).coeFn_toLp,
    Lp.coeFn_add (smoothQuotientPoincareL2 N Finset.univ T)
      (smoothQuotientPoincareL2 N Finset.univ U)] with q happ ht hu hadd
  rw [happ,hadd,ht,hu]
  exact congrFun hQ q

theorem smoothQuotientL2_scale (N : ℕ) [NeZero N] {n : ℕ}
    (c : ℂ) (T : Fin n → SmoothCompactTensor) :
    smoothQuotientPoincareL2 N Finset.univ (fun i => scaleSmoothTensor c (T i)) =
      c • smoothQuotientPoincareL2 N Finset.univ T := by
  have hQ : quotientTensorPoincare N Finset.univ
      (fun i => (scaleSmoothTensor c (T i)).toCompactTensor) =
      c • quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) := by
    funext q
    exact Quotient.inductionOn q (fun z => congrFun (smoothPoincare_scale N c T) z)
  apply Lp.ext
  filter_upwards [
    (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i => (scaleSmoothTensor c (T i)).toCompactTensor)).coeFn_toLp,
    (quotientTensorPoincare_memLp_two N Finset.univ (fun i => (T i).toCompactTensor)).coeFn_toLp,
    Lp.coeFn_smul c (smoothQuotientPoincareL2 N Finset.univ T)] with q hscaled ht hsmul
  rw [hscaled,hsmul,ht]
  exact congrFun hQ q

theorem smoothQuotientL2_empty (N : ℕ) [NeZero N] :
    smoothQuotientPoincareL2 N Finset.univ (Fin.elim0 : Fin 0 → SmoothCompactTensor) = 0 := by
  apply Lp.ext
  filter_upwards [
    (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i : Fin 0 => ((Fin.elim0 i : SmoothCompactTensor)).toCompactTensor)).coeFn_toLp,
    Lp.coeFn_zero ℂ 2 (carrierPushforward N)] with q hq hzero
  rw [hq,hzero]
  exact Quotient.inductionOn q (fun z => by
    simp [quotientTensorPoincare,finiteCompactTensorPoincare,finiteCoreFunction])

/-- ONE literal finite compact smooth Poincare family represents every
actual typed quotient-core vector, including all linear-combination cross terms. -/
theorem exists_finite_poincare_representation (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor),
      (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T := by
  apply smoothCore_induction N (P := fun u => ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor),
    (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T) _ _ _ _ u
  · intro s
    exact ⟨s.1,s.2,rfl⟩
  · exact ⟨0,Fin.elim0,(smoothQuotientL2_empty N).symm⟩
  · intro u v hu hv
    obtain ⟨n,T,hT⟩ := hu
    obtain ⟨m,U,hU⟩ := hv
    refine ⟨n+m,appendSmoothTensors T U,?_⟩
    change (u : QuotientL2 N)+(v : QuotientL2 N) = _
    rw [hT,hU,smoothQuotientL2_append]
  · intro c u hu
    obtain ⟨n,T,hT⟩ := hu
    refine ⟨n,fun i => scaleSmoothTensor c (T i),?_⟩
    change c • (u : QuotientL2 N) = _
    rw [hT,smoothQuotientL2_scale]

theorem actualCoreLaplacian_eq_family_output (N : ℕ) [NeZero N] (u : smoothCore N)
    {n : ℕ} (T : Fin n → SmoothCompactTensor)
    (hT : (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T) :
    actualCoreLaplacian N u =
      quotientTensorLaplacianPoincareL2 N Finset.univ (fun i => (T i).toCompactTensor) := by
  let s : SmoothSeed := ⟨n,T⟩
  have hu : u = seedCoreElement N s := Subtype.ext hT
  rw [hu,actualCoreLaplacian_seed]
  rfl

/-- Simultaneous representation of both actual operator coordinates by
the SAME finite family, suitable for the genuine finite-family energy identity. -/
theorem exists_finite_input_output_family (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor),
      (u : QuotientL2 N) = smoothQuotientPoincareL2 N Finset.univ T ∧
      actualCoreLaplacian N u =
        quotientTensorLaplacianPoincareL2 N Finset.univ (fun i => (T i).toCompactTensor) := by
  obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
  exact ⟨n,T,hT,actualCoreLaplacian_eq_family_output N u T hT⟩

end
end ImbalancedChen.Part3.Gamma0SmoothCoreFinitePoincareRepresentation20261025a
