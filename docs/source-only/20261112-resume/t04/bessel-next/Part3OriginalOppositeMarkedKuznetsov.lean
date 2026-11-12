import ImbalancedChen.Part3ActualOppositeBesselTransform

/-! The actual opposite-sign Kuznetsov identity for the two marked
physical probes at the manuscript level and cusps. -/
namespace ImbalancedChen.Part3.OriginalOppositeMarkedKuznetsov20261112

noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
open ActualOppositeBesselTransform20261112 ActualMarkedBruhatTest20261112
open ActualCuspOneGeometricPairing20261112 ActualMarkedGeometricSeries20261112
open OriginalMarkedArithmeticTrace20261112 ActualContinuousPoincarePairing20261110
open OriginalContinuousPoincarePackets20261110 ActualOrdinaryContinuousModes20261110
open ActualContinuousClassFourier20261110 OriginalContinuousClassRemoval20261110
open ActualCuspDenominatorClasses20261110 OriginalNativeCuspFunctionals20261102
open ActualCuspBasisWhittakerCoefficients20261102 ActualFullCuspEigenbasis20261026b
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalTwoZSourceAssembly20261102 OriginalNonzeroCuspOneSource20261102
open ImbalancedChen.P3ZActualPrimaryShortEndpoint (signedY)
open P3NativePeriod64SamplingSourceOnly (D4)

theorem negative_row_index (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    {z n : ℕ} (hn : n∈nCarrier D k z) (ha : D.block.atom.residue ≠ 0)
    (hs : traceNegative D k negativeM=true) : traceIndex D k negativeM z n<0 := by
  have h := traceIndex_natAbs_pos D k negativeM z hn ha
  rw [traceIndex_natAbs] at h
  rw [traceIndex_eq_signedY,hs,signedY,if_pos rfl]
  exact neg_neg_of_pos (by exact_mod_cast h)

private theorem probe_basis (N : ℕ) (hN : 0<N) (i : actualCuspBasisIndex N hN) (ψ : ℝ → ℂ) :
    orderProbe 1 ψ (star (basisOrder N hN i))=orderProbe 1 ψ (basisOrder N hN i) := by
  unfold basisOrder
  split
  · simp only [Complex.star_def,Complex.conj_ofReal]
  · rw [show ∀ x : ℝ,star ((x:ℂ)*I)= -((x:ℂ)*I) from fun x => by simp [Complex.star_def],
      probe_neg_order]

def modulusTerm (Φ : ℝ → ℂ) (z p : ℕ) (h : ℤ) (d : ℕ+) : ℂ :=
  if hd : z.Coprime (d : ℕ) then
    cuspOneMatrixSum z d hd (p : ℤ) h/(traceModulus z d : ℂ) *
      Φ (4*Real.pi*Real.sqrt ((p : ℝ)*(h.natAbs : ℝ))/traceModulus z d)
  else 0

def continuousDensity (Φ : ℝ → ℂ) (z : ℕ) [NeZero z] (t : ℝ) (X Y : Parameters z → ℂ) : ℂ :=
  oppositeWeight Φ t*(∑ a : Parameters z,star (X a)*Y a)/
    (4*(Real.pi : ℂ)*(Real.cosh (Real.pi*t) : ℂ))

/-- The sign hypothesis is the output of the original residue and
Poisson-sign calculation for the entire row. At level one the remaining
opposite-sign row is still off the diagonal. -/
theorem original_opposite_trace (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (ha : D.block.atom.residue ≠ 0) (upper negativeM : Bool)
    (hs : traceNegative D k negativeM=true) (J j : ℕ) (ell : D4 → ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hpψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hpφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    let hN := NeZero.pos z.val
    let Φ := orbitTest (-1) ψ φ
    let ind := traceIndex D k negativeM z.val
    let B := traceBeta D r k upper negativeM ell z.val
    let W := (commonPoissonCompleted J j (ell 1)).weight
    let G := fun t => continuousDensity Φ z.val t
      (fun a => M J j ell (fun h => nativeR a false h t))
      (fun a => source D r k z upper negativeM ell (fun h => nativeR a true h t))
    let F := fun i : actualCuspBasisIndex z.val hN =>
      (8*kTransform (basisOrder z.val hN i) Φ)*
        (star (originalMFunctional J j ell z.val hN i)*originalNFunctional D r k upper negativeM ell z.val hN i)
    Integrable G ∧ Summable F ∧
      (∀ n∈nCarrier D k z.val,∀ p∈commonMBlock J j,Summable (modulusTerm Φ z.val p (ind n))) ∧
      (∑ n∈nCarrier D k z.val,∑ p∈commonMBlock J j, W p*B n*∑' d : ℕ+,modulusTerm Φ z.val p (ind n) d) =
        (∑' i,F i)+(∫ t,G t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let Φ := orbitTest (-1) ψ φ
  let ind := traceIndex D k negativeM z.val
  have E (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) :
      geometricTerm z.val p (ind n) ψ φ=modulusTerm Φ z.val p (ind n) := by
    funext d
    have s : (ind n).sign= -1 := Int.sign_eq_neg_one_of_neg (negative_row_index D k negativeM hn ha hs)
    rw [geometricTerm,s] <;> rfl
  have Z (n : ℕ) (hn : n∈nCarrier D k z.val) (p : ℕ) : pairDiagonal z.val p (ind n) ψ φ=0 := by
    have hp : (0:ℤ)≤p := Int.natCast_nonneg p
    have h := negative_row_index D k negativeM hn ha hs
    have ne : (p:ℤ)≠ind n := ne_of_gt (h.trans_le hp)
    simp only [pairDiagonal,sourceDiagonal,ne,and_false,if_false,star_zero,mul_zero]
  have C (t : ℝ) (X Y : Parameters z.val → ℂ) :
      regularIntegrand z.val ψ φ t X Y=continuousDensity Φ z.val t X Y := by
    rw [regularIntegrand,continuousDensity,show oppositeWeight Φ t=probeWeight ψ φ t from
      induced_weight ψ φ hψ hcψ hpψ hφ hcφ hpφ t]
  have L (i : actualCuspBasisIndex z.val (NeZero.pos z.val)) :
      star (orderProbe 1 ψ (basisOrder z.val (NeZero.pos z.val) i))*
        orderProbe 1 φ (basisOrder z.val (NeZero.pos z.val) i) =
        8*kTransform (basisOrder z.val (NeZero.pos z.val) i) Φ := by
    have H := (induced_transform (basisOrder z.val (NeZero.pos z.val) i) ψ φ hψ hcψ hpψ hφ hcφ hpφ).2
    rw [probe_basis] at H
    exact H.symm
  have H := original_marked_arithmetic_trace D r k z ha upper negativeM J j ell ψ φ hψ hcψ hpψ hφ hcφ hpφ
  dsimp only at H ⊢
  simp_rw [C,L] at H
  refine ⟨H.1,H.2.1,fun n hn p hp => by rw [← E n hn p]; exact H.2.2.1 n hn p hp,?_⟩
  refine Eq.trans ?_ H.2.2.2
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro p hp
  rw [Z n hn p,E n hn p,zero_add]

end
end ImbalancedChen.Part3.OriginalOppositeMarkedKuznetsov20261112
