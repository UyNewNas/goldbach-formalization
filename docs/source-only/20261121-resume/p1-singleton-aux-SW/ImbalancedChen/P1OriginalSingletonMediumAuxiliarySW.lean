import ImbalancedChen.P1OriginalSingletonMediumWindow
import ImbalancedChen.P1OriginalSingletonMediumRectangles
import all ImbalancedChen.P4BOriginalMediumAuxiliaryBound

/-!
SOURCE CANDIDATE / NOT COMPILED.

Apply the existing actual-role analytic supplier to the original singleton
profile and its first-medium fibre. The raw arithmetic estimate, real
Mobius clipping, normalized-log Abel argument and finite row dictionary
are reused. One constant and one physical-N threshold precede all charts,
positions, complementary owners, real intervals, frequencies, auxiliary
integers, moduli and primitive residues. This is auxiliary SW for the
individual HB head, not the signed three-modulus medium estimate.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumAuxiliarySW
noncomputable section
open Classical Filter
open scoped BigOperators
open Part3 (auxiliarySWError)
open Part3.ActualRoughContourParameters20261026b (roughZ)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords blockWords_spec)
open P5Z.ExactOriginalSmoothDyadicPartition (R beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCap hbCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P5Z.ActualSelectedRoughSlotAPDictionary (intervalCarrier)
open P5Z.ActualLowerNormalizedAtlasOccurrence (integerProfile rowRoles)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector ofFn_blockVector)
open P5Z.OriginalChartRoughCutoff (roughF)
open P5Z.OriginalWRetainedChartModesSW (auxiliarySWError_const_mul_exact)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalMediumHBHead (alpha source scalar logRole scalar_pos restores alpha_one alpha_rough)
open P4BOriginalHighRankPostModulusRow (H bandwidthOrder eventually_local_twists)
open P1OriginalSingletonOneLongGeometry (original_cutoff_singleton)
open P1OriginalSingletonMediumWindow (eventually_original_medium_window)
open private normalized_rough_window from ImbalancedChen.P4BOriginalMediumAuxiliaryBound

/-- The actual singleton head satisfies the all-auxiliary/all-modulus SW
estimate on every real subinterval of its original right-closed block.
The logarithm role is normalized at its own U; the same positive scalar
is restored in the second estimate, paid by one extra log of accuracy.
No desired error estimate or arbitrary smooth-profile class is an input. -/
theorem eventually_singleton_selected (K : ℕ) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L)
    {kap zeta kappa kap0 : ℝ} (hkap : kap < 1)
    (hz : 0 < zeta) (hz1 : zeta ≤ 1/400) (hk : 0 < kappa)
    (ht : kap0 < kappa/(4*(1+kappa))) (ht1 : kap0 < 1) :
    ∃ Csw : ℝ, 0 < Csw ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (cj t : ℕ) (bs : Fin t → Block) (i : Fin t) (B : Block),
      (∃ n ∈ fibre bs i B, integerProfile kap 6 N cj kap0 n ≠ 0) →
      firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
        (List.ofFn bs) = some i.val →
      let U := (lower (bs i) : ℝ)
      let x := U*(lower B : ℝ)
      let Z := beforeHBCutoff K [cj]
      ∀ (role : Role) (Y tau : ℝ), |tau| ≤ (Real.log x)^L →
        (∀ n, ‖alpha (bs i) Z Y role tau n‖ ≤ 1) ∧
        (∀ n, alpha (bs i) Z Y role tau n ≠ 0 → ∀ p : ℕ,
          p.Prime → p ∣ n → roughF x < (p : ℝ)) ∧
        ∀ lo hi : ℝ, U ≤ lo → lo ≤ hi → hi ≤ 2*U →
        ∀ k q residue : ℕ, 0 < k → 0 < q → residue.Coprime q →
          ‖auxiliarySWError (intervalCarrier lo hi)
            (alpha (bs i) Z Y role tau) k q residue‖ ≤
              Csw*U*(k.divisors.card : ℝ)/(Real.log x)^(A+1) ∧
          ‖auxiliarySWError (intervalCarrier lo hi)
            (source (bs i) Z Y role tau) k q residue‖ ≤
              Csw*U*(k.divisors.card : ℝ)/(Real.log x)^A := by
  obtain ⟨Csw,hC,x0,_,Hraw⟩ := normalized_rough_window (A+1) L (2*zeta)
    (by linarith) hL (by linarith)
  refine ⟨Csw,hC,?_⟩
  filter_upwards [eventually_original_medium_window K (max x0 (Real.exp 1))
    hkap hz hz1 hk ht ht1] with N Hwin
  intro cj t bs i B alive selected
  dsimp only
  let U : ℝ := lower (bs i)
  let x : ℝ := U*(lower B : ℝ)
  let v : ℝ := (2 : ℝ)^(6*K+3)*R cj
  let Z : ℝ := beforeHBCutoff K [cj]
  obtain ⟨hxMin,hx,_,_,_,hU1,hUlo,_,hUtop,hxv,hvx,hZ,_⟩ :=
    Hwin cj t bs i B alive selected
  have hx0 : x0 ≤ x := (le_max_left _ _).trans hxMin
  have hxp : 0 < x := zero_lt_one.trans hx
  have hlog1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxp).mpr ((le_max_right _ _).trans hxMin)
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hlog1
  intro role Y tau hTau
  refine ⟨fun n => alpha_one _ _ _ _ _ n,
    fun n hn p hp hd => hZ.trans_lt (alpha_rough hn p hp hd),?_⟩
  intro lo hi hLo hLH hHi k q residue hk' hq hres
  have hNormal : ‖auxiliarySWError (intervalCarrier lo hi)
      (alpha (bs i) Z Y role tau) k q residue‖ ≤
      Csw*U*(k.divisors.card : ℝ)/(Real.log x)^(A+1) := by
    have hh := Hraw hx0 hxv hvx (bs i) hU1 hUlo hUtop role Y tau lo hi
      hTau hLo hLH hHi k q residue hk' hq hres
    simpa only [Z, original_cutoff_singleton, roughF, roughZ, v, U, x] using hh
  refine ⟨hNormal,?_⟩
  have hScalar : scalar (bs i) role ≤ Real.log x := by
    cases role with
    | one => simpa only [scalar, logRole, Bool.false_eq_true, if_false] using hlog1
    | mobius => simpa only [scalar, logRole, Bool.false_eq_true, if_false] using hlog1
    | logarithm =>
      simpa only [scalar, logRole, if_true, U] using
        Real.log_le_log (show (0 : ℝ) < 2*U by linarith) hUtop
  have hSource : source (bs i) Z Y role tau =
      (fun n => (scalar (bs i) role : ℂ)*alpha (bs i) Z Y role tau n) :=
    funext (restores (bs i) Z Y role tau)
  rw [hSource, auxiliarySWError_const_mul_exact, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scalar_pos (bs i) role)]
  calc
    _ ≤ Real.log x*(Csw*U*(k.divisors.card : ℝ)/(Real.log x)^(A+1)) :=
      mul_le_mul hScalar hNormal (norm_nonneg _) hlog.le
    _ = _ := by
      rw [Real.rpow_add hlog, Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hlog A).ne',hlog.ne']
      ring

/-- Apply the estimate to the literal one-group HB rows used by the
already proved singleton mediumAtlas expansion. The actual real HB
truncation and actual selected role are retained. The generic retained
frequency-cube supplier is reused with its original cutoff H; this is
not a new Fourier-tail, modulus-atom or full mediumAtlas payment. -/
theorem eventually_actual_singleton_row (K modeOrder : ℕ) (A : ℝ) (hA : 0 ≤ A)
    {kap zeta kappa kap0 : ℝ} (hkap : kap < 1)
    (hz : 0 < zeta) (hz1 : zeta ≤ 1/400) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (ht : kap0 < kappa/(4*(1+kappa))) (ht1 : kap0 < 1) :
    ∃ Csw : ℝ, 0 < Csw ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (cj j : ℕ) (bs : List Block), bs ∈ blockWords (hbCap cj) (2*(j+1)) →
      ∀ (i : Fin (2*(j+1))) (B : Block),
      (∃ n ∈ fibre (blockVector (2*(j+1)) bs) i B,
        integerProfile kap 6 N cj kap0 n ≠ 0) →
      firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs = some i.val →
      let bv := blockVector (2*(j+1)) bs
      let U := (lower (bv i) : ℝ)
      let x := U*(lower B : ℝ)
      let Z := beforeHBCutoff K [cj]
      ∀ xi : Fin (2*(j+1)) → ℝ,
        xi ∈ (outsideCube (2*(j+1)) (H N modeOrder))ᶜ →
        (∀ n, ‖alpha (bv i) Z (hbCutoff cj) (rowRoles j i) (xi i) n‖ ≤ 1) ∧
        (∀ n, alpha (bv i) Z (hbCutoff cj) (rowRoles j i) (xi i) n ≠ 0 →
          ∀ p : ℕ, p.Prime → p ∣ n → roughF x < (p : ℝ)) ∧
        ∀ lo hi : ℝ, U ≤ lo → lo ≤ hi → hi ≤ 2*U →
        ∀ k q residue : ℕ, 0 < k → 0 < q → residue.Coprime q →
          ‖auxiliarySWError (intervalCarrier lo hi)
            (alpha (bv i) Z (hbCutoff cj) (rowRoles j i) (xi i)) k q residue‖ ≤
              Csw*U*(k.divisors.card : ℝ)/(Real.log x)^(A+1) ∧
          ‖auxiliarySWError (intervalCarrier lo hi)
            (source (bv i) Z (hbCutoff cj) (rowRoles j i) (xi i)) k q residue‖ ≤
              Csw*U*(k.divisors.card : ℝ)/(Real.log x)^A := by
  let L : ℝ := ((bandwidthOrder modeOrder+1 : ℕ) : ℝ)
  obtain ⟨Csw,hC,Hsw⟩ := eventually_singleton_selected K A L hA
    (by dsimp [L]; positivity) hkap hz hz1 hk ht ht1
  refine ⟨Csw,hC,?_⟩
  filter_upwards [Hsw, eventually_original_medium_window K 1 hkap hz hz1 hk ht ht1,
    eventually_local_twists modeOrder hk1] with N hSW hWindow hFrequency
  intro cj j bs hbs i B alive selected
  dsimp only
  intro xi hxi
  let bv := blockVector (2*(j+1)) bs
  let x : ℝ := (lower (bv i) : ℝ)*(lower B : ℝ)
  have hselected : firstMedium (originalMediumLow zeta [cj])
      (originalMediumHigh zeta [cj]) (List.ofFn bv) = some i.val := by
    dsimp only [bv]
    rw [ofFn_blockVector (blockWords_spec _ _ _ hbs).1]
    exact selected
  have hgeom := hWindow cj (2*(j+1)) bv i B alive hselected
  obtain ⟨_,hx,_,hNx,_,_,_,_,_,_,_,_,_⟩ := hgeom
  have hTau : |xi i| ≤ (Real.log x)^L := by
    simpa only [L, Real.rpow_natCast] using
      hFrequency x hx hNx (2*(j+1)) xi hxi i
  exact hSW cj (2*(j+1)) bv i B alive hselected (rowRoles j i) (hbCutoff cj) (xi i) hTau

end
end ImbalancedChen.P1OriginalSingletonMediumAuxiliarySW
