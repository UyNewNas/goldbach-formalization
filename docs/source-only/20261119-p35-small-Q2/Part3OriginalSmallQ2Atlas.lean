import ImbalancedChen.Part3OriginalSmallScaleTransport
import ImbalancedChen.Part3OriginalSixTailPhysicalPayment

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
The actual occupied rough owner supplies S<=2*Q2. A common threshold
converts a fixed small-Q2 condition to the previously proved-candidate
small-S reduced-pair estimate. This is not the full spectral return.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalSmallQ2Atlas20261119
open Classical Finset Filter
open scoped BigOperators MatrixGroups
open ImbalancedChen.Part3
open OriginalMediumPhysicalE3Block MediumGlobalDyadicOwnership20261028
open OriginalSamePsiS1OwnedAtlas OriginalLambdaTrimPoissonFamily20261028
open OriginalActualPoissonTightH20261028
open ActualOriginalSpectralScales20261028
open ActualFixedFeatureCountGeometrySourceOnly ActualCompletedZeroPaymentSourceOnly
open ActualCompletedHardTailMass20261026b ActualPhysicalRawLabelPolynomialSourceOnly
open ActualPhysicalHardEpsilonSelectionSourceOnly
open OriginalMaskedOuterEnergy20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalCompletedReciprocalSource20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalExceptionalPostRemovalPair20261113
open OriginalSmallScaleTransport20261119 (smallS_pair)
open OriginalSixTailPhysicalPayment20261102 (tightOriginalData)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- One C and one X are fixed before the admissible atom, occupied key,
and all tight-atlas labels. The small-Q2 condition is an explicit
subfamily condition; the complementary keys remain unbounded here. -/
theorem tight_atlas_smallQ2_pair {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C X : ℝ, 0 < C ∧ 1 ≤ X ∧
    ∀ (b : ℕ) (sigma kappa c0 : ℝ) (atom : MediumAtom)
      (hA : MediumAdmissible b sigma kappa c0 atom),
    X ≤ atom.scale → atom.Q2 ≤ atom.scale^(δ/4) →
    ∀ (z y : ℝ) (k : Key), k ∈ keyBank atom z y →
    ∀ (Csep : ℕ) (channel : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k)
      (negative : Bool) (rectangle : Rectangle) (st st' : ℕ × ℕ)
      (polarS polarR polarN : Fin 4),
    let D := tightOriginalData atom z y k hA Csep channel small hd negative
      rectangle st st' polarS polarR polarN
    ∀ (r : ZMod (prefixPeriod D.key)) (blockKey : BlockKey)
      (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ),
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let F := mFactor D blockKey upper J j ell
    let G := nFactor D r blockKey upper negativeM ell
    (∑ a : Slots D blockKey upper, F a * G a)^2 ≤
      ((2+Real.log (4*V+1))^2 *
        (((6*atom.scale^δ)*(C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M) +
          (6*atom.scale^δ)*(C*((1+Z)*(1+M))^ε*(Z+M)*M))/4)) *
      ((4*sieveConstant*(1+rowLength blockKey/Z))*
        ∑ q : ↥(levels D blockKey upper), rowMass D r blockKey q.val) := by
  obtain ⟨C, cp, hpair⟩ := smallS_pair hε hδ.le
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < δ/4 by positivity)).eventually_ge_atTop 2)
  refine ⟨C, max 1 X, cp, le_max_left _ _, ?_⟩
  intro b sigma kappa c0 atom hA hx hQ2 z y k hk Csep channel small hd
    negative rectangle st st' polarS polarR polarN
  dsimp only
  let D := tightOriginalData atom z y k hA Csep channel small hd negative
    rectangle st st' polarS polarR polarN
  intro r blockKey upper negativeM J j ell
  have hx1 : 1 ≤ atom.scale := (le_max_left 1 X).trans hx
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le hx1
  have hhalf : 2 ≤ atom.scale^(δ/4) := hX atom.scale ((le_max_right 1 X).trans hx)
  have hp : 0 ≤ atom.scale^(δ/4) := Real.rpow_nonneg hxpos.le _
  have hSraw : scaleS D.key ≤ 2*atom.Q2 := by
    change scaleS k ≤ 2*atom.Q2
    have h := (actual_rough_owner_geometry hA z y k hk).2.1
    simpa only [scaleS, roughS] using h
  have hS : scaleS D.key ≤ atom.scale^(δ/2) := by
    calc
      _ ≤ 2*atom.Q2 := hSraw
      _ ≤ 2*atom.scale^(δ/4) := mul_le_mul_of_nonneg_left hQ2 (by norm_num)
      _ ≤ atom.scale^(δ/4)*atom.scale^(δ/4) := mul_le_mul_of_nonneg_right hhalf hp
      _ = atom.scale^(δ/2) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  exact hpair D atom.scale r blockKey upper negativeM J j ell hx1 hS

end ImbalancedChen.Part3.OriginalSmallQ2Atlas20261119
end
