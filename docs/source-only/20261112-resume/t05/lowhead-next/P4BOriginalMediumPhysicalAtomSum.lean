import ImbalancedChen.P4BOriginalMediumAtomReconstruction

/-! The whole free level sum of this actual first-medium fibre, with its
original signed word scalar, is the sum of the native signed atom errors.
Both the Fourier phase and the residue N stay fixed in the reindexing. -/
namespace ImbalancedChen.P4BOriginalMediumPhysicalAtomSum
noncomputable section
open Classical Filter
open scoped BigOperators
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.HBRightClosedDyadicRoles (owner)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionThirdFactor (factor gamma restoring thirdSupport splitAt tensor tensor_eq)
open P4BOriginalMediumAtomFamily (Index support)
open P4BOriginalMediumSignedFibre (originalMode scalar free_fibre)
open P4BOriginalMediumAtomReconstruction (withOwners word_errors)

private theorem complex_tensor (P : Params) (hN : 1<P.N) (x U eta : ℝ) (F : ℕ→ℂ) :
    (∑ d∈products P,(free P d:ℂ)*F d)=
      ∑ J∈P.words,
        let S := splitAt P x U eta J
        (restoring P x U eta J:ℂ)*∑ a∈support P S.1,∑ b∈support P S.2.1,∑ c∈thirdSupport P J S.2.2,
          (factor P S.1 a:ℂ)*(factor P S.2.1 b:ℂ)*(gamma P J S.2.2 c:ℂ)*F (a*b*c) := by
  apply Complex.ext
  · simpa only [tensor,support,Complex.re_sum,←Complex.ofReal_mul,Complex.re_ofReal_mul]
      using (tensor_eq P hN x U eta (fun d => (F d).re)).symm
  · simpa only [tensor,support,Complex.im_sum,←Complex.ofReal_mul,Complex.im_ofReal_mul]
      using (tensor_eq P hN x U eta (fun d => (F d).im)).symm

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
def onWord (j : {J // J∈I.P.words}) : Index order zeta kap0 :=
  { I with J := j.val, word := j.property }

def boxedErrors (K : ℕ) (A : Index order zeta kap0) : ℂ :=
  ∑ D∈(support A.P A.groups.1).image owner,
  ∑ E∈(support A.P A.groups.2.1).image owner,
  ∑ G∈(thirdSupport A.P A.J A.groups.2.2).image owner,
    ((withOwners A D E G).atom K).signedError

theorem all_free_words (K : ℕ) (hN : 1<I.P.N) (hu : 1<I.U) :
    exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun d => (free I.P d:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ j∈I.P.words.attach,
        (restoring I.P I.x I.U I.eta j.val:ℂ)*boxedErrors K (onWord I j) := by
  rw [free_fibre I K hu,complex_tensor I.P hN I.x I.U I.eta]
  apply congrArg (fun a : ℂ => (scalar I:ℂ)*a)
  rw [←Finset.sum_attach I.P.words]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun v : ℂ => (restoring I.P I.x I.U I.eta j.val:ℂ)*v)
  exact (word_errors (onWord I j) K).symm

/-- The exact original row with no separate nonunit-head premise.
The common threshold precedes all live legal widths and physical words. -/
theorem eventually_native_free_words (K A : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index A zeta kap0,I.P.N=N →
      exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun d => (free I.P d:ℂ))
        completeProduct I.P.N (originalMode I K)=
        (scalar I:ℂ)*∑ j∈I.P.words.attach,
          (restoring I.P I.x I.U I.eta j.val:ℂ)*boxedErrors K (onWord I j) := by
  filter_upwards [P4BOriginalMediumFibreSWWindow.eventually_window K A 1 hz hz1 hk hkz ht ht1,
    eventually_ge_atTop (2:ℕ)] with N h hN
  intro I hIN
  have h' := h
  rw [←hIN] at h'
  obtain ⟨_,_,_,_,hu,_,_,_,_⟩ := h' I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C
    I.live (P4BOriginalMediumFibreSWWindow.first_spec I.selected)
  exact all_free_words I K (by rw [hIN]; omega) hu

end
end ImbalancedChen.P4BOriginalMediumPhysicalAtomSum
