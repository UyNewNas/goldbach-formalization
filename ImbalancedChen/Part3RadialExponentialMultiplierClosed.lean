import ImbalancedChen.Part3ActualKRadialLogConjugation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual unbounded multiplication operator f(r) |-> exp(r) f(r) has a
closed graph in L2(dr) x L2(dr). The proof extracts two actual almost
everywhere subsequences from the two L2 limits. There is no boundedness
assumption on exp, no chosen continuous representative and no closedness
premise. This is the potential coordinate in the genuine radial form for
-d²/dr²+exp(2r), distinct from the constant-mode cusp quarter potential.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory Filter

abbrev RadialL2 := Lp ℂ 2 (volume : Measure ℝ)

def exponentialProduct (f : ℝ → ℂ) (r : ℝ) : ℂ := (Real.exp r : ℂ) * f r

/-- Both limits are actual L2 limits. The pointwise multiplication
relation is retained a.e. for each term and proved for the limits. -/
theorem exponentialProduct_closed_under_L2_limits
    (f g : ℕ → RadialL2) (F G : RadialL2)
    (hf : Tendsto f atTop (nhds F)) (hg : Tendsto g atTop (nhds G))
    (hrel : ∀ n, (g n : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      exponentialProduct (f n)) :
    (G : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] exponentialProduct F := by
  obtain ⟨ns, hns, hfae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨ks, hks, hgae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ r ∂(volume : Measure ℝ),
      ∀ n, g n r = exponentialProduct (f n) r := ae_all_iff.2 hrel
  filter_upwards [hfae, hgae, hall] with r hrF hrG hrRel
  have hprod : Tendsto (fun i => (Real.exp r : ℂ) * f (ns (ks i)) r)
      atTop (nhds ((Real.exp r : ℂ) * F r)) :=
    (hrF.comp hks.tendsto_atTop).const_mul (Real.exp r : ℂ)
  have hseq : (fun i => g (ns (ks i)) r) =
      (fun i => (Real.exp r : ℂ) * f (ns (ks i)) r) := by
    funext i
    exact hrRel (ns (ks i))
  rw [hseq] at hrG
  exact tendsto_nhds_unique hrG hprod

def exponentialMultiplierGraph : Set (RadialL2 × RadialL2) :=
  {p | (p.2 : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)] exponentialProduct p.1}

theorem isClosed_exponentialMultiplierGraph : IsClosed exponentialMultiplierGraph := by
  apply IsSeqClosed.isClosed
  intro f p hf hlim
  exact exponentialProduct_closed_under_L2_limits (fun n => (f n).1)
    (fun n => (f n).2) p.1 p.2
    ((continuous_fst.tendsto p).comp hlim)
    ((continuous_snd.tendsto p).comp hlim) hf

/-- The actual exponential coordinate cannot survive a zero physical
L2 limit. This conclusion is derived from the closed multiplier graph. -/
theorem exponentialProduct_limit_zero
    (f g : ℕ → RadialL2) (G : RadialL2)
    (hf : Tendsto f atTop (nhds 0)) (hg : Tendsto g atTop (nhds G))
    (hrel : ∀ n, (g n : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      exponentialProduct (f n)) : G = 0 := by
  have h := exponentialProduct_closed_under_L2_limits f g 0 G hf hg hrel
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with r hr hz
  simp only [exponentialProduct, hz, mul_zero] at hr
  exact hr.trans hz.symm

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
