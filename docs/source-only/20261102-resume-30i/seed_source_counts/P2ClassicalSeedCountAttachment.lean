import ImbalancedChen.P2SameQPhysicalRosserSeed
import ImbalancedChen.P2AllW1StablePrefixRawInduction
import MathlibNt.Wu2008DoubleSieve.PhiBounded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The error-paid classical seed has literal prime-tuple labels, the same Q
in every fibre, the original Theta, and no assumed source equality or count
licence. This is the classical subcase of the original seed obligation.
It does not establish the enhanced-level receiver distribution, the positive
four W2 rounds, frozen184+64, or the distinct seed-only430 history.
-/
namespace ImbalancedChen.P2ClassicalSeedCountAttachment

noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions P2SameQSeedCoprimeMean
open P2ActualMarkedCountState (Query markedTheta)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2AllW1StablePrefixRawInduction (markedState markedState_encloses)
open scoped Classical BigOperators

def tupleProduct {i : ℕ} (t : Fin i → ℕ) : ℕ := ∏ j,t j

/-- No product injectivity is used: each original tuple is a separate label. -/
theorem labelled_count_eq_wuBoxPhi {i : ℕ} (N : ℕ) (delta : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) :
    markedPhi N ((N:ℝ)^(1/2-delta)) (Fintype.piFinset W) tupleProduct
      (fun _ => 1) (fun _ _ => True) s = wuBoxPhi N delta W s := by
  rw [wuBoxPhi_eq_tuple_sum]
  unfold markedPhi
  apply sum_congr rfl
  intro t ht
  simp [frozenCount,frozenCarrier,sourceSieveCount,tupleProduct,cutoff,wuLocalCutoff]

/-- The actual labelled normalizer equals the convolution normalizer by
the proved multiplicity formula, not by merging equal products once. -/
theorem labelled_Theta_eq_boxTheta {i : ℕ} (N : ℕ) (Q : ℝ)
    (W : Fin i → Finset ℕ) :
    markedTheta N Q (Fintype.piFinset W) tupleProduct (fun _ => 1)=boxTheta N Q W := by
  unfold markedTheta boxTheta
  congr 1
  simpa only [tupleProduct,one_mul,mul_div_assoc] using
    (boxConvolution_sum_fibres W (fun d => wuSingularSeries (d*N)/
      ((Nat.totient d:ℝ)*Real.log (Q/(d:ℝ))))).symm

/-- Actual prime-window membership supplies positivity and target
coprimality. The squared-prefix source condition supplies a uniform power
lower bound for Q/B, including the empty tuple. -/
theorem classical_tuple_source_geometry {i k N : ℕ} {delta Delta : ℝ}
    {V : Fin i → ℝ} (hN : 1≤N) (hdelta : 0<delta) (hdeltahi : delta<1/2)
    (hV : ∀j,(N:ℝ)^(delta^(k+1))≤V j)
    (hprefix : boxSquaredPrefixes ((N:ℝ)^(1/2-delta)) V)
    {t : Fin i → ℕ} (ht : t∈Fintype.piFinset (convolutionWuWindows N Delta V)) :
    0<tupleProduct t ∧ (tupleProduct t).Coprime N ∧
      (N:ℝ)^(wuLocalExponent k delta)≤
        (N:ℝ)^(1/2-delta)/(tupleProduct t:ℝ) := by
  have hd := mem_image_of_mem (fun u : Fin i → ℕ => ∏j,u j) ht
  have hg := wuLocal_support_bounds hN hdelta hdeltahi hV
    ((boxSquaredPrefixes_iff _ _).mp hprefix) hd
  refine ⟨hg.1,?_,hg.2.2⟩
  unfold tupleProduct
  exact Nat.Coprime.prod_left (fun j _ =>
    (mem_convolutionWuWindows.mp (Fintype.mem_piFinset.mp ht j)).2.1)

/-- One threshold precedes depth, windows, tuple labels and all parameters
1<=s<=10. Both sides have their exact physical cutoff and original Theta.
The signed AP error and coprime/model normalization are paid by the actual
foundational suppliers; no endpoint/count licence is a premise here. -/
theorem classical_two_sided_count_seed (k : ℕ) (hk : 1≤k)
    {delta epsilon : ℝ} (hdelta : 0<delta) (hdeltahi : delta<1/2)
    (hepsilon : 0<epsilon) :
    ∃ N0 : ℕ, 4≤N0 ∧ ∀ N : ℕ, N0≤N → Even N →
      ∀ i : ℕ, i≤k → ∀ Delta : ℝ,
      1+Real.log (N:ℝ)^(-4:ℝ)≤Delta →
      Delta<1+2*Real.log (N:ℝ)^(-4:ℝ) →
      ∀ V : Fin i → ℝ, Antitone V →
      (∀j,(N:ℝ)^(delta^(k+1))≤V j) →
      boxSquaredPrefixes ((N:ℝ)^(1/2-delta)) V →
      ∀ s : ℝ, 1≤s → s≤10 →
      (wuLowerCoefficient s-epsilon)*
          markedTheta N ((N:ℝ)^(1/2-delta))
            (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct (fun _ => 1)≤
        markedPhi N ((N:ℝ)^(1/2-delta))
          (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct
          (fun _ => 1) (fun _ _ => True) s ∧
      markedPhi N ((N:ℝ)^(1/2-delta))
          (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct
          (fun _ => 1) (fun _ _ => True) s≤
        (wuUpperCoefficient s+epsilon)*
          markedTheta N ((N:ℝ)^(1/2-delta))
            (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct (fun _ => 1) := by
  obtain ⟨NL,hL⟩ := wu_boxPhi_lower_source_bounded k hk hdelta hdeltahi hepsilon
  obtain ⟨NU,hU⟩ := wu_boxPhi_upper_source_bounded k hk hdelta hdeltahi hepsilon
  refine ⟨max 4 (max NL NU),le_max_left _ _,?_⟩
  intro N hN he i hik Delta hlo hhi V horder hV hprefix s hs hs10
  have hNL : NL≤N := (le_max_left NL NU).trans ((le_max_right 4 (max NL NU)).trans hN)
  have hNU : NU≤N := (le_max_right NL NU).trans ((le_max_right 4 (max NL NU)).trans hN)
  rw [labelled_count_eq_wuBoxPhi,labelled_Theta_eq_boxTheta]
  exact ⟨(hL N hNL he i hik Delta hlo hhi V horder hV hprefix s hs hs10).2,
    (hU N hNU he i hik Delta hlo hhi V horder hV hprefix s hs hs10).1⟩

/-- All H generations are attached to these same source labels with no
new count invariant, no lost multiplicities, and no changed descendant Q.
This is an arithmetic attachment; it asserts no positive H248 entry. -/
theorem classical_H_marked_count_enclosure {i k N : ℕ} {delta Delta : ℝ}
    {V : Fin i → ℝ} (hN : 4≤N) (hdelta : 0<delta) (hdeltahi : delta<1/2)
    (hV : ∀j,(N:ℝ)^(delta^(k+1))≤V j)
    (hprefix : boxSquaredPrefixes ((N:ℝ)^(1/2-delta)) V)
    (bank : List Query) (rounds : ℕ) (s : Query) :
    (markedState N ((N:ℝ)^(1/2-delta))
        (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct
        (fun _ => 1) (fun _ _ => True) bank rounds).lower s≤wuBoxPhi N delta
          (convolutionWuWindows N Delta V) s.val ∧
    wuBoxPhi N delta (convolutionWuWindows N Delta V) s.val≤
      (markedState N ((N:ℝ)^(1/2-delta))
        (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct
        (fun _ => 1) (fun _ _ => True) bank rounds).upper s := by
  have hNreal : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hg (t : Fin i → ℕ)
      (ht : t∈Fintype.piFinset (convolutionWuWindows N Delta V)) :=
    classical_tuple_source_geometry (k := k) (by omega : 1≤N)
      hdelta hdeltahi hV hprefix ht
  have hpow : 1<(N:ℝ)^(wuLocalExponent k delta) :=
    Real.one_lt_rpow hNreal (wuLocalExponent_pos k hdelta hdeltahi)
  have hc := markedState_encloses N ((N:ℝ)^(1/2-delta))
    (Fintype.piFinset (convolutionWuWindows N Delta V)) tupleProduct
    (fun _ => 1) (fun _ _ => True) bank rounds s
    (fun t ht => (hg t ht).1) (fun _ _ => by norm_num)
    (fun t ht => hpow.trans_le (hg t ht).2.2)
  rwa [labelled_count_eq_wuBoxPhi] at hc

end
end ImbalancedChen.P2ClassicalSeedCountAttachment
