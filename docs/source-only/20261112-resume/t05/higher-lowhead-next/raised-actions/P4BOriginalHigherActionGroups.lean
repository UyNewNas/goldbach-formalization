import ImbalancedChen.P4BOriginalHigherActionKeys
import ImbalancedChen.P4BOriginalHigherWordGrouping

namespace ImbalancedChen.P4BOriginalHigherActionGroups
noncomputable section
open scoped BigOperators
open Classical VariableEnvelope
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowRepresentative (d t atThird)
open P4BOriginalHigherActionWinner (SourceAction)
open P4BOriginalHigherActionKeys (needsAction chosen chosen_genuine genuine labels sel rest s localE coverLevel)
open P4BOriginalHigherLowBins (Groups theta)
open P4BOriginalHigherLowLocalWindows (theta_window conversion selected_window cover_power)
open P4BUpperSelectedBoxCapacity (endpoint endpoint_positive groups_partition monomials)
open P4BOriginalHigherLowTensor (word restore whole_word)
open P4BOriginalCollisionTensor (free products)
open P4AHeldTaggedCompilerSupport (J0)

def bins (P : Params) (x U z : ℝ) (J : List ℕ) (b : SourceAction P) : Groups :=
  let V := theta P.N x z (coverLevel P J b+localE P/4)
  P4BUpperSelectedBoxCapacity.groups (x^(V-2*z)) (U/x^z) (actualPrimeFineLabelIntegerUpper P.N P.T)
    (labels P (sel P J b)) (labels P (rest P J b)) J

def split (P : Params) (x U z : ℝ) (J : List ℕ) : Groups :=
  if h : needsAction P J then bins P x U z J (chosen P J h) else P4BOriginalHigherLowBins.split P x U z J

theorem split_perm (P : Params) (hN : 1<P.N) (x U z : ℝ) {J : List ℕ} (hJ : J∈P.words) :
    let S := split P x U z J
    (S.1++(S.2.1++S.2.2)).Perm J := by
  unfold split
  split_ifs with h
  · apply groups_partition
    exact P4BOriginalHigherActionKeys.labelled P J _ hN hJ (chosen_genuine P J h).1
  · exact P4BOriginalHigherLowBins.split_perm P x U z hJ

theorem same_word (P : Params) (hN : 1<P.N) (x U z : ℝ) {J} (hJ : J∈P.words) (F : ℕ→ℝ) :
    word P J (split P x U z J) F=word P J (P4BOriginalHigherLowBins.split P x U z J) F := by
  rw [whole_word P J _ (split_perm P hN x U z hJ),whole_word P J _ (P4BOriginalHigherLowBins.split_perm P x U z hJ)]

theorem complete_signed (P : Params) (hN : 1<P.N) (x U z : ℝ) (F : ℕ→ℝ) :
    (∑ J∈P.words,word P J (split P x U z J) F)-(∑ q∈P.S,P.rho q*F q)=
      ∑ q∈products P,P4BOriginalCollisionTensor.error P q*F q := by
  rw [Finset.sum_congr rfl (fun J hj => same_word P hN x U z hj F)]
  exact P4BOriginalHigherLowTensor.complete_signed P hN x U z F

theorem endpoints (P : Params) (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (step : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0<P.omega) {J : List ℕ} (hJ : J∈P.words)
    (h4 : 4≤J.length) (hlow : t P J 0≤mu) {x U z : ℝ} (hx : 1<x) (hz : 0<z)
    (hzE : z≤localE P/512) (hb : P.T*((J0 P.omega:ℝ)+1)≤z) (hlo : x^(1-z)≤(P.N:ℝ))
    (hhi : (P.N:ℝ)≤x^(1+z)) (hU : x^(2*z)≤U) (hU' : U≤x^(1/3+z/2)) (hell : 2*P.ell≤z/16) :
    let S := split P x U z J
    let H := actualPrimeFineLabelIntegerUpper P.N P.T
    let a := endpoint H S.1
    let b := endpoint H S.2.1
    let c := endpoint H S.2.2*x^(2*P.ell)
    a<U*x^(-z/100) ∧ U^2*b*c^2<x^(1-8*(z/100)) ∧
      x^(7/32:ℝ)*U*a*b^5*c^2<x^(2-15*(z/100)) ∧
      U^(23/16:ℝ)*a*b^(73/16:ℝ)*c^(39/16:ℝ)<x^(2-15*(z/100)) := by
  by_cases hraw : atThird P J
  · have h : ¬needsAction P J := fun hh => hh.2.2.1 hraw
    have hez : z≤(P.e:ℝ)/512 := by
      change z≤P4BOriginalHigherActionMargins.reserve P.e P.r P.n/4/512 at hzE
      linarith only [hzE,(P4BOriginalHigherActionMargins.reserve_bounds he P.r P.n).2.2.1,(by exact_mod_cast he : 0<(P.e:ℝ))]
    simpa only [split,dif_neg h] using P4BOriginalHigherLowEndpointBounds.original P hN he hes step ho hJ
      ⟨h4,hlow,hraw⟩ hx hz hez hb hlo hhi hU hU' hell
  · have hwin := (P4BOriginalHigherActionKeys.needsAction_iff P hN he hes step ho.le hJ).mpr ⟨h4,hlow,hraw⟩
    let b := chosen P J hwin
    let H := actualPrimeFineLabelIntegerUpper P.N P.T
    let E := localE P
    let M := coverLevel P J b
    let v' := theta P.N x z (M+E/4)
    let A := U/x^z
    let S := bins P x U z J b
    have nat := P4BOriginalHigherActionKeys.endpoints P J b hN he hes step ho hJ hlow hraw (chosen_genuine P J hwin) hb
    obtain ⟨hE,hEs,hM,hMc,hs,hs',hg,hdown,hup,hfull,hrest,hpos⟩ := nat
    have p : (labels P (sel P J b)++labels P (rest P J b)).Perm J :=
      P4BOriginalHigherActionKeys.labelled P J b hN hJ (chosen_genuine P J hwin).1
    have hp := zero_lt_one.trans hx
    have hn : 0<(P.N:ℝ) := by exact_mod_cast (show 0<P.N by omega)
    have hA : 1≤A := (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mpr (by
      rw [one_mul]; exact (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : z≤2*z)).trans hU)
    have hAu : A≤x^(1/3-z/2) := (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mpr (by
      rw [←Real.rpow_add hp,show (1/3:ℝ)-z/2+z=1/3+z/2 by ring]; exact hU')
    obtain ⟨hQ,hQ'⟩ := conversion hn hx hz hlo hhi
    obtain ⟨_,_,hθ,hθc⟩ := theta_window .first hE hEs hz hzE hM hMc hQ hQ'
    change 1/2≤v' at hθ; change v'≤cap at hθc
    have hD : (P.N:ℝ)^(M+z)≤x^(v'-2*z) := by
      rw [cover_power hn hx]; apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le : 1≤(P.N:ℝ))
      linarith only [hzE,hE]
    have hrest' : actualDwellSupport (x^(v'-2*z)/endpoint H (labels P (sel P J b))) ((labels P (rest P J b)).map H) :=
      fun i hi => (hrest i hi).trans (div_le_div_of_nonneg_right hD (by rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]; positivity))
    obtain ⟨hEl,hEu⟩ := selected_window (k:=z) hn hx hE hEs hz hzE le_rfl hlo hhi hM hMc hs hs' hg hdown hup
    have relax : actualSelectedSubproductUpper (1+z) v'≤actualSelectedSubproductUpper 1 v' := by
      unfold actualSelectedSubproductUpper; exact min_le_min le_rfl (by linarith only [hz])
    have Hm := monomials (alpha:=1) hx hz (by linarith only [hzE,hEs] : z≤1/12) hθ
      (hθc.trans (by norm_num [cap])) H _ _ _ p hpos hA hAu (fun i h => (hfull i h).trans hD) hrest'
      hEl (hEu.trans (Real.rpow_le_rpow_of_exponent_le hx.le relax))
    have perm' := split_perm P hN x U z hJ
    change ((split P x U z J).1++((split P x U z J).2.1++(split P x U z J).2.2)).Perm J at perm'
    rw [split,dif_pos hwin] at perm'
    have pos (l : List ℕ) (hl : ∀p∈l,p∈S.1++(S.2.1++S.2.2)) : 0<endpoint H l :=
      endpoint_positive _ _ (fun p hp' => hpos p (perm'.mem_iff.mp (hl p hp')))
    have hB := P4AOriginalFiniteFallbackOriginalLength.beta_and_length (alpha:=1) hx hz hell
      (zero_lt_one.trans_le hA) (pos S.1 (by intro i hi; simp [hi]))
      (pos S.2.1 (by intro i hi; simp [hi])) (pos S.2.2 (by intro i hi; simp [hi]))
      Hm.1 Hm.2.1 Hm.2.2.1 Hm.2.2.2
    have hAU : A*x^z=U := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hp _).ne'
    simpa only [split,dif_pos hwin,hAU,mul_one] using hB

def rule : P4BOriginalHigherWordGrouping.Rule := ⟨split,by
  intro P hN x U z J hJ; exact split_perm P hN x U z hJ⟩

end
end ImbalancedChen.P4BOriginalHigherActionGroups
