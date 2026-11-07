import ImbalancedChen.CurrentChenBuchstabRefinement
import ImbalancedChen.Certificates.PairedV2

/-!
# The proved Buchstab barrier on the actual first adopted fibre

Part 2 supplies the exact support and its whole-fibre argument inequality.
Part 5 supplies the global bound for the actual pinned Buchstab function.
These lemmas compose those suppliers without adding an analytic premise.

The Part 2 integral already has coefficient `K / 80 = (K / 4) * (1 / 20)`.
This pointwise bridge does not insert a second Buchstab multiplier, claim
all adopted rows have passed, or supply their retained arithmetic parent.
-/

namespace ImbalancedChen.Certificates.PairedV2

theorem first_fibre_buchstab_eleven_twentieths {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (11 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) := by
  rcases first_fibre_argument hs with ⟨_, _, _, _, _, _, hargument⟩
  exact ImbalancedChen.currentChen_buchstab_eleven_twentieths hargument

theorem first_fibre_buchstab_gain {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2 := by
  have h := first_fibre_buchstab_eleven_twentieths hs
  linarith

end ImbalancedChen.Certificates.PairedV2
