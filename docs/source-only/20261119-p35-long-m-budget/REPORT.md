# P3.5: wider long-m branch at the same transport budget

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734` was read
at `4cae0510f7c5c830391d38982d6b13eb9467a0a9`. The enclosing commit is
the new SHA. This packet adds `Part3OriginalLongMSharpBudget.lean` and
this report under `docs/source-only/20261119-p35-long-m-budget/`.
Candidate SHA-256:
`9508880040d554c869af3f0d118fcb4ac54c5c52a38d1e88518d041047b4053c`.

## Candidate deduction and physical scope

The previous candidate `longM_transport_factor` paid `2*x^delta` when
`Z<=V*x^delta` by replacing its positive 3/4 power with the base. The new
proposed `longM_sharp_transport_factor` retains that existing 3/4 power.
For fixed `delta>=0`, `x>=1`, original `V=2^j`, `M=V-1/2`, either
actual `Z=fixedZ D upper`, and either original level endpoint `Q=Z/2,Z`,
it uses the wider explicit frequency condition

    Z <= V*x^(4*delta/3)

and proposes the same squared-energy transport payment

    max(1, max(V,Z^2/V)/(Q+M))^(3/4) <= 2*x^delta.

The physical denominator gives `V/(Q+M)<=2` and `Z/(Q+M)<=2`.
Thus the unpowered max is at most `2*x^(4*delta/3)`; applying 3/4 yields
`2^(3/4)*x^delta<=2*x^delta`. This deduction uses the previous actual
3/4 coefficient-transport source, not an assumed new spectral estimate.
The name `sharp` refers only to preserving that 3/4 exponent in this
elementary budget; it is not sharp Pascadi J or the requested 7/32 gap.

`occupied_sharp_longM_pair` composes this proposed bound with the same
actual reduced Cauchy pair and the literal nonempty common Poisson block
at `globalCutoff D x (eta/2)`. Both level intervals, one common phase,
strict exceptional slots, n-dependent row mass, both chart/sign flags,
and the existing `epsilon`/`eta` parameters are preserved. `2*x^delta`
is an added and explicitly displayed **squared-energy** fee.

`occupied_sharp_longM_scale_limit` calls the prior physical cutoff
candidate at exponent `4*delta/3`. It records the necessary condition

    S <= 2*x^(4*delta/3+eta/2).

It does not imply that every scale satisfying this inequality is occupied
or that the complementary large-S range is controlled. Raw oldform and
continuous return, the numerical gap and denominator, sharp J, complete
(24), the two zero lanes, actual tail, 14eta/28eta Fourier fees, 128C
extension and the global reserve are all still open. There is no extra
target-shaped hypothesis or new axiom in this packet.

Finite scale arithmetic only: take `x=2^120`, `delta=eta=1/10`,
`S=2^19`, `V=2^24`, lower-chart `Z=S^2` and global-cutoff integer
`J=S*x^(eta/2)=2^25`. Exact integer checks give: the widened condition is
true, the old `Z<=V*x^delta` condition is false, the old small-S
condition is false, and `[V,min(2V,J+1))` is nonempty. This is not a
constructed admissible OriginalData or nonzero spectral row, and is not
a proof or Lean elaboration.

## Source and external-input boundary

* Previous `docs/source-only/20261119-p35-long-m/Part3OriginalLongMTransport.lean`,
  Git blob `838f46b36664aaac0cc9bddf96fe1cecdb512882`, supplies the
  cutoff-based necessary scale limit with a free nonnegative exponent.
* `docs/source-only/20261119-p35-all-chart-lossy/Part3OriginalAllChartLossyPair.lean`,
  blob `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`, supplies the inherited
  reduced pair and its 3/4 transport candidate. Neither source nor its
  import closure has been compiled in this environment.
* The exact common block and global cutoff are in
  `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean`,
  blob `00a797ac77cb444479ce097f4b44c56930489e32`.
* Paper pin `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  main blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §§7 and 10(v)–(vii),
  matches the earlier handoffs. The exact Pascadi v3 A/J, ABL v1 3.1–3.2,
  regular sieve and numerical gap remain external inputs in that source;
  this packet does not reprove or axiomatize them.

## Validation and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not inspected. Independent review: not done. `UNEVALUATED`: yes,
including inherited source bodies. Neither `lean` nor `lake` is available
in the task environment, and the exact dependency closure is unstaged;
no compiler command ran, so no compiler exit code or log exists. The
recorded configuration remains Lean `leanprover/lean4:v4.33.0-rc1`,
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native
`09b97db5764ade1246bfb77206baa1b124760958`. Stack limit: 8192 KiB;
virtual memory: unlimited. No resource was increased.

`sha256sum` returned the source hash above. The `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` token scan returned 1
(no matches). The stated finite integer scale check returned
`wider=true, old=false, nonempty_Ico=true, old_small_S=false` and exit 0.
These are not compilation. No CI, Codex or user machine was invoked.
Next stage and elaborate the frozen source closure, check transitive
axioms and obtain independent review; separately handle the complement
with sharp J or another truly payable input and account for delta alongside
all remaining original spectral and Fourier expenses.
