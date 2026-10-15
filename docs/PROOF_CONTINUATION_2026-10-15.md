# Mathematical proof continuation — 15 October 2026

This branch continues the mathematical proofs from Dot's integration commit
`3c51704ff4da3abc94cd06e39e62ee2a1bc4f6af`. It does not replace Dot's CI work
or change the authoritative automation control files. The manuscript remains
`ba6ec11d800eccc54406490631895e174de85766`; the target is still the full
Theorem 1.1 and Corollary 1.2 with the original `currentC` and `currentK`.

**Neither `hLower` nor `hUpper` is proved.** All results below are components.
The new leaves are not imported into `ImbalancedChen.lean`; a successful
existing root build would therefore not validate them.

## New mathematical results with executed checks

| Module | Mathematical content | Verification |
| --- | --- | --- |
| `CurrentChenPairLevelGeometry` | Actual pair multiplier, integer Rosser level, compact U5 profile, and restricted U6 profile | Strict compilation; original-object stock kernel replay; complete 17-declaration types, inventory and transitive axiom audit |
| `CurrentChenPairRosser` | Finite lower Rosser estimate for the actual quotient source, with the true `phi(b*d)` main term, full AP/centre errors and physical support `b*d <= Q` | Strict compilation; original-object stock kernel replay; complete 12-declaration audit |
| `CurrentChenUpsilon6KernelBuffer` | Integrability, positivity on the corrected product domain, and the actual logarithmic kernel integral limit as the product buffer tends to zero | Strict compilation; original-object stock kernel replay; complete 24-declaration audit |
| `CurrentChenUpsilon6OrdinarySieveKernel` | Identification with the canonical normalized continuous lower sieve factor, and the same buffer limit | Strict compilation; original-object stock kernel replay; complete 17-declaration audit |
| `Part3CenteredFourier` | Exact centered additive Fourier identities at composite moduli, retaining actual prime labels, weights and the primitive centre | Strict compilation; original-object stock kernel replay; complete 28-declaration audit |
| `Certificates/PairedV2FullBuchstab` | The actual Buchstab gain bounds the certified fibre kernel with `K/80 = (K/4)*(1/20)` used once | Strict compilation; original-object stock kernel replay; complete 4-declaration audit |
| `CurrentChenPairHarmonicMean` | The actual fifth prime-pair selector, its strict ordered triangle, true reciprocal-totient weights and varying-profile harmonic integral limit | Strict compilation; original-object stock kernel replay; complete 25-declaration audit |
| `CurrentChenPairMovingHarmonic` | The same integral at the genuine rounded integer row parameter, with the actual total phi-weight bound paying uniform perturbations | Strict compilation; original-object stock kernel replay; complete 10-declaration audit |
| `ActualSieveGapTailDecay` | Canonical continuous sieve gap positivity, monotonicity and quadratic tail decay, with the real source DDE supplied | Strict compilation; original-object stock kernel replay; complete 11-declaration audit |
| `ActualSieveGapTailBounds` | Exact reference value at three, the normalized `3/s^2` bound and the explicit logarithmic tail-envelope limit | Strict compilation; original-object stock kernel replay; complete 12-declaration audit |
| `Part3ComplexDispersion` | Actual complex-row Cauchy, centered norm-square and double-label identities, retaining the full moduli and primitive centre | Strict compilation; original-object stock kernel replay; complete 30-declaration audit |
| `ActualThirdPrefixTailIntegralCore` | Canonical correction kernel, finite noncompact triple-integral bounds and tail convergence allowing the cap/selector to vary with the cutoff | Strict compilation; original-object stock kernel replay; complete 59-declaration audit |
| `CurrentChenUpsilon5FiniteMean` | Actual U5 counts above the same row-dependent Rosser density sum, with full ordinary BV and centre costs paid; a fixed `B` precedes arbitrary `epsilon` | Strict compilation; original-object stock kernel replay; complete 17-declaration audit |

These thirteen modules contain **266 complete owned declarations**, including
private and generated declarations. The count is an inventory size, not
266 independent major mathematical theorems.

The U6 limit is an analytic integral limit on the literal corrected rectangle.
It does not exchange the arithmetic `N` limit with the buffer limit, supply the
`E` mask or the stronger `h248` kernel, or certify the adopted numerical `L6`.

## Candidates that must not be counted as completed proofs

The six unaccepted source files are preserved in a separate source-only
commit. Their exact hashes and original failed attempts are listed in
`verification/proof-continuation/2026-10-15/unaccepted-candidates.json`.
They are excluded from the 13-module / 266-declaration acceptance count.

* `CurrentChenPairDensity` and `CurrentChenUpsilon5OrdinaryMean` contain the
  proposed actual U5 ordinary mean argument. The new one-sided density route
  avoids the unnecessary two-sided density limit and its `ActualRosserOddBox`
  import. Independent source review confirmed the uniform thresholds,
  nonnegative factors, epsilon budget, true total phi-weight bound and final
  count statement. The density's combined imports still failed the 6144 MiB Lean
  resource check at about 6.31 GiB RSS, before target elaboration. The final
  integral-normalized count mean remains unexecuted; its finite BV/centre
  payment is verified separately above. A source review is not execution evidence.
* `CurrentChenUpsilon6OrdinaryMean` is an unfinished source candidate through
  the fixed-positive-buffer selector/harmonic/normalized-main-sum layer.
  The final actual quotient-count Rosser/BV payment is not written or checked.
* `Part3ReciprocalAPSupplier` specializes fixed upstream reciprocal-phase
  estimates to the actual full modulus and gamma gates. Its new target has
  not been compiled: the limited bootstrap stopped at an external prerequisite
  resource failure. Ordinary BV does not thereby reach the stronger
  physical distribution cap.
* `ActualThirdPrefixTailIntegral` retains the broad arithmetic tuple/profile
  bridge. The canonical integral core is verified separately, but this
  wrapper, the actual adopted extended selector and its measurable/Fubini/
  mean assembly remain unverified obligations.
* `Certificates/PairedV2FullCertificate` connects the actual natural numerator
  sums to the full analytic integral. It still requires the complete original
  strip verification chain. Dot's pilot is not all-strip acceptance.

The finite Fourier and complex-dispersion identities do not supply the
common completion, reciprocal-phase dictionary or aggregate gcd estimate
needed for the analytic distribution bound. The Buchstab kernel comparison does not pay arithmetic parent
licensing or the mean-value passage.

The scalar tail and integral candidates have been split at an actual import
boundary: `ActualThirdPrefixTailIntegralCore` keeps the canonical kernel,
noncompact integral bounds and cap-tail convergence; the original broad
module retains only the arithmetic tuple/profile bridge. This removes the
large density/transport imports from the core, without proving the remaining
adopted-selector or arithmetic-mean identification.

## External work reused

The fixed mathlib and `goldbach` dependency commits in `lake-manifest.json`
are unchanged. Existing prime harmonic measures, Rosser estimates, canonical
continuous sieve functions, Buchstab estimates and additive-character
orthogonality are reused rather than reimplemented.

In particular, source inspection of the pinned `goldbach` commit
`09b97db5764ade1246bfb77206baa1b124760958` found actual unconditional
`completeKloosterman_weil` and reciprocal progression suppliers in
`LiLiuPrereqFouvryCompleteWeil` and `LiLiuPrereqFouvryProgressionWeil`.
The selected 129-module `goldbach` source set passed a forbidden-token screen;
that screen does not constitute kernel replay, a compiled new consumer,
or the missing current strong distribution theorem.

## Verification scope and resources

Successful owned-module audits compare the complete serialized declaration
inventory with the imported environment, export full types, reject unsafe,
partial and axiom declarations, and check transitive axioms are contained in
`propext`, `Classical.choice`, `Quot.sound`. Original bundled `leanchecker`
replays the actual owned object. This is not a claim that every external
imported declaration was independently replayed.

The historical runtime-v1 source walker recognized plain `import` headers
and omitted `public import` headers used by the pinned mathlib. Its recursive
closure sizes and recursive cache bindings are therefore incomplete. Actual
Lean compilation, stock replay and the Lean environment/type/axiom census
process the real imports; those executed owned-module checks are distinct
from this metadata limitation. No external cache is promoted to full
independent acceptance on the strength of that walker. Its original tools
and receipts are preserved, with the corrected inventory recorded separately.

One heavy process runs at a time with two Lean threads. The default Lean
budget is 4096 MiB. Measured import failures justified specific 6144 MiB
runs with an identity-bound 6656 MiB RSS monitor; the monitor is periodic,
not an operating-system hard cap. Resource failures remain failures.
No dependency pin, proof checker, analytic axiom or theorem premise was
weakened to obtain a pass.

The finite U5 payment initially exceeded the budget through an unrelated
normalization import. Replacing that import by the existing explicit
`singularNormalization_lower` bound and a concrete logarithmic threshold
preserved the complete BV-paid count statement. Its final strict source
run peaked at about 4.49 GiB, compared with the earlier 6.36 GiB failure.
All approved compiler/checker processes had terminated at this checkpoint.

Exact successful receipts, logs, type exports and source/object hashes are
archived under `verification/proof-continuation/2026-10-15/`. Imported cache
objects used during development are not automatically promoted to complete
independent audit status. In particular, inherited remote-cache entries are
development-only even when their exact source/object hashes match.

## Next mathematical obligations

1. Compile and replay the actual U5 mean chain, resolving its old import
   resource obstruction without changing the required analytic statement.
2. Pay the actual strong distribution/dispersion obligations with the full
   prime source, moduli, weights, primitive centre and errors retained.
3. Complete the adopted-selector density, tail and coefficient assembly for
   the real upper count; do not assume the final bound as a supplier.
4. Close all eleven corrected current lower mean terms, the actual paired
   deletion licenses and numerical constants, then discharge `hLower`.
5. Discharge `hUpper` for every fixed `1/2 < b < 1`, assemble the current
   main theorem and corollary, and run the full required integration gates.
