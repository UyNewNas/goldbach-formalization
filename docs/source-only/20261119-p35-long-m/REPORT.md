# P3.5: occupied long-m transport and its physical range

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734` was read
at `2152035f969bc1e0fe8f5d47aba008f4c5c0d6eb`. The commit containing this
packet is the new SHA. This packet adds only
`Part3OriginalLongMTransport.lean` and this report under
`docs/source-only/20261119-p35-long-m/`. Candidate source SHA-256:
`663b26e0aedab639b3475f3788ba41e9eced627c200ab0b840036516745619be`.

## Precise candidate results

Fix nonnegative delta and eta and `x>=1`. For the literal dyadic Poisson
block `V=2^j`, the actual chart `Z=fixedZ D upper`, and the inherited
`M=V-1/2`, suppose the block is occupied at the **original common**
`globalCutoff D x (eta/2)` and falls in the physical subrange

    Z <= V*x^delta.

The proposed `longM_transport_factor` uses `Q>=Z/2`, including both
original lower endpoints `Q=Z/2,Z`, and derives

    max(1, max(V,Z^2/V)/(Q+M))^(3/4) <= 2*x^delta.

Indeed `M>=V/2` and `Q>=Z/2` give `V/(Q+M)<=2` and
`Z/(Q+M)<=2`; the displayed branch condition gives `Z/V<=x^delta`.
Thus both terms inside the physical threshold cost at most `2*x^delta`.
The final power 3/4 is bounded by the base because the base is >=1.

`occupied_longM_pair` then composes this exact charge with the preceding
actual post-removal pair on **both** real level intervals, retaining one
phase, the same true `globalCutoff`, both original chart/sign flags, the
strict exceptional slots and the level-dependent n-side row mass. The
initial-mean epsilon, cutoff eta and squared-energy fee delta are kept
independent. The condition concerns the actual frequency and chart, not
an assumed version of the target spectral estimate.

This branch extends the earlier sufficient small-S condition in parameter
space, but it is not the full physical range. `occupied_longM_scale_limit`
records an explicit limitation: with `S=scaleS D.key`, the original
occupied-block cutoff and the displayed branch condition imply

    S <= 2*x^(delta+eta/2).

Here `Z>=S^2`, while the existing exact global cutoff gives
`V<=2*x^(eta/2)*D.cScale/D.bScale = 2*x^(eta/2)*S`.
The new theorem does not claim every scale below the necessary cap has an
occupied actual row, nor that data outside the branch are bounded.

As a finite scale-level consistency check only, choose `x=2^100`,
`delta=eta=1/10`, `S=2^10`, `V=2^14`, lower-chart `Z=S^2`, and
`J=S*x^(eta/2)=2^15`. Integer arithmetic confirms `Z<=V*x^delta`, the
prior small-S condition `S<=x^(delta/2)` fails, and the literal interval
`[V,min(2V,J+1))` is nonempty. This is not a constructed admissible
`OriginalData`, a nonzero n-side row, a universal proof or Lean checking.

The inherited 3/4 coefficient-transport supplier remains source-only;
the added `2*x^delta` is a separately allocated squared-energy loss, not
the requested spectral gap or sharp full-range Pascadi J. Raw discrete
oldform and continuous return, gap denominator, full (24), both zero
lanes, cutoff tail, distinct 14eta/28eta weights, original 128C extension
and joint reserve remain unresolved. No target estimate is assumed.

## Source pins and verification

* `docs/source-only/20261119-p35-all-chart-lossy/Part3OriginalAllChartLossyPair.lean`,
  Git blob `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`: previous reduced
  pair with explicit 3/4 transport. It and its transitive imports remain
  uncompiled.
* `docs/source-only/20261102-resume-30p/exceptional_j_eta/Part3OriginalAdditionalSpectralCosts.lean`,
  blob `e957c4985864f7ea8124d333cd9f7efb82363ada`: occupied common-block
  scale bound, with the factor 2 from the actual ceil cutoff.
* `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean`,
  blob `00a797ac77cb444479ce097f4b44c56930489e32`: literal global cutoff
  and `Ico (2^j) (min (2^(j+1)) (J+1))` common block.
* Paper `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  main blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24)–(25)
  and §10(v)–(vii), remains the same pin. Pascadi v3 A/J, ABL v1 3.1/3.2,
  the regular sieve and numerical gap remain separately documented inputs;
  none is axiomatized or newly proved by this packet.

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not inspected. Independent review: not performed. `UNEVALUATED`:
yes, including source-only dependencies. Lean/Lake are unavailable in
the existing environment and the pinned import closure is unstaged; no
compiler ran and no compiler exit status or log exists. The configured
pins are Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` and native
`09b97db5764ade1246bfb77206baa1b124760958`; configuration is not runtime
verification. Stack limit 8192 KiB and virtual-memory limit unlimited;
no resources were expanded.

`sha256sum` produced the candidate hash above. The precise `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` scan returned 1 (no
matches). The stated integer scale check returned all four booleans true
and exit 0. Neither is elaboration. No CI, Codex, or user machine was
invoked. Next check the exact staged closure and proof terms; establish
whether an original nonzero row can occupy this interval; account for the
delta charge in the full reserve, and handle its complement with the
sharper averaged input or a separately justified reduction.
