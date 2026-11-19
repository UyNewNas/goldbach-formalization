# P3.5: small-Q2 tight-atlas specialization, source-only handoff

## Baseline and files

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734` was read at
`9c02f68dfb8258f8feeb9006e11d72c724296238`; the containing commit supplies
the new SHA. This packet adds only `Part3OriginalSmallQ2Atlas.lean` and
this report in `docs/source-only/20261119-p35-small-Q2/`.

Candidate source SHA-256:
`9a1bcfecf64c57e169abf81b3d4829ed6154deb6d6f16ec16a17f366733d2cd4`.

## Precise proposed adaptation

Fix `epsilon>0`, `delta>0`. The candidate `tight_atlas_smallQ2_pair`
selects the original reduced-pair constant C and one threshold X before
the admissible atom, its original occupied key, the earlier prefix,
rectangles, polarizations, both actual Z-chart flags, Poisson signs,
cutoffs and Fourier labels. It applies to the genuine `tightOriginalData`
record built from `MediumAdmissible`, `k in keyBank atom z y`, and
`small in activeD atom k`.

It replaces the previous candidate's direct `S<=x^(delta/2)` premise by
the following narrower condition on the paper's original modulus length:

    x = atom.scale >= X,       atom.Q2 <= x^(delta/4).

The existing actual rough-owner geometry gives `S<=2*Q2` for precisely
the occupied original key. Choose X, depending only on delta, such that
`x^(delta/4)>=2` for every `x>=X`; then

    S <= 2*Q2 <= 2*x^(delta/4) <= x^(delta/2).

The previous small-S candidate supplies the same two-chart, both-sign
reduced-pair bound, with its explicit extra squared-energy charge
`6*x^delta` and the independent initial-mean epsilon. No `S` bound or
spectral conclusion is postulated on top of the named Q2 condition. The
same phase, both endpoint-corrected J intervals and the level-varying
n-side row mass are inherited from the exact source the previous candidate
calls. This is source-level composition only until all imports elaborate.

The Q2 condition is **not** asserted for every admissible atom, and no
individual occupied nonzero source has been constructed in this run. To
check that it is compatible with the manuscript's displayed numerical
scale inequalities, take sigma=1/200, kappa=0, c0=1, `|a|=x`,
`N=x^(1/5)` and `Q1=Q2=Q3=1`. For x>1 the four strict exponent pairs
are `(0,39/200)`, `(2/5,24/25)`, `(67/160,77/40)`, `(23/80,77/40)`,
all in increasing order. Moreover `Q2=1<=x^(delta/4)` for delta>0.
This checks only those paper-level scale inequalities; it is not a Lean
proof, a construction of an occupied key or a nonzero spectral row, nor
a certificate of every condition on an admissible data record.

The complementary large-Q2/small-S mixed region is not handled by this
specialization; the original small-S theorem still applies when its
condition is independently satisfied. The unbounded-S branch, the sharp
full J estimate and 7/32, raw oldform/continuous return, denominator,
both zero lanes, tail, 14eta/28eta weights, 128C enlargement and joint
reserve are not proved. In particular the displayed `6*x^delta` charge
must be allocated in addition to the other fees; it is not a spectral
gap or an alternative proof of (24).

## Exact source selection and external boundary

* `docs/source-only/20261119-p35-small-S/Part3OriginalSmallScaleTransport.lean`,
  Git blob `54e439c04d9789333b31f9735e675f981c045ce3`: original small-S
  pair candidate, uncompiled, with its separately frozen upstream pair.
* `docs/source-only/20261102-resume-30r/uniform_seven32/Part3OriginalSixTailPhysicalPayment.lean`,
  Git blob `9cb0685d512b97d6165b8d1840b168f84c6c340c`: only the existing
  `tightOriginalData` definition is used; its tail argument is not redone.
* `docs/source-only/20261028-resume-30g/medium_variance/Part3ActualOriginalSpectralScales.lean`,
  Git blob `e983a994505e495bd5318787ee0782ecf4ea310b`: original occupied
  `actual_rough_owner_geometry`, including `roughS k<=2*atom.Q2`. Its
  `roughS` is definitionally the same `2^k.u` as `scaleS`.
* Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  main blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §§1 and 7,
  is the same pin as the preceding handoff. Section 7 identifies S with
  the rough Q2 length; §10 specifies the separate Pascadi A/J, ABL,
  regular, normalized trace and numerical gap inputs. This packet does
  not add, reprove or disguise any of those external inputs.

## Verification and next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the inherited source-only candidate closure. The current
environment has no Lean/Lake executables and no staged pinned imports;
no compiler command ran, and no compiler exit code or log exists. The
base configuration records Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, and native
`09b97db5764ade1246bfb77206baa1b124760958`. The shell stack limit is
8192 KiB; virtual memory is unlimited. No resource was increased.

`sha256sum` produced the candidate hash above. The exact token search
`rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 (no
matches). A Python `fractions.Fraction` check of the four numerical
exponent pairs exited 0 and returned all strict; it does not execute Lean.
No CI, Codex, or user machine was invoked. Next, verify the actual
nonempty-key scope and allocate delta against the original total reserve,
then elaborate the exact frozen dependency closure and this candidate.
The large-S complement needs a sharp independent J input or another
actually payable bound, with all downstream costs retained.
