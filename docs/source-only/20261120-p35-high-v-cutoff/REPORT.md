# P3.5: exact intersection of high-V and actual global cutoff

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`dc813f8b623e97d5aa9ece6a051e951c72593123`. The containing commit is the
new SHA. Packet path `docs/source-only/20261120-p35-high-v-cutoff/`.
Lean source SHA-256:
`bc7684155026376e1b2ebc0cfc96f89f9fe605bef5c2da4476fdd4c1d618950e`.

## Exact candidate and manuscript relevance

The parent high-V statement requires `2*S^2 <= 2^j` on the two physical
charts. It left open whether a retained dyadic frequency block could
satisfy this condition. The current source derives the exact answer
from the actual common block and global cutoff, rather than assuming a
continuous inequality at the cutoff:

    J = globalCutoff D x epsilon
      = ceil((D.cScale / D.bScale) * x^epsilon),
    exists j in blockIndices J, commonMBlock J j nonempty
      and 2*S^2 <= 2^j
    iff J > 0 and 2*S^2 <= 2^(Nat.log 2 J).

The maximal retained dyadic left endpoint is used, not J itself. The
source proves the preliminary sharp equivalence `commonMBlock J j`
nonempty iff `2^j <= J`; the final clipped block is half-open at J+1,
so equality at J is retained. The reverse direction chooses exactly the
last log-2 block, whose index is in the original `blockIndices`.

Additionally, the candidate uses the literal identities
`D.cScale=D.bScale*S` and `J=ceil(S*x^epsilon)` to show the **necessary**
strict inequality `2*S^2 < S*x^epsilon+1` whenever such a retained
high-V block exists. Its contrapositive rules out this entire subcase
when `S*x^epsilon+1 <= 2*S^2`. The `+1` and strict inequality preserve
the actual ceiling; the paper's real threshold is not substituted for
the integer cutoff. These results are intended to route the parent
high-V estimate only to eligible dyadic blocks.

Nonempty here refers to the original **frequency block**. It does not
assert nonempty `chartLevels`, an actual nonzero beta, or a nonzero
spectral contribution. The real inequality is necessary, not claimed
sufficient; the exact iff above also captures the dyadic gap. No
instantiation of x, epsilon or the current packet geometry is supplied,
so this packet does not assert that the intersection actually occurs
or is absent in the full paper family. It does not add a new cutoff,
change either zero lane or truncate the actual tail.

## Sources and boundary

The full parent `Part3OriginalOppositeBlockHighV.lean`, blob
`bff8a915a55f496f154b0abf66710fdea9e89aff`, and its report were read.
The actual `Part3OriginalCommonPoissonLanes.lean`, blob
`00a797ac77cb444479ce097f4b44c56930489e32`, defines the exact
`positiveM`, `blockIndices`, `commonMBlock` and `globalCutoff`, and
keeps the reflected sign, both zero lanes and tail in the parent source.
`Part3OriginalPoissonPrimaryRows.lean`, blob
`a79de85826ebb58ea2eb10e649e6250c2a344236`, uses that single global J on
all six original pieces. `Part3OriginalCompletedReciprocalSource.lean`,
blob `a99ba7e76f13c45beac5bd459334c9a75dc7c5a7`, supplies the literal
ratio `cScale/bScale=S`; `Part3OriginalTwoZSourceAssembly.lean`, blob
`62d248aa63bd5d66db39f681732ead8291d8c7ae`, defines actual upper Z.
The exact `Nat.le_log_of_pow_le` and `Nat.pow_log_le_self` declarations
were checked in pinned mathlib `Mathlib/Data/Nat/Log.lean`, and the
`Nat.ceil_lt_add_one` use in pinned floor sources. The expected names
and proof scripts remain unelaborated.

The manuscript body at
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was rechecked: blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, matching
the chain. Distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`
and the actual global-cutoff passage in proof-library blob
`7a706f119d7835e860fce9a385118456319ae68c` were read. No new external
input is introduced. Prior Pascadi v3, ABL v1, regular sieve and gap
registrations and unfulfilled ranges remain unchanged.

## Verification and next obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the parent proof bodies. No exact import closure is
staged. `command -v lean` and `command -v lake` each exited 1 with no
output; no compiler ran, so there is no compiler exit code or log.
Repository pin files reread: Lean `leanprover/lean4:v4.33.0-rc1`,
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions are not
verifiable. Stack 8192 KiB and virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the hash above. The candidate scan `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; neither is compilation or a transitive axiom audit. No CI ran.
The root and docs/source-only `AGENTS.md` lookups returned 404.

Next stage and kernel-replay the exact import chain. Apply the iff to
the actual x/epsilon/scale constraints and prove chart occupancy only if
available. Handle the complementary physical regime, actual oldform
and raw-n expenses, chart test budgets, missing sharp full-weight J,
regular/holomorphic and continuous parts. Keep both zero lanes, actual
tail, 14eta/28eta, 128C enlargement, N threshold order and reserves.
