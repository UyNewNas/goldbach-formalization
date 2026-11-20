# P3.5: sufficient and excluding conditions at the actual last block

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`20446ab414117b347c1f63d47ff111970b0bbf9a`. The containing commit is the
new SHA. Packet directory `docs/source-only/20261120-p35-high-v-last-block/`.
`Part3OriginalHighVLastBlock.lean` SHA-256:
`cbe7536fa650dba9363ae0134a81fd8e81d496acfac800f5fbc73c4233b730d1`.

## Proposed exact deduction

Write S=`scaleS D.key`>=1, J=`globalCutoff D x eta`=ceil(S*x^eta),
j=Nat.log 2 J, and Z1=`fixedZ D true`=2*S^2. On the actual original
data, `last_block_highV_of_large_cutoff` states that

    0 < x and 4*S <= x^eta
      imply j in blockIndices J,
            commonMBlock J j nonempty, and Z1 <= 2^j.

Indeed the exact original ceiling covers S*x^eta, so J>=4*S^2;
`J < 2^(j+1)=2*2^j` then gives `2*S^2 < 2^j`, and J>0 supplies the
literal last clipped block. The source proves the weak endpoint needed
by the parent and keeps the original ceiling and half-open block.

Conversely, `no_highV_of_small_cutoff` proves that `x^eta <= S` excludes
every retained high-V block: S*x^eta+1<=2*S^2 follows from S>=1 and the
parent's exact strict-ceiling obstruction. These sufficient conditions
are not complementary; the actual transition region is decided by the
parent's exact dyadic iff, not by extrapolating either sufficient bound.

`last_block_opposite_initial_bound` composes the positive case with
`opposite_block_highV_initial_price`: it chooses the exact original
J and last j, proves the block nonempty, and obtains the existing
opposite full-block inequality for the same j, J, both physical chart
scales, original Fourier coefficient and original level-dependent raw
n cost. The parent C is selected before D and all moving parameters;
the two chart budgets precede r and Poisson sign. The composite sign
restriction and all nonexceptional/continuous terms remain explicit.
No new spectral bound, oldform estimate, target-shaped hypothesis, or
unproved coefficient-independence statement is introduced.

The positive theorem is conditional on the actual scale inequality; it
does not construct admissible OriginalData satisfying it, assert that a
physical chart or beta is nonzero, or claim a whole-family contribution.
It removes only the additional 3/4 transport multiplier for this block;
the inherited baseline price, raw n loss, test-profile costs and other
spectral terms remain. It does not prove (24), full J or full-cost 7/32.

## Sources and boundary

The full parent `Part3OriginalHighVActualCutoff.lean`, blob
`43daf48469b10177f80ed131f79e51e802119070`, and its report were reread.
The preceding `Part3OriginalOppositeBlockHighV.lean`, blob
`bff8a915a55f496f154b0abf66710fdea9e89aff`, supplies the precise
uncompiled high-V full-block statement. The actual source of common
blocks and global cutoff is blob `00a797ac77cb444479ce097f4b44c56930489e32`;
the exact fixed chart scales are blob `62d248aa63bd5d66db39f681732ead8291d8c7ae`.

The full existing long-m source blob `838f46b36664aaac0cc9bddf96fe1cecdb512882`
and wider-budget source blob `7328fb7b76d60d5f9e1bbabfc49a7425406c64d2`
were read. They give necessary upper scale bounds and reduced-pair
estimates with an explicit transport fee; this packet instead gives a
sufficient condition for the last actual block and consumes the raw
opposite full-block candidate. Neither proves that an actual nonzero
arithmetic row exists. Pinned mathlib `Mathlib/Data/Nat/Log.lean`
supplies `Nat.lt_pow_succ_log_self` and `Nat.pow_log_le_self` with the
same dyadic endpoints.

The manuscript body pin
`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`
was confirmed as blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`;
original (24) and the global real cutoff were reread in distribution
blob `19f9672bc9b6d455045213c5e23e10433a9569d2`. No external theorem is
newly introduced. Pascadi v3, ABL v1, regular input and spectral-gap
registrations and unsupplied ranges retain the prior status.

## Verification and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including parent candidate bodies. No exact import closure is
staged. `command -v lean` and `command -v lake` each exited 1 without
output. No compiler ran; no compiler exit code or log exists. Config
pins reread: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot be
verified. Stack 8192 KiB, virtual memory unlimited, unchanged.
`sha256sum` exited 0 with the hash above. Candidate `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` exited 1 without
matches; these are not compilation or a transitive-axiom check. No CI
ran. Applicable root/docs AGENTS checks were previously recorded absent.

Next stage and elaborate the exact import chain, kernel replay and
audit axioms. Instantiate the scale inequality on the actual allowed
family, separately establish any needed nonzero-row occupancy, and
handle all other dyadic blocks. Pay the raw n/oldform expenses and test
budgets, supply the missing sharp J/gap and regular/continuous/
holomorphic estimates, and preserve both zero lanes, actual tail,
14eta/28eta, 128C, N-threshold order and reserve payment.
