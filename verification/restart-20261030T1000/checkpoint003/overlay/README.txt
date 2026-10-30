Approved dependency overlay — stage001

Base package: goldbach 09b97db5764ade1246bfb77206baa1b124760958.
This is NOT unmodified fixed-pin source. dependency.patch adds noncomputable
to finiteNodeAtomSum, finiteNodeVariationSum, finiteNodeStieltjesSum only.
All original declaration types and equation/proof body source bytes remain unchanged.
Native executable code is deliberately no longer generated for these definitions.

Reconstruction: require exact clean base package and verify manifest base hashes;
check dependency.patch SHA256, then git apply --check and git apply that patch
inside the goldbach package. Verify every patched source SHA256 against manifest.
Do not apply to a different pin or silently ignore other package changes.

Validation: local overlay001 genuine Lake -M4096/full outputs/setup, trust0;
full own-declaration transitive axiom audit permits only propext, Classical.choice,
Quot.sound; exact own-declaration kernel replay against imports; independent PASS.
45 own declarations. Local aggregate sampled RSS6144MiB, 1800s/source, absolute
round deadline 2026-10-30T14:30:00Z. This is not a claim that full CI is green.

The main repository does not yet automatically apply this overlay in CI.
Source patch preservation is separate from CI integration and full-root success.
