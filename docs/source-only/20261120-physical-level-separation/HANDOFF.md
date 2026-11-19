# Durable P1.4 handoff — physical level separation

Live branch: chatgpt/p1-full87-physical-level-separation-20261120-0505
Parent confirmed: b25c0cd95edb7934d85c79b9beb4d35984697f4f
Proof source commit: f6637ec2054653579763fa853a4dc7a8965ce7af
Source: docs/source-only/20261120-physical-level-separation/P4AOriginalFull87PhysicalLevelSeparation.lean
Source blob: cc25cdbc586269761706a9876426a07c0aab0ea1

STOP POINT: New candidate proves for real original quotient a, Q=a*(p::pre).prod > N/2, hence Q is OUTSIDE any physical cutoff B with 2B<=N. For any coefficient genuinely supported d<=B, rho(Q)=0. This invalidates the prior implicit plan to identify the original one-shell full-Q AP with the manuscript SAME-rho physical coefficient directly. It does NOT invalidate the finite one-shell AP identity or assert that the manuscript theorem is false.

Next ACTUAL math action: reconstruct physical R_N(n)=sum_{d|n}rho_N(d), with n=N-P and d the true small/rough divisor. Find the actual physical coefficient source, its distinct modulus support and original same-parent occurrence aggregation. Match that rho_N(d) with the manuscript smooth labelled-prime product PP, rather than identifying d=n. Confirm the final physical level B is <=N/2 for sufficiently large even N under frozen parameters. Keep lower-half separate and preserve every occurrence and sign.

Verify on pinned Lean v4.33.0-rc1/mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/native 09b97db5764ade1246bfb77206baa1b124760958. Local lean/lake/elan exit 127, so status stays SOURCE_ONLY/UNEVALUATED/UNCOMPILED; no kernel replay, axiom audit or independent check. Do not run CI or modify main.

For all further work, read latest branch HEAD and this packet's REPORT, REGISTRY and INPUT_BOUNDARY; do not return to initial 9649ab3 as a baseline.