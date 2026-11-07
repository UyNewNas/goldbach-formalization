# I medium_assembly: original signed arithmetic payments

The focused local step is implemented in source; the broad restricted-medium task is OPEN. Both Lean modules are uncompiled, `kernel_verified=false`, and `formal_credit=0`. The assigned model and effort in I/TASKS are `gpt-6.1-sol` / `xhigh`; this is assignment metadata, not an independent runtime attestation.

Only `docs/source-only/20261102-resume-30i/medium_assembly` was written. No compiler, Lean/lake/build, CI, checker, finite mathematical replay, quota inspection, subagent, commit, production edit, H edit or older-source edit was performed. Validation consists of manual comparison of source statements/proof bodies and original passages, read-only declaration searches, local existence checks and SHA256 inventories. Independent review and user-owned compilation are still required.

## Original obligation and selected missing step

The current production caller is `ImbalancedChen.Part3.RestrictedMediumObligation` in `ImbalancedChen/Part3DistributionTargets.lean`, on branch `codex/proof-continuation-20261015`, HEAD `25afcbff11562df51ef7ac5113c879123fcd64c6`. The actual `MediumAtom`, `MediumAdmissible`, primitive coprime mean, `signedError`, `UniformAuxiliarySW` and complete target were read directly. The original physical modulus remains `q1*q2*q3`; x is atom.U*atom.V, and the theta=7/32 range monomials and original moving signed residue are unchanged.

The authoritative manuscript body is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, proposition `prop:current-medium`, lines 125–168. Its detailed internal proof is `paper/source/modules/distribution-medium-completion-20261010.txt`: lines 94–124 give the original product and occupied-key geometry; lines 126–137 distinguish the initial one-bounded-beta branch from the general divisor-bounded-beta transfer; lines 156–169 give the preliminary exact-product deletion and the distinct S2 mean-weighted single-zero restoration; lines 183–189 give the two different off-diagonal S3 single zeros; lines 192–257 fix the same MT/P and original outer Cauchy scale. Exact current raw hashes are recorded in REGISTRY.

H has three genuine, independently defined inputs, rather than a completed parent medium theorem. Its S1 lane pays the actual LINEAR smooth discard in the initial B=0 branch and inserts it into G's unchanged signed entrance. Its S2 lane pays the actual `singleZeroCorrection` with its right-leg reciprocal-totient mean at `fixedDScale=V*U^2/(Q1*2^k.d)`, but leaves all-key assembly open. Its S3 lane pays `restorationCorrection=actualDiagonal-actualFirstZero-actualSecondZero`, including both genuine off-diagonal single zeros, at the original outside scale. H's S2 correction is not either S3 single zero. I consumes these exact proof declarations without assuming a final residual bound.

The previously missing step removed here is the S2 mean-weighted single-zero payment after the real outerL2 and BOTH owner-bank multiplicities, followed by its joint insertion with H S3 restoration in the existing original residual and in H's signed B=0 entrance at one uniform threshold.

## Source route and declarations

`Part3OriginalAllKeyS2SingleZeroPayment.lean` names only the actual outside norm budget `actualOuterS2SingleZeroBudget`, not another residual ledger. `original_all_key_S2_singleZero_log_payment B kappa A` consumes H's `exists_actual_S2_singleZero_arbitrary_log kappa D` at

    D = A + betaMomentOrder(B) + 12.

The actual key membership is unfolded from `originalNumericKeys`; no free-key geometry is assumed. The already proved outerL2<=6*Y*betaL2 cancels the actual fixedDScale denominator Y. The genuine ordinary beta divisor-square mean supplies betaL2<=2*V*C_beta^p*log(x)^p. The two actual key multiplicities cost `(2*C_key)^12*log(x)^12`. Thus the proved all-key constant is

    Cs = 12*Cz*C_beta^p*(2*C_key)^12,

and the returned scale is precisely x^2/log(x)^A. The local H constant and threshold were chosen before every atom, residue, receiver and occupied key. I fixes B before requesting D and preserves that ordering. A can be any real for this all-key arithmetic theorem.

`Part3OriginalS123CombinedArithmeticPayment.lean` proves `original_signed_packets_le_after_S2_S3_split` by H's actual source identity

    remainingCorrectionKey = restorationCorrection + offDiagonalOmitted - diagonalRetained.

Only the real parts of `restorationCorrection` and `singleZeroCorrection` are replaced by their norms. The remaining signed source is kept, including `+offDiagonalOmitted`, `-diagonalRetained`, `+roughReplacementCorrection`, `-genuineDiagonalZero`, and `-2*(actualS2NonzeroModes-otherRoughCorrection)`. The optional real summand g carries the original zero-Gram term in the existing actual residual; g=0 is used only where H's paid entrance has already paid it. This is an elementary quantified sum lemma, not a new residual definition or a supplied source-binding hypothesis.

`original_all_key_S2_S3_correction_log_payment` combines the genuine budgets as restoration+2*S2-single-zero with constant `Cc=Cr+2*Cs` and threshold `max Xr Xs`. It has no SW, spectral, retained-source-smallness or whole residual premise.

`exists_actualResidualFunctional_S2_S3_arithmetic_paid` uses G's exact `actualResidualFunctional_eq_complete_original_packets`, then the preceding split and genuine payment. It applies to arbitrary fixed B and leaves the original zero-Gram real part explicit, together with every unpaid signed source. This is a consumer in the existing F/G `actualResidualFunctional`; that definition is neither modified nor replaced.

`uniformAuxiliarySW_one_bounded_original_signed_source_arithmetic_paid` consumes H's actual B=0 paid linear entrance and the preceding joint correction theorem. It returns one constant `Ce+3*Cc` and one threshold `max Xe Xc`, chosen before every family atom. S1/P, S2 zero-Gram, preliminary exact products, actual LINEAR smooth discard, S2 mean-weighted single zero and S3 restoration therefore share a single error allocation. The original factor 3, outerL2, twice-counted owner bank and factor 2 on S2 are unchanged. A>0 is the same requested final log precision. No unpaid term is declared small.

## Actual eliminated obligations

- S2's independently counted mean-weighted single-zero correction now has its genuine complete outside payment, for arbitrary fixed B, with no assumed aggregate estimate.
- Its fixedDScale denominator is reconciled with the actual keyY and outerL2; the original beta moment and two bank multiplicities are paid once at explicit precision A+p+12.
- H's distinct S2 and S3 corrections are jointly paid at one atom-independent threshold, with their original S2 factor two.
- The payment is attached to the unchanged original actualResidualFunctional by its independently proved complete source identity.
- The actual signedError entrance in the manuscript's initial B=0 branch removes both residual correction obligations, in addition to its already paid S1/P, zero-Gram, exact-product and linear-discard obligations, at one uniform threshold.

These are source-level implementations and dependency connections. They do not assert kernel acceptance or completion of the original restricted-medium estimate.

## Remaining internal dependencies and limits

The general-B actual LINEAR discard and signed entrance are owned by `/root/i_linear_general_beta`. No completed declaration from that task was available when this scope was authored. Its dependency remains OPEN; the B=0 entrance cannot be silently generalized. The independent all-B residual and outside-correction results here remain available to its eventual genuine consumer.

The actual S3 rough/gcd/close-pair/large-coefficient/nonzero-shift cutoff corrections are owned by `/root/i_s3_gcd_corrections` and their original source producers. No provisional peer proof is consumed. They remain inside the full `retainedSourceKey` until the genuine clean-source comparison is proved. Their source names and dependency nodes are retained, not relabeled as external inputs.

The final displayed signed remainder still contains the full retained Poisson source, omitted Fourier modes, retained Fourier diagonal, roughReplacement, genuine zero diagonal, actual S2 nonzero modes and otherRoughCorrection. All coefficient/scale summations, retained phase and Abel costs, nonclean/product-cutoff/non-Hermitian branches, clean E1/E2 return and regular/exceptional/m=0 physical spectral estimate remain unproved by this assembly. The all-B actualResidualFunctional theorem also leaves zero-Gram explicit; only the separate H B=0 entrance has already paid it.

P1/P2, internal K/PP, full dispersion assembly, the full original RestrictedMediumObligation/Target and Goldbach 1+1.748 remain OPEN. No new mathematical manuscript contradiction was found in this focused algebra-and-scaling step. These remaining mathematical proof obligations are separate from installation/elaboration gaps.

## External inputs and installation evidence

No new external assumption is introduced. The final B=0 entrance retains exactly H's `PrimitiveShiuTauBoundary 1 (1/10) (1/10)` foundational interface: fixed constants before natural X,H,q,b, primitive residue and the stated H/q range, with its displayed prime Euler exponential. This is an inherited named Shiu input, not an externalized medium/P1/P2/S2/S3 estimate. Its provenance and formal-supplier obligations remain those of the exact H/G registries pinned here. Source-only import closure, and the genuine classical inputs inherited by already implemented S1/P declarations, are not newly certified by this local delivery.

Both new modules must be installed at their recorded `ImbalancedChen/*.lean` targets along with the selected source-only predecessors. No installation is performed. Mathlib is pinned by the current manifest revision, with no compiled-credit inheritance. The historical H S3 report's claim that the exact `Part3OriginalS2PaperBlockEmbedding` draft path was absent is not inherited: the current file at `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Saving-Sol6/Part3OriginalS2PaperBlockEmbedding.lean` was directly found and rehashed as `e790c1946a2380ec6a0eedf27b3e4efae831c1c26adf4415671fc309d0f4bf01`. This is local existence evidence, not proof that the whole module import DAG is installed.

REGISTRY contains exact source/import/install/manuscript/dependency hashes. The root delivery message separately freezes the two Lean files, REGISTRY and this REPORT; no self-referential registry hash is asserted. Delivered bytes should remain frozen pending root/reviewer coordination.

Root authorized a metadata-only refreeze after the independent H review identified superseded predecessor metadata observations. The current absolute paths were directly rehashed: H S3 REGISTRY is `643085aa82a89fb18b1c1feb84801221a0e0c65b7609bcee5650ebc1ba1b7317`, H S3 REPORT is `dc6ee30d9d01c0688874b58e9e1f59b74aa497f1430795aecb081a4cdc13b9ba`, and the final H medium review is `3dedcb9f03552230e5b8652ad19f7724dfdd5f1db2dffd9c3ed095cf18ca5ee2`. REGISTRY now pins those current metadata bytes. The earlier values were historical observations of subsequently superseded metadata; no mathematical import changed. Both I Lean files retain their original hashes `2deaf3e8b0b18266505357277a3c1156af34ac21780a9f2862f95f9d016f9d45` and `4ec605824b28d51406a4042c9034747a66c94988563e96f839ad1834d8dc5362`. No mutable I/TASKS digest is recorded as a mathematical import.
