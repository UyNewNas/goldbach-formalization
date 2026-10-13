# Part2 Round5 handoff — E0 raw ordinals [128,192)

STATUS: CANDIDATE / NOT YET CERTIFIED. Only E0 [0,128) is currently formally accepted. Do not count this as a completed Lean proof.

Frozen manuscript ba6ec11d800eccc54406490631895e174de85766; common baseline 1a80c1bcce67886f699d097fc37fd245cd3620bf; parent Part2 HEAD 817d0da055d9ccd15b6461278f0201446bd28ee7.
Corpus SHA256 f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7; preserve CRLF original and LF row-stream identity.
New [128,192) LF SHA256 2afc4ad5661676de82d4a9af6a101ad2e0f487ae46c98a155710fcda122e811e; full [0,192) LF SHA256 b32c7adb0daff5b9de4da559d4597ff805ed7bd644268b348795fcd52959a8fa.
Source Git blobs: PairedV2Batch128To192Data 91a43426ac475bed88182ab1a39c3f4997902b12; PairedV2Batch128To192 50a61d52d0f3d469286c96862e37a0ae026304a5; PairedV2Prefix192 a3bb190fce8f9f3e210cc7f325adb668bd089aed.

Exact rational candidates (denominator 10^20): new batch [203922704131873,203922822975162]; combined prefix [610834375909440,610834730821178]. These bounds are NOT proved until successful kernel replay.
Composition uses inherited Fin 128 plus new Fin 64 (not 128+128); Fin.sum_univ_add must establish exact rowIntegral append. Static inspection found 192 distinct strictly ordered source grid pairs, but this is not integral-mask certification.

Acceptance next: existing strict trustLevel=0, warningAsError=true per-leaf build, original leanchecker replay, defining-module full compiler-type and transitive-axiom audit, only propext/Classical.choice/Quot.sound, CI for exact SHA and source/olean/import/checker hash receipts. Do not change inherited acceptance hashes.
Historic geometry, full mask, parent permission, saved-floor, K/c, P1 J/I/old/nu/cap binding remain separate open obligations; exact_Z != cap.
On verified success, save verification/part2/round5/batch128-to192/receipt.json with actual proof/evidence SHA and CI links, then advance only to E0 [192,256).
