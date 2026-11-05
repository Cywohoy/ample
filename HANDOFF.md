# Workspace checkpoint — 2026-11-05

This repository is a sibling of `Textbook/` and `LeanFoundations/`. The detailed
resumption guide is `../LeanFoundations/HANDOFF.md`. Keep all three checkpoint
commits together; the published dependency pins still identify older sources.

The current library uses standard Lean 4.35.0 and does not depend on a textbook,
Verso, Batteries or mathlib. Do not resume the archived CTT experiment.
Mathematical modules are generated from complete `savedLean` blocks in Textbook.
Update that source and run `Textbook/scripts/sync_ample.py`; do not edit generated
exports independently. Twelve modules passed synchronization on 2026-11-05.

The checkpoint includes the recent Elem structure, unique-value interface and
notation, equivalence instances, quotient interfaces, two-stage cardinal addition,
and Nat-only sum/product helpers. The associated tactic changes and regression
tests are committed with the mathematics. Existing generic finite-sum APIs remain
in use by other library lemmas.

Local experiments and test evidence, normally ignored under `tmp/`, are committed
as a chunked ZIP snapshot in `handoff/2026-11-05/`, at the user's request. Its
manifest lists exact files and checksums. Restore all three repositories with
`python ../LeanFoundations/handoff/restore_local.py --workspace <parent>`.
The restore tool preserves historical evidence and rebases only live local config.
Build/dependency caches and credentials are excluded. The user explicitly asked
to include temporary working material and upload the checkpoint to the remote;
the snapshot therefore includes review notes and proofs in this public repository.

Run `lake build`, `lake exe ample-demo`, then `lake build` in `Examples/Consumer`.
The library build was rerun successfully at this checkpoint. The previous full
consumer/book/browser validation is retained in the 2026-10-27 evidence, rather
than claimed as a new full run. Checkpoint commits are pushed to origin/main
for transfer. Commit titles include `[skip ci]` to avoid
triggering the old textbook's automatic deployment. Website publication and
dependency release updates remain separate work.
