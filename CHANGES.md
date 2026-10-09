# Changes from v1.0.0

- Add TerminalAnchorRepair.lean and TerminalAnchorCount.lean: explicit repair,
  no-new-copy argument, all-depth freeness, exact physical edit count, optimum.
- Add unchanged independently audited PenultimateRepair.lean: depth-four
  counterexample to the complete penultimate-negative-column repair.
- Add Repairs.lean as the extension entry point; retain the original umbrella
  and all original proof modules byte-for-byte.
- Add ordinary proofs, exact follow-up statements, attribution/prior-work note,
  statement/axiom checkers, independent literal counterexample checker,
  finite physical/oracle checkers and a portable integrated replay wrapper.
- Update README, THEOREM, NOTICE, PROVENANCE and reproduction status to explain
  the additional result and its scope. Preserve historical baseline notices
  and packaging receipts under provenance/V1_*.
- Regenerate final payload manifest/checksums and add integrated verification
  receipts. No compiled proof, local cache, credentials, Git metadata, private
  development paths or raw conversation transcripts are shipped.

BASELINE_COMPARISON.json records added/modified/removed payload files against
the pinned commit. FILE_MANIFEST.json freezes the final deliverables.
This is a separate local candidate; v1.0.0 itself is not edited.
