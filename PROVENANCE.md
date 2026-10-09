# Follow-up source provenance

Baseline: v1.0.0 commit `45248e57ab1c2197419981bba04e1cde050494ca`, extracted
from its verified clean Git checkout. Original proof files and frozen checkers
are byte-identical; `proof-source-manifest.json` remains the original record.
Historical baseline provenance and packaging status are preserved under
`provenance/V1_*`. The original paper and audit artifacts retain their own
scope; their exact-count claims are not relabeled Lean-certified.

Added optimal-repair sources originate in a separate frozen scratch proof.
The source hashes before integration were:

- TerminalAnchorRepair.lean: `d6fff01dec518aa5d5a685ddb8256168122c909b4732406ddc8e87cd6cf256ef`
- TerminalAnchorCount.lean: `e2b8029982c22ca641befcf90ac9f51fef580e4c0bb3f54e95a605930e526f79`

Integration changes only the repair-module documentation comment and the
count-module import path to the package-qualified name. Candidate hashes are
in `FILE_MANIFEST.json`; they are distinct from those frozen scratch hashes.
The ordinary proof review accepted the argument independently (reviewed
proof SHA-256 `c7ac840e24e9feb664884fa117caf574c7715b8f9bddf4c02ced8b4a3663856e`).
The public companion proof removes private execution/status material and
updates the already-completed formalization wording; its mathematical
argument is retained. `check_terminal_anchor.py` is the separately written
reviewer's scanner with only output-path/usage adjustments.

PenultimateRepair.lean is unchanged from the separately audited counterexample
source, SHA-256 `ee5fed2f1212e22efc3036805c4ad0288f81f6cc84535d7ae6f7ef7b431de0ee`.
The separate literal Lean checker and physical audit helper are included.
That review found a missing-metadata packaging defect, corrected here by
including the final payload manifest and checksums. It found no mathematical
or build defect. Its generic support lemmas do not extend the fixed-depth
non-freeness theorem to every depth.

All review claims are reported with their scopes in REPRODUCTION_STATUS.md.
Public summaries omit private paths, conversation identifiers and raw
transcripts; they do not claim to be the original full review snapshots.
The independent formal audit also passed: all 38 submitted modules were
freshly rebuilt, all were replayed, and the complete imported environments
of the optimum theorem and independent semantic checker were replayed into
an empty kernel environment. Its report SHA-256 is
`ef6853462183a130831a1a27ef51068cd86d526ae03a537d925113b5973534a3`.
The reviewer semantic, nonvacuity and axiom-closure Lean checkers are included
with only the package-qualified import adjustment. Their source origins and
review summary are recorded in validation/followup/INDEPENDENT_REVIEWS.json.
The normalized minimum identity is formally proved by the semantic checker,
not added to or attributed to the original two submitted modules.

Dependencies and compiler pins remain unchanged. Official Lean 4.34.1 commit
`5045d0056413266e57c625dcd7c365b10e377c52` and pinned mathlib source hashes
are checked before integration rebuild; imported mathlib/cache artifacts are
trusted. The compiler is not bootstrapped and mathlib is not rebuilt from
source. The original release and frozen research inputs remain immutable.
