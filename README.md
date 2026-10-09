# A four by four obstruction to polynomial ordered binary matrix removal

This release contains a Lean proof that the ordered binary pattern

```text
0110
1001
1010
0111
```

has no polynomial ordered removal bound. Every copy uses independently increasing row and column embeddings and matches all sixteen bits, including zeros. Distance is the actual minimum fraction of entries that must be changed to make a binary matrix free of this pattern, with changes allowed anywhere and in either direction.

The theorem says that no positive real constants c and C guarantee at least c times epsilon to the power C times n to the power eight copies in every matrix epsilon-far from being pattern-free. The stronger result also supplies arbitrarily small positive epsilon and arbitrarily large orders beyond any prescribed epsilon-dependent size threshold. See `THEOREM.md` for the exact statement and theorem names.

All 36 project Lean modules are byte-identical to the frozen source accepted by the independent Lean audit on 9 October 2026. The audit rebuilt the project with official Lean 4.34.1 and checked its fully quantified meaning, unrestricted edit distance and ordinary copy count. The final foundational dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`. It found no proof holes, added axioms, unsafe dependencies or missing declarations. This is formal verification under the disclosed Lean trust base, not independent compiler bootstrapping, a complete mathlib source rebuild or human referee endorsement. See `audit/README.md` and `PROVENANCE.md`.

Building on OpenAI's signed-tree construction and the exact four by four candidate proposed in ProveIt, we prove that this pattern has no polynomial ordered binary removal bound by establishing sparse-zero localization for every ordered copy, including unpinned embeddings, and formalize the obstruction in Lean. The candidate, construction, protected-selection distance method and mode order are inherited. Two focused prior-work challenges found no equivalent proof in the sources they checked as of 9 October 2026. This supports an attributed contribution statement, not a claim of worldwide first discovery or minimum pattern size.

## Reproduction

Python 3.12 or later, git and an independently verified official Lean 4.34.1 toolchain are required for full restoration and reproduction. No compiler, dependency checkout, Git history, precompiled project proof or dependency cache is bundled. Sources are restored at exact recorded pins, and the mathlib source archive and recorded source trees are checked before cache use. The audit tested macOS arm64. Other platforms have not been independently tested for this package.

After cloning or extracting the release, run these quick checks from the package root, or use absolute script paths from any working directory:

```sh
python3 checkers/verify_release.py
python3 checkers/check_host.py
python3 audit/checkers/compare_hosts.py
```

The two host helpers compare bundled Lean exports with independently constructed or research-fixture matrices. They are bounded implementation checks, not substitutes for the all-depth proofs. Both have been run from a relocated package. The first helper also accepts explicit `--exports`, `--fixtures` and `--output` paths.

For the full proof rebuild, set `LEAN4_BIN` to the absolute bin directory of a verified official Lean 4.34.1 distribution. On the tested macOS arm64 platform, optionally set `LEAN4_ARCHIVE` to its original tar.zst archive to check the digest recorded in `DEPENDENCIES.json`. Then run:

```sh
sh checkers/reproduce.sh
```

This command downloads the exact pinned mathlib source and eight transitive repositories when absent, restores needed artifacts from mathlib's official hash-keyed cache, and re-elaborates all 36 project modules sequentially with `-j2`. The unchanged quantified statement checker runs afterward; logs go to the newly generated `evidence` directory. The packaging wrapper and dependency restoration were adapted for this slim release; the original frozen reproduction route was independently tested by the auditor. The release validation receipt states which release checks were executed locally.

To check freshly generated host exports after a successful rebuild:

```sh
"$LEAN4_BIN/lake" env lean -j2 checkers/ExportHost.lean
python3 checkers/check_host.py --exports evidence --fixtures fixtures/research --output evidence/host-comparison.json
"$LEAN4_BIN/lake" env lean -j2 audit/checkers/IndependentStatements.lean
```

The official tested compiler archive is [Lean 4.34.1 macOS arm64](https://github.com/leanprover/lean4/releases/tag/v4.34.1), SHA-256 `65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`. Its reported commit is `5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`; its archive SHA-256 is `a8c019444a1edd6091d8416e492e218a311db340dafbea96c61c6dc358c28f05`. Platform-specific compiler digests differ; do not apply the macOS archive digest to another platform.

The included `paper/report.pdf` and `paper/report.tex` are the unchanged ordinary mathematical report. They predate the completed formalization, so their then-current statements about absent Lean certification are superseded by this package's formalization and audit status. Their exact-copy formula is reviewed by the ordinary audits but is not part of the Lean-certified claims listed here. Historical script paths in that paper refer to its original research archive; use this README for the release package's reproduction commands. `mathematical-checks/audit_checker.py` is the separately written ordinary-audit checker. Run it from the package root after creating an `evidence` directory; its depth-six run is finite evidence and takes substantially longer than the quick host comparisons.

## License and credits

Published and maintained by [Erebos Labs (@erebos-labs)](https://github.com/erebos-labs). The proof, manuscript, checkers and reviews were prepared with ChatGPT/Codex assistance at the publisher's direction. The supporting audits were AI-assisted; no human referee endorsement is claimed.

The new material in this release is licensed under Apache 2.0; see `LICENSE` and `LICENSE_STATUS.md`. Existing third-party texts retain their original terms. `NOTICE.md` credits OpenAI/math and ProveIt and explains the contribution boundary. This release does not claim a new candidate or construction, worldwide priority, or minimum pattern size.
