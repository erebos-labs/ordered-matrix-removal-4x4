# Ordered binary matrix removal: exact host repair distance

Release v1.1.0 extends [v1.0.0](https://github.com/erebos-labs/ordered-matrix-removal-4x4/tree/45248e57ab1c2197419981bba04e1cde050494ca)
with an explicit optimal repair for its host and a counterexample to an earlier
repair. The pattern is

```text
0110
1001
1010
0111
```

Copies use independently strictly increasing row and column embeddings and
match all sixteen bits. Edits may occur anywhere in either direction.
For every h≥1, m=2^h and n=(14h+2)m, the terminal-anchor repair is H4-free
and changes exactly m² physical cells. The inherited unrestricted lower bound
therefore attains equality: the minimum edit distance of this host is m²
(normalized distance 1/(14h+2)²). The formal theorem supplies an attaining
matrix and a lower bound for every free alternative.

Zeroing dummy rows against the entire negative-column class at depth h−1
is a different repair. A newly created copy proves that repair fails at h=4.
The formal counterexample does not assert failure at every depth.

- [Exact statements and theorem names](THEOREM.md)
- [Complete ordinary optimal-repair proof](paper/terminal-anchor-proof.md)
- [Depth-four counterexample](paper/penultimate-repair-counterexample.md)
- Lean entry point: `import OrderedMatrixRemoval4.Repairs`
- [Verification scope](REPRODUCTION_STATUS.md), [provenance](PROVENANCE.md), and [prior work](PRIOR_WORK.md)

The original 36 proof modules, original umbrella and frozen statement checkers
remain byte-identical to v1.0.0. The original no-polynomial-removal theorem
is retained. `paper/report.tex` and `paper/report.pdf` are unchanged historical
baseline material; their statements about certification or absence of an
exact upper bound predate this follow-up. The new proof is the Markdown
companion, not a relabeling of that historical paper.

## Reproduction

Requirements: Python 3.12+, git, and a verified official Lean 4.34.1 toolchain.
Dependency pins, source hashes and compiler information are in
`DEPENDENCIES.json`; mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Set `LEAN4_BIN` to the official
toolchain bin directory. The optional `LEAN4_ARCHIVE` checks the recorded
macOS-arm64 archive digest; another platform needs its own official digest.

Quick integrity and finite checks, from the package root:

```sh
python3 checkers/verify_release.py
mkdir -p evidence
python3 checkers/check_host.py
python3 checkers/check_penultimate_repair.py
python3 checkers/check_terminal_anchor.py
```

Full pinned restoration, source rebuild, statement checks and kernel replay:

```sh
sh checkers/reproduce_followup.sh --download
```

This restores exact dependency sources and uses official mathlib cache objects.
With dependencies/cache already present, omit `--download` for an offline run.
Every project module is re-elaborated from source, sequentially with two Lean
threads. The new modules and independent quantified/literal checkers are replayed
with official `leanchecker`. The independent semantic checker proves the
release-defined attained minimum and normalized distance explicitly. Outputs go
to local `evidence/` and `.lake/`, which are excluded from the payload manifest.
Kernel replay uses the same Lean kernel and imported dependencies; it is not
an independent compiler implementation or a full mathlib source rebuild.

The finite scanner checks all compressed column quadruples through depth four
and a literal physical depth-one expansion, with positive/negative and random
controls. These are bounded consistency checks; they do not replace the
all-depth proof or prove compression optimal for unrestricted repairs.

## License and attribution

The release preserves Apache 2.0 and all inherited notices and dependency
licenses. See [NOTICE.md](NOTICE.md) and [LICENSE_STATUS.md](LICENSE_STATUS.md).
The host, pattern, mode order and lower-bound strategy are inherited from
OpenAI/math, ProveIt and v1.0.0. The additional result concerns the specified
4×4 host. The prior 5×5 construction already has an m²-distance equality
theorem. No worldwide-first, repair-uniqueness or pattern-minimality claim is
made. Work and supporting independent audits were AI-assisted; no human
referee endorsement is claimed. The follow-up was published as v1.1.0. Local-candidate/no-publication wording in the frozen package describes its preparation stage; see [PUBLICATION_STATUS.md](PUBLICATION_STATUS.md) for the later publication record and evidence limits.
