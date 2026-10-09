# Attribution and contribution boundary

The original notice is preserved verbatim in `provenance/V1_NOTICE.md`;
`provenance/PROVEIT_NOTICE.txt` and `provenance/FROZEN_NOTICE.md` are unchanged.
All original license texts and third-party notices remain applicable.

[OpenAI/math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Polynomial-removal-fails-for-ordered-binary-matrices-September-25-2026)
supplies the signed-tree construction, role vectors, thresholds, mode order
and protected-selection arbitrary-edit lower-bound method.
[ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/bfbfe915186310fdf745a7a089e7dd88eeb773b1/Combinatorics/OrderedMatrices/Research/ordered-matrix-removal)
supplies the explicit H4 candidate, its two-anchor host and smaller-anchor
obstacle; its 5×5 construction already has exact m² repair distance.
[v1.0.0](https://github.com/erebos-labs/ordered-matrix-removal-4x4/tree/45248e57ab1c2197419981bba04e1cde050494ca)
supplies the original all-copy localization and unrestricted physical
lower-bound formalization. These contributions are not claimed as new here.

The added work is the terminal-anchor repair, its all-depth freeness and
exact-distance proof, and the depth-four counterexample to the full
penultimate-negative-column repair, with Lean formalization and reproducible
checks. The three added proof modules were written locally and use imported
baseline APIs. The count proof applies the inherited lower bound after
establishing freeness. Original project proof modules were not edited.

Prepared with ChatGPT/Codex assistance at the publisher's direction. Separate
AI-assisted reviews checked the ordinary proof and earlier counterexample.
No human peer review, upstream endorsement, worldwide priority, unique repair
or minimum pattern size is claimed. This is a local follow-up candidate for
Erebos Labs (@erebos-labs), not an executed publication action.

The existing root Apache-2.0 LICENSE applies to publisher material as stated
in LICENSE_STATUS.md. Third-party text and dependency terms remain unchanged.
No dependency checkout, toolchain or private source snapshot is distributed.
