This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## Where to look first

* `INDEX.md` — machine-generated map of all 156 Lean files: per file a headline, its
  namespaces, its project imports and reverse dependencies, and every declaration it
  introduces, plus an alphabetical index of all declarations.  Regenerate it with
  `python3 analysis/generate_index.py` after adding or renaming files.
* `analysis/RESOURCE_INVENTORY.md` — what this environment provides (Lean/Mathlib versions,
  available Mathlib mechanisms, Python tooling, network) and what external formal
  libraries do and do not contain for the remaining open obstruction.

## Coding theory: two notions of mutual correlated agreement

The repository contains two notions of mutual correlated agreement for linear codes: the
one used throughout the project's own soundness development
(`Root.CodingTheory.GG25Literal.StrongMCA`, built on the bad-set predicate of
`Root/CodingTheory/AlphabetMCA.lean`), and the literal notion of Goyal–Guruswami,
Definition 2.8 (`Root.CodingTheory.GG25Literal.GG25MutualCorrelatedAgreement`, case `ℓ = 1`,
perfect version), added for comparison with the literature.  The project's notion implies
the GG25 notion (`strongMCA_implies_GG25MCA`), and — the outcome of the formal comparison —
the converse holds as well (`strongMCA_iff_GG25MCA`), because the two bad sets are equal
radius by radius.  Consequently the difference between the constant proved in this
repository and the constant quoted in the literature is a difference of proofs, not of
definitions; see §45 of `RESULTS.md` and rows O52–O54 of `DISCREPANCIES.md`.

