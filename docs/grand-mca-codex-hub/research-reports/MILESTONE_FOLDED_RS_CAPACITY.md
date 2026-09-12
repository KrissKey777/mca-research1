# Milestone — Folded Reed–Solomon: unconditional capacity-level mutual correlated agreement

This note consolidates the folded Reed–Solomon strand of the project, which is **closed**.
Nothing in it may be modified by later work (freeze list); it is recorded here so that the
ordinary–Reed–Solomon strand can be developed against a stable baseline.

All statements below are machine-checked in Lean 4 / Mathlib, contain no `sorry` and no
`admit`, introduce no `axiom`, and are audited in `RequestProject/Main.lean` with
`#print axioms`: each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## 1. The result

For folded Reed–Solomon codes the mutual-correlated-agreement (MCA) parameter is controlled
**up to capacity**, with an explicit field-size threshold and a **linear** list size, and
with no remaining side hypothesis.

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| F1 | The agreement-excess budget follows from the subspace design alone, for candidate sets of at most `r+1` codewords | `Root.CodingTheory.Folded.foldedRS_excessBudget` | `RequestProject/Root/CodingTheory/FoldedRSLinearUnconditional.lean` |
| F2 | Folded RS is list decodable with list size `L + 1 = 2^11` at radius `1 − ρ − η`, `η = 2^-10` — unconditionally | `Root.CodingTheory.Folded.foldedRS_listDecodable_linear_unconditional` | same |
| F3 | At `n = 2^20` blocks, `η = 2^-10`, list size `2^11`: `ε_mca(1 − ρ − η) ≤ 2^-128` whenever `|F| ≥ 26·2^158` — unconditionally | `Root.CodingTheory.Folded.foldedRS_threshold_linear_2_158_unconditional` | same |

The chain that produces them:

```
subspace design
      │  hasExcessBudgetUpTo_of_design          (ExcessBudgetBounded.lean)
      ▼
HasExcessBudgetUpTo C T (L+2)
      │  listDecodable_of_hasExcessBudgetUpTo   (ExcessBudgetBounded.lean)
      ▼
ListDecodable C e (L+1)                          ⟶  F2
      │  the MCA machinery of FoldedMCA.lean
      ▼
ε_mca ≤ 2^-128 at |F| ≥ 26·2^158                 ⟶  F3
```

The supporting general results are `Root.CodingTheory.WEB.weightedExcessBound` (the Weighted
Excess Bound), `Root.CodingTheory.Alphabet.excessBound_layerFamily`,
`Root.CodingTheory.Alphabet.flagCertificate_of_finrank_le` and
`Root.CodingTheory.Alphabet.flagCertificate_of_card_le`.

## 2. The threshold is `26·2^158`, not `2^160`

The arithmetic is tight: with `θ = 512` and list size `2^11` the constant that comes out of
the proof is

```
26 · 2^158 = (13/8) · 2^162 ,     so   2^162 ≤ |F| ≤ 2^163 .
```

This exceeds `2^160`. The original success criterion "threshold `≤ 2^160`" is therefore
**not** met, and the correct statement of the target is `26·2^158`. The earlier quadratic
`2^173` theorem and the conditional `2^158` theorems are retained unchanged, as required.

## 3. Refuted lemmas along the way

Three statements that were proposed as ingredients turned out to be false, and are recorded
as formal refutations rather than removed:

| # | Proposed statement | Status | Lean witness |
| --- | --- | --- | --- |
| R1 | "A flat partition has independent direction subspaces" | **False.** Explicit `𝔽₃` counterexample on five points with a three-part partition: every transversal is affinely independent, yet two parts have equal one-dimensional direction spaces | `Root.CodingTheory.Alphabet.badParts_transversal_affineIndependent`, `Root.CodingTheory.Alphabet.flatPartition_directions_not_indepOn` (`FlatPartitionIndependenceFails.lean`) |
| R2 | Occupancy weights `(|T_j|−1)/dim K_j` on a flat partition give the flag certificate ("unit weights") | **Cannot work**, for a second and independent reason: coverage also needs every coordinate to be explained by one part. For `C = {(a,b,a+b)} ⊆ 𝔽₂³`, `y = (0,0,1)` every flat partition of `S = C` is three singletons and all weights vanish, although a certificate does exist | `analysis/correct_flat_partition_check.py` (19/28, 470/504 and 344/828 instances admit no occupancy-weight certificate) |
| R3 | `flagCertificate_of_finrank_le` with no hypothesis at all | **False as stated**, already at `r = 0`, where a certificate would force `|S| = 1`. The proved form carries the layer: `V ≤ C`, `dim V ≤ r`, `S` inside a coset of `V` | `flagCertificate_of_finrank_le` (`FlagCertificateGeneral.lean`) |

Likewise `foldedRS_excessBound` for *arbitrary* candidate sets is unavailable for the reason
of R3; the proved form is the bounded one, `HasExcessBudgetUpTo … (r+1)`, which costs nothing
downstream because the list-size argument only ever inspects candidate sets of `L + 2`
codewords.

## 4. Audit

`lake build` is clean. `RequestProject/Main.lean` contains

```
#print axioms Root.CodingTheory.Folded.foldedRS_excessBudget
#print axioms Root.CodingTheory.Folded.foldedRS_listDecodable_linear_unconditional
#print axioms Root.CodingTheory.Folded.foldedRS_threshold_linear_2_158_unconditional
#print axioms Root.CodingTheory.Alphabet.badParts_transversal_affineIndependent
#print axioms Root.CodingTheory.Alphabet.flatPartition_directions_not_indepOn
```

and each reports exactly `[propext, Classical.choice, Quot.sound]`.

Full narrative: `RESULTS.md` §53. Deviations from the original brief: `DISCREPANCIES.md`
§8.7.
