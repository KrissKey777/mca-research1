# Reed–Solomon proximity gaps and mutual correlated agreement — blueprint vs. Lean witnesses

This note maps each item of the requested coding-theory programme to the Lean declaration
that discharges it, or records it as open.  Everything listed as *proved* compiles in this
repository with no `sorry` and depends only on `propext`, `Classical.choice` and `Quot.sound`
(the `#print axioms` audit lives at the end of `RequestProject/Main.lean`).

Notation: `D ⊆ F` is the evaluation domain, `n = |D|`, `k` the degree bound (`RS_k(D)` is the
code of words `x ↦ p(x)` with `deg p < k`), `e` a radius in *positions* (`δ = e/n`).

## Step 1 — Hamming metric and linear codes (`Root/CodingTheory/Hamming.lean`)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| `hammingDistance`, `relativeHammingDistance` | `Root.CodingTheory.hammingDistance`, `relativeHammingDistance` | proved (metric axioms: `hammingDistance_comm`, `hammingDistance_triangle`, `relativeHammingDistance_le_one`) |
| linear code as a `Submodule F (↥D → F)`, minimum distance | `minDistance`, `minDistance_eq`, `minDistance_le_hammingDistance` | proved |
| unique decoding below half the minimum distance | `eq_of_lt_half_minDistance` | proved |

The domain is the coercion `↥D` of a `Finset F`, so `Fintype.card ↥D = |D|` (`card_domain`).

## Step 2 — Reed–Solomon code (`Root/CodingTheory/ReedSolomon.lean`)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| `reedSolomonCode F D d` | `Root.CodingTheory.reedSolomonCode` | proved to be a submodule |
| minimum distance `= |D| − d + 1` | `reedSolomon_minDistance` (for `1 ≤ d ≤ |D|`) | proved |
| unique decoding for RS | `reedSolomon_unique_decoding` | proved |

The requested `Polynomial.natDegree_nroots_le` does not exist under that name in the pinned
Mathlib; the zero-count bound is derived from `Polynomial.card_roots'`.

## Step 3 — Interpolation and Schwartz–Zippel (`Root/CodingTheory/PolynomialInterpolation.lean`)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| existence **and uniqueness** of the interpolant of degree `< |D|` | `existsUnique_interpolant` | proved |
| number of zeros of a nonzero polynomial inside a finite set | `card_roots_in_le`, `card_roots_in_lt_of_degree_lt` | proved |
| Schwartz–Zippel, expressed with `Root/Prob.lean` | `schwartz_zippel` | proved |

## Step 4 — Local test and proximity gap

| blueprint item | Lean witness | status |
| --- | --- | --- |
| the subset test, its acceptance probability | `IsLocallyConsistent`, `goodSubsets`, `acceptProb`, `acceptProb_eq_probOf_uniform` | proved |
| **T1** `α(f) ≤ C(n,k)·C(m,s)/C(n,s)` | `proximity_gap_subsets` | proved |
| contrapositive gap: high acceptance ⇒ a nearby codeword | `proximity_gap`, `proximity_gap_distToCode` | proved |
| sharpness (no threshold below `C(a,s)/C(n,s)`) | `le_acceptProb_of_agreement` | proved |
| the formula `C(n − ⌊(1−δ)n⌋, s − k + 1)/C(n,s)` proposed in the request | — | **not proved; not a correct general bound** (for `f` in the code the acceptance probability is `1`) |

## Step 5 — Lines and correlated agreement

| blueprint item | Lean witness | status |
| --- | --- | --- |
| restriction to an affine line keeps the degree; completeness of the line test | `degree_comp_lineMap_lt`, `reedSolomon_restrict_line` | proved |
| **correlated agreement from two good points** | `correlated_agreement_of_two` | proved |
| probabilistic version (`> 1/|F|` good `z`) | `proximity_gap_lines` | proved |
| **T2** — the FRI soundness bound `δ_d(f) ≤ 1 − α(f) + c·d/q` | — | **open** (O14) |

## Step 6 — Mutual correlated agreement (`Root/CodingTheory/MCA.lean`)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| `(S,δ)`-closeness, lines, good/bad points | `IsCloseOn`, `LineCloseOn`, `IsBad`, `badSet` | definitions |
| `ε_mca` of a line and of the code | `epsMCA`, `epsMCAmax`, `epsMCA_le_epsMCAmax` | definitions + proved |
| **L1 (line closure)** | `line_closure` | proved |
| `ε_pg ≤ ε_ca ≤ ε_mca` | — | **not stated as a chain of three quantities**; the implication carrying the content is proved instead: `correlatedAgreement_of_epsMCA_lt` |
| **Table 1, unique-decoding row** (`3e < n − k + 1`): `#bad ≤ n`, hence `ε_mca ≤ n/|F|` | `card_badSet_le`, `epsMCA_le`, `epsMCAmax_le` | proved |
| headline consequence: acceptance `> n/|F|` on a line ⇒ one common agreement set for the whole line | `correlatedAgreement_of_prob_gt` | proved |
| Table 1, Johnson-radius rows | — | **open** (O16).  The proof sketch supplied with the blueprint is not valid as written; it assumes the line-closure property it is meant to produce |
| asymptotic threshold `δ* = 1 − √ρ` | — | **open** (O17); nothing here asserts it |

The proved row is self-contained.  Either the set of good `z` on the line has at most `n`
elements — and then the bad set, being contained in it, is small — or two good points already
force codewords `q₀, q₁` and a common agreement set `T`; a disjointness argument shows the
sets `S_γ \ T` for good `γ` are pairwise disjoint, which pushes `|T|` up to `n − e`, and every
bad `γ` then contributes a *distinct* position outside `T`.

## Step 7 — List decoding (`Root/CodingTheory/Johnson.lean`)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| two distinct codewords agree in `≤ k − 1` positions | `card_agreementSet_le_of_ne` | proved |
| list of codewords with agreement `≥ t` | `decodingList` | definition |
| **list-size bound** `L·(t² − n(k−1)) ≤ n·t` | `johnson_list_bound` | proved |
| explicit `L ≤ n·t/(t² − n(k−1))` for `n(k−1) < t²` | `card_decodingList_le` | proved |
| `L ≤ 1` in the unique-decoding regime `n + (k−1) < 2t` | `card_decodingList_le_one` | proved |
| the Johnson bound with its sharpest constant / the capacity-approaching list decoder | — | **not formalised** |

The bound is obtained by the classical second-moment argument (double counting of the
"pass count" `m(x)`, the pairwise agreement bound, Cauchy–Schwarz); it is genuinely valid
beyond the unique-decoding radius, but it is weaker than the sharp Johnson bound.

## Step 8 — Correlated agreement from list decoding, and the MCA row beyond unique decoding

(`Root/CodingTheory/CorrelatedAgreement.lean`, `Root/CodingTheory/MCAJohnson.lean`;
`n = |D|`, `G = goodZ k e f₀ f₁`, `Λ(k,t) = listSizeMax D k t`.)

| blueprint item | Lean witness | status |
| --- | --- | --- |
| the quantity `Λ(C,e)` (largest list of codewords at agreement `≥ t`) | `listSizeMax` | definition |
| `Λ ≥ 1` | `one_le_listSizeMax` | proved |
| pair `q₀, q₁` reconstructed from two points of the line | `exists_line_pair`, `card_inter_polyAgreement_ge_of_pair` | proved |
| **Theorem CA** in the requested form `Λ(C,e) < #G ⇒ correlated agreement` | — | **open** (O18) |
| Theorem CA as proved: `2e·Λ(k, n − 2e) + 1 < #G ⇒ ∃ q₀,q₁ agreeing with `f₀,f₁` on `≥ n − e` positions` (no hypotheses at all) | `correlatedAgreement_of_card_goodZ_gt` | proved |
| **MCA row** `#bad ≤ n·Λ` and `ε_mca ≤ n·Λ/|F|`, for `2e + k ≤ n` | `card_badSet_le_listSizeMax`, `epsMCA_le_listSizeMax`, `epsMCAmax_le_listSizeMax` | proved |
| headline consequence: acceptance `> n·Λ/|F|` ⇒ one common agreement set for the whole line | `correlatedAgreement_of_prob_gt_johnson` | proved |
| `Λ` made explicit by the Johnson bound | `listSizeMax_le_johnson`, `half_johnson_conditions` | proved |
| explicit bound `ε_mca ≤ n·(n·t/(t² − n(k−1)))/|F|`, `t = n − 2e`, for `2e + √(n(k−1)) < n` | `epsMCAmax_le_johnson` | proved |
| the Johnson-radius threshold `δ < 1 − √ρ` | — | **open** (O17); what is proved reaches `δ < (1 − √ρ)/2` |

The mechanism: one good `z₀ ≠ 0` is fixed; each further good `z` gives an explicit pair
`(Q₀ z, Q₁ z)` of codewords with `Q₀ z + z₀·Q₁ z = p_{z₀}` and `Q₀ z + z·Q₁ z = p_z`, agreeing
with `f₀, f₁` on `≥ n − 2e` positions.  So `z ↦ Q₀ z|_D` maps `G \ {z₀}` into a list of `f₀` of
size `≤ Λ`, and each fibre of that map has `≤ 2e` elements unless the common agreement set
already reaches `n − e`.  The bad points of the line then either all sit in a small `G`, or
each contributes a distinct position outside the common agreement set.
