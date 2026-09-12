# Folded Reed–Solomon MCA — design decisions and status

This note answers the design questions raised before the folded work started, and records
what the answers turned into in the Lean sources.  Everything referenced here builds and is
`sorry`-free; the open items are listed in `DISCREPANCIES.md`, rows O44–O48.

---

## 1. Representation of folded words

**Chosen: `D → (Fin s → F)`**, i.e. words `↥B → Fin s → F` with alphabet `A = Fin s → F`.

Reasons:

* the Hamming layer already in the project (`Root/CodingTheory/Hamming.lean`) is stated for
  `ι → F` with an *arbitrary* type in the alphabet slot and `DecidableEq` only, so
  `hammingDistance` and `agreementSet` apply to `↥B → (Fin s → F)` with **no new code**, and
  a distance of `1` is a whole block — exactly the folded (block) metric;
* `Submodule F (↥B → Fin s → F)` is available with no work: `Pi.addCommGroup` / `Pi.module`
  give the module structure of the ambient space, and the code is the range of a linear map;
* `Polynomial.eval` needs no adaptation: the code is the image of `p ↦ (x ↦ (i ↦ p(γ^i x)))`,
  which is `Polynomial.eval` applied `s` times per block;
* pointwise line combinations `f₀ + γ • f₁` are the module action of the *scalar* field `F`
  on the alphabet, which is exactly what the challenge structure needs.

`Matrix (Fin s) D F` was rejected: matrix indexing puts the block index in the wrong slot for
the Hamming metric (a matrix "column" is not a coordinate of the code), and `Matrix` carries
multiplication instances that are irrelevant here.  A custom `Alphabet F s` structure was
rejected because it would need its own `AddCommGroup`, `Module`, `Fintype`, `DecidableEq`
instances, all of which `Fin s → F` already has.

## 2. Generalising the MCA definitions

**Chosen: one new generic file, no refactor of the existing ordinary-RS files.**

`Root/CodingTheory/AlphabetMCA.lean` develops the whole MCA layer for

* a finite field `F` — the challenges are drawn from `F`, never from the alphabet;
* a finite index type `ι` — the positions/blocks;
* an alphabet `A` with `[AddCommGroup A] [Module F A] [DecidableEq A]`;
* an arbitrary `F`-linear code `C : Submodule F (ι → A)`.

It carries `AgreeOn`, `LineAgreeOn`, `CloseTo`, `IsBad`, `badSet`, `goodZ`, `epsMCA`,
`epsMCAmax`, `MinDistGe`, and the proofs: line closure, MCA ⇒ correlated agreement, the
two-challenge extraction, and the unique-decoding bound `#bad ≤ n` whenever `3e` is below the
minimum distance.

Rather than rewriting `MCA.lean` (which many later files depend on), the two developments are
*bridged*: `AlphabetInstances.lean` proves `AgreeOn ↔ IsCloseOn`, `LineAgreeOn ↔ LineCloseOn`,
`IsBad ↔ IsBad`, `badSet = badSet`, `epsMCA = epsMCA` for `A = F` and the Reed–Solomon code,
and re-derives the ordinary bound through the generic layer.  This is the low-risk option: the
existing results keep their statements and proofs, and nothing is duplicated for the folded
case.

A `HammingSpace` typeclass was not introduced — the Hamming layer is already generic, so the
class would carry no information.

## 3. Modelling the folding element γ

**Chosen: `γ : F` together with an explicit distinctness hypothesis on the domain.**

`Root.CodingTheory.Folded.IsFoldingDomain B s γ` says: for `x, y ∈ B` and `i, j < s`,
`γ^i x = γ^j y → x = y ∧ i = j`.  This is exactly what every counting argument needs (the
`s·|B|` unfolded points are pairwise distinct), it is checkable, and it is implied by the
usual construction: `isFoldingDomain_of_cosets` derives it from `γ ≠ 0`, `γ^m ≠ 1` for
`0 < m < s` (γ of order at least `s`), `0 ∉ B`, and the `⟨γ⟩`-cosets of `B` being distinct.

Modelling γ as a multiplicative action of `Fin s` on the domain was rejected: it hides the
distinctness assumption, which is the only part that does any work, and it forces the domain
to be a quotient object, complicating `Polynomial.eval`.

For the design/counting statements no further assumption on γ is needed.  (The `r ≥ 2`
subspace-design bound will need the order of γ to be exactly `s`; that is available from the
same criterion.)

## 4. Mathlib components used

`Submodule F (Fin s → F)`, `Pi.module`, `Pi.addCommGroup`, `LinearEquiv`, `Matrix`,
`Module.finrank`, `Module.rank`, `Matrix.det`, `Polynomial.eval`, `Finset.card_bij`,
`LinearMap.ker` all exist.  Two names from the original checklist do **not** exist as written:

* `Submodule.finrank` — the correct spelling is `Module.finrank F ↥C`;
* `Pi.instModule` — the instance is `Pi.module`.

Also used: `Polynomial.degreeLT` with `Polynomial.degreeLT.basis` (giving
`finrank (degreeLT F k) = k`), `LinearMap.finrank_range_of_inj`, `Finset.card_image_of_injOn`.
Nothing else had to be built from scratch for the definitional layer.

## 5. Is the additive margin law reusable?

**Yes, unchanged.**  `AdditiveMargin.lean` is a statement about the *bad challenge sets*
`B₁, B₂ ⊆ F` and the uniform distribution on `(F × F)^s`; the alphabet never appears.  It
therefore applies verbatim to the generic bad sets, and this is now recorded in Lean:
`Alphabet.falseAcceptProb_le_of_margins` states the law for two folds over two possibly
different codes with two possibly different alphabets.  The only per-code input is a bound on
`|badSet|`, which the generic layer supplies.

The concrete folded instance is `Folded.soundness_folded_two_folds`.

## 6. Order of work

The order actually followed, and the one recommended, is:

1. the alphabet-generic MCA layer (`AlphabetMCA.lean`) — done;
2. instantiation at `A = F`, checking it reproduces the ordinary definitions — done;
3. the folded code, its dimension and its block distance (`FoldedRS.lean`) — done;
4. folded MCA in the unique-decoding regime (`FoldedMCA.lean`) — done, unconditional;
5. subspace design: definition + the `r = 1` case with the sharp constant — done;
6. curve-decodability: definition + `curve-decodable ⇒ MCA`, alphabet-generic — done;
7. a general-`r` design bound by double counting, `Σ_i dim(W ∩ C_i) ≤ (q^r − 1)·⌊(k−1)/s⌋`
   (`SubspaceDesignGeneric.lean`) — done, unconditional, but with a constant exponential
   in `r`;
8. **open**: the sharp `r ≥ 2` design bound `τ(r) = sρ/(s−r+1)` (folded Wronskian) and the
   capacity-radius curve-decodability instance; these are the two inputs still missing for a
   capacity-level folded MCA theorem (`DISCREPANCIES.md` O44, O45).

The syndrome-space and additive-margin theorems already in the project shorten step 4 (the
concrete `2⁻¹²⁸` statement is a one-line application), but they do not shorten step 8 — those
need genuinely new mathematics, not a repackaging of the existing bounds.

## 7. Status of the ordinary-RS Johnson path

Frozen and still conditional; recorded as `DISCREPANCIES.md` O46.  The folded (GG25) route is
the main route from now on, recorded as O47.

## 8. Numerical pre-verification

* `analysis/linear_alphabet_mca_check.py` — brute force over `GF(q)`, `q ≤ 13`, `s ≤ 5`,
  `k ≤ 3`: folding hypothesis, block distance, `r = 1` design bound, `#bad ≤ |B|` in the
  unique-decoding regime, `badSet ⊆ goodZ`, empty bad set for lines inside the code, and the
  product form behind the margin law.
* `analysis/subspace_design_check.py` — exhaustive enumeration of all `r = 1, 2` subspaces of
  the folded code on eight instances; exact rational comparison with the GG25 shape via Z3.

Both scripts run and pass; no counterexample was found to anything formalised.
