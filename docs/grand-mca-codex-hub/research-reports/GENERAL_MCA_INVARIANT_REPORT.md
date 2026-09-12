# General MCA theory — novelty gate and the invariant-level theorem

**Status: `[GENERAL-INVARIANT]`** for the main deliverable, together with
**`[SUBSUMED-BY-SOTA]`** for the proposed `ℓ`-layer separation bound of Question A.

Everything asserted below as a theorem is machine-checked, `sorry`-free, and uses only
`propext`, `Classical.choice`, `Quot.sound` (audit file `RequestProject/GenMCAAxiomAudit.lean`).
No external literature could be consulted in this environment, so the comparison with
Bordage–Chiesa–Guan–Manzur (CCC 2026) is made against the statement **as described in the
task** ("all polynomial generators have MCA for every linear code, tight in unique decoding"),
not against a printed text.

---

## 1. Question A — the novelty gate: the proposed bound is strictly weaker than what is
already in this repository

The proposed statement was

    (ℓ+1)e + μ < N   ⟹   #Bad ≤ max(ℓ−1, (ℓ−1)ℓe).

The repository already contains, for the arity-`ℓ` power generator over Reed–Solomon
(`RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean`):

    1 ≤ k,  k + (ℓ+1)e ≤ |D|   ⟹   #Bad ≤ (ℓ−1)(e+1)      (`card_badSetG_le_sharp`)

in *the same window* (`σ = k−1`, so `k + (ℓ+1)e ≤ |D| ⟺ σ + (ℓ+1)e < |D|`), and
`PolynomialGeneratorSharpness.lean` shows that `(ℓ−1)(e+1)` is **attained**.  Since
`(ℓ−1)(e+1) ≤ (ℓ−1)·ℓe` for all `ℓ ≥ 2, e ≥ 1`, and the existing bound is exactly sharp, the
proposed counter is dominated: for `ℓ = 3, e = 10` it would give `60`, the true maximum is
`22`.  Formalising it "as a weaker special case" was therefore rejected, exactly as the gate
instructed.

What *was* worth doing is the direction the gate points at: replacing the two ad-hoc
hypotheses (Reed–Solomon code, power generator) by invariants.

## 2. Question B — the invariant-level theorem

`RequestProject/Root/CodingTheory/GeneralMCAInvariant.lean` proves the theorem once, from
three numbers.

* **Code geometry.** `Separated C σ`: two codewords of the linear code `C ⊆ (Ω → F)` that agree
  on more than `σ` positions are equal.  The least such `σ` is `N − d(C)`.  No evaluation
  structure is assumed.  `separated_of_zeroBound` specialises it to evaluation codes: a space
  of functions in which a nonzero element vanishes at most `σ` times.
* **Generator geometry.** `ZeroEvading Γ ℓ g B`: for every nonzero `c ∈ F^ℓ` the functional
  `γ ↦ ∑_j g γ j · c j` vanishes at most `B` times on the challenge alphabet `Γ ⊆ F`.  In
  geometric terms the challenge curve `γ ↦ (g γ j)_{j<ℓ}` meets no hyperplane of `F^ℓ` in more
  than `B` points; `B = ℓ−1` says the curve is an **arc**.
* **Domain geometry.** `N = |Ω|` and the radius `e`.

**Main theorem** (`card_badSetAbs_le`, and `card_badSetAbs_le_of_zeroEvading`):

    Separated C σ,  ZeroEvading Γ ℓ g B
      ⟹  ( σ + (B+2)e < N  ⟹  #Bad ≤ B(e+1) )
      and, for an interpolating generator, ( σ + (ℓ+1)e < N  ⟹  #Bad ≤ max(ℓ−1, B(e+1)) ).

`interp_of_card_gt` is the one structural lemma: more than `B` challenges of a zero-evading
generator cannot lie in a hyperplane, so their generator vectors span `F^ℓ` and interpolation
is *not* an extra hypothesis — the arc condition alone drives both halves of the proof
(recovering the codeword family, and charging bad challenges to residual positions).
`allCloseOn_of_card_close_gt` is the correlated-agreement form: more than `max(ℓ−1, B(e+1))`
close challenges force one common agreement set.

Three consequences worth stating explicitly.

1. **The bound does not depend on `|F|` at all**, and the challenge alphabet may be an
   arbitrary subset `Γ ⊆ F` (subgroup, subfield, coset, …); `ε_mca = #Bad/|Γ|`.
2. **The bound is attained** (`exists_card_badSetAbs_eq_sharp`): with `B = ℓ−1` and
   `σ = k−1` there is a word family whose abstract bad set has exactly `B(e+1)` elements.  So
   no theorem in the pair of invariants `(σ, B)` can do better.
3. **The window is optimal** (`GeneralMCAWindowSharp.lean`,
   `exists_badSetAbs_ge_at_window_boundary`): at `σ + (ℓ+1)e = N` — one unit past the
   hypothesis — the bad set is *unbounded*: for every `N` there is a smooth Reed–Solomon
   instance (`D = μ_{p−1}`, `ℓ = 2`, `e = 2`) with more than `N` bad challenges.

## 3. Instances (`GeneralMCAInstances.lean`, `GeneralMCAReedMuller.lean`)

| generator | invariant `B` | comment |
|---|---|---|
| power `γ^j` | `ℓ−1` | `zeroEvading_pow`; the classical case |
| monomial `γ^{E j}`, distinct exponents | `max_j E j` | `zeroEvading_monomial`; batching/folding generators |
| any polynomial generator with linearly independent components of degree `≤ B` | `B` | `zeroEvading_polyGen` |
| **rational (Cauchy)** `1/(γ − a_j)` on `Γ = F ∖ {a_j}` | `ℓ−1` | `zeroEvading_cauchy`; **not** a polynomial generator |

| code | invariant `σ` | comment |
|---|---|---|
| any linear code of minimum distance `d` | `N − d` | `separated_of_minDistance` |
| Reed–Solomon `RS_k(D)` | `k−1` | `separated_rsCode` |
| any evaluation code with a zero bound | `σ` | `card_badSetAbs_evaluation_le`; for an AG code `C_L(G)` on a curve the hypothesis is the classical "a nonzero `f ∈ L(G)` has at most `deg G` zeros", i.e. `σ = deg G` |
| Reed–Muller `RM_n(d, S)` on the grid `S^n` | `d·|S|^{n−1}` | `separated_rmCode`, proved from Mathlib's Schwartz–Zippel; the evaluation domain is not `P¹` |
| any code folded by blocks of size `s` (alphabet `F^s`) | `⌊σ/s⌋` | `separated_foldCode`, `card_badSetAbs_folded_le`; with `C = RS_k` this is folded Reed–Solomon |

The symbol alphabet of the code is an arbitrary `F`-vector space `M`; the challenge alphabet
stays inside `F`.  This is what makes the folded row possible: the proof of the fibre bound
uses a linear functional on `M` separating the residual symbol, and nothing else.

`card_badSetG_le_via_general` re-derives the concrete Reed–Solomon polynomial-generator bound
of `PolynomialGeneratorMCA.lean` from the abstract theorem, so the general statement is checked
to be at least as strong as the concrete one it replaces.

**Relation to the external SOTA gate.** Against "all polynomial generators have MCA for every
linear code, tight in unique decoding", the theorem here matches the generality on the code
side (any linear code, through `σ = N − d`) and *extends* the generator side: what is used is
not that the generator is polynomial but that its challenge curve is zero-evading.  The Cauchy
generator is a concrete member of the extended class that is not polynomial; the arc-invariant
formulation also covers generators given by any zero-bounded family of functions on `Γ`.  On
the code side it covers Reed–Muller and (conditionally on the classical zero bound) AG
evaluation codes.  This is a genuine but *lateral* strengthening: it does not improve the
unique-decoding radius, and the exactness results of §2 show it cannot be improved in these
invariants.

## 4. Prize gate — honest scope

This does **not** advance Grand MCA.  Everything proved here lives strictly inside the
unique-decoding-type window `σ + (ℓ+1)e < N`, and §2.3 shows that window is the last
admissible line for *these* invariants: any statement beyond it must use structure that
`(σ, B, N)` does not see (the fine geometry of the list of nearby codewords, or of the
evaluation domain — e.g. smoothness of `μ_{2^k}`), because the counterexample family at the
boundary is itself a smooth Reed–Solomon instance.  In that sense the contribution to the
Grand-MCA programme is a **barrier**: it delimits exactly what invariant-level reasoning can
give, and identifies the two places where new information must enter.

Nothing in the repository's earlier counterexamples or sharpness witnesses was modified or
removed; the `ℓ = 3` counterexample, the coset families, the twin-coset and window results are
all untouched, and the coset family is now *used* to prove the optimality of the window.

## 5. Files

* `RequestProject/Root/CodingTheory/GeneralMCAInvariant.lean` — invariants, main theorems.
* `RequestProject/Root/CodingTheory/GeneralMCAInstances.lean` — generator and code instances,
  Reed–Solomon recovery, sharpness of the bound.
* `RequestProject/Root/CodingTheory/GeneralMCAReedMuller.lean` — Reed–Muller instance via
  Schwartz–Zippel.
* `RequestProject/Root/CodingTheory/GeneralMCAWindowSharp.lean` — optimality of the window.
* `RequestProject/GenMCAAxiomAudit.lean` — axiom audit of all of the above.
