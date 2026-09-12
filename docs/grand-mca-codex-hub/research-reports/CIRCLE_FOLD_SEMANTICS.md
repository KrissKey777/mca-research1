# Circle-FRI: exact semantics of one inversion fold

This file fixes, once and for all, the semantics used by
`RequestProject/Root/CodingTheory/CircleFRIProverWord.lean`.  Nothing in that file
deviates from what is written here.  It is deliberately narrow: it describes **one**
round of the circle fold, on **one** line of words, and it makes **no** Circle-STARK
claim.

Throughout, `F` is a field with `2 ≠ 0` and

```
FFT.Circle F = { p : F × F // p.x ^ 2 + p.y ^ 2 = 1 }
```

is the circle group of `RequestProject/CircleGroup.lean`, whose group inverse is
`p⁻¹ = (p.x, −p.y)`.

---

## 1. The circle fold map

The fold is the **inversion involution**

```
J : FFT.Circle F → FFT.Circle F ,    J (x, y) = (x, −y) = p⁻¹ .
```

`J` is an involution (`J (J p) = p`), it fixes exactly the points with `y = 0`
(i.e. `(±1, 0)` when they exist), and `(J p).x = p.x`.

In Lean: `Root.CodingTheory.circleFoldInv`, with `circleFoldInv_x`,
`circleFoldInv_y`, `circleFoldInv_involutive`.

## 2. The projected domain

Let `D : Finset (FFT.Circle F)` be the pre-fold domain.  The **projected domain** is
the image of `D` under the `x`-projection:

```
π D  :=  D.image (fun p => p.x)   :   Finset F .
```

In Lean: `Root.CodingTheory.circleProj`.  This is an ordinary finite subset of `F`,
so the post-fold code is an *ordinary* Reed–Solomon code on `π D`, **not** a circle
code.  This is the whole point of the round: the fold leaves the circle.

A **fold section** is a map `σ : ↥(π D) → FFT.Circle F` with

* `(σ u).x = u`      (`σ` is a section of the projection),
* `(σ u).y ≠ 0`      (`σ u` is not a fixed point of `J`),
* `σ u ∈ D`.

Such a `σ` exists exactly when no point of `D` needed for the projection has
`y = 0`; the sufficient hypothesis used in Lean is `∀ p ∈ D, p.y ≠ 0`, which is
satisfied by the twin-coset domains of Circle-FFT (they are disjoint from the two
`y = 0` points).  In Lean: `Root.CodingTheory.exists_circleFoldSection`.

Note that `π D` is *not* assumed to be `D.card / 2`; no cardinality relation between
`D` and `π D` is used anywhere.  All hypotheses are stated on `(π D).card`.

## 3. The first layer

For a word `w : FFT.Circle F → F` (a total function; on the protocol side it is the
prover's word, whose values outside `D` are irrelevant because only `σ u` and
`J (σ u)` are ever read):

```
foldFst w σ  :  ↥(π D) → F ,     (foldFst w σ) u = ( w (σ u) + w (J (σ u)) ) / 2 .
```

In Lean: `Root.CodingTheory.circleFoldFst`.

## 4. The second layer

```
foldSnd w σ  :  ↥(π D) → F ,     (foldSnd w σ) u = ( w (σ u) − w (J (σ u)) ) / (2 · (σ u).y) .
```

In Lean: `Root.CodingTheory.circleFoldSnd`.  The division by `(σ u).y` is exactly why
`(σ u).y ≠ 0` is part of the definition of a fold section.

The tested line of the round is `γ ↦ foldFst w σ + γ · foldSnd w σ` on `↥(π D)`,
which is the line of `Root.CodingTheory.badSet` / `Root.CodingTheory.epsMCA` of
`MCA.lean` for the ordinary Reed–Solomon code of degree bound `k` on `π D`.

## 5. What the second layer is: `b(x)`, not `y·b(x)`

Let `w` be the total circle word of the pair `(a, b)`:

```
circleWordTotal a b  :  FFT.Circle F → F ,    (circleWordTotal a b) p = a(p.x) + p.y · b(p.x) .
```

Then, for every `u : ↥(π D)`,

```
(foldFst (circleWordTotal a b) σ) u = a(u) ,
(foldSnd (circleWordTotal a b) σ) u = b(u) .
```

So the second layer is **`b(x)` itself — an ordinary univariate polynomial evaluated
on the projected domain**.  It is *not* `y · b(x)` and it is not a circle word: the
factor `y` is divided out by the definition of `foldSnd`, and this is legitimate
precisely because `y ≠ 0` on the section.  This is the content of
`circle_fold_snd_eq_eval_b`.

Both identities are pointwise identities of functions on `↥(π D)`; no genericity, no
degree hypothesis and no hypothesis on `a` is used for them.  Only `2 ≠ 0` and the
two section conditions.

## 6. The `ZeroCountLt` predicate used

The abstract predicate is the one already in the project
(`ZeroCountSecondLayer.lean`), unchanged:

```
Alphabet.ZeroCountLt (C : Submodule F (ι → A)) (t : ℕ) (f : ι → A) : Prop :=
  ∀ c ∈ C, f ≠ c → (agreementSet f c).card < t
```

It is instantiated at

* `ι := ↥(π D)`, `A := F`,
* `C := reedSolomonCode F (π D) k`, the ordinary RS code of degree bound `k` on the
  projected domain,
* `f := foldSnd (circleWordTotal a b) σ = eval b`.

The instance proved is `circle_fold_secondLayer_zeroCountLt`: if `deg b < t` and
`k ≤ t`, then `ZeroCountLt (reedSolomonCode F (π D) k) t (foldSnd w σ)`.  The proof
is the classical root count: a nonzero polynomial of degree `< t` has fewer than `t`
roots.

## 7. The role of `t`, and which domain inequality is used

`t` is a **strict upper degree bound on the second layer** (`deg b < t`), used
simultaneously as the zero-count parameter.  It is *not* an agreement slack and it is
not a decoding radius.  The decoding radius is the separate parameter `e`.

The domain inequality used in this file is

```
        2 · e + t  ≤  (π D).card                     (★)
```

i.e. the **`2e + t`** form, on the **projected** domain.  The other inequality that
appears in the project,

```
        2 · e + 2 · t + 1  ≤  D.card                 (★★)
```

belongs to `CircleZeroCount.lean` and to a *different* statement: there the second
layer is a circle word `a + y·b` tested against the **circle code** on `D`, and the
zero count of a circle word is governed by its norm `a² − (1 − x²)b²`, of degree up
to `2t`, whence the factor 2 and the extra `+1` (the `+1` is necessary; a witness at
`2e + 2t = |D|` with `#Bad = 2` is recorded in `analysis/circle_bridge_falsification.py`).

The two are not in conflict and are never mixed:

| statement | domain | code | second layer | inequality |
|---|---|---|---|---|
| `CircleZeroCount.card_badSet_circle_le_one` | `D` (circle) | `circleCode D k` | circle word `a + y·b` | `2e + 2t + 1 ≤ D.card` |
| `CircleFRIProverWord.circle_fri_one_round_card_badSet_le_one` | `π D` (projected, ⊂ F) | `reedSolomonCode F (π D) k` | ordinary polynomial `b` | `2e + t ≤ (π D).card` |

The present file's round is the second row: **after** the fold the instance is
univariate, so the univariate `2e + t` bookkeeping is the correct one, and the
factor-2 penalty of the circle norm is not paid.

## 8. Degree window

The `#Bad ≤ 1` conclusion needs the second layer to be **outside** the code but
inside the zero-count window:

```
        k ≤ deg b  <  t .
```

If instead `deg b < k` the second layer is a codeword and the bad set is *empty*
(`circle_fri_one_round_badSet_eq_empty`, via `badSet_eq_empty_of_codeword_snd`).
Nothing is claimed when `deg b ≥ t`.

## 9. Scope limits

* One round, one line, one prover word of the stated form.
* No multi-round soundness, no Circle-STARK statement, no claim about the composition
  of rounds, no claim about words that are not of the form `a(x) + y·b(x)`.
* The strong MCA/`Bad` definitions are untouched.
