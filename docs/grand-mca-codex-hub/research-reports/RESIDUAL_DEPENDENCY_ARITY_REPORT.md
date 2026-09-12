# SYNDROME-DIRECTION / HIGHER-ARITY GATE — STEP 1 verdict

## OUTCOME

```
HIGHER-ARITY-DEPENDENCY
```

The mandatory arity check fails: it is **not** true that every nontrivial dependency among
residual challenges contains a 3-supported dependency. The smallest exact example has

* **arity 4** (four distinct challenges),
* **width `w = 2`**,
* over the **five element field**,

and no three of its four challenges are dependent. Per the mission's stop rule (STEP 4, "stop
after the first exact obstruction"), STEP 2 (canonical directions) and STEP 3 (cross-adapter) were
**not entered**: no direction fibre bound, no boundary claim, no line/direction bridge is asserted.

All work is additive. New modules:

* `RequestProject/Root/CodingTheory/ResidualDependencyArity.lean`
* `RequestProject/ResidualDependencyArityAxiomAudit.lean` — `#print axioms` for all nine
  load-bearing declarations; each prints `[propext, Classical.choice, Quot.sound]`. No `sorry`,
  no `native_decide`, no new axiom. Nothing existing was modified.

---

## STEP 1 — the exact definitions under test

From `Root.CodingTheory.SplitPencil.card_le_two_mul_width_of_regular` and
`Root.CodingTheory.ResidualDependency.*`, a **challenge-compatible dependency** for challenges
`γ : ι → F` with syndrome vectors `v : ι → (Fin w → F)` is a family `c : ι → F` with

```
∑ i, c i • v i = 0        and        ∑ i, (c i * γ i) • v i = 0 .
```

This is `ResidualArity.IsChallengeDependency`, a literal transcription of the gate hypothesis
(the hypothesis quantifies over *arbitrary* `(γ, v)`; splitness, monicity, `Q ∣ Xⁿ − 1`, the
domain `D` and the words `f₀, f₁` do not occur in it).

A **3-supported dependency** is `ResidualArity.IsTripleDependency γ v σ`: a nonzero dependency of
the subfamily indexed by an *injective* `σ : Fin 3 → ι`. Injectivity of `σ` (and, in the example,
of `γ`) is what makes the count a count of **distinct challenges**, not of supports, locators or
arbitrary vectors.

`isChallengeDependency_iff_joint` (PROVED) identifies dependencies with linear dependences of the
**joint vectors** `V i = (v i, γ i • v i) ∈ F^w × F^w`. Minimal dependencies are therefore exactly
the circuits of the matroid of the `V i`, and the arity question becomes: can a circuit be longer
than three?

## The exact arity interval

| bound | statement | status |
| --- | --- | --- |
| arity `≥ 3` | `eq_zero_of_pair_supported`: a dependency vanishing outside two distinct indices is zero (distinct `γ`, nonzero `v`) | PROVED |
| arity `≤ 2w+1` | `exists_dependency_of_two_width_lt_card`: any `> 2w` challenges already carry a nonzero dependency, so a minimal dependency uses at most `2w+1` challenges | PROVED |
| `w = 1 ⇒ arity 3` | `tripleDependency_of_width_one`: at width one *every* injective triple of challenges with nonzero syndrome vectors is dependent | PROVED |

So at width one — the width of the previously constructed official model — arity-3-completeness
holds, and the interval `[3, 2w+1]` degenerates to `{3}`. That is exactly why the earlier
three-challenge classification looked complete; it is an artefact of `w = 1`.

## The obstruction: an exact arity-4 example

`arity_four_no_smaller_dependency` (PROVED, kernel `decide`, no `native_decide`):

* field `F = ZMod 5`, width `w = 2`;
* challenges `γ = (1, 2, 3, 4)` — pairwise distinct (proved);
* syndrome vectors `v i = (1, γ i⁻¹) = (1,1), (1,3), (1,2), (1,4)` — all nonzero (proved);
* coefficients `c = (1, 4, 4, 1)`, all nonzero (proved), satisfying **both** dependency equations;
* **every** dependency `c'` of this family with `c' i = 0` for some `i` is identically zero
  (exhaustive over all `5⁴ = 625` coefficient families).

`arity_four_no_triple_dependency` (PROVED) restates the last item in challenge form: for every
injective `σ : Fin 3 → Fin 4` there is **no** 3-supported dependency. Hence the arity-4 dependency
contains no 3-supported dependency, and the implication under test is false.

Why it works, in one line: the joint vectors are `(1, γ⁻¹, γ, 1)`, four points of the Segre
quadric `x₀x₃ = x₁x₂` lying in the plane `x₃ = x₀`; a plane section of a smooth quadric is a
conic, which contains no three collinear points, so the four joint vectors are dependent while
every three of them are independent. Any three of them are independent because the relevant
`3 × 3` minor is `γ₀γ₁γ₂` times a Vandermonde determinant.

**Minimality.**

* Arity: 4 is the least arity above 3, and arities 1, 2 are impossible
  (`eq_zero_of_pair_supported`).
* Width: `w = 1` is excluded by `tripleDependency_of_width_one`, so `w = 2` is the smallest width
  admitting the phenomenon.
* Field: four distinct challenges force `4 ≤ #F` (`four_le_card_of_injective`), so no field with
  fewer than four elements can carry an arity-4 example. The example is given over the smallest
  *prime* field with at least four elements; whether the four-element field also carries one is
  not claimed here.
* Optimality inside the interval: `2w + 1 = 5` for `w = 2` is the a priori ceiling; the example
  realises arity 4. No claim is made that arity `2w+1` is attained for every `w`.

**Scope label.** `EXACT_MODEL_FOR_THE_GATE_HYPOTHESIS`. The example is an exact counterexample to
the arity-3 implication *for the hypothesis as stated* — which is what the gate consumes — and it
is stated with distinct challenges and nonzero syndrome vectors, i.e. with all the nondegeneracy
the gate ever supplies. It is **not** a deployed-row statement: nothing here exhibits an official
pair `(f₀, f₁)` at the deployed parameters with four residual challenges in this position, and
nothing here excludes one.

## Where the obstruction is provably *not* realised: locator degree one

For monic degree-one locators `Q i = X − a i` the official syndrome vectors are the values of a
single affine line:

```
(synRestrict w 1 f₁ (Q i)) j = gsynd f₁ (X^{j+1}) − a i · gsynd f₁ (X^j),   i.e.  v i = s − a i • r,
```

and likewise for `f₀`. `affine_family_collinear` (PROVED) shows that the pencil relation
`s' − a i • r' = −γ i • (s − a i • r)` at three points with distinct `γ` and nonzero syndrome
vectors forces `s` and `r` to be proportional, hence all syndrome vectors to be nonzero multiples
of one vector. (The determinant obstruction: eliminating `s'` and `r'` gives `α • s + β • r = 0`
with `α = 0` forcing `γ` affine in `a`, and then `β = −d(a₂−a₁)(a₀−a₁)(a₀−a₂) ≠ 0`.)

Consequently `official_degree_one_triple_dependency` (PROVED): at `e = 1`, **every** triple of
official residual challenges (pencil-kernel monic degree-one locator, nondegenerate `f₁`-syndrome)
carries a nonzero challenge-compatible dependency, for *any* width. So at locator degree one the
arity is always three, the dependency-free subfamily has at most two challenges, and the
higher-arity phenomenon above cannot occur. The deployed locator degree is `e = 978944`; nothing
here transfers to it in either direction.

## Consequences for the direction route

Because the arity question is settled *negatively*, the direction programme cannot be entered as
planned:

* The intended STEP 2 statement — "three distinct challenges in one projective direction ⇒ the
  exact compatible dependency" — remains true as previously proved (it is
  `ResidualDependency.dependency_of_collinear` / `collinear_of_three_dependency`), but its
  converse-style use for *classification* fails: a dependency need not come from three collinear
  syndrome vectors. Partitioning residual challenges by projective direction `[v_γ]` can therefore
  miss dependencies entirely, and a fibre bound would not bound the exceptional set.
* Any future direction argument must control circuits of every arity up to `2w+1`
  (`2w + 1 = 139265` at the deployed row), not just triples; the width-1 intuition does not carry.

## HARD STOP

Not entered, per the mission rule: canonical direction definitions, projective fibre counting,
the cross-adapter comparison with affine codeword lines, boundary claims `z ≥ t−1`, general
projective theory, and any bound on `#ResidualBad` or `#Bad`.

## Claim labels

| Claim | Label |
| --- | --- |
| Dependency ⇔ dependence of the joint vectors `(v i, γ i • v i)` | PROVED |
| No dependency on one or two distinct challenges | PROVED |
| More than `2w` challenges always carry a dependency (circuits have `≤ 2w+1` challenges) | PROVED |
| Width one ⇒ every injective triple is dependent (arity 3 complete) | PROVED |
| Arity-4 dependency with no 3-supported dependency, `w = 2`, `F = ZMod 5` | PROVED, exact model for the gate hypothesis |
| Four distinct challenges require `4 ≤ #F` | PROVED |
| Degree-one official syndrome vectors are collinear; every official triple at `e = 1` is dependent | PROVED |
| An arity-4 residual dependency at the deployed row | open, not claimed |
| Any bound on `#ResidualBad` or `#Bad` | not claimed |
