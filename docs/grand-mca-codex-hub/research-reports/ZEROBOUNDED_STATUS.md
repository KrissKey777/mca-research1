# `ZeroBounded`: exact logical status

Scope: the generic mechanism of `RequestProject/Root/CodingTheory/ZeroLocusGeneral.lean`
(`Alphabet.ZeroBounded`, `card_badSet_le_one_of_zeroBounded`) and the zero-count layer of
`ZeroCountSecondLayer.lean` (`Alphabet.ZeroCountLt`, `card_badSet_le_one_of_zeroCount`).
Everything asserted here as *proved* is a Lean theorem in
`RequestProject/Root/CodingTheory/ZeroLocusListSize.lean`, checked by `lake build`, with
`#print axioms` reporting only `propext, Classical.choice, Quot.sound`
(audit block at the end of `RequestProject/Main.lean`).

Notation: `C ≤ V ≤ (ι → A)` linear codes, `n = |ι|`, `e` the decoding radius,
`f₀, f₁` the two layers of the tested line, `#Bad = (badSet C e f₀ f₁).card`,
`d(f, C) = min_{c ∈ C} hammingDistance f c`.

---

## 1. Is `ZeroBounded` a minimum-distance statement?  Yes, exactly.

Already proved in `ZeroLocusGeneral.lean`:

```
zeroBounded_iff_minDistGe :  ZeroBounded V t  ↔  MinDistGe V (n − t + 1)
```

So as a property *of a code*, `ZeroBounded V t` carries no information beyond the minimum
distance of `V`.  The abstraction is a repackaging, not a new code property.  This settles the
first question of the mission in the negative: no novelty should be claimed for `ZeroBounded`
as a code invariant.

New in this phase, the converse direction of the same observation at the level of dimension:

```
finrank_le_of_zeroBounded :  ZeroBounded V t  →  Module.finrank F V ≤ t      (alphabet A = F)
```

i.e. the Singleton bound: a code can only feed the mechanism a parameter `t` at least as large
as its own dimension.  This is used in §5 below.

## 2. What does the `#Bad ≤ 1` proof actually use?  A single distance inequality.

Define, for the tested word alone,

```
FarFrom C r f  :=  ∀ c ∈ C, r < hammingDistance f c            (“d(f, C) > r”)
```

Proved:

```
card_badSet_le_one_of_farFrom :  FarFrom C (2e) f₁  →  #Bad ≤ 1
epsMCA_le_one_div_of_farFrom  :  FarFrom C (2e) f₁  →  ε_mca ≤ 1/|F|
```

with **no** further hypothesis: `f₁ ∉ C` and `2e < n` are consequences
(`notMem_of_farFrom`, `le_card_of_farFrom`), not assumptions.

And the hypothesis package of the previous theorem is *equivalent* to it:

```
farFrom_iff_exists_zeroCountLt :
    FarFrom C (2e) f₁  ↔  f₁ ∉ C ∧ ∃ t, ZeroCountLt C t f₁ ∧ 2e + t ≤ n
```

(the optimal parameter being `t = n − 2e`).  So:

* **the zero-count formulation `ZeroCountLt C t f₁ + 2e + t ≤ n` is exactly the statement
  `d(f₁, C) > 2e`** — the numerical slack `2e + t ≤ n` is what converts the zero count into a
  distance, and nothing else happens;
* the theorem is a reformulation of the standard unique-decoding argument: *if the second
  layer is outside the radius-`2e` ball around the code, two bad challenges are impossible*.
  It is a clean and code-agnostic packaging, and should be presented as that.

## 3. Which assumptions are necessary and which are convenient?

| assumption of `card_badSet_le_one_of_zeroBounded` | status |
|---|---|
| `f₁ ∉ C` | *convenient*: implied by `FarFrom C (2e) f₁` |
| `2e + t ≤ n` | *necessary in the zero-count phrasing*, but only as the bookkeeping that turns "few agreements" into "large distance"; absorbed into `FarFrom` |
| `ZeroBounded V t` for an ambient `V` | *strictly stronger than needed* (§4) |
| `C ≤ V`, `f₁ ∈ V` | needed only to state the ambient hypothesis; gone in the `FarFrom` version |
| linearity of `C` | **necessary** (used by `line_closure` and by the two-challenge interpolation) |
| alphabet an `F`-module | necessary in the same way; no field structure on `A` is used |

## 4. A strictly weaker sufficient condition exists — and it is `FarFrom`

`FarFrom` is implied by the ambient-code package (`farFrom_of_zeroBounded`), and the
implication is strict.  Formal separation (`namespace Separation`, same file), over `F₅`,
`ι = Fin 5`, `e = 1`:

* `C = span{(1,1,0,0,0)}`, `f₁ = (1,1,1,1,1)`;
* `farFrom_sepWord : FarFrom C 2 f₁` — every codeword differs from `f₁` in at least the last
  three positions, so `d(f₁, C) ≥ 3 > 2 = 2e`.  Hence `card_badSet_le_one_sep`: `#Bad ≤ 1` for
  every first layer;
* `no_zeroBounded_ambient : ∀ V ⊇ C, ∀ t, ZeroBounded V t → ¬ (2·1 + t ≤ 5)` — any ambient `V`
  contains the weight-2 codeword `(1,1,0,0,0)`, which vanishes at 3 positions, forcing `t ≥ 4`
  and `2e + t = 6 > 5 = n`.

So on this instance the `ZeroBounded` theorem is inapplicable while the `FarFrom` theorem
applies.  Structurally: `ZeroBounded` is a hypothesis about *all* of an ambient code and hence
implicitly demands `d(C) > 2e`; `FarFrom` only constrains the tested word, and the tested code
`C` may have arbitrarily bad minimum distance.

**Answer to "is `#Bad ≤ 1` implied by a still weaker condition?" — yes, `FarFrom`, and it is
weakest for this proof: the two-challenge interpolation produces a codeword within distance
`2e` of `f₁`, so the hypothesis `d(f₁,C) > 2e` is precisely the negation of the only way the
argument can fail.**  A strictly weaker *sufficient* condition would have to allow a codeword
within distance `2e` of `f₁`; §5 of `ZERO_LOCUS_FRONTIER.md` shows what happens then (the
conclusion `#Bad ≤ 1` becomes false, so no weakening of the hypothesis keeps the conclusion
`≤ 1` — it must be traded for `≤ L`).

## 5. Can the theorem be strengthened without leaving unique decoding?

Not in the `#Bad ≤ 1` conclusion: the conclusion is exactly sharp at the boundary
(`#Bad = 2` occurs as soon as `d(f₁, C) ≤ 2e`, see `ZERO_LOCUS_EXPERIMENTS.md` §2).

It can be strengthened *in coverage*, by adding the complementary regime — see
`ZERO_LOCUS_FRONTIER.md`.  The combined statement proved there,

```
card_badSet_le_two_mul_of_six_mul_lt_minDist :  6e < d(C)  →  #Bad ≤ max 1 (2e),
```

has **no hypothesis on the second layer at all** and improves the project's previous generic
row `#Bad ≤ n` (under `3e < d`) to `#Bad ≤ 2e` (under `6e < d`).

## 6. Where does the mechanism sit?

Unchanged: `2e + t ≤ n`, i.e. `d(f₁,C) > 2e`, is inside unique decoding.  Nothing in this
phase touches Johnson or capacity, and no such claim is made.
