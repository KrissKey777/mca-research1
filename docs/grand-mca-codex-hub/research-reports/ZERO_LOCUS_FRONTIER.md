# The zero-locus frontier: what replaces `ZeroBounded` when one bad candidate is not enough

All statements labelled **Theorem** are Lean theorems in
`RequestProject/Root/CodingTheory/ZeroLocusListSize.lean`, built by `lake build`, free of
`sorry`/`admit`, with `#print axioms` giving only `propext, Classical.choice, Quot.sound`.
Statements labelled **Experiment** are exact-arithmetic computations
(`analysis/zero_locus_list_size*.py`, `analysis/circle_factor_two_check.py`; outputs saved).
Statements labelled **Conjecture** are not proved.  Nothing here is a capacity or Johnson
claim.

Notation: `C ≤ (ι → A)` a linear code over `F` with an `F`-module alphabet `A`, `n = |ι|`,
`d = d(C)`, radius `e`, line `γ ↦ f₀ + γ f₁`, `#Bad = (badSet C e f₀ f₁).card`,
`w = d(f₁, C)`.

---

## 1. The starting point, restated

**Theorem (far regime).**  `card_badSet_le_one_of_farFrom`:
`d(f₁, C) > 2e  ⇒  #Bad ≤ 1`.
This is the weakest form of the previously proved mechanism; see `ZEROBOUNDED_STATUS.md` for
its equivalence with the `ZeroCountLt`/`ZeroBounded` packages and for the formal separation
showing it is *strictly* weaker than the ambient-code hypothesis.

## 2. What the failure mode says the generalisation must be

`ZERO_BOUNDED_FAILURE_MODE.md`: the argument breaks only when a codeword sits within distance
`2e` of `f₁`, and then the auxiliary codewords attached to different bad challenges may
differ.  So the right question is not "how many zeros does a nonzero word have" (that is
minimum distance again), but:

> when the difference `f₁ − q` to a nearby codeword `q` is *small*, how much freedom is left
> for a bad challenge?

Answer: each bad challenge is pinned by one position where `f₁ − q ≠ 0`, and distinct bad
challenges need distinct positions.  The controlling parameter is therefore the size of the
**complement of the zero locus** of `f₁ − q` — the "zero-locus complexity" of the mission
brief, in the only form that survived contact with the proof.

## 3. The list-size theorem (`L > 1`)

**Theorem (close regime).**  `card_badSet_le_hammingDistance`:

```
MinDistGe C d,  q ∈ C,  2e + 2·d(f₁,q) < d      ⇒      #Bad ≤ d(f₁,q).
```

Equivalently `card_badSet_le_card_compl_zeroLocus`: with `Z = agreementSet f₁ q` the zero
locus of `f₁ − q`,

```
#Bad  ≤  n − |Z| .
```

Auxiliary facts proved on the way, both of independent use:

* `badSet_sub_codeword` — `badSet C e f₀ (f₁ − q) = badSet C e f₀ f₁` for `q ∈ C`: the bad set
  depends on the second layer **only through its coset modulo `C`** (see §7 on syndromes);
* `card_badSet_le_hammingWeight` — the normalised form (`q = 0`).

This is a genuine `L > 1` statement: for `w = d(f₁,q) ≥ 2` it bounds the bad set by `w`, and
the bound is attained.

**Experiment (sharpness, T1 of `zero_locus_list_size_targeted.py`).**  Reed–Solomon `[10,4]`
over `F₁₁` (`d = 7`), `e = 1`, `f₁ = (1,1,0,…,0)` (so `w = 2`), `f₀ = (1,2,0,…,0)`:
`#Bad = 2 = w`, inside the regime `2e + 2w = 6 < 7 = d`.  Same picture for `[12,5]` over `F₁₃`
and `[10,3]` over `F₁₁`.

**Experiment (necessity of the regime).**  Reed–Solomon `[4,2]` over `F₅`, `e = 1`, `w = 2`
(`2e + 2w = 6 ≥ 3 = d`): `#Bad = 4 > w`.  So the hypothesis `2e + 2w < d` cannot be dropped.

**Theorem (the two regimes combined).**
`card_badSet_le_two_mul_of_six_mul_lt_minDist`: `6e < d ⇒ #Bad ≤ max 1 (2e)` — with **no**
hypothesis on the second layer.  For comparison, the project's previous alphabet-generic row
(`AlphabetMCA.card_badSet_le`) gives `#Bad ≤ n` under `3e < d`.

## 4. Does this leave unique decoding?

**No — and this should not be overstated.**  The close regime `2e + 2w < d` is *inside* the
unique-decoding radius as well: it forces `w < d/2`, i.e. `q` is the unique nearest codeword to
`f₁`.  What the theorem adds is *coverage*, not radius: it controls the regime that the far
theorem cannot see (second layer close to the code), and it does so with a list bound `L = w`
rather than `L = 1`.

The precise current position:

| second layer | condition | conclusion | proved |
|---|---|---|---|
| `w = 0` | — | `#Bad = 0` | `badSet_eq_empty_of_snd_mem` |
| `w` small | `2e + 2w < d` | `#Bad ≤ w` | `card_badSet_le_hammingDistance` |
| `w` large | `w > 2e` | `#Bad ≤ 1` | `card_badSet_le_one_of_farFrom` |
| gap `(d−2e)/2 ≤ w ≤ 2e` | — | `#Bad` up to `|F| − 1` | counterexamples, `ZERO_LOCUS_EXPERIMENTS.md` |

**Decoding radius regime: unique decoding throughout.**  No Johnson-radius statement is
proved, attempted or implied.

## 5. The circle factor 2: answer B/D, not A

The mission asked whether the circle's zero bound `2t' + 1` (against `t` for Reed–Solomon) is
an artefact of the proof.

**Theorem.**  `finrank_le_of_zeroBounded`: `ZeroBounded V t ⇒ finrank V ≤ t` (Singleton).
So the parameter a code can supply to the mechanism is bounded below by its own dimension.

The circle code of degree bound `t'` is spanned by the `2t'` words `xʲ` and `y·xʲ`, so its
dimension is `2t'` whenever those are independent on the domain, and hence no argument
whatsoever can give it a zero bound below `2t' − 1`.

**Experiment (`analysis/circle_factor_two_check.py`).**  Exhaustive over the full circle of
`F₅, F₇, F₁₁, F₁₃`:

| `p` | `|D|` | `t'` | dim | max zeros of a nonzero codeword | proved bound `2t'` | Singleton floor `dim−1` |
|---|---|---|---|---|---|---|
| 7 | 8 | 2 | 4 | 4 | 4 | 3 |
| 11 | 12 | 2 | 4 | 4 | 4 | 3 |
| 13 | 12 | 2 | 4 | 4 | 4 | 3 |
| any | — | 1 | 2 | 2 | 2 | 1 |

The maximum is *attained*: the proved bound `#zeros ≤ 2t'` is exactly sharp for the circle
code, and for ordinary Reed–Solomon the analogous bound `#zeros ≤ t−1` is exactly sharp as
well.  Hence:

* **A (artefact of the current proof): refuted.**  The bound is attained, so no better proof
  exists for the same code;
* **B (unavoidable invariant of the circle construction): supported**, in the precise sense
  that the circle code of degree bound `t'` has dimension `2t'`, twice that of the univariate
  code of the same degree bound;
* **D (instance of a general zero-locus complexity parameter): supported** — the parameter is
  the code dimension, via Singleton.  There is no separate "geometric" `κ`: for every code
  family tested, the zero bound equals `dim` up to `±1`, i.e. `κ = dim / t`.  For RS `κ = 1`,
  for the circle code `κ = 2`, and the reason is the number of independent layers, not the
  geometry of the curve;
* **C (removable under stronger hypotheses): no**, unless one shrinks the code (e.g. imposes
  `b = 0`, which is the univariate code again).

Consequently the candidate parameter `κ` of the mission brief is *not* introduced as a new
definition: it would be a synonym for the dimension of the ambient code, and the Lean statement
that expresses it is `finrank_le_of_zeroBounded`.  Rule 8 ("prefer the weakest theorem that
survives") and rule 9 ("prefer general abstractions") both point to not adding it.

## 6. Cross-code test of the new abstraction

The list-size theorem is stated for an arbitrary linear code over an arbitrary module alphabet;
it has therefore *no* per-code hypotheses to verify.  What was tested numerically is whether it
is vacuous or weak on the four families:

| family | in-regime instances | violations of `#Bad ≤ w` | max `#Bad` observed in regime |
|---|---|---|---|
| ordinary Reed–Solomon | 82 + targeted | 0 | 2 (= `w`, attained) |
| random linear codes | 17 + 529 targeted | 0 | 2 |
| folded Reed–Solomon (block alphabet) | 4 | 0 | 1 |
| exhaustive RS `[4,2]/F₅` | 281 250 | 0 | 1 |

The abstraction survives the change of algebraic geometry because it never used any: the only
code-specific input is the minimum distance `d`.

## 7. Syndrome information: reducible, not extra

**Theorem.**  `badSet_sub_codeword`: `badSet C e f₀ (f₁ − q) = badSet C e f₀ f₁` for every
`q ∈ C`.

So the bad set is a function of the *coset* `f₁ + C`, i.e. of the syndrome of `f₁`, and of
`f₀`.  Both proved regimes are stated in terms of the coset weight `d(f₁, C)`, which is the
minimum weight of the syndrome's coset.  Therefore:

* syndrome information about the second layer is exactly the information the mechanism uses —
  it provides no strictly stronger handle than the zero-locus/distance formulation;
* conversely no zero-locus statement can distinguish two words with the same syndrome.

This answers Phase 8 in the "NO" branch: the reduction is formal, and no syndrome library is
built.

## 8. Where the route stops

The gap `(d − 2e)/2 ≤ w ≤ 2e` (nonempty iff `d ≤ 6e`) is a hard barrier for this route: inside
it, `#Bad` reaches `|F| − 1` in explicit exact-arithmetic instances, so *no* bound depending
only on `(e, w, d, n)` can hold there.  Crossing it requires controlling the whole list of
codewords within distance `2e` of `f₁`, i.e. a genuine list-decoding hypothesis — which is a
different mechanism from the zero locus of a single difference.

**Conjecture (not proved, supported by the scans).**  If `L` is the number of codewords within
distance `2e` of `f₁`, then

```
#Bad  ≤  max(1, L · 2e) .
```

Checked on all 783 830 scanned instances (ordinary RS, random linear codes, folded RS,
exhaustive RS `[4,2]/F₅`), including every instance inside the gap: **0 violations**.  The
`max(1, ·)` is not cosmetic — the variant `#Bad ≤ L · max(1, 2e)` is refuted immediately by
`L = 0`, `#Bad = 1` (e.g. RS `[4,2]/F₅`, `e = 0`, `w = 1`), and that refutation is recorded in
`ZERO_LOCUS_EXPERIMENTS.md` §5.

The pinning argument of §3 yields the conjecture only when the auxiliary codewords `h_γ` are
forced to agree, so a proof needs a new ingredient (a way of grouping bad challenges by their
auxiliary codeword).  It is recorded as a conjecture, not a result, and it is *not* a
Johnson-radius statement: `2e` is still the unique-decoding-style radius.

## 9. Summary against the mission's success conditions

* **A — a strictly weaker abstraction than `ZeroBounded`:** achieved (`FarFrom`, with a formal
  separation);
* **B — a genuine list-size theorem with `L > 1`:** achieved
  (`card_badSet_le_hammingDistance`, attained at `L = 2`), inside unique decoding;
* **C — a natural zero-locus complexity parameter:** the honest answer is that it collapses to
  the code dimension (`finrank_le_of_zeroBounded`); no new parameter is introduced;
* **D — syndrome information reducible to the present framework:** achieved
  (`badSet_sub_codeword`);
* **E — a barrier:** identified and documented with explicit counterexamples (§8).

## 10. Final report

1. **Strongest theorem actually proved.**  Two, in complementary regimes, both for an arbitrary
   linear code over an arbitrary module alphabet:
   `card_badSet_le_hammingDistance` (`2e + 2·d(f₁,q) < d(C)` ⇒ `#Bad ≤ d(f₁,q)`, a list-size
   bound attained at `L = 2`) and `card_badSet_le_one_of_farFrom` (`d(f₁,C) > 2e` ⇒
   `#Bad ≤ 1`, the weakest form of the old mechanism).  Their combination
   `card_badSet_le_two_mul_of_six_mul_lt_minDist` (`6e < d ⇒ #Bad ≤ max(1,2e)`) is the
   strongest hypothesis-free statement.
2. **Strongest conjecture supported by experiments.**  `#Bad ≤ max(1, L·2e)` where `L` is the
   number of codewords within distance `2e` of the second layer: 0 violations in 783 830 exact
   instances, no proof.
3. **Strongest counterexample found.**  Inside the gap `(d−2e)/2 ≤ w ≤ 2e` the bad set reaches
   `|F| − 1` (folded RS over `F₁₁`, `n = 6`, `d = 3`, `e = 2`, `w = 3`, `#Bad = 10`), so no
   bound depending only on `(e, w, d, n)` can hold there.  Also: the circle zero bound `2t'` is
   attained, so it is not improvable.
4. **Exact current decoding-radius regime.**  Unique decoding throughout.  `FarFrom` is the
   complement of the radius-`2e` ball; the list-size theorem needs `d(f₁,q) < d/2`.  Nothing
   at or beyond the Johnson radius is proved, attempted or implied.
5. **Recommended next mission.**  Attempt the conjecture of §8 by grouping bad challenges
   according to their auxiliary codeword `h_γ`: each group is controlled by the pinning
   argument of §3, so a bound on the number of groups (a list-decoding hypothesis at radius
   `2e`) would give the conjecture.  That is the first point where a genuine list-decoding
   input becomes necessary, and it is the honest entry point to the Johnson question — not
   before.
