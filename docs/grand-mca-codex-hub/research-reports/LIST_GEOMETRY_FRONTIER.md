# List-geometry frontier: the capacity refinement, and where the argument now stops

Follow-up to `LIST_GEOMETRY_PROBE.md` and `GEOMETRIC_CHARGING_AUDIT.md`.

Notation.  `C` a linear code in `ι → A` over a field `F` (`A` an `F`-module; for Reed–Solomon
`A = F` and `C = RS[n,k]`), `n = |ι|`, `d = d(C)`, radius `e`, line `γ ↦ f₀ + γ f₁`,
`w = d(f₁,C)`, `L = L(f₁,2e) = {q ∈ C : d(f₁,q) ≤ 2e}`, `#Bad = |badSet C e f₀ f₁|`.
All experiments live in the **gap** `¬(2e < w) ∧ ¬(2e + 2w < d)`, where the single-zero-locus
theorems of `ZeroLocusListSize.lean` say nothing.

Scripts (exact integer arithmetic over prime fields, no floats, no random verdicts):
`analysis/list_geometry_frontier.py` (+ `…_output.txt`),
`analysis/achieved_slopes_probe.py` (+ `…_output.txt`).

---

## 1. Starting point

`ListGeometrySlopeBound.lean` proved, unconditionally,

```
#Bad ≤ max 1 (∑_{q ∈ L} d(f₁,q))        and       #Bad ≤ max 1 (2e·|L|)
```

by charging every bad parameter to a pair `(q, x)`: `q` a *secant slope* of the witness
configuration (always a member of `L`) and `x` a position where `f₁ ≠ q`.

That counting allows a single nearby codeword to absorb `d(f₁,q)` bad parameters.  The question
of this round was whether the geometry of the whole list forbids that.

## 2. The new mechanism: a slope class is a disjoint packing

Fix a slope `q`; inside its class the witness codewords are affine, `c_γ = h + γ·q`.  Because the
witness agreement set has at least `n − e` positions, a bad `γ` of the class satisfies

```
f₀(x) + γ·f₁(x) = h(x) + γ·q(x)        for all but at most e positions x,
```

hence for at least `d(f₁,q) − e` of the `d(f₁,q)` positions where `f₁ ≠ q`.  Two distinct
parameters of the same class can never solve that equation at the same position — subtracting
gives `(γ − γ')·(f₁(x) − q(x)) = 0`.  So the class is a **disjoint packing of nonempty sets of
size ≥ max(1, d(f₁,q) − e) inside a set of size `d(f₁,q)`**:

```
|class(q)| · max(1, m − e) ≤ m,   m = d(f₁,q),
|class(q)| ≤ cap(e,m) := m                    if m ≤ e,
             min(m, ⌊m/(m − e)⌋)              if m > e.
```

`cap(e,m) ≤ e + 1` for every `m`, and `cap(e,m) ≤ 2` as soon as `3e < 2m` (in particular at the
extremal distance `m = 2e`, `e ≥ 1`).

### Consequences (all proved in Lean, `RequestProject/Root/CodingTheory/ChargingCapacity.lean`)

| statement | Lean name |
| --- | --- |
| `\|B\| ≤ cap(e, d(f₁,r))` for a slope class `B` (abstract packing lemma) | `Alphabet.card_le_chargeCap` |
| `Q ⊇ L ⇒ #Bad ≤ max 1 (∑_{q∈Q} cap(e, d(f₁,q)))` | `Alphabet.card_badSet_le_sum_chargeCap` |
| `Q ⊇ L ⇒ #Bad ≤ max 1 ((e+1)·\|Q\|)` | `Alphabet.card_badSet_le_succ_mul_card` |
| all `q ∈ Q` have `3e < 2·d(f₁,q)` ⇒ `#Bad ≤ max 1 (2·\|Q\|)` | `Alphabet.card_badSet_le_two_mul_card_of_two_mul_le` |
| explicit-list forms | `…_nearbyList` variants |
| Reed–Solomon realisations | `rs_card_badSet_le_sum_chargeCap`, `rs_card_badSet_le_succ_mul_card` |

Gains over the previous round: the per-codeword factor drops from `2e` to `e + 1` (and to `2`
in the extremal regime), the hypothesis "every element of `Q` is close to `f₁`" is no longer
needed for the list-size form, and `cap(e,m) ≤ m` makes the weight form strictly sharper.

`lake build` is clean; every declaration reports axioms exactly
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no new axioms.

## 3. Experimental status

`analysis/list_geometry_frontier.py`, **34 514 gap instances** over
RS[4,2]/F₅, RS[4,3]/F₅, RS[5,2]/F₅, RS[5,3]/F₅, RS[6,2]/F₇, RS[6,3]/F₇, RS[6,4]/F₇, RS[7,3]/F₇,
RS[5,2]/F₁₁, RS[6,3]/F₁₁, RS[6,2]/F₁₃ (exhaustive over coset representatives in the small
families, sampled cosets in the large ones):

| candidate | violations |
| --- | --- |
| load bound `\|class(q)\| ≤ cap(e, d(f₁,q))` (over **all** witness choices) | 0 |
| `#Bad ≤ max(1, ∑_q cap(e, d(f₁,q)))` — **proved** | 0 |
| `#Bad ≤ max(1, (e+1)·\|L\|)` — **proved** | 0 |
| `#Bad ≤ max(1, ∑_q d(f₁,q))`, `#Bad ≤ max(1, 2e·\|L\|)` (previous round) | 0 |
| `#Bad ≤ 1 + ∑_q (d(f₁,q) − 1)` (not proved) | 0 |
| `#Bad ≤ max(1, 2·\|L\|)`, `#Bad ≤ max(1, \|L\| + e)` (not proved) | 0 |

The last two rows are unrefuted but **unproved**, and they are not adopted: the mechanism above
gives no reason for them, and they are far weaker questions than the one in §4.  Aggregate
sharpening measured over the same instances: `∑_q d(f₁,q) − ∑_q cap(e,d(f₁,q)) = 414 796` in
total (e.g. the extremal RS[6,3]/F₁₁ `e = 2` instance: `∑d = 522` versus `∑cap = 276`, with
`#Bad = 11`).

## 4. Where the argument now stops — the *achieved-slope* count

Write `A` for the number of **distinct slopes actually achieved** by the bad set.  The proved
chain is

```
#Bad = ∑_{achieved q} |class(q)|  ≤  ∑_{achieved q} cap(e, d(f₁,q))  ≤  ∑_{q ∈ L} cap(e,d(f₁,q))  ≤  (e+1)|L| .
```

`analysis/achieved_slopes_probe.py` (2 033 gap instances with `#Bad ≥ 2`) measures each step:

* the first two steps are essentially tight — `#Bad ≤ ∑_{achieved} cap` was attained with
  ratio `1.0`;
* the third step is where everything is lost: the largest observed `A` is **9** while the
  largest `L` is **136**;
* and `A` itself admits no cheap bound: `A ≤ e + 1` (670 violations), `A ≤ 2e` (438),
  `A ≤ w + 1` (545) and even `A ≤ n` (33 violations, e.g. RS[6,3]/F₁₁, `e = 2`, `n = 6`,
  `A = 7`, and up to `A = 9` with `#Bad = 10`) all fail.

So the residual obstacle is now sharply localised: **bound the number of achieved slopes**, i.e.
the size of the sub-list of `L` realised as secant slopes.  That is exactly a list-decoding /
Johnson-type question, and it is not answered here.  Every invariant of the *list* alone
(pairwise zero loci and their intersections, `dim span(L − q₀)`, `max_{0≠p∈W}|Z(p)|`, syndrome
dimension) was already shown in `LIST_GEOMETRY_PROBE.md` to be constant across buckets in which
`#Bad` varies, and the present run reproduces that: in every discriminating bucket
(`same p, n, d, e, w`, different `#Bad`) the separating-invariant set is empty for
`dim W` and `maxZeroW`.

## 5. What is *not* claimed

* No bound on `|L(f₁,2e)|` or on `A` is proved.  Inside the gap `|L|` can be a large fraction of
  the code, and there the theorems above are weaker than the trivial `#Bad ≤ |F|`.
* No Johnson-radius, list-decoding-capacity or ordinary-RS-capacity statement is proved or
  implied, and no performance claim follows.
* The unrefuted-but-unproved candidates `#Bad ≤ max(1, 2|L|)`, `#Bad ≤ max(1, |L| + e)` and
  `#Bad ≤ 1 + ∑(d(f₁,q) − 1)` are conjectures supported only by the instances listed above.
* Negative results (`A ≰ n`, etc.) are exact counterexamples on the instances recorded, not
  general theorems.

## 6. Why the charging route saturates here

The achieved-slope count is squeezed between the two sides of the new theorem:

```
A ≤ #Bad − 1        (each bad parameter carries exactly one slope)
#Bad ≤ ∑_{achieved q} cap(e, d(f₁,q)) ≤ (e+1)·A + 1 .
```

So `A` and `#Bad` determine each other up to the factor `e + 1`: *bounding the achieved-slope
count is the same problem as bounding `#Bad`*.  The charging/packing mechanism has therefore
extracted everything it can — it converts the question into a question about the nearby-codeword
list and nothing smaller.  Any further progress must come from outside: a genuine bound on
`|L(f₁,2e)|` (Johnson-type or interpolation-based list decoding), which is not proved here.  What
the present round guarantees is the exchange rate: **any** list-size bound `B ≥ |L(f₁,2e)|` now
yields `#Bad ≤ max(1, (e+1)·B)`, and `#Bad ≤ max(1, 2·B)` when the nearby codewords sit at
distance `> 3e/2`.

## 7. Next mathematical target, and the verdict of this round

Since `A` and `#Bad` are equivalent up to the factor `e + 1` (§6), the only remaining lever is a
bound on the size of the nearby-codeword list itself,

    |L(f₁,2e)| = #{q ∈ C : d(f₁,q) ≤ 2e},

for radii `2e` inside the gap.  That is precisely Johnson/list-decoding territory and is *not*
proved here; the contribution of this round is that the exchange rate is now optimal for the
charging mechanism (`e + 1` per nearby codeword, `2` in the extremal regime) and unconditional.

Verdict, in the terms of the mission's stop conditions: the *list-geometry* invariants
(pairwise zero loci and intersections, `dim W`, `max_{0≠p∈W}|Z(p)|`, syndrome dimension) give no
information beyond minimum-distance-free counting — they are constant across instances in which
`#Bad` varies — while the *packing* structure inside a slope class does give strictly more, and
has now been extracted in full.  Further progress requires external list-decoding machinery, not
another invariant of the same kind.
