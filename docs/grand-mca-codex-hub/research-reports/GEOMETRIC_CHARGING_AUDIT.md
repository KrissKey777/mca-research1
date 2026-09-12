# Geometric charging for the MCA bad set

Mission report: *is the bad set of a line controlled by a **disjoint charging** of the whole
nearby-codeword list, rather than by a single zero locus?*

**Answer: yes, and the charging is purely linear-algebraic — nothing in it is
Reed–Solomon-specific.**  The numerical list inequality is a corollary of the charging map, not
the other way round.  Every claim below is either a Lean theorem (built by `lake build`, no
`sorry`, axioms exactly `propext, Classical.choice, Quot.sound`) or an exact-arithmetic
experiment with a saved output file.  No Johnson, list-decoding-capacity or performance claim is
made anywhere.

---

## Phase 0 — the definitions (unchanged) and what they depend on

Definitions are those of `RequestProject/Root/CodingTheory/AlphabetMCA.lean`; none was modified.
`C ≤ (ι → A)` is a submodule (linear code) over a field `F` with an `F`-module alphabet `A`;
`n = |ι|`, `d = d(C)`, radius `e`, line `γ ↦ f₀ + γ·f₁`.

| notion | definition | file |
|---|---|---|
| `AgreeOn C S f` | `∃ c ∈ C, ∀ x ∈ S, f x = c x` | `AlphabetMCA.lean` |
| `LineAgreeOn C S f₀ f₁` | `∀ γ, AgreeOn C S (f₀ + γ f₁)` | `AlphabetMCA.lean` |
| `IsBad C e f₀ f₁ γ` | `∃ S, n ≤ |S| + e ∧ AgreeOn C S (f₀ + γ f₁) ∧ ¬ LineAgreeOn C S f₀ f₁` | `AlphabetMCA.lean` |
| `badSet`, `#Bad` | `{γ : IsBad …}`, its cardinality | `AlphabetMCA.lean` |
| `L(f₁, r)` | `{q ∈ C : d(f₁,q) ≤ r}` (`nearbyList C e f₁` for `r = 2e`) | `ListGeometrySlopeBound.lean` |
| `w` | `d(f₁, C)` | — |

### Which facts are RS-specific?

| fact | needs | verdict |
|---|---|---|
| secant slope `(γ−γ')⁻¹·(c−c')` is a codeword | `C` a submodule, `F` a field | **not** RS, not even MDS |
| slope lies within `2e` of `f₁` (`hammingDistance_slope_le`) | agreement sets of size `≥ n−e`, counting | **not** RS: pure Hamming counting |
| affine structure `c γ = h + γ·q` inside a slope class | field scalars, module alphabet | **not** RS |
| pinning: a bad `γ` differs from its slope somewhere on `S` (`exists_pin`) | `line_closure`, i.e. submodule only | **not** RS |
| position determines the parameter | `A` a module over the **field** `F` (`γ·v = γ'·v, v ≠ 0 ⇒ γ = γ'`) | **not** RS |
| the old regime hypotheses `2e + 2w < d`, `w > 2e` | minimum distance | MDS/parameter-specific, and **no longer needed** |

So the charging theorem lives one level below Reed–Solomon: the "local geometric axiom" the
mission asked for is satisfied by *every* linear code over a module alphabet.  Reed–Solomon
enters only when one wants a **bound on the size of the list** `L(f₁,2e)` — that, and only that,
is where MDS/Johnson-type input would be needed.

---

## The charging lemma (Lean: `Alphabet.exists_charging`)

> If `1 < #Bad`, there is a map `chg : F → (ι → A) × ι` such that for every bad `γ`
> * `(chg γ).1 ∈ C` and `d(f₁, (chg γ).1) ≤ 2e` — the charged codeword is in the list `L(f₁,2e)`;
> * `f₁ ((chg γ).2) ≠ (chg γ).1 ((chg γ).2)` — the charged position lies in the "resource packet"
>   `supp(f₁ − q)`, i.e. on the Hamming geodesic from `f₁` to `q`;
> * `chg` is injective on the bad set — **distinct bad parameters consume distinct resources**.

Mechanism (all four steps are Lean lemmas in
`RequestProject/Root/CodingTheory/ListGeometrySlopeBound.lean`):

1. **Slope ⇒ list.**  Two bad parameters `γ ≠ γ'` with witnesses `(S,c)`, `(S',c')` agree on
   `S ∩ S'`, of size `≥ n − 2e`, where `(γ−γ')·f₁ = c − c'`; hence the secant slope
   `q = (γ−γ')⁻¹·(c−c')` satisfies `d(f₁,q) ≤ 2e` (`hammingDistance_slope_le`, `slope_mem`).
2. **Charge.**  Fix one bad `γ₀`; charge each bad `γ` to its slope towards `γ₀`
   (and `γ₀` itself to the slope of some other bad parameter).
3. **Affine class.**  Inside one slope class the witness codewords are affine,
   `c γ = h + γ·q` with the intercept `h = c γ₀ − γ₀·q` depending on the slope only.
4. **Pinning.**  If `f₁` agreed with `q` everywhere on `S γ` then `f₀` would agree with `h` there
   too, so the whole line would agree on `S γ` and `γ` would not be bad (`exists_pin`).  Hence
   some `x ∈ S γ` has `f₁ x ≠ q x`, and there `γ·(f₁ x − q x) = h x − f₀ x` **determines** `γ`.

Corollaries (all in the same file, all unconditional):

| statement | Lean name |
|---|---|
| `#Bad ≤ max 1 (∑_{q ∈ Q} d(f₁,q))` for any `Q ⊇ L(f₁,2e)` | `card_badSet_le_sum_hammingDistance` |
| `#Bad ≤ max 1 (2e·|Q|)` | `card_badSet_le_two_mul_mul_card` |
| `#Bad ≤ max 1 (∑_{q ∈ L(f₁,2e)} d(f₁,q))` | `card_badSet_le_sum_nearbyList` |
| `#Bad ≤ max 1 (2e·|L(f₁,2e)|)` | `card_badSet_le_two_mul_mul_card_nearbyList` |
| empty list ⇒ `#Bad ≤ 1` (the old far regime) | `card_badSet_le_one_of_empty_list` |
| unique nearby codeword `q` ⇒ `#Bad ≤ max 1 (d(f₁,q))`, **no** `2e+2w<d` hypothesis | `card_badSet_le_hammingDistance_of_unique_nearby` |

Reed–Solomon realisation (Part 6 of the file), obtained from the code-generic theorem through
the existing bridge `badSet_eq_alphabet_badSet`, i.e. Reed–Solomon is used only as *a linear
code*:

| statement | Lean name |
|---|---|
| `#Bad ≤ max 1 (∑_{q∈Q} d(f₁,q))` for the RS code of degree `< k` on `D` | `rs_card_badSet_le_sum_hammingDistance` |
| `#Bad ≤ max 1 (2e·|L(f₁,2e)|)` for the same | `rs_card_badSet_le_two_mul_mul_card` |

Relation to what existed before:

* `card_badSet_le_one_of_farFrom` (`w > 2e ⇒ #Bad ≤ 1`) is the case `L = ∅`;
* `card_badSet_le_hammingDistance` (`2e + 2w < d ⇒ #Bad ≤ w`) is the case `|L| = 1`, and the new
  version **drops the minimum-distance hypothesis**, so it applies inside the gap
  `(d−2e)/2 ≤ w ≤ 2e` where the old one does not;
* the bound is now driven by a list invariant, so **any** bound on `|L(f₁,2e)|` (from any source)
  immediately bounds `#Bad`.  This is the bridge the mission asked for; no such list bound is
  claimed here.

---

## Phase 1–2 — experiments (exact arithmetic)

Scripts and saved outputs: `analysis/geometric_charging_probe.py`
(`analysis/geometric_charging_probe_output.txt`, incremental state in
`analysis/geometric_charging_progress.json`), `analysis/geometric_charging_extra_checks.py`
(`…_output.txt`), and the earlier `analysis/list_geometry_probe.py`
(`…_output.txt`).  Instances are enumerated over coset representatives (exhaustive up to the
proved invariance `badSet_sub_codeword`), restricted to the gap
`¬(2e < w)` and `¬(2e + 2w < d)`, i.e. exactly where the previous theorems say nothing.

### Charging structure — 39 530 gap instances with `#Bad ≥ 2`

| question | measurement |
|---|---|
| does every bad parameter have a witness in `L(f₁,2e)`? | yes, 39 530/39 530 |
| is a charged position always found? | yes, 39 530/39 530 |
| is the charging injective? | yes, 39 530/39 530 |
| does each charged position lie in `supp(f₁ − q)` (on the geodesic `f₁ → q`)? | yes, 39 530/39 530 |
| is the load of a slope `q` at most `d(f₁,q)`? | yes, 39 530/39 530 |
| maximal load of a single slope | 3 |
| do different slope classes reuse the same *position*? | yes, often (71 032 collisions) — the resources are disjoint as **pairs**, not as positions |

The last row is the reason a naive "positions only" bound must fail, and it does (H4 below).

### Falsification hierarchy

| hypothesis | verdict | smallest counterexample found |
|---|---|---|
| **H0** `#Bad ≤ max(1, Σ_{q∈L} d(f₁,q))` | **survives** (and is proved in Lean) | — |
| **H1** `#Bad ≤ Σ_{q∈L} d(f₁,q)` (no floor) | refuted | `RS[4,1]` over `F₅` (`d=4`), `e=1`, `f₁=(0,1,2,3)`, `f₀=0`: `L = ∅`, `#Bad = 1 > 0`. The floor `1` is needed **exactly** when the list is empty |
| **H2** `#Bad ≤ max(1, w)` | refuted | `RS[4,2]` over `F₅`, `e=1`, `w=1`, `f₀=(0,0,1,0)`, `f₁=(0,0,0,1)`: `#Bad = 3 > 1` |
| **H3** `#Bad ≤ max(1, MST mass of {f₁} ∪ L)` | survives, but **collapses**: over 582 distinct gap configurations the spanning-tree mass equalled the radial sum in *every* case (the star at `f₁` is optimal, since codewords are `≥ d` apart while the list lies within `2e ≤ d` of `f₁`). Tree geometry gives nothing beyond the radial sum here | — |
| **H4** `#Bad ≤ max(1, |⋃_{q∈L} supp(f₁ − q)|)` (boundary/branching mass) | refuted | `RS[6,3]` over `F₇`, `e=2`, `f₀=(0,0,0,0,1,0)`, `f₁=(0,0,0,0,0,1)`: boundary mass `6`, `#Bad = 7`. Note this also refutes `#Bad ≤ n` |
| **H5** `#Bad ≤ max(1, max_{q∈L} d(f₁,q))` | refuted | `RS[4,2]` over `F₅`, `e=1`: `max d = 2`, `#Bad = 3` |

So among the candidate invariants exactly one survives, and it is the one the charging map
produces.  The "branching"/boundary route is dead: `#Bad` can exceed the number of positions
touched by the whole list, because two bad parameters may charge the same position through
different slopes.

---

## What this does *not* claim

* No bound on `|L(f₁,2e)|` is proved.  In the gap the list can be large (e.g. `|L| = 76` in the
  `RS[6,3]/F₇` instance above), so the theorem does not by itself beat `#Bad ≤ |F| − 1` there.
* No Johnson-radius, list-decoding-capacity, or ordinary-RS capacity statement is proved,
  attempted, or implied.
* No performance claim.

## Next mathematical target

The charging lemma reduces the MCA question to a pure list-size question:

> bound `|L(f₁,2e)|` (or, better, `∑_{q ∈ L} d(f₁,q)`) for the codes of interest.

That is precisely a Johnson-type statement, and it is now the *only* missing ingredient: with any
such bound `B`, the Lean corollary `card_badSet_le_two_mul_mul_card` turns it into
`#Bad ≤ max(1, 2e·B)` with no further work.  A second, cheaper target suggested by the data is
the observed maximal slope load 3: whether `∑_{q ∈ L} min(d(f₁,q), κ)` with a small absolute
constant `κ` is already an upper bound is *not* proved and was not tested adversarially.
