# The Residual RS Structure Theorem

**Status.** Everything stated here as a theorem is machine-checked and `sorry`-free; the axiom
audit `RequestProject/ResidualRSStateAxiomAudit.lean` reports only `propext`,
`Classical.choice`, `Quot.sound` for all 36 declarations of the two new modules.

New modules (both build clean, nothing existing was modified or deleted):

* `RequestProject/Root/CodingTheory/ResidualRSState.lean`
* `RequestProject/Root/CodingTheory/ResidualRSShortening.lean`
* `RequestProject/Root/CodingTheory/ResidualRSSharpness.lean`

Plan and refined instruction: `GRAND_MCA_RESIDUAL_PROGRAMME.md`.

Notation: `n = |D|`, `C = RS_k(D)`, `e` the radius, `q = |F|`,
`#Bad = |badSet k e f₀ f₁|`, official badness as in `MCA.lean`.

---

## 1. The strongest new structural theorem

> **Residual RS Structure Theorem.**  Let `(a,b)` be a received pair supported on a window `A`.
> If no local shortening of `A` hides a codeword — that is, if
> `Short(C, A ∪ Z) = 0` for every `Z` with `|Z| ≤ e` — then
> ```
> #Bad ≤ e + 1     and     #Bad ≤ |supp a ∪ supp b|.
> ```
> The hypothesis is a pure dimension condition: by the *exact* criterion
> `Short(C,B) = 0 ↔ (B = ∅ ∨ k + |B| ≤ n)`, it holds precisely when `k + |A| + e ≤ n`
> (given `|A| + e ≤ n`), and it fails as soon as `n < k + |A| + e`.

Moreover the bad set is then **explicitly described**: every bad challenge is a *slope* of the
residual pair,
```
badSet ⊆ { −a(x)/b(x) : x ∈ supp a ∪ supp b },
```
and if the maximum `e + 1` is attained (with `e ≥ 1`) the residual support has exactly `e + 1`
points, one per bad challenge.

Lean:

```
Root.CodingTheory.card_badSet_le_succ_of_no_invisible_direction   -- the theorem
Root.CodingTheory.badSet_subset_image_residualSlope               -- slope localisation
Root.CodingTheory.card_pairSupport_eq_of_card_badSet_ge           -- the extremal case
Root.CodingTheory.exists_badSet_subset_image_residualSlope        -- canonical form
Root.CodingTheory.shortCode_eq_bot_iff                            -- the exact criterion
Root.CodingTheory.card_badSet_le_of_supported                     -- numerical form
Root.CodingTheory.card_badSet_le_card_pairSupport_of_card         -- support form
```

Making the residual state and its invariant first class:

```
Root.CodingTheory.ResidualRSState              -- (A, p₀, p₁) with defects vanishing off A
Root.CodingTheory.ResidualRSState.badSet_eq    -- faithful: the bad set is unchanged
Root.CodingTheory.jointDefect                  -- rank of the smallest residual state
Root.CodingTheory.exists_residualRSState_jointDefect
Root.CodingTheory.jointDefect_le_rank
Root.CodingTheory.jointDefect_le_two_mul_of_one_lt   -- descent:  ≥2 bad ⟹ jointDefect ≤ 2e
Root.CodingTheory.card_badSet_le_succ_of_jointDefect -- rigidity in the invariant
Root.CodingTheory.card_badSet_le_jointDefect
Root.CodingTheory.residual_rigidity_dichotomy
```

### What is new relative to what was banked

The banked sharp theorem (`ShadowDescentSharpBound.card_badSet_le_succ_of_third`) reads
`#Bad ≤ e + 1` **under the capacity condition `k + 3e ≤ n`** (plus `1 ≤ k`). The new theorem
replaces `3e` by `jointDefect + e`, where `jointDefect ≤ 2e` always holds once two challenges
are bad. Consequences:

* the capacity theorem is now a **corollary** with *no* auxiliary hypothesis
  (`card_badSet_le_succ_of_capacity_residual`);
* the bound holds **arbitrarily far beyond capacity** whenever the received pair happens to be
  jointly close to the code: rigidity is governed by the *proximity of the instance*, not by the
  rate/radius pair. A row with `k + 3e ≫ n` is still rigid if its residual state is small;
* the count also improves to `#Bad ≤ jointDefect` when the residual state is smaller than `e+1`.

The theorem is *not* a Johnson-type or overlap-counting statement, and it uses no list-decoding
input: the code enters only through "a polynomial of degree `< k` with `k` roots is `0`", i.e.
at the evaluation-code level. The Reed–Solomon structure is used only in the shortening
criterion.

### Sharpness in the new region

The constant cannot be improved anywhere the new hypothesis reaches
(`ResidualRSSharpness.exists_badSet_card_eq_succ_residual`): for every `k, e` with
`k + 2e + 1 ≤ n` there is a received pair with **exactly** `e + 1` bad challenges — take
`b = 1_T`, `a = −x·1_T` on a set `T` of `e + 1` domain points, whose slope at `x ∈ T` is `x`
itself.  For `e ≥ 2` the hypothesis `k + 2e + 1 ≤ n` is strictly weaker than `k + 3e ≤ n`, so
this is sharpness in a region the banked sub-capacity construction does not cover.

---

## 2. The conceptual mechanism

Write `T = supp a ∪ supp b ⊆ A` and let `γ` be bad with official window `S`, explained by a
polynomial `q` of degree `< k`.

1. **Visibility.** `q` is forced to vanish on `S`. Two independent reasons, and they are the same
   reason in two representations:
   * *counting*: `|S \ A| ≥ (n − e) − |A| ≥ k`, and on `S \ A` the residual pair is zero, so `q`
     has `k` roots (`noInvisible_of_card`);
   * *shortening*: the word of `q` lies in `Short(C, A ∪ Sᶜ)`, a shortening at a window of size
     `≤ |A| + e`, which is `0` exactly under the same inequality
     (`noInvisible_of_shortCode_eq_bot`, `shortCode_eq_bot_iff`).

   This is the answer to the question posed in the brief: *what prevents arbitrarily many
   invisible projective directions* is the triviality of the family of shortenings
   `Short(C, A ∪ Z)`, `|Z| ≤ e`, and that triviality is an exact dimension condition on the
   **residual** domain, not on the ambient one.

2. **Officiality produces a witness point.** If `S ∩ T = ∅` the whole line would be explained on
   `S` by the zero polynomial, contradicting noncontainment. So `S ∩ T ≠ ∅`, and every point of
   it lies in the *challenge zero set* `M_γ = {x ∈ T : a x + γ·b x = 0}`.

3. **A point cannot kill two challenges.** If `x ∈ M_γ ∩ M_{γ'}` with `γ ≠ γ'` then `b x = 0`,
   hence `a x = 0`, hence `x ∉ T`. So the `M_γ` are pairwise disjoint (`challengeZeros_disjoint`).

4. **Each `M_γ` is large.** `T \ M_γ ⊆ Sᶜ`, so `|M_γ| ≥ |T| − e`.

Disjoint nonempty subsets of `T` give `#Bad ≤ |T|`; the size bound gives
`#Bad·(|T| − e) ≤ |T|`; together `#Bad ≤ e + 1`. Steps 2–4 use only linearity of the code, and
no hypothesis at all on `k`, `e`, `n`.

In one line: **a residual state is a pencil on `≤ |A|` coordinates; each bad challenge consumes
a nonempty private part of that support; the only way to have many challenges is to have an
invisible codeword, i.e. a nontrivial shortening.**

---

## 3. The cost when the hypothesis fails

Beyond the residual threshold the deviation codewords are stratified by their support outside
`A`, each stratum being a shortening. Counting through the nodal factorisation
(`card_localLowWeightCodewords_le`) and feeding it into the banked localised cluster bound gives,
for `3e ≤ n` and with **no other hypothesis**:

```
#Bad ≤ (e+1) · (1 + C(n, e) · q^(k − (n − 3e)))          (card_badSet_le_residual_cost)
```

against the banked global form `#Bad ≤ (e+1)·(1 + C(n, 3e)·q^(k − (n − 3e)))`
(`card_badSet_le_explicit_cost`). The combinatorial factor drops from `≈ n^{3e}` to `≈ n^{e}`:
only the part of a deviation living *outside the residual window* is free; the part inside `A`
is already accounted for by the descent.

---

## 4. Boundary audit

A theorem strong enough to close the deployed rows must not also close the known extremal
families. It does not:

* `le_jointDefect_polyWord_pow`: for the gap-one pencil (`f₁ = x^k`) the joint defect is at least
  `n − k`, because `x^k` disagrees with every codeword on at least `n − k` points;
* `not_residual_hypothesis_polyWord_pow`: hence `n < k + jointDefect + e` for every `e ≥ 1` —
  the residual hypothesis fails, exactly as it must, since that family realises `C(n, k+1)` bad
  challenges.

More generally the contrapositive `lt_jointDefect_of_card_badSet_gt` says that *every* instance
with `#Bad > e + 1` is jointly far from the code, so all the superpolynomial families already in
this repository are certified to have large residual states. Consistency is a theorem here, not
an observation.

---

## 5. The smallest remaining obstruction to Grand MCA

The theory now has exactly two numerical inputs about the residual rank `r = jointDefect`:

```
descent   :  #Bad ≥ 2   ⟹  r ≤ 2e                (jointDefect_le_two_mul_of_one_lt)
rigidity  :  r ≤ n − k − e  ⟹  #Bad ≤ e + 1      (card_badSet_le_succ_of_jointDefect)
```

Composing them gives precisely the banked sub-capacity theorem, and nothing more:
`#Bad > e + 1 ⟹ n < k + 3e` (`lt_card_of_card_badSet_gt`). Therefore:

> **The single remaining obstruction is the gap `2e` versus `n − k − e`.**  Grand MCA in this
> language is the statement that an instance with many bad challenges admits a residual state of
> rank `≤ n − k − e` (equivalently: that the descent can be improved below `2e`, or that the
> deviation codewords can be absorbed into the codeword pair).

Two concrete forms of the missing input, both stated in objects that now exist:

1. **Sharper descent.** Is there, for every instance with `m` bad challenges, a residual state of
   rank `≤ 2e − f(m)` (or `≤ e + o(e)`)? The current descent uses only two challenges; the
   remaining `m − 2` are unused. Any strict improvement of the constant `2` immediately moves the
   rigidity threshold from `k + 3e ≤ n` towards capacity.
2. **Absorbing the invisible directions.** If `γ` is bad with an invisible codeword `c`
   (`c ∈ Short(C, A ∪ Z) \ {0}`), can `c` be subtracted so as to produce a residual state of
   smaller rank for a *subfamily* of the challenges? This is the functorial/descent form: a
   well-founded invariant that strictly decreases along "adjoin the invisible codeword".
   `shortCode_eq_bot_iff` says exactly when such a `c` exists, and
   `exists_shortCode_ne_bot_of_residual` produces one; what is missing is a transport of the
   official witnesses along that subtraction.

Nothing in this file claims a bound beyond capacity better than the cost bound of §3, and no
performance or implementation claim is made.
