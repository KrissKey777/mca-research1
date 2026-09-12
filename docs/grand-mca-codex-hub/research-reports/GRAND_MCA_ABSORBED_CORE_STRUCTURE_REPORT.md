# The intrinsic structure of a family of absorbed invisible cores

*Companion to `RequestProject/Root/CodingTheory/AbsorbedCore{Module,Directions,Descent,Filtration,ExactSequence,Witness}.lean`.
Everything below is machine-checked and `sorry`-free; the axiom audit is
`RequestProject/AbsorbedCoreAxiomAudit.lean` (only `propext`, `Classical.choice`, `Quot.sound`).
All statements are for an arbitrary linear code `C ≤ (ι → A)` over an arbitrary alphabet module
`A` over a field `F`; no Reed–Solomon structure is used anywhere.*

## The question

> What is the intrinsic algebraic structure of a family of absorbed invisible cores inside one
> residual rank-two state?

## The answer

**It is not a number, it is a torsor over a module — and the module is a shortening of the
code.**

Fix a received pair `(f₀, f₁)` and a window `W ⊆ ι`.  Let

```
absorbedCores C f₀ f₁ W = { (c₀,c₁) ∈ C × C : supp(f₀−c₀) ∪ supp(f₁−c₁) ⊆ W }
corePairs     C W       = Short(C,W) × Short(C,W)
```

be, respectively, the family of absorbed cores producing a residual state inside `W`, and the
module of pairs of codewords supported inside `W`.

1. **Torsor theorem** (`absorbedCores_bijOn_corePairs`, `absorbedCores_eq_coset`).  The family is
   empty or an affine space over `corePairs C W`: subtraction by any member is a bijection onto
   that module.  *The family's structure does not depend on the received pair at all* — only on
   the code and the window.  Differences of absorbed cores are exactly the invisible cores
   hidden by the window (`sub_mem_corePairs`, `add_mem_absorbedCores`).
2. **Lattice behaviour** (`absorbedCores_inter`, `shortening_inter`, `shortening_mono`).  The
   window assignment is monotone and meet-preserving on both sides:
   `absorbedCores(W) ∩ absorbedCores(W') = absorbedCores(W ∩ W')` and
   `Short(C, W ∩ W') = Short(C,W) ⊓ Short(C,W')`; the least window carrying a given state is its
   joint support (`mem_absorbedCores_jointSupport`).
3. **The complexity bound — why families cannot stay complicated**
   (`finrank_shortening_le`, `finrank_shortening_add_dist_le`).  A Singleton-type argument gives
   `dim Short(C,W) ≤ (|W| + 1 − d)·dim A`, hence the family has dimension
   `≤ 2(|W| + 1 − d)·dim A`.  Read backwards (`dist_le_card_of_shortening_ne_bot`): a
   `t`-dimensional core family forces `d + t ≤ |W| + 1`.  Complexity of the family is *paid for*
   in residual rank; this is a dimension argument, not a counting argument.
4. **Terminal or core** (`terminal_or_core`, `subsingleton_absorbedCores_of_noCore`).  For every
   window: either the state supported there is unique — the family is a *point*, a finite
   terminal structure — or the code contains a nonzero word of weight `≤ |W|`, a genuine
   invisible core, and then the family has size `|Short(C,W)|² ≥ |F|²`.  There is no intermediate
   behaviour.
5. **The instance-independent container** (`lowWeightCore`, `sub_mem_lowWeightCore`,
   `lowWeightCore_eq_iSup_shortening`, `lowWeightCore_eq_bot_iff`).  All absorbed cores of all
   states of rank `≤ ρ` lie in one canonical submodule of the code, the span of its words of
   weight `≤ 2ρ`; it is the supremum of the small shortenings, and it vanishes exactly when
   `NoCore` holds.

## The canonical invariant: a filtration, not a scalar

Attach to a window the subspace of directions in which the rank-two extension degenerates:

```
Lost(W) = { (α,β) ∈ F² : α·f₀ + β·f₁ ∈ C ⊔ P_W } ≤ F².
```

* `Lost` is monotone, and `Lost(W) = ⊤` **iff** the received pair can be absorbed into `W`
  (`lostDirections_eq_top_iff_nonempty`).
* Since `dim F² = 2`, two independent lost directions force `⊤` (`eq_top_of_det_ne_zero`).  So a
  window is in exactly one of three regimes (`lostDirections_trichotomy`): nothing lost, a single
  projective point — the **fixed shadow** (`exists_span_of_ne_bot_of_ne_top`,
  `lostDirections_eq_span_of_ne_top`) — or total collapse.
* Consequently the filtration `W ↦ Lost(W)` has exactly **two jumps**, and their positions are
  the canonical invariants

  ```
  pencilDefect = min { |W| : Lost(W) ≠ ⊥ }   ≤   jointDefect = min { |W| : Lost(W) = ⊤ }
  ```

  (`pencilDefect_le_card_of_ne_bot`, `exists_window_card_eq_pencilDefect`,
  `jointDefect_le_card_of_eq_top`, `exists_window_card_eq_jointDefect`,
  `pencilDefect_le_jointDefect`).  The pencil defect is the least distance from the code of a
  nonzero direction of the pencil.
* The middle regime is **not vacuous**: `AbsorbedCoreWitness.lean` exhibits a two-position
  instance over `𝔽₂` with `pencilDefect = 1 < 2 = jointDefect` and an explicit fixed shadow.  So
  the pair `(pencilDefect, jointDefect)` is strictly finer than the scalar `jointDefect`.

## Relation to fixed shadows, the deviation map and Rank2

* **Fixed shadows** are the middle regime of the filtration: a window explains at most one
  challenge unless the state collapses onto it (`challenge_unique_or_collapse`), and the set of
  challenges a window explains is a single challenge or the whole field
  (`explained_subsingleton_or_all`).  The "projective direction" of the banked theory is the
  generator of `Lost(W)`.
* **The deviation map**: two distinct `e`-close challenges are two independent lost directions at
  a window of size `≤ 2e`, so they *force* the residual state down to rank `≤ 2e`
  (`jointDefect_le_two_mul_of_two_close`).  The deviation map cannot take two independent values
  without a descent.
* **Rank2 / `E/C`**: `Lost(W)` is exactly the set of directions realised by a word of the
  extension `E = C + ⟨f₀,f₁⟩` supported in `W`, modulo the code
  (`mem_lostDirections_iff_sup_shortening`), and in dimensions
  (`finrank_lostDirections_add_finrank_shortening`)

  ```
  dim Lost(W) + dim Short(C,W) = dim Short(E,W) + dim Lost(∅),
  ```

  the exact sequence `0 → Short(C,W) → Short(E,W) → K_W → 0` read on `F² ≅ E/C`.  For a genuinely
  rank-two state (`Lost(∅) = ⊥`) this is `dim Lost(W) = dim Short(E,W) − dim Short(C,W)`, and
  since `dim Lost(W) ≤ 2` the extension hides at most two dimensions more than the code
  (`finrank_shortening_extension_le`).

## Terminal structure or canonical descent

`canonical_terminal_or_core` — **no hypotheses at all**:

> either the rank-minimal residual state is **unique** (a canonical normal form: the torsor of
> states has a distinguished point, and absorption has a genuine terminus), or the code contains
> a nonzero invisible core of weight `≤ 2·jointDefect`.

The second branch is a certificate: it forces `d ≤ 2·jointDefect`.  Hence
`exists_unique_minimal_state`: as soon as `2·jointDefect < d`, the terminal object exists and is
a point.  `descent_or_minimal` gives the step form (a state is rank-minimal or strictly
improvable) and `exists_core_of_stateRank_lt` shows every descent step subtracts a genuine
nonzero core, so the descent terminates in at most `stateRank` steps.
`canonical_state_and_badSet` puts the two sides together: under the invisible-core hypothesis and
`jointDefect ≤ e`, the instance has a unique canonical residual state *and* at most `e + 1` bad
challenges — structural terminality and numerical rigidity are the same phenomenon.

## What repeated absorption really decreases

Absorption *inside* a window changes nothing: it is a translation in a torsor, so no invariant
can decrease there — that is the content of the torsor theorem, and the reason the correct
invariant is the orbit, not the representative.  Between windows, the descent is by strict
decrease of the state rank, and the associated modules `Short(C, W)` form a descending
filtration under inclusion of windows (`shortening_mono`).  The terminal object is a point
exactly when the relevant shortening vanishes, i.e. exactly when `NoCore` holds
(`lowWeightCore_eq_bot_iff`).

## The smallest remaining obstruction

Everything above is unconditional, but the *quantitative* terminal branch needs the window to be
smaller than the minimum distance: `Short(C,W) = ⊥` is guaranteed only for `|W| < d`, and
uniqueness of the minimal state only for `2·jointDefect < d`.  The remaining gap is therefore a
single question about the code, not about the instance:

> for which windows `W` with `d ≤ |W|` is `Short(C,W) = ⊥` — equivalently, how large is the set
> of windows of size `≥ d` that hide no codeword?

Every statement above is uniform in that question: given the vanishing of the relevant
shortenings, the family is a point and the descent terminates; given a nonvanishing one, the
theory returns a genuine invisible core of weight `≤ |W|` together with the exact dimension of
the freedom it creates.  Closing the gap between `2·jointDefect` and `d` — the same gap recorded
by the earlier residual-absorption work — is exactly what a general terminal-or-descent theorem
without a distance hypothesis would require.

## Scope

No performance or implementation claim is made.  The witness section proves only what it states:
that the fixed-shadow regime is realisable, so the two jumps of the filtration can differ.
