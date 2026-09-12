# The theory of residual absorption

**Status.** Everything stated below as a theorem is machine-checked and `sorry`-free.  Axiom
audit: `RequestProject/ResidualAbsorptionAxiomAudit.lean` (all declarations report only
`propext`, `Classical.choice`, `Quot.sound`).

New modules (nothing existing was modified or deleted):

* `RequestProject/Root/CodingTheory/ResidualAbsorption.lean` — the theory;
* `RequestProject/Root/CodingTheory/ResidualAbsorptionCost.lean` — the cost of an invisible core;
* `RequestProject/Root/CodingTheory/ResidualAbsorptionSequence.lean` — the exact sequence;
* `RequestProject/Root/CodingTheory/ResidualAbsorptionSharp.lean` — sharpness and the
  Reed–Solomon corollary.

Notation throughout: `ι` a finite position set, `A` an alphabet (an `F`-module),
`C ⊆ A^ι` an arbitrary **linear** code, `d` a lower bound for its minimum distance,
`e` the radius, `f₀, f₁` a received pair, `E = C + ⟨f₀,f₁⟩` the rank-two extension,
`goodZ` the set of `e`-close challenges, `badSet` the official MCA bad set.
Everything is stated at this level of generality; Reed–Solomon appears only in §6.

---

## 1. The central question, and the answer

> **What algebraic operation should "absorbing an invisible codeword/core" really mean, and
> what invariant must it reduce?**

**Answer.**  A received pair is only ever given *modulo the code*.  The genuine object is the
pair of cosets `(f₀ + C, f₁ + C)`, equivalently the rank-two extension `C ⊆ E` with its marked
identification `E/C ≅ F²`.  A **residual state** is a choice of representatives
`a = f₀ − q₀`, `b = f₁ − q₁` with `q₀,q₁ ∈ C`.  The states form a **torsor under `C × C`**, and

> **absorbing an invisible codeword = translating in that torsor,**

i.e. replacing `(a,b)` by `(a − u, b − v)` with `u,v ∈ C`.  The invariant it must reduce is the
**joint support**

```
rank(a,b)  =  |{ x : a x ≠ 0 ∨ b x ≠ 0 }|            (`jointSupport`)
```

and — this is what makes absorption a *theory* rather than bookkeeping — the operation is
**semantics-preserving**: it changes neither badness, nor its official window, nor the close
set, nor the invariant:

```
Absorption.agreeOn_residual_iff      Absorption.lineAgreeOn_residual_iff
Absorption.isBad_residual_iff        Absorption.badSet_residual_eq
Absorption.cosetWeight_residual_eq   Absorption.jointDefect_residual_eq
```

Because the invariant is a natural number, the descent is automatically well-founded; its
terminal value is the canonical invariant of the instance.

---

## 2. The canonical invariant

```
jointDefect C f₀ f₁  =  min { rank(f₀ − q₀, f₁ − q₁) : q₀, q₁ ∈ C }        (`jointDefect`)
```

* it is attained — a terminal state exists (`exists_minimal_state`);
* it is an invariant of the pair of cosets, i.e. of `E/C` (`jointDefect_residual_eq`);
* it dominates the pointwise invariant: `d(f₀+γf₁, C) ≤ jointDefect` for **every** `γ`
  (`cosetWeight_lineComb_le_jointDefect`) — the joint defect is the *generic* distance along the
  line, and the close challenges are exactly the points where that distance drops;
* it is computed by a unique-decoding criterion: a state of rank `r` with `2r < d` is already
  terminal, so `jointDefect = r` (`jointDefect_eq_of_two_mul_lt`).  This is the rank-two
  analogue of unique decoding and it makes the invariant effective;
* two bad challenges force `jointDefect ≤ 2e` (`jointDefect_le_two_mul_of_one_lt`) — the one
  strict descent step the theory provides for free;
* the canonical chain is therefore `(f₀,f₁) → (f₀ − q₀, f₁ − q₁)` with the terminal state, and
  it preserves the whole official datum (`exists_terminal_descent`).

The pointwise shadow of the same construction is the **coset weight** `cosetWeight C f = d(f,C)`,
the terminal invariant of absorption at a single challenge, with the same terminality criterion
`2·wt < d` (`cosetWeight_eq_of_two_mul_lt`) and the same torsor description of a step
(`absorbedCore_weight_le`: the absorbed core has weight at most the sum of the two
representative weights).

---

## 3. The strongest structural theorem

Write `r = jointDefect C f₀ f₁` and

```
NoCore C w  :=  ∀ c ∈ C, c ≠ 0 → w < wt c                                  (`NoCore`)
```

— "no **invisible core** of weight `w`".

> **Residual Absorption Theorem** (`card_badSet_le_succ_of_noCore`).
> If `NoCore C (r + e)` then
> ```
> #bad ≤ e + 1      and      #bad ≤ r .
> ```
> No hypothesis on the alphabet, the code, the rate or the radius.

> **Close-set form** (`card_goodZ_le_succ_of_noCore`).  Under the same hypothesis, either
> `r ≤ e` — the line has *correlated agreement at radius `e`*, so **every** challenge is close —
> or at most `e + 1` challenges are close at all.

> **Trichotomy** (`absorption_trichotomy`).  Unconditionally, for every line and radius:
> ```
> r ≤ e     ∨     #close ≤ e + 1     ∨     ∃ c ∈ C, c ≠ 0, wt c ≤ r + e .
> ```

> **Equality case** (`jointDefect_eq_succ_of_card_badSet_eq`).  If `1 ≤ e` and the maximum
> `#bad = e + 1` is attained under `NoCore C (r+e)`, then `r = e + 1` exactly: the terminal
> residual state has one position per bad challenge.

> **Converse** (`exists_core_of_card_badSet_gt`).  `#bad > e + 1` *certifies* an invisible core:
> a nonzero codeword of weight `≤ r + e`.

> **General unique-decoding corollary** (`card_badSet_le_succ_of_minDist`).  For an arbitrary
> linear code over an arbitrary alphabet, `3e < d ⟹ #bad ≤ e + 1`.

The last statement improves the previously available general bound
`Root.CodingTheory.Alphabet.card_badSet_le` (`3e < d ⟹ #bad ≤ |ι|`) to the sharp constant, and
it removes the Reed–Solomon structure and the hypothesis `1 ≤ k` from the anchor theorem
`Root.CodingTheory.card_badSet_le_succ_radius`.  It is a corollary of the absorption theorem
because `r ≤ 2e` and hence `r + e ≤ 3e < d`.

### The mechanism, in one paragraph

Fix the terminal state `(a,b)` and let `T` be its support, `|T| = r`.  At a close challenge the
line word `a + γb` has weight `≤ r`, while the coset leader has weight `≤ e`; their difference is
a codeword of weight `≤ r + e`, hence `0` under `NoCore` — *absorption at `γ` is already
complete* (`weight_le_of_closeTo`).  So each close challenge annihilates at least `r − e`
positions of `T`, and a position cannot annihilate two challenges (`challengeZeros_disjoint`).
The **drop divisor** of a state therefore has degree at most its rank
(`sum_card_challengeZeros_le` — no hypothesis at all), and `#close·(r−e) ≤ r`
(`card_mul_sub_le`) gives `e + 1`.  Officiality is used exactly once, to produce a *nonempty*
annihilated set for a bad challenge (`challengeZeros_nonempty_of_isBad`), which is what yields
the second bound `#bad ≤ r` and covers the degenerate branch `r ≤ e`.

---

## 4. The other branch: finite structural cost

When invisible cores exist, the failure of one state to serve all challenges is measured by a
single map, the **deviation map**

```
Φ(γ) = leader(f₀ + γ f₁) − (q₀ + γ q₁) ∈ C                                 (`deviation`)
```

— the codeword that must be absorbed at `γ`.  Absorbing it moves the state exactly onto the
leader (`lineComb_sub_deviation`), so the fibres of `Φ` are the clusters of challenges served by
one common absorbed state; each fibre is a pencil and has at most `e + 1` elements
(`card_fibre_le_succ`).  Hence

> **Cost bound** (`card_goodZ_le_succ_mul_card_image`, `absorption_dichotomy`).  Either `r ≤ e`,
> or
> ```
> #close ≤ (e + 1) · #image Φ ,
> ```
> and every element of `image Φ` is `0` or an invisible core of weight `≤ r + e`
> (`hammingWeight_deviation_le`).

With no core the image is `{0}` and the bound collapses to `e + 1`
(`card_goodZ_le_of_no_core`).  This is the disjunction the programme asked for:

```
InvisibleResidualStructure  ⟹  CanonicalStrictResidualDescent  ∨  FiniteStructuralCost ,
```

with the *same* invariant `r` controlling both branches and the *same* object — the invisible
core — separating them.

---

## 5. The exact sequence: shortening, kernel shadow, rank-two extension

Let `P_Z` be the space of words supported in a window `Z` and `Short(M,Z) = M ⊓ P_Z`.  Then
`E ⊓ (C ⊔ P_Z)` is the preimage in `E` of the kernel shadow `K_Z ⊆ E/C` — the directions lost by
deleting `Z` — and the modular law for `C ≤ E` gives

```
E ⊓ (C ⊔ P_Z)  =  C ⊔ Short(E,Z)                        (`extension_inf_sup_eq`)
```

hence the rank form of the short exact sequence `0 → Short(C,Z) → Short(E,Z) → K_Z → 0`:

```
dim (E ⊓ (C ⊔ P_Z)) + dim Short(C,Z) = dim Short(E,Z) + dim C      (`finrank_kernelShadow`)
```

and, with no invisible core at `Z`, `dim K_Z = dim Short(E,Z)`
(`finrank_kernelShadow_of_noCore`).  Two identifications complete the picture:

* `NoCore C w ↔ ∀ Z, |Z| ≤ w → Short(C,Z) = ⊥` (`noCore_iff_shortening_eq_bot`) — the intrinsic
  hypothesis of the theory *is* the vanishing of all small shortenings, for an arbitrary linear
  code (previously available only through the Reed–Solomon dimension count);
* `d(f,C) ≤ w ↔ ∃ Z, |Z| ≤ w, f ∈ C ⊔ P_Z` (`cosetWeight_le_iff_exists_window`,
  `mem_goodZ_iff_exists_window`) — closeness is a statement about the filtration of the ambient
  space by the spaces `C ⊔ P_Z`, not about windows chosen by hand.

So *shortening*, *kernel shadow* and *rank-two extension* are three terms of one sequence, and
the ambiguity in lifting a lost direction to a genuinely small-support word is exactly the
shortened code — which is precisely the invisible core that absorption has to remove.

---

## 6. Sharpness: the minimal obstruction

The hypothesis is exactly right at the boundary.  The banked hole witness
(`UniqueDecodingHoleWitness.lean`: `F₁₃`, `D = {0,…,7}`, `k = 3`, `e = 2`, so
`3e = 6 = |D| − k + 1 = d`) has four bad challenges, so

* `3e ≤ d` does **not** suffice: `not_forall_card_badSet_le_succ_of_three_mul_le`;
* read through the theory, the witness must have a large residual state and carry a core, and it
  does: `3 ≤ jointDefect ≤ 4` (`three_le_jointDefect_hole`, `jointDefect_hole_le`) and
  `∃ c ≠ 0 ∈ C, wt c ≤ jointDefect + 2` (`exists_core_hole`).

Specialising the general theorem along `Root.CodingTheory.badSet_eq` recovers the sharp
Reed–Solomon bound `#bad ≤ e + 1` for `3e < |D| − k + 1` (`card_badSet_rs_le_succ`) by a route
that mentions neither evaluation, nor windows, nor interpolation.

**The minimal obstruction to a general Grand MCA corollary** is therefore now a single, purely
code-theoretic statement:

> the descent stops exactly when `C` acquires a nonzero codeword of weight `≤ jointDefect + e`,
> and — since `jointDefect ≤ 2e` is *attained* — exactly at `d ≤ 3e`.

Two ways forward, both now expressible in objects that exist:

1. **Improve the descent below `2e`.**  The bound `jointDefect ≤ 2e` uses only two challenges.
   Any bound `jointDefect ≤ 2e − f(#bad)` moves the threshold `3e < d` towards `2e < d`.  The
   hole witness shows the target cannot be `2e < d` itself with the constant `e + 1`, so the
   correct statement in the gap `2e ≤ d ≤ 3e` must be a *larger* constant or a *structured*
   conclusion; the cost bound of §4 is currently the only general statement there.
2. **Bound `#image Φ`.**  By §4 this is the *only* remaining quantity: `#close ≤ (e+1)·#image Φ`
   is unconditional beyond the degenerate branch, and the image consists of invisible cores.  A
   bound on the number of distinct absorbed cores of weight `≤ r + e` is equivalent to a bound
   on the bad set.

---

## 7. Relation to the banked objects

* **Rank-two extension `E/C`** — now the primary object: every statement of the theory is proved
  invariant under change of representative, so it is literally a statement about `E/C`.
* **Restriction-rank kernels / kernel shadows** — the middle term of §5; the rank loss at `Z` is
  `dim Short(E,Z) − dim Short(C,Z)`.
* **Deviation codewords** — the image of `Φ`; §4 shows they are the *only* obstruction and that
  each carries at most `e + 1` challenges.
* **Fixed-shadow pencils** — the fibres of `Φ`: a fixed absorbed core is a fixed state, and a
  state is a pencil, whence the constant `e + 1`.
* **Residual RS states / joint defect** — the Reed–Solomon instance of §2; the present
  `jointDefect` agrees with it in spirit and is defined for an arbitrary linear code, with the
  new terminality criterion `2r < d` and the new invariance statements.
* **Polynomial shortening and locator structure** — replaced by `noCore_iff_shortening_eq_bot`:
  the shortening criterion is no longer a Reed–Solomon dimension count but the definition of the
  invariant.
* **HigherDD / syndrome maps** — not needed for any statement here; the theory is stated in the
  quotient/representative language and uses no basis.

## 8. Honest scope

All results are upper bounds on the number of bad or close challenges, plus one sharpness
statement at `3e = d` obtained from a banked witness.  Nothing here claims a bound in the range
`2e ≤ d ≤ 3e` better than the cost bound of §4, nothing is claimed about attainment beyond the
recorded equality case, and no performance or implementation claim is made.
