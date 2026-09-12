# Johnson structural dichotomy — mission report

**FINAL STATUS: REDUCE.**  The Johnson-radius MCA theorem is now reduced to *exactly one*
explicitly named missing lemma, and every other ingredient is machine-checked and
unconditional.  New sorry-free Lean module:
`RequestProject/Root/CodingTheory/JohnsonStructuralDichotomy.lean` (builds; axioms
`propext`, `Classical.choice`, `Quot.sound` only; audited in `RequestProject/Main.lean`).

---

## MAIN THEOREM

Everything is stated for a line `f₀ + γ·f₁` over an evaluation domain `D`, `n = |D|`,
dimension `k`, radius `e`, `t = n − e`, with `badSet k e f₀ f₁` the set of *bad* challenges
(`γ` whose combination is close on some `S` with `|S| ≥ t` while the line is not commonly
close on that same `S`).

**Dichotomy (`johnson_escape_or_structure`, unconditional).**  For every line and every
threshold `c`, at least one of

* **ESCAPE** — the badness witnesses form a Johnson set family:
  `#Bad · (t² − n·c) ≤ n·t`.  At `c = k` this is informative precisely when `k·n < t²`,
  i.e. **exactly at the Johnson radius**;
* **STRUCTURE** — some codeword pair `(q₀,q₁)` has a common agreement set
  `T = {x : f₀ x = q₀ x ∧ f₁ x = q₁ x}` with `|T| ≥ c + 1`, *and* explains two distinct bad
  challenges.

The structure branch is cashed out by two further unconditional theorems:

* **`card_explainedSet_le`** — for *every* codeword pair,
  `#{γ explained by (q₀,q₁)} + |T| ≤ n`.  (The residual witness sets `S_γ \ T` are nonempty
  and pairwise disjoint inside `D \ T`.)
* **`unexplainedBadSet_eq_empty_of_large_pair`** — as soon as `|T| ≥ k + e`, *every* bad
  challenge is explained, so the previous item alone bounds the whole bad set by `n − |T|`.

Consequently (`card_badSet_le_of_gapBound`, `epsMCAmax_le_johnson_of_gapBound`):

```
#Bad ≤ max ( Bfar , n − (c+1) + Bgap )
```

where `Bfar` is the Johnson count of the escape branch and `Bgap` is the bound of the missing
lemma below.

## STAGE I STATUS — proved, in the following exact sense

The Stage-I classification asked for "either escape, or the whole interpolation module is
forced into a controlled common degeneracy".  The version that is now a theorem replaces the
GS interpolation module by the object the counting actually consumes: the *codeword pair*
`(q₀,q₁)` and its common agreement set.  `johnson_escape_or_structure` is unconditional, has
no budget hypotheses, no multiplicity schedule and no non-degeneracy assumption, and its
structure branch is genuinely usable — the pair it produces already explains two bad
challenges, and `card_explainedSet_le` charges every challenge it explains against `|T|`.

The link with the curve-line picture of `CurveLineDegeneracy.lean` is exact: a curve line is
the extreme case `|T| = n` of the structure branch.

## STAGE II STATUS — proved outside one window

* `|T| ≥ k + e`: proved, `#Bad ≤ n − |T| ≤ n − k − e` (`unexplainedBadSet_eq_empty_of_large_pair`
  + `card_explainedSet_le`).  This re-derives the near half of the near/far dichotomy from a
  different, purely disjointness-based argument.
* no pair with `|T| ≥ c + 1`: proved, the Johnson count `#Bad·(t² − n·c) ≤ n·t`.
* `c + 1 ≤ |T| < k + e`: **open** — this is the missing lemma.

## EXACT MISSING LEMMA

`GapBound k e c Bgap D` (a `def` in the new module, stated but not proved):

> for every line and every codeword pair whose common agreement set satisfies
> `c + 1 ≤ |T| < k + e`, the number of bad challenges **not explained** by that pair is at
> most `Bgap`.

Two unconditional theorems make this the *minimal* remaining statement:

* `card_inter_lt_of_not_explained` — an unexplained bad challenge has **every** one of its
  badness witness sets meeting `T` in fewer than `k` points.  So the missing lemma concerns
  only badness witnesses almost disjoint from a large common-agreement set.
* `exists_pair_explaining_of_isBad` + `card_badSet_le_of_explaining_family` — an equivalent
  covering formulation: every bad challenge *is* explained by some codeword pair with
  `|T| ≥ k` (interpolate `f₁` through `k` points of its witness set), and
  `#Bad ≤ Σ_P (n − |T_P|) ≤ (#pairs used)·(n − k)`.  So the Johnson-radius question is exactly
  **how many codeword pairs are needed to explain one line**.  At the prize schedule any
  bound `≤ 2³⁸` on that covering number suffices.

## JOHNSON THRESHOLD CONNECTION

The escape branch is informative iff `n·c < t²`; the near branch needs `|T| ≥ k + e`.  With
`c = k` the escape condition is *literally* `k·n < t²`, i.e. `t > √(kn)` — the Johnson
condition.  So the phase transition asked for is visible in the theorem itself: at `c = k`
the counting branch switches on exactly at `t² = kn`, and the residual window
`k < |T| < k + e` is non-empty exactly when `t² ≤ n(k + e − 1)`, which is precisely the
complement of the regime `(1−δ)² > ρ + δ` where the previously certified radius
`δ = (3 − √(5+4ρ))/2` lives.  The two known mechanisms of this repository (near/far and
pair covering) are the two endpoints of that window; nothing between them is elementary.

This is a *reformulation*, not a proof, of "Johnson radius is the threshold": the transition
that is proved is the transition of the counting branch, not the impossibility of degeneracy
above it.

## CERTIFIED RADIUS

**Unconditional: unchanged**, `δ = 0.177124…` at `ρ = 1/2` (`nearFar_rho_half`).  Nothing in
this session raises the unconditional radius, and no such claim is made.

**Conditional (on `GapBound`)**: `johnson_rho_half_delta_quarter` — at `|D| = 2²⁰`,
`k = 2¹⁹` (`ρ = 1/2`), `e = 262145`, i.e. **δ = 262145/2²⁰ = 0.2500009… > 1/4**, any
`Bgap ≤ 2³¹` gives `ε_mca ≤ 2⁻¹²⁸` for every field with `|F| ≥ 2¹⁶⁰` (the repository's own
hypothesis; a fortiori at the KoalaBear sextic field, `B_max = 2^57.93`).

**Unconditional at that schedule, escape branch only**: `escape_rho_half_delta_gt_quarter` —
a line with no codeword pair explaining two bad challenges on more than `2¹⁹` common
positions has at most **13** bad challenges.  Here `t² − n·k = 68717903873 > 0`, so the
Johnson-radius counting really is switched on at `δ > 1/4`.

## GAIN OVER 1/4

**Zero, unconditionally.**  The `δ > 1/4` statement is conditional on `GapBound`.  The
conditional gain over the frontier `δ = 1/4` at `ρ = 1/2` is the minimal one
(`+2⁻²⁰` in relative radius); the point of the schedule is to cross the frontier, not to
optimise past it.  Note that at `ρ = 1/2` the frontier `δ = 1/4` *is* the unique-decoding
radius `(1−ρ)/2`, so any `δ > 1/4` is genuinely beyond unique decoding: at `e = 262145` one
has `n − 2e = k − 2`, so two badness witnesses no longer meet in `k` positions — by two
positions.  Every elementary argument tried in this session fails exactly there.

## NOVELTY RISK

**High for the mathematics, low for the artefact.**  Correlated agreement for lines up to the
Johnson bound is a known target (Ben-Sasson–Carmon–Ishai–Kopparty–Saraf, *Proximity gaps for
Reed–Solomon codes*), and the counting ingredients used here (Johnson set-family bound,
two-witnesses-build-a-codeword-line, Lagrange interpolation through `k` points) are all
standard.  No novelty is claimed for the mechanisms.  What is new here is the packaging: the
unconditional escape/structure alternative with a *usable* structure branch, the
explained/unexplained accounting `#explained + |T| ≤ n`, and the reduction of the whole
Johnson-radius question to a single covering number.  Whether the missing lemma is already
implied by the literature was **not** verified; no priority claim is made either way.

## NEXT PROOF MOVE

Attack the missing lemma through the **key-equation / Hankel pencil** reformulation, which
this session identified as the most promising route and did not formalise:

for a `(k+1)`-subset `B ⊆ D` let `a_B`, `b_B` be the single RS parity checks of `f₀|B`,
`f₁|B`.  Then `γ` is bad **iff** there is a `t`-subset `A` with `a_B + γ·b_B = 0` for all
`B ⊆ A` and `b_B ≠ 0` for at least one such `B`.  Every bad challenge is therefore the root
of an explicit **degree-one** annihilator `a_B + Z·b_B`, and in syndrome form the condition
is that the Hankel matrix `H(S⁽⁰⁾ + Z·S⁽¹⁾)` of size `(n−k−e)×(e+1)`, whose entries are
*affine* in `Z`, drops rank at `Z = γ`.  Two consequences to pursue, in order:

1. if some `(e+1)`-minor of that pencil is not identically zero, then `#Bad ≤ e + 1`
   immediately (a polynomial of degree `≤ e+1` in `Z`);
2. otherwise the pencil has a kernel over `F(Z)`; a primitive kernel vector `G(X,Z)` of
   `X`-degree `≤ e` and `Z`-degree `≤ e` yields the annihilator family
   `{G(x, Z) : x ∈ D, G(x,·) ≢ 0}` and a bound `#Bad ≤ n·e + 1 ≈ 2³⁸` — comfortably inside
   the prize budget — **provided** one can show that the specialised kernel vector really is
   a valid error locator for each bad `γ`.  That last implication is where the multiplicity
   of the kernel (dimension `k + 2e + 1 − n`, equal to `3` at the schedule above) has to be
   controlled; past unique decoding the kernel is never trivial, so step 1 alone never fires.

The project's existing Welch–Berlekamp / Hankel / Padé modules
(`WelchBerlekampPencil.lean`, `Hankel*.lean`, `SyndromeSpace.lean`) are the natural place to
build this.
