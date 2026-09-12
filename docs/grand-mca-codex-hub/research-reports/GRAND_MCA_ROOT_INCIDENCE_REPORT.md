# Grand MCA — root incidence of the official erasure selection

**STATUS: `DECISIVE_REDUCTION`.**

`GRAND_MCA_SAFE` is **not** claimed, `GRAND_MCA_UNSAFE` is **not** claimed, and no unconditional
numerical bound on `#Γ` is claimed. What is delivered is one new mechanism with a sharp deployed
numerical target, plus an unconditional structural constraint on any deployed counterexample.

Frozen deployed parameters (unchanged):

```
p = 2130706433,  F = F_{p^6},  D = μ_{2^21},  n = 2097152,  k = 1048576,
e = 978944,      t = n − e = 1118208,        w = n − k − e = 69632,
B* = 274980728111395087  ( = |F| / 2^128 ).
```

New Lean modules (purely additive; nothing existing was modified):

* `RequestProject/Root/CodingTheory/LocatorRootIncidence.lean`
* `RequestProject/LocatorRootIncidenceAxiomAudit.lean` — `#print axioms` for all 21 load-bearing
  declarations; every one prints `[propext, Classical.choice, Quot.sound]`. No `sorry`, no
  `admit`, no `native_decide`, no new axiom.

---

## 1. `STATUS`

`DECISIVE_REDUCTION`: one sharply stated remaining theorem, with an explicit numerical target,
whose proof finishes the deployed row.

## 2. Strongest new theorem

**Root incidence of the official erasure selection.**
Let `Γ` be a finite set of scalars (the *distinct* challenges, never supports, locators or
witnesses), let each `γ ∈ Γ` own an erasure set `E γ` of size `≥ e` inside the domain, and suppose
that for every domain point `x` outside an exceptional finset `Z` there is a **nonzero** polynomial
`g x` of degree `≤ d` **in the challenge variable** which vanishes at every `γ ∈ Γ` whose erasure
set contains `x`. Then

```
#Γ · (e − |Z|)  ≤  n · d.                     (card_mul_le_of_rootFamily)
```

Two specialisations are proved:

* `d = 1`, `g x = P(x) + γ·R(x)`: if the official locators `Q_γ = ∏_{x ∈ E γ}(X − x)` lie on one
  affine line `P + γ·R` of the locator space, then `#Γ · (e − |Z_R|) ≤ n`
  (`card_mul_le_of_affine_locator_family`);
* the degenerate case `g x = 1`-free: if no domain point is erased by more than `d` challenges then
  `#Γ · e ≤ n · d` (`card_mul_le_of_multiplicity`).

The mechanism is genuinely *nonlinear in the locator*: it uses that a domain point is a **root** of
the split locator, and that root membership is a polynomial condition on `γ`. It is therefore not
blocked by `SplitLocatorChallengeCount.linear_functional_vanishing_on_splitLocators` (split
locators span the whole locator space, so no linear shadow of splitness can see anything), and not
by the kernel-dimension obstruction of `GlobalChallengeAnnihilator`
(`dim ker(A + γB) ≥ e + 1 − w = 909313` for every `γ`), which concerns the *linear* relaxation.

The official bridge is the repository's maximal-erasure normalisation: the canonical selection
`erasureSel` gives, for every official bad challenge, an official witness window of co-size exactly
`e` (`erasureSel_spec`), so every statement above applies to `badSet 1048576 978944 f₀ f₁` itself
(`card_badSet_mul_le_of_multiplicity`, `card_badSet_mul_le_of_rootFamily`).

## 3. Exact consequence for distinct `γ`

All conclusions bound `(badSet 1048576 978944 f₀ f₁).card`, i.e. the number of **distinct official
finite challenges**, for the official `IsBad` predicate of `MCA.lean` with its same-window
non-containment semantics (`IsCloseOn` on `S`, `¬ LineCloseOn` on the *same* `S`). No support,
locator, witness or multiplicity count is substituted for it.

* `deployed_badSet_le_of_official_multiplicity` — if in the canonical official selection every
  single domain point is erased by at most `128360144567623878` bad challenges, then
  `#Bad ≤ B*`.
* `deployed_badSet_le_of_official_rootFamily` — if for every domain point the challenges erasing it
  are roots of one nonzero polynomial of degree `≤ 128360144567623878`, then `#Bad ≤ B*`.
* `deployed_badSet_le_two_of_official_affine_locators` — if the official locators lie on one affine
  line whose exceptional locus meets `D` in at most `279893` points, then `#Bad ≤ 2`.
* `deployed_badSet_le_of_affine_locator_family` — in the general affine case, `#Bad ≤ 2097152`.
* `deployed_epsMCAmax_le_of_official_multiplicity` — the probabilistic form,
  `ε_mca ≤ B*/|F| = 2^{−128}`, through the repository's `deployed_security_iff`.
* `deployed_counterexample_concentration` — **unconditional**: if the deployed row were unsafe,
  a *single* domain point would have to be erased by more than `128360144567623878` of the bad
  challenges. Every official counterexample is forced to be this concentrated.

## 4. Deployed numerical consequences

* The multiplicity threshold is exact and sharp: `n · 128360144567623878 ≤ B* · e`, and the
  inequality fails at `128360144567623879` (`deployed_multiplicity_threshold_sharp`). So the
  criterion is `d ≤ ⌊B*·e/n⌋ = 128360144567623878 ≈ 1.2836 · 10^17`.
* The degree budget in the algebraic criterion is the same `1.2836 · 10^17`. For comparison, a
  Cramer-type (determinantal) selection from the `w`-row syndrome pencil would have degree
  `≤ w = 69632`, i.e. a factor `1.8 · 10^12` *below* what the criterion needs. Any algebraic
  selection of the official locators, of any degree up to `1.2836 · 10^17`, finishes the deployed
  row.
* The affine case is a factor `> 1.3 · 10^11` below `B*` (`deployed_affine_margin`).
* Arithmetic of the competing one-point descent (`x` erased ⇒ badness for `(D∖{x}, k, e−1)`, same
  `w`): the agreement `t = 1118208` is invariant under shortening and `t² = k · 1192464` exactly,
  so the shortened instance only enters the Johnson regime `t² > k·n'` at `n' ≤ 1192463`
  (`johnson_threshold_after_shortening`), i.e. after `904689` steps
  (`johnson_shortening_steps`), each of which can cost a factor `n_i/e_i > 2`; the accumulated
  `2^904689` dwarfs `B*` (`target_lt_two_pow_shortening_steps`). The descent-to-Johnson route is
  therefore quantitatively hopeless at this row, and the root-incidence criterion is not a
  disguised descent: it asks for *algebraicity in the challenge*, not for a smaller instance.

## 5. The single next theorem to attack

> **T\*.** For the deployed row and every official pair `(f₀,f₁)`: for each `x ∈ D` the set
> `Γ_x = { γ : x lies in some official exact-`e` erasure witness of γ }` is contained in the zero
> set of a nonzero polynomial in `γ` of degree at most `128360144567623878`
> (equivalently: `#Γ_x ≤ 128360144567623878`).

`T*` implies `#Γ ≤ B*` and `ε_mca ≤ 2^{−128}` at the deployed row, by
`deployed_badSet_le_of_official_rootFamily` / `deployed_badSet_le_of_official_multiplicity`, both
already proved. The natural attack is to produce the annihilating polynomial from the syndrome
pencil **together with** the divisibility `Q_γ | X^n − 1`: by the recorded obstruction, the linear
relaxation alone yields the zero eliminant, so the polynomial must use at least one genuinely
nonlinear consequence of splitness — the smallest candidate being the multiplicative constraint
`Q_γ(0) ∈ μ_n` (valid because `n` is even and all roots lie in `μ_n`) combined with the pencil
equation at the single point `x`.

## Do-not-reopen compliance

Not used and not reopened: raw/support counting as a *bound source* (the incidence count is used
only to *state* the reduction target, and the descent arithmetic is used only to kill a competing
route), generic Hankel-kernel dimension, DIM2/Hankel–Cramer, overlap-only globalization,
UniversalOrbit tuning, subgroup-tower and quotient-pair routes, generic post-Johnson constant
improvement, and the glue-pencil challenge-counting route (permanently closed; not touched).
