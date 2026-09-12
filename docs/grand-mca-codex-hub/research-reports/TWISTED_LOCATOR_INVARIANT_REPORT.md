# Heavy-point twist and bounded multiplicative invariants of the locator

**Returned outcome: (2)** — a deployed theorem which converts *any* large fibre into an explicit
low-complexity locator structure, and, in the presence of that structure being algebraic, into
`#Γ ≤ B*`.  Outcomes (1), (3) are **not** claimed; a partial, exactly quantified form of (4) is
recorded in §6 (it kills the linear part of the twisted data, not every bounded-invariant
approach).

Frozen deployed parameters (unchanged):

```
p = 2130706433,  F = F_{p^6},  D = μ_{2^21},  n = 2097152,  k = 1048576,
e = 978944,      t = n − e = 1118208,        w = n − k − e = 69632,
B* = 274980728111395087  ( = |F| / 2^128 ),  d* = 128360144567623878 (old per-point budget).
```

New Lean modules (purely additive; nothing existing was modified):

* `RequestProject/Root/CodingTheory/TwistedLocatorInvariant.lean`
* `RequestProject/TwistedLocatorInvariantAxiomAudit.lean` — `#print axioms` for all 34
  load-bearing declarations.  No `sorry`, no `admit`, no `native_decide`, no new axiom.

`DECISIVE_REDUCTION` from `GRAND_MCA_ROOT_INCIDENCE_REPORT.md` is kept verbatim, and the exact
heavy-point fibre formulation `Γ_x = { γ : x ∈ official exact-e erasure witness of γ }` is kept as
the target of §5 there.  Nothing in this report presents "there exists a polynomial annihilator of
degree ≤ d*" as progress: every annihilator used below is built from a **bounded invariant given in
advance of the challenge set** (§4), and the fibre statements of §3 use no annihilator at all.

---

## 1. The exact transformed syndrome equations

Fix `x ∈ D` and split the official locator `Q_γ = (X − x)·R_γ`, `deg R_γ = e − 1`.
With the repository's syndrome coefficients `s_j(f) = gsynd f (X^j)` define the **twisted syndrome
direction**

```
s'_j(f, x) := s_{j+1}(f) − x·s_j(f)                 (`twistSyn`)
```

Then (`gsynd_X_sub_C_mul`, `gsynd_twisted_expansion`, `twisted_key_equations`):

```
gsynd f ((X − x)·R·X^d)  =  Σ_{m<N} R_m · s'_{m+d}(f, x)        (deg R < N)
```

and therefore, for every official bad challenge `γ` and every point `x` erased by it
(`official_twisted_key_equations`), the `w` official locator equations become **exactly**

```
Σ_{m < e} (R_γ)_m · ( s'_{m+d}(f₀,x) + γ · s'_{m+d}(f₁,x) )  =  0,      d = 0,…,w−1.
```

This is the precise bookkeeping of one fixed heavy point:

> **one fixed point removes exactly one unknown (`e+1 → e`) and gains no equation (`w → w`).**

## 2. The divisibility constraint

`qPoly_dvd_X_pow_sub_one`: on a domain inside `μ_n`, `Q_γ ∣ X^n − 1` (the roots are distinct
points of `D`, the factors are pairwise coprime).  `exists_cyclotomic_cofactor` produces the unique
`Ψ_x` with `(X − x)·Ψ_x = X^n − 1`, and `twisted_locator_dvd` gives the transformed constraint

```
R_γ ∣ (X^n − 1)/(X − x) = Ψ_x .
```

## 3. The bounded multiplicative invariant — the non-tautological quantitative lemma

`qPoly_eval_zero_pow_eq_one`: because `n = 2^21` is even and `D ⊆ μ_n`,

```
Q_γ(0) = (−1)^e ∏_{y ∈ E_γ} y  ∈  μ_n ,        i.e.  Q_γ(0)^n = 1 ,
```

for **every** challenge, with no hypothesis on `γ` (`deployedConstTerm_pow_eq_one`).  The invariant
therefore has an image of at most `n = 2097152` values.  This is the lemma that makes the
programme quantitative, and it is obtained *before* formalising any counting:

* `card_le_of_bounded_invariant` — an invariant with `≤ N` values and fibres of `≤ M` elements
  bounds the challenge set by `N·M`;
* `card_le_of_rootOfUnity_invariant`, `card_le_of_pair_rootOfUnity_invariant` — one and two
  `μ_n`-valued invariants: `#Γ ≤ n·M` and `#Γ ≤ n²·M`.

**Deployed consequences (all about `(badSet 1048576 978944 f₀ f₁).card`, the number of distinct
official bad challenges):**

* `deployed_badSet_le_of_constantTerm_multiplicity` — if the *locator constant term* determines the
  official bad challenge up to multiplicity `131121028953`, then `#Bad ≤ B*`.
* `deployed_badSet_le_of_two_rootOfUnity_invariants` — any **two** `μ_n`-valued invariants whose
  common fibres have `≤ 62523` elements give `#Bad ≤ B*`.
* `deployed_epsMCAmax_le_of_constantTerm_multiplicity` — the probabilistic form,
  `ε_mca ≤ B*/|F| = 2^{−128}`, through the repository's `deployed_security_iff`.
* `deployed_counterexample_constantTerm_concentration` — **unconditional**: if the deployed row
  were unsafe, then more than `131121028953` distinct official bad challenges would have to carry
  *one and the same* locator constant term, i.e. their erasure sets would all have the same
  product in `μ_n`.  This is the promised "every larger fibre has explicit low-complexity locator
  structure": the fibre is multiplicatively degenerate, not merely large.

**The exact invariant budget** (`invariant_budget_two_but_not_three`,
`deployed_constantTerm_multiplicity_threshold_sharp`):

```
n · 131121028953 ≤ B* < n · 131121028954 ,          n² · 62523 ≤ B* < n³ .
```

So at this row the budget is *exactly two* `μ_n`-valued invariants (with multiplicity slack
`62523`); three independent `μ_n`-valued invariants overshoot `B*` even with multiplicity one.

## 4. The algebraic form: the constant-term dichotomy

Suppose the invariant admits a bounded coprime rational presentation in the challenge,

```
Q_γ(0) · v(γ) = u(γ)   for all official bad γ,   IsCoprime u v,   deg u, deg v ≤ w = 69632,
```

(the natural budget: a Cramer-type selection from the `w`-row syndrome pencil has degree `≤ w`).
Then `u(γ)^n = v(γ)^n` on the bad set, and the annihilator is `u^n − v^n`, a polynomial built from
`(u,v)` **alone** — it does not mention the bad set, so it is not the tautological root polynomial.
`algebraic_invariant_dichotomy` / `deployed_constantTerm_dichotomy` give:

> either `u` and `v` are constants — every official bad challenge has the *same* locator constant
> term (the degenerate branch, and exactly the structure of the concentration theorem) —
> or `#Bad ≤ n · w = 146028888064`,

a factor above `1.8·10^6` below `B*` (`deployed_algebraic_constantTerm_margin`), and hence
`#Bad ≤ B*` (`deployed_badSet_le_of_algebraic_constantTerm`).

**Strength gained over `LocatorRootIncidence`.**  The earlier criterion needed, for *every* domain
point, a nonzero polynomial of degree `≤ d* = 1.2836·10^17` in `γ` cutting out membership in the
erasure set.  The present criterion needs **one scalar function** of `γ` — the locator constant
term — to be a bounded rational function of degree `≤ 69632`.  The multiplicative constraint
`Q_γ(0) ∈ μ_n` supplies the remaining factor `n` of degree for free.

## 5. Where this lands the heavy-point fibre programme

`Γ_x` is *not* bounded here, and `T*` of `GRAND_MCA_ROOT_INCIDENCE_REPORT.md` §5 stays open.  What
has changed is that the counting no longer has to go through the point-incidence at all: the
official challenge count is now controlled by a **single multiplicative functional of the whole
erasure set**, whose value space is `μ_n`.  Both remaining routes are explicit:

1. show that the constant term is an algebraic function of `γ` of degree `≤ 6.1·10^10` on the bad
   set (any degree up to `B*/n = 1.311·10^11` suffices), or
2. exhibit a second `μ_n`-valued invariant independent of the constant term with common fibres of
   at most `62523` challenges.

## 6. The exact obstruction that is proved (partial (4))

* `official_locator_eval_zero`: `Q_γ(0) = −x·R_γ(0)`.  The constant term of the twisted locator is
  determined by the constant term of the untwisted one and by the fixed point.  **The heavy-point
  twist produces no second independent multiplicative invariant of this kind**; route 2 above must
  use a genuinely different functional (e.g. a coset-product, whose value space must still be
  bounded by `n` to stay inside the budget of §3).
* `finrank_ker_ge_of_fewer_equations`, `deployed_twisted_system_underdetermined`: after the twist
  the official system is `w = 69632` equations in `e = 978944` unknowns, so its solution space has
  dimension `≥ 909312` (`deployed_twist_deficiency`).  Hence no determinantal/Cramer elimination
  from the twisted *linear* data alone can produce a nonzero annihilator, and rigidifying it by
  fixing more points needs `909312` of them, i.e. a search of size `n^909312 ≫ B*`
  (`deployed_target_lt_domain_pow_deficiency`).

This is an obstruction for the *linear* part of the heavy-point data only.  It is **not** a proof
that all bounded-invariant approaches fail: §3–§4 show precisely which multiplicative data still
closes the row, and §3's budget arithmetic shows exactly how much of it is allowed.

## Do-not-reopen compliance

Not used and not reopened: the tautological root polynomial of the challenge set (every polynomial
used is built from `(u,v)` or from `μ_n`-membership, both given independently of the bad set),
unconstrained kernels as a *bound source* (the kernel statement of §6 is used only negatively, to
kill the linear route), one-point descent, support counting, raw/support counting as a bound
source, generic Hankel-kernel dimension, DIM2/Hankel–Cramer, overlap-only globalization,
UniversalOrbit tuning, subgroup-tower and quotient-pair routes, generic post-Johnson constant
improvement, and the glue-pencil challenge-counting route (permanently closed; not touched).
