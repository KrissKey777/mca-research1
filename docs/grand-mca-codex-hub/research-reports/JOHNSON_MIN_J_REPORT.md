# JOHNSON BOTTLENECK MINING — the weakest property below (ND∃)

Scope: the Guruswami–Sudan Johnson chain in `RequestProject/Root/CodingTheory/`.
No work outside it.  Everything asserted as *proved* below is a `sorry`-free Lean
declaration whose only axioms are `propext`, `Classical.choice`, `Quot.sound`.
Everything asserted as *computed* is an exact (integer / rational) computation by a
committed script; nothing here rests on floating point, sampling, or heuristics.

New Lean: `RequestProject/Root/CodingTheory/CurveLineDegeneracy.lean` (builds).
New exact computations: `analysis/min_j_budget.py`, `analysis/min_j_adversarial.py`,
`analysis/min_j_debug.py`.

---

## GATE 1 — proof-dependency extraction

Backwards trace from the final conditional `ε_MCA` theorem.  Chain, in order:

```
epsMCAmax_le_of_schedule_separable            (NDExistsReduction.lean)
threshold_rho_half_bchks_separable
threshold_rho_quarter_bchks_separable
  ↓
epsMCAmax_le_disc_of_bad_flex                 (DiscriminantMCA.lean)
  ↓
epsMCA_le_disc
  ↓
card_badSet_le_disc
  ↓
card_badSet_le_natDegree_discLine
  ↓
eval_discLine_eq_zero_of_isBad                ← FIRST DOWNSTREAM CONSUMER
  ↓
eval_discLine_eq_zero_of_agreement
  ↓
GS.sq_dvd_of_agreement  +  discRes_eq_zero_of_sq_dvd
```

### Use-by-use table

**(1) full Y-degree `deg_Y Q = bY`**

- ASSUMPTION: `Q.natDegree = bY` (an exact equality, not a bound).
- EXACT CONSEQUENCE: the line discriminant `discLine b x₀ Q` is a *specified* polynomial
  in `Z` of degree `≤ (2bY − 1)·dZ`, and its non-vanishing is equivalent to separability
  of the Y-degree-`bY` specialisation.
- DOWNSTREAM CONSUMER: `epsMCAmax_le_disc_of_bad_flex` only.
- CAN WEAKEN: **YES — already weakened.**  `epsMCAmax_le_disc_of_bad_flex` takes the
  degree as a *flexible* parameter `b` and quantifies over evaluation points; the
  evaluation point `x₀` is supplied by `exists_eval_C_ne_zero`.  Full Y-degree is *not*
  load-bearing.

**(2) discriminant non-vanishing `discLine b x₀ Q ≠ 0`**

- ASSUMPTION: one nonzero polynomial in `F[Z]`.
- EXACT CONSEQUENCE: `#{γ : discLine.eval γ = 0} ≤ natDegree discLine ≤ (2b − 1)·dZ`.
- DOWNSTREAM CONSUMER: `card_badSet_le_natDegree_discLine` — the *only* counting step in
  the whole chain.
- CAN WEAKEN: **YES, but only in one direction** (see GATE 2, P7/family): the counting
  step needs nothing about `Q` except *some* nonzero annihilator of the bad set.  It does
  not need it to be a discriminant.

**(3) squarefreeness / `SeparableInY Q` / `gcd(Q, ∂_Y Q) = 1` / root distinctness**

- ASSUMPTION: `SeparableInY Q` (equivalently: no square factor of positive Y-degree over
  the relevant fraction field).
- EXACT CONSEQUENCE: exactly and only `discLine b x₀ Q ≠ 0`, via
  `discRes_eq_zero_of_sq_dvd` contraposed.
- DOWNSTREAM CONSUMER: (2).
- CAN WEAKEN: **YES in principle, NO within the present chain** — see the central finding.

### CENTRAL GATE-1 FINDING (the actual bottleneck)

`eval_discLine_eq_zero_of_isBad` opens the badness hypothesis as

```lean
obtain ⟨S, hScard, ⟨p, hpdeg, hpS⟩, -⟩ := hz
```

The final `-` **discards the `¬ LineCloseOn` conjunct of `IsBad`.**  Consequently the
lemma — and therefore everything above it — does not in fact bound the *bad* set: it
bounds the strictly larger **close** set

```
Close := { γ : the point f₀ + γ f₁ of the line agrees with a codeword on ≥ k + e points }.
```

This is the whole bottleneck, and it is a *logical*, not an algebraic, one:

> **Any property MIN-J of `Q` that leaves `eval_discLine_eq_zero_of_isBad` unchanged is
> false.**  For the spike lines of `SpikeLineCounterexample.lean`, `#Close = |F|`, so no
> annihilator of `Close` of degree `< |F|` exists at all, whatever `Q` is.

So the minimal dependency graph collapses to a single edge:

```
[ some nonzero w ∈ F[Z] vanishing on Bad, deg w ≤ B ]  ⟹  #Bad ≤ B  ⟹  ε_MCA ≤ B/|F|
```

and every algebraic hypothesis above it (full Y-degree, discriminant, squarefreeness,
gcd, root distinctness) exists purely to *manufacture* that one `w` — and manufactures
one that annihilates `Close`, which is too much to ask.

**Answer to the primary question: ND∃ is strictly stronger than what the chain consumes.**
The chain consumes only `discLine b x₀ Q ≠ 0` for *one* free evaluation point.  But this
is not the good news it looks like, because of the `Close` vs `Bad` gap.

---

## GATE 2 — strictly weaker properties P1–P7

Verdicts, against the *existing* chain (i.e. with `eval_discLine_eq_zero_of_isBad`
unchanged):

| | property | verdict |
|---|---|---|
| P1 | `deg_Y Q = bY` | **not needed at all** — already removed by `epsMCAmax_le_disc_of_bad_flex`; sufficient to have `natDegree Q ≤ bY` and a free evaluation point. |
| P2 | `deg_Y(Q / gcd(Q, ∂_Y Q)) ≥ r` | insufficient for *every* `r`. The separable part yields an annihilator only of the **close** set, and `#Close = |F|` on spike lines. No `r < ∞` helps. |
| P3 | `deg gcd(Q, ∂_Y Q) ≤ s` | same, for every `s ≥ 0`; `s = 0` is squarefreeness, already refuted. |
| P4 | `≥ r` distinct Y-roots/factors | same. |
| P5 | one separable factor of degree `≥ r` | same; and refuted directly by `GCD-SEP∃`'s refutation. |
| P6 | bounded repeated-factor multiplicity | **the only survivor in spirit** — but it must be paired with a *new* counting step that consumes `¬ LineCloseOn`. See MIN-J below. |
| P7 | nonzero (sub)resultant instead of full discriminant | a genuine weakening of the *algebra* (degree cost `(2bY−1)dZ` unchanged), but it still produces a single annihilator of `Close`, so it does not repair the chain by itself. |

**Minimum `r` / maximum `s` for the existing budget: none exists.**  Within the
single-annihilator paradigm the required `r`/`s` are not finite, because the failure is
not one of degree but of the set being annihilated.

### The repair, and what it costs

Replace the single annihilator by a **family**, one per evaluation point:

```
G := gcd(Q, ∂_Y Q)  (primitive in F[Z][X][Y]),
w_x(Z) := G(Z, x, f₀(x) + Z·f₁(x))     for x ∈ D,        deg w_x ≤ dZ + bY,
```

plus the subresultant (gcd-degree-jump) term of degree `≤ (2bY − 1)·dZ` and the two
leading-coefficient terms of degree `≤ dZ` each.  `¬ LineCloseOn` enters exactly here:
a bad `γ` is close on `S` but the line is not uniformly close, so either the separable
part of `Q` sees `γ` (subresultant term) or the *repeated* part `G` vanishes along the
whole of `S` — and the latter is what `¬ LineCloseOn` must forbid.

The counting step of that repair is formalised and unconditional:

* `card_badSet_le_of_annihilator_family` — `#Bad ≤ N·d` from `N` nonzero annihilators of
  degree `≤ d` covering the bad set;
* `epsMCA_le_of_annihilator_family` — the corresponding `ε_mca ≤ N·d / |F|`.

---

## GATE 3 — prize budget (exact, `analysis/min_j_budget.py`)

Largest `B` with `B/|F| ≤ 2^-128`:

| field | `log₂|F|` | `B_max` |
|---|---|---|
| `|F| ≥ 2^160` (repository certificate statements) | 160 | `2^32` |
| KoalaBear sextic extension (actual challenge field) | 185.9321 | **`2^57.9321`** |

What the chain spends, and what the repair would spend:

| schedule | single annihilator `(2bY−1)dZ` | family of `n` `n(dZ+bY)+(2bY−1)dZ+2dZ` |
|---|---|---|
| `ρ = 1/2` (`n=2^20, k=524288, e=306096, m=866, L=642769488, bY=1225, dZ=1318349`) | `3 228 636 701 = 2^31.5883` | `1 386 904 900 023 = 2^40.3350` |
| `ρ = 1/4` (`n=2^20, k=262144, e=523263, m=768, L=403177215, bY=1537, dZ=1182344`) | `3 633 343 112 = 2^31.7587` | `1 245 024 911 256 = 2^40.1793` |

So the repair needs `|F| ≥ 2^168.34` (`ρ=1/2`) resp. `2^168.18` (`ρ=1/4`) for `2^-128`;
at KoalaBear⁶ it gives `ε_mca ≤ 2^-145.60` resp. `2^-145.75`.

**Conclusion: the factor-`|D|` loss of the family repair is entirely affordable at the
real field, but NOT at the `|F| ≥ 2^160` hypothesis the repository's current statements
carry.**  The slack is ~`2^17.6` bits at KoalaBear⁶ and *negative* at `2^160`.  That is
the exact answer to "how much degeneracy can we tolerate": we may pay a factor `|D| = 2^20`
in the bad-set bound and stay under budget at the real field.

---

## GATE 4 — adversarial falsification (exact, no sampling)

### MIN-J, version 1

> **MIN-J v1.** For some admissible interpolant `Q`, the repeated part
> `G = gcd(Q, ∂_Y Q)` does not vanish identically along a whole witness set: there is no
> `S ⊆ D`, `|S| ≥ k + e`, with `G(Z, x, f₀(x)+Z f₁(x)) ≡ 0` for all `x ∈ S`.

This is exactly the property the family repair consumes, and it is genuinely weaker than
squarefreeness (it tolerates arbitrarily large repeated parts, as long as their zero set
misses one point of every witness set).

**MIN-J v1 survives the spike lines** — the family that killed `ND∃`, `SF∃`, `CO∃` and
`GCD-SEP∃`.  Exact instance `q=7, n=5, k=1, e=2, m=2, L=5, dZ=12`, whole interpolation
space enumerated: `G = Y − p`, its zero set is `D ∖ {spike}`, which misses the spike point
of the unique witness set, and `Bad = {1}`.

**MIN-J v1 is nevertheless FALSE**, by a new family.

### The curve lines (new counterexample family)

Take `a, b ∈ F[X]` with `deg a < k ≤ deg b = K`, and

```
f₀ = a|_D ,      f₁ = b|_D .
```

The formal line `f₀ + Z f₁` then *lies on the curve* `a + Z·b` at **every** point of `D`.
Running the GS double-root lemma over `F[Z]` with weight `K + 1` instead of `k` — legal by
`wdegLt_weight_le`, at the budget price `(K+1−k)·bY` — forces

```
(Y − (a + Z·b))² ∣ Q      for EVERY admissible Q      (curveLine_sq_dvd, Lean)
```

whenever `L + (K+1−k)bY ≤ m|D|` and `L + (K+1−k)bY − (K+1) ≤ (m−1)|D|`.  Hence
`¬ SeparableInY Q` for every admissible `Q` (`curveLine_not_separableInY`), and the zero
set of the repeated part is **all of `D`** — so MIN-J v1 fails maximally.

**SMALLEST ADVERSARIAL TEST / COUNTEREXAMPLE (exact, entire interpolation space):**

```
F = GF(5),  D = {0,1,2,3},  k = 1,  e = 2,  m = 2,  L = 4,  dZ = 10
f₀ = (0,0,0,0),   f₁ = (0,1,2,3)        (a = 0, b = X)
dim of interpolation space = 27,   G = Y − Z·X for every Q,   Bad = {0}.
```

Confirmed at `(q,n,k,K,e) = (5,4,1,1,2)`, `(7,5,1,1,3)`, `(7,6,2,2,3)`; `#Bad = 1` in every
case.  An exhaustive line sweep at `q=5,n=4,k=1,e=2,m=2,L=4,dZ=10` over all 1024 orbits
found 990 with empty interpolation space and exactly 2 nondegenerate ones, both of them
curve lines.

**SCALABLE: YES.**  The two forcing budgets `L + (K+1−k)bY ≤ m·n` and
`L + (K+1−k)bY − (K+1) ≤ (m−1)·n` hold with `K = k` at *both* prize schedules; the Lean
instantiations `dichFar_fails_rho_half` and `dichFar_fails_rho_quarter` verify the
arithmetic at `|D| = 2^20`.

### Two consequences

**(a) (DICH) is dead, not merely unproven.**  The proposed dichotomy was: a line is either
*near* the codeword-line variety (small bad set directly) or *far* (some separable
interpolant).  Curve lines with `k ≤ K < k + e` are **as far as a line can be** — any pair
of codewords agrees with them on at most `K` positions
(`curveLine_card_polyAgreement_le`) — and yet admit **no** separable interpolant, while
having a nonempty bad set.  `dichFar_fails` (Lean) states exactly this.

**(b) Degeneracy and harmlessness are the same inequality.**  Curve lines are harmless:

* `curveLine_card_badSet_le_one` (Lean, unconditional, no interpolation, no schedule):
  if `K + e < |D|` and `k ≤ K + 1` then `#Bad ≤ 1`.
  Proof: a bad `γ` forces `a + γb` to agree with a codeword on `> K` points, hence to *be*
  it, i.e. `deg(a + γb) < k`; two such `γ` would make both `a` and `b` codewords and the
  line uniformly close, contradicting `¬ LineCloseOn`.

Let `K*` be the largest degree at which a curve forces total degeneracy,

```
K* = max { K : L + (K+1−k)bY ≤ m|D|  and  L + (K+1−k)bY − (K+1) ≤ (m−1)|D| }
   ≈ k + k·e/t ,        t = |D| − e .
```

Then, exactly,

```
K* < t   ⟺   k·|D| < t²   ⟺   t > √(k·|D|)   ⟺   the radius is inside the Johnson bound
```

(arithmetic half formalised as `degeneracy_threshold_lt_witness_size`).  Numerically:
`K* = 740604 < t = 742480` at `ρ=1/2`, `K* = 523433 < t = 525313` at `ρ=1/4`.

So **inside the Johnson regime, every line that forces the whole interpolation space to
degenerate has at most one bad challenge.**  The mechanism that kills the discriminant
route is the very mechanism that makes the killed lines harmless.

---

## GATE 5 — generic pencil

Not applicable in the intended form.  MIN-J v1 did not survive, and the obstruction found
is **not** a proper subvariety of a pencil: for a curve line, `(Y − (a+Zb))² ∣ Q` holds for
*every* point of the interpolation space, so for `Q_λ = Q₀ + λQ₁` the obstruction
polynomial satisfies

```
R_x(λ) ≡ 0        identically in λ.
```

There is no generic-position escape.  This is a structural, whole-space degeneracy, and it
is exactly why "pick a better interpolant" cannot rescue the single-annihilator paradigm.

---

## GATE 6 — GS ↔ module bridge

Not built, and deliberately so: the policy is "no abstract framework from analogy", and
Gate 5 exposed a whole-space obstruction rather than a rank/gcd obstruction that a bridge
could resolve.  The one place a subresultant identity is still wanted is the *separable*
term of the family repair (P7); it is recorded as the next test, not as a result.

---

## GATE 7 — frontier test

Exact (`analysis/min_j_budget.py`):

| | certified today | Johnson target | Δδ | crosses `1/4`? | 128-query gain |
|---|---|---|---|---|---|
| `ρ = 1/2` | `δ = 0.177124` | `δ = 0.291916` | **`+0.114792`** | **YES** | **`+27.745` bits** |
| `ρ = 1/4` | `δ = 0.287258` | `δ = 0.499022` | **`+0.211764`** | **YES** | **`+65.105` bits** |

Ultimate Johnson radius at `ρ=1/2`: `1 − 1/√2 = 0.292893`.  A surviving Johnson theorem
therefore does clear the `δ > 1/4` frontier at `ρ = 1/2`.  No FREEZE.

---

## DICH POLICY

Trigger 1 fired: MIN-J v1 is **scalably false**.  But the same computation *kills* (DICH)
outright (`dichFar_fails`), so the fallback route is closed rather than opened.  No DICH
work was done and none should be.

---

## REQUIRED OUTPUT

**ND∃ NECESSARY:** **NO.**  The chain consumes only `discLine b x₀ Q ≠ 0` at one free
evaluation point (not full Y-degree, not gcd `= 1`, not root distinctness).  But this is a
negative result twice over: every weakening *within the single-annihilator paradigm* is
equally false, because the consuming lemma discards `¬ LineCloseOn` and hence bounds
`Close`, not `Bad`, and `#Close = |F|` on spike lines.

**MIN-J:** *(v1, the property actually consumed by the family repair)* — for some
admissible interpolant `Q`, the repeated part `G = gcd(Q, ∂_Y Q)` does not vanish
identically along a whole witness set.  *(v3, the surviving refinement)* — additionally,
the X-degree of any repeated root of `Q` along the line exceeds `K*`; equivalently the
line is not a curve line of degree `≤ K*`.

**EXACT DOWNSTREAM USE:** `discLine b x₀ Q ≠ 0` in `card_badSet_le_natDegree_discLine`,
reached through `eval_discLine_eq_zero_of_isBad`, which destructures `IsBad` and discards
the `¬ LineCloseOn` conjunct.

**MAXIMUM TOLERABLE DEGENERACY:** a factor `|D| = 2^20` in the bad-set bound (family of
one annihilator per evaluation point), i.e. repeated parts of arbitrary degree `≤ bY` are
tolerable provided their zero locus misses one point of each witness set.  Total spend
`2^40.34`.  Not tolerable: a repeated root along the *whole* domain (curve lines).

**PRIZE-SUFFICIENT B:** `B ≤ 2^57.93` at the actual KoalaBear sextic field
(`log₂|F| = 185.9321`); `B ≤ 2^32` under the repository's `|F| ≥ 2^160` hypothesis.  The
family repair costs `2^40.34` — sufficient at the real field, **insufficient** at `2^160`.

**SMALLEST ADVERSARIAL TEST:** `GF(5)`, `D = {0,1,2,3}`, `k=1`, `e=2`, `m=2`, `L=4`,
`dZ=10`, `f₀ = 0|_D`, `f₁ = X|_D`; entire 27-dimensional interpolation space enumerated
exactly, no sampling.

**COUNTEREXAMPLE:** the curve lines `f₀ = a|_D`, `f₁ = b|_D` with `deg a < k ≤ deg b = K`.
Every admissible interpolant is divisible by `(Y − (a+Zb))²`; the repeated part vanishes on
all of `D`.  `Bad = {0}` in the minimal instance.

**SCALABLE:** **YES** — the forcing budgets hold with `K = k` at both prize schedules
(`dichFar_fails_rho_half`, `dichFar_fails_rho_quarter`, `|D| = 2^20`).

**GENERIC-PENCIL OBSTRUCTION:** none available — `R_x(λ) ≡ 0` identically, the square is a
whole-space property of the interpolation module, not a codimension-one condition.

**GS↔MODULE BRIDGE:** not built (no exact identity established; deliberately not
constructed by analogy).

**RADIUS IF MIN-J TRUE:** `δ = 0.291916` at `ρ=1/2`, `δ = 0.499022` at `ρ=1/4`
(Johnson `1 − 1/√2 = 0.292893` at `ρ=1/2`).

**Δδ:** `+0.114792` (`ρ=1/2`), `+0.211764` (`ρ=1/4`).

**128-QUERY BIT GAIN:** `+27.745` bits (`ρ=1/2`), `+65.105` bits (`ρ=1/4`).

**STATUS:** **REDUCED.**  ND∃ shown unnecessary; MIN-J v1 isolated and then scalably
killed; (DICH) killed as a by-product; the surviving statement is MIN-J v3 together with
the identity `K* < t ⟺ Johnson`, which shows the killed lines are harmless.  Not PROVE (no
Johnson theorem yet), not KILL (the barrier is confined to curve lines of degree `≤ K*`,
which are provably harmless).

**NEXT SINGLE TEST:** can a repeated root of X-degree `> K*` be forced?  Equivalently: is
there a line, not a curve line of degree `≤ K*`, whose entire interpolation space shares a
square factor?  No forcing mechanism is known above `K*` — the double-root lemma runs out
of budget there — so a proof that none exists would upgrade MIN-J v3 from a conjecture to
the decisive lemma, and it is the only remaining obstruction between the family repair and
the Johnson radius.

---

## Honesty caveats

* The exhaustive small-field sweeps are at parameters where the GS admissibility side
  condition `h2 : L − k ≤ (m−1)(n−e)` is *not* met with room to spare; genuinely
  GS-admissible Johnson instances need `n ≳ 22` with `dZ ≳ 60`, giving interpolation
  matrices around `4818 × 4758`, which was out of computational reach here.  The curve-line
  mechanism is nonetheless proved in Lean at arbitrary parameters, including the prize
  schedules, so the scalability claim does not depend on those sweeps.
* No Johnson-radius theorem is proved.  The `Δδ` and bit-gain figures are the *value* of
  the target, not a certified improvement.
* The family repair's counting step is formalised; its *algebra* (constructing the `w_x`
  and the subresultant term from `Q`) is not.

## Lean inventory (all `sorry`-free, axioms `propext, Classical.choice, Quot.sound`)

`RequestProject/Root/CodingTheory/CurveLineDegeneracy.lean`:

* `wdegLt_weight_le` — raise the weight of a weighted-degree bound.
* `curveWord` (def), `curveWord_apply`.
* `curveLine_sq_dvd` — every admissible interpolant of a curve line has a double root
  along the curve.
* `curveLine_not_separableInY`.
* `curveLine_card_polyAgreement_le` — curve lines are far from the codeword-line variety.
* `curveLine_degree_add_smul_lt_of_isBad`, `curveLine_card_badSet_le_one` — curve lines
  have at most one bad challenge, unconditionally.
* `curveLine_isBad_zero` — and that bad challenge exists.
* `dichFar_fails`, `dichFar_fails_rho_half`, `dichFar_fails_rho_quarter` — (DICH) is false.
* `card_badSet_le_of_annihilator_family`, `epsMCA_le_of_annihilator_family` — the counting
  step of the family repair.
* `degeneracy_threshold_lt_witness_size` — the arithmetic half of `K* < t ⟺ Johnson`.
