# NEAR-u — adversarial kill gate (no Lean)

This report executes the five gates of the NEAR-u kill order. **No Lean was written**: the
gate conditions for formalisation are not met, and Gate 1 terminated the chain.

Everything marked *certificate* is an exact finite-field computation with an explicit witness
polynomial for every challenge counted; everything marked *exhaustive* enumerates the complete
bad set. Neither is Lean-verified. Nothing here changes any existing Lean theorem.

Artefacts: `analysis/near_u_adversarial_kill.py` (harness: exact bad set, adversarial linear
solver), `analysis/near_u_counterexample.py` (the kill), `analysis/near_u_maxbad_search.py`
(maximisation).

---

## The statement under attack

`D ⊆ F_q`, `|D| = n`, code `RS_k`, radius `e`, `ρ = k/n`, `δ = e/n`. A line whose two
coefficient words are supported on a set `E` with `|E| = u` (i.e. the line obtained after
subtracting a codeword line that agrees with the original line on `n − u` positions). Bad set
in the sense of `MCA.lean`:

```
γ ∈ Bad  ⟺  ∃ S ⊆ D, |S| ≥ n − e,  a₀ + γ a₁ agrees on S with a deg<k polynomial,
             and a₁ agrees on S with no deg<k polynomial.
```

```
(NEAR-u)   #Bad ≤ e + 1        for      n − k − e  <  u  ≤  n − √(kn).
```

---

## GATE 1 — ADVERSARIAL SEARCH: the conjecture is FALSE

The previous evidence (`analysis/near_u_window_probe.py`) sampled `(a₀,a₁)` at random. The
correct move is to *solve* for the line instead of sampling it. Doing so exposes two
independent badness mechanisms whose costs are different, and the maximum of the sum is
attained by superimposing them.

**Mechanism Z (zero-codeword witnesses).** For `x ∈ E` with `a₁(x) ≠ 0` put
`γ_x = −a₀(x)/a₁(x)`. The word `a₀ + γ_x a₁` vanishes at `x` and off `E`. If it is nonzero at
the remaining `u − 1` points of `E` and `u − 1 ≤ e`, the *zero* polynomial agrees with it on a
set `A ⊇ (D \ E) ∪ {x}` of size `n − e`. When `|D \ E| = n − u ≥ k` the only deg<k polynomial
vanishing on `A ∩ (D \ E)` is `0`, and `a₁(x) ≠ 0`, so `a₁` is not close on `A`. Cost: the
`γ_x` are the roots of the coordinatewise ratio, so the witness sets are *disjoint* and this
mechanism alone yields at most `⌊u/(u−e)⌋` bad challenges — exactly `e + 1` at `u = e + 1`.
**This is the source of the observed ceiling: the conjectured bound `e+1` is just the `u = e+1`
value of `u/(u−e)`, not a barrier of its own.**

**Mechanism A (algebraic witness with maximal root collision).** Put all `e` errors outside
`E`: choose `R ⊆ D \ E` with `|R| = n − u − e` and let `g = Π_{x∈R}(X − x)`. Then `deg g < k`
iff `e ≥ (n − k)/2` — i.e. exactly at and above the unique-decoding radius — and `g` agrees
with the word on `E ∪ R`, a set of size `n − e`. `a₁` is not close there as soon as `a₁|E` is
not a scalar multiple of `g|E`. Cost: `n − k − e` linear conditions on `(a₀,a₁) ∈ F^{2u}`,
and in the window `n − k − e < u`, so the conditions are affordable.

**The kill.** Take `u = e + 1` and satisfy both at once. Fix `γ*`, choose `a₁ : E → F^×` with
the `u` ratios `g(x)/a₁(x)` pairwise distinct, and set

```
      a₀|E  =  g|E  −  γ* · a₁|E ,        a₀ = a₁ = 0  off  E .
```

Then `γ*` is bad by Mechanism A, and the `u = e+1` distinct values
`γ_x = γ* − g(x)/a₁(x)` (all `≠ γ*`, since `g` has no root in `E`) are bad by Mechanism Z:

```
      #Bad  ≥  e + 2  >  e + 1 .
```

Admissibility: `(n−k)/2 ≤ e` and `e + 1 ≤ n − ⌈√(kn)⌉`, i.e. **the whole open window, at every
rate, from the unique-decoding radius up to Johnson**. The construction is field-agnostic
(only `q ≳ u` is used, to make the ratios distinct).

### STRONGEST ADVERSARIAL TEST (certificates, exact)

Every line below exhibits an explicit witness polynomial for each counted challenge, verified
exactly: `|A| ≥ n − e` and `a₁` not interpolable on `A`.

| q | n | k | e | u | ρ | δ | window | certified #Bad | e+1 |
|---|---|---|---|---|---|---|--------|---------------|-----|
| 11, 13, 101, 1009 | 7 | 1 | 3 | 4 | 0.143 | 0.4286 | (3,4] | 5 | 4 |
| 11, 13 | 8 | 2 | 3 | 4 | 0.250 | 0.375 | (3,4] | 5 | 4 |
| 29 | 24 | 12 | 6 | 7 | 0.500 | 0.250000 | (6,7] | 8 | 7 |
| 37 | 32 | 16 | 8 | 9 | 0.500 | 0.250000 | (8,9] | 10 | 9 |
| 67, 1009 | 64 | 32 | 16 | 17 | 0.500 | 0.250000 | (16,18] | 18 | 17 |
| 137 | 128 | 64 | 33 | 34 | 0.500 | 0.257812 | (31,37] | 35 | 34 |
| 137, 2³¹−1 | 128 | 64 | 36 | 37 | 0.500 | 0.281250 | (28,37] | 38 | 37 |
| 101 | 64 | 16 | 24 | 25 | 0.250 | 0.375 | (24,32] | 26 | 25 |

Stacking two algebraic witnesses (`a₀|E = g_{R₁}|E`, `a₁|E = g_{R₂}|E − g_{R₁}|E`, so that
`γ = 0` and `γ = 1` are both of type A) raises every ρ = 1/2 row by one more:
certified `#Bad ≥ e + 3` — `11` at `(32,16,8)`, `19` at `(64,32,16)`, `39` at `(128,64,36)`,
over `q = 37, 67, 1009, 137, 2³¹−1` alike.

### MAX #Bad / (e+1)

Exhaustive computation of the *complete* bad set on the minimal instance
(`n = 8, k = 2, e = 3, u = 4`, window `(3,4]`) gives

```
   #Bad = 8 = 2(e+1)      for q = 11, 13, 17, 23, 101, 1009, 10007   (ratio 2.000)
```

and hill-climbing from the construction does not improve on it. Same ratio at
`n = 12, k = 3, e = 5, u = 6` (`#Bad = 12 = 2(e+1)`, `q = 17`). The exact value is
**independent of `q` over four orders of magnitude**, so the violation is not a small-field
artefact and persists at prize-field size.

```
MAX #Bad / (e+1)  =  2.000   (exhaustive, minimal instance)
                  ≥  (e+3)/(e+1)  certified at every tested ρ = 1/2 point up to n = 128
```

### Minimal counterexample

Smallest admissible instance overall (`n = 7`; a scan of all `(n,k,e)` with `n < 7` finds no
instance satisfying `(n−k)/2 ≤ e`, `u = e+1 ≤ n − √(kn)`, `n−k−e < u`, `u ≤ n−k`,
`0 ≤ n−2e−1 ≤ k−1`):

```
q = 11,  D = {0,…,6},  n = 7,  k = 1,  e = 3,  u = 4,  E = {0,1,2,3},  ρ = 1/7, δ = 3/7
R = ∅,  g = 1,  γ* = 1
a₀|E = (9, 8, 7, 6)    a₁|E = (3, 4, 5, 6)    (a₀ = a₁ = 0 on {4,5,6})
Bad = {1, 3, 8, 9, 10},  #Bad = 5 > 4 = e + 1     (exhaustive; also 5 at q = 13, 101, 1009)
```

Smallest instance attaining the ratio `2`:

```
q = 11,  D = {0,…,7},  n = 8,  k = 2,  e = 3,  u = 4,  E = {0,1,2,3},  ρ = 1/4, δ = 3/8
R = {4},  g = X − 4,  γ* = 1
a₀|E = (9, 2, 6, 10)   a₁|E = (10, 8, 1, 1)   (a₀ = a₁ = 0 on {4,5,6,7})
Bad = {1, 2, 3, 4, 5, 6, 8, 10},  #Bad = 8 = 2(e+1) > 4 = e + 1.
```

---

## GATE 2 — SCALABILITY

**Yes — the family scales in `n` and is not field-dependent.** For every `(n, k, e)` with

```
   (n − k)/2 ≤ e         (at or above unique decoding)
   e + 1 ≤ n − ⌈√(kn)⌉   (u = e+1 lies in the probed window; this also gives u ≤ n − k)
```

the construction above is defined and certifies `#Bad ≥ e + 2` (and `≥ e + 3` in the two-`R`
form). At `ρ = 1/2` these conditions hold for every `n ≥ 24` and every
`δ ∈ [(1−ρ)/2, 1−√ρ)` — the entire region the conjecture was meant to serve. Verified
explicitly at `n = 8, 12, 24, 32, 64, 128` and `q` from `11` to `2³¹−1`.

**SCALABLE COUNTEREXAMPLE: YES → NEAR-u is KILLED.**

The scalable mechanism is informative but *not new*: mechanism Z is the same near-codeword-line
geometry (a line supported on `u ≈ e` positions, one bad challenge per support coordinate) that
produced the **spike lines** which refuted `(ND∃)`. The correct shape of the truth in the
window is therefore not `e + 1` but something of order `u/(u−e)` plus an `O(u/(n−k−e))` term;
`e + 1` is only the value of the first term at the extreme point `u = e + 1`, and it is
violated as soon as the second term is nonzero — which the window itself guarantees.

Per the gate instruction the negative result is **not** formalised: the mechanism is a
rediscovery of the spike geometry already Lean-verified in
`RequestProject/Root/CodingTheory/SpikeLineCounterexample.lean`, so formalising it would add
no new mathematics.

---

## GATE 3 — SYMBOLIC RADIUS PAYOFF (computed anyway, for the record)

Even under the *false* conjecture the payoff is nil at `ρ = 1/2`, so NEAR-u was already frozen
before Gate 1 finished. With near threshold `τ₀` (near half must cover all `u ≤ n − τ₀`) the
far half needs the Johnson condition `(n − e)² > n(τ₀ − 1)`, i.e. `δ < 1 − √(τ₀/n)`. The near
half is available for `τ₀ = k + e` (proved) and, under the conjecture, down to
`τ₀ = √(kn)`; hence `τ₀/n = min(ρ + δ, √ρ)` and

```
   δ_max^{NEAR-u}(ρ)  =  max { (3 − √(5+4ρ))/2   if ρ + δ ≤ √ρ ,
                               1 − ρ^{1/4}       if ρ + δ > √ρ }      (self-consistent branch)
```

| ρ | branch 1 `(3−√(5+4ρ))/2` | branch 2 `1−ρ^{1/4}` | δ_max^{NEAR-u} | already proved |
|---|---|---|---|---|
| 1/2 | **0.177124** (consistent) | 0.159104 (inconsistent) | **0.177124** | 0.177124 |
| 1/4 | 0.275255 (inconsistent) | **0.292893** (consistent) | 0.292893 | 0.287258 |
| 1/8 | 0.327396 (inconsistent) | **0.405396** (consistent) | 0.405396 | 0.398752 |
| 1/16 | 0.354356 (inconsistent) | **0.500000** (consistent) | 0.500000 | 0.491867 |

```
δ_max^{NEAR-u}(1/2) = (3 − √7)/2 = 0.177124344…
```

which is *exactly* the radius already certified by `nearFar_rho_half`.

```
CROSSES 1/4:  NO      Δδ = 0.000000      128-query bit gain = 0.000 bits
```

(Reference points at `ρ = 1/2`: `−128·log₂(1−δ)` is `36.000` bits at `δ = 0.177124`,
`53.125` at the `0.25` frontier, `64.000` at Johnson `0.292893`.)

Crossing `1/4` at `ρ = 1/2` would require the near half down to `τ₀/n < (1−δ)² = 0.5625`, i.e.
`u` up to `0.4375 n` — far outside the conjecture's own ceiling `u ≤ n − √(kn) = 0.2929 n`, and
squarely inside the regime the `(CL)` probe reports as unstructured. **No version of NEAR-u
inside its window can reach the frontier.**

---

## GATE 4 — MINIMAL LEMMA

Not applicable: Gate 3 does not cross `1/4`, and Gate 1 refuted the statement. For the record,
no bound `#Bad ≤ B` of any size helps here: the radius ceiling `1 − √(τ₀/n)` is set by the far
half and by the window's own upper limit `τ₀ ≥ √(kn)`, not by the constant `B`. Improving `B`
from `L²` to `e+1` changes only the field-size requirement, never `δ`.

---

## GATE 5 — COMPARISON

| criterion | A. NEAR-u | B. ND∃ → Johnson (via (DICH)) |
|---|---|---|
| expected radius at ρ=1/2 | 0.177124 (= status quo; **0** gain) | 0.292893 (Johnson), `Δδ = +0.115769`, `+27.99` bits / 128 queries |
| cheapest remaining lemma | none — statement refuted | (DICH): near half for lines *near* the codeword-line variety + separability only for lines far from it |
| falsifiability | **falsified** (this report) | (ND∃)/(SF∃)/(CO∃)/(GCD-SEP∃) already falsified; (DICH) still standing |
| proof complexity | n/a | high: GS interpolation over `F[Z]`, double-root lemma, distance-to-variety case split |
| dependence on Johnson/list-decoding machinery | low | high (the whole point) |
| novelty | none — the killing family is the spike geometry again | the *dichotomy formulation* is the new element |
| score | `P_success = 0`, `V_radius = 0`, `V_novelty = 0`, `C_research` spent | `P_success` MEDIUM-LOW, `V_radius` HIGH, `V_novelty` MEDIUM, `C_research` HIGH |

NEAR-u is **strictly dominated** by ND∃/(DICH) on every axis: zero radius value even if true,
and it is not true.

---

## REQUIRED OUTPUT

```
NEAR-u STATUS:               KILLED (false in its own open window, at every tested rate)

STRONGEST ADVERSARIAL TEST:  superposition of the zero-codeword mechanism at u = e+1
                             (e+1 disjoint single-coordinate witness sets) with one (or two)
                             maximal-root-collision witnesses g = Π_{x∈R}(X−x), |R| = n−u−e,
                             all e errors pushed outside E.  Exact certificates at
                             (n,k,e) = (8,2,3), (12,3,5), (24,12,6), (32,16,8), (64,32,16),
                             (128,64,33), (128,64,36); q from 11 to 2³¹−1.

MAX #Bad / (e+1):            2.000   (exhaustive: #Bad = 2(e+1), q-independent)
                             certified ≥ (e+3)/(e+1) at every ρ = 1/2 point tested

SCALABLE COUNTEREXAMPLE:     YES.  Defined for all (n,k,e) with (n−k)/2 ≤ e and
                             e+1 ≤ n − ⌈√(kn)⌉ — i.e. the whole window, unique decoding
                             through Johnson, every n ≥ 24 at ρ = 1/2, every field.

SYMBOLIC δ_MAX:              δ_max^{NEAR-u}(ρ) = max{ (3−√(5+4ρ))/2 , 1−ρ^{1/4} }
                                                  (self-consistent branch)
                             δ_max^{NEAR-u}(1/2) = (3−√7)/2 = 0.177124344…

CROSSES 1/4:                 NO

Δδ:                          0.000000  (identical to the already-certified nearFar_rho_half)

128-QUERY BIT GAIN:          0.000 bits

MINIMAL SURVIVING LEMMA:     none.  No bound #Bad ≤ B rescues the route: the ceiling is the
                             far half's Johnson condition together with the window limit
                             τ₀ ≥ √(kn), which is independent of B.

NEAR-u SCORE:                P_success 0 · V_radius 0 · V_novelty 0            → dead
ND∃ SCORE:                   P_success MEDIUM-LOW · V_radius HIGH (+27.99 bits)
                             · V_novelty MEDIUM · C_research HIGH              → only live route

DECISION:                    KILL NEAR-u.  RETURN TO ND∃ (specifically (DICH)).
                             No Lean written; nothing formalised.

NEXT SINGLE TEST:            Test (DICH) against the family that killed NEAR-u.  The near half
                             of (DICH) must survive precisely the lines used here: supported on
                             u = e+1 positions off a codeword line, with #Bad = 2(e+1) ≫ e+1.
                             So the single next probe is: for lines at distance exactly u from
                             the codeword-line variety, measure max #Bad as a function of
                             (u, e, n−k) adversarially (not randomly) and fit the true law
                             — the data so far says  #Bad ≈ u/(u−e) + O(u/(n−k−e)),  capped by
                             the list size.  (DICH) is only worth pursuing if that law, with
                             the far half's Johnson condition, still admits δ > 1/4 at ρ = 1/2.
```

---

## Consistency with the existing Lean theorems

No Lean theorem in this repository is contradicted. The proved near half,
`card_badSet_le_succ_radius_of_near_codeword_line`, assumes `k + e ≤ |T|` with
`|T| = n − u`, i.e. `n − k − 2e ≥ 1` at `u = e + 1`. The counterexample family requires
`e ≥ (n − k)/2`, i.e. `n − k − 2e ≤ 0`. **The two conditions are exact complements: the
counterexamples begin precisely one step past the hypothesis of the theorem.** That is the
sharpest possible statement of where the near half stops, and it is why the window
`n − k − e < u ≤ n − √(kn)` can never be entered by this mechanism.

`nearFar_rho_half` (`δ = 0.177124` at `ρ = 1/2`), `nearFar_ceiling`, the pair-covering
certificates and all `ND∃`-related Lean results are untouched by this report.
