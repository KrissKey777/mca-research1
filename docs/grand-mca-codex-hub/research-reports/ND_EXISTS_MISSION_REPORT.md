# Mission report — PROVE OR KILL (ND∃)

Scope: the single bottleneck of the Johnson-radius MCA route,

> **(ND∃)** for every formal RS line with `Bad ≠ ∅` there is an admissible Guruswami–Sudan
> interpolant `Q` inside the schedule `(k, L, m, bY, dZ)` and an evaluation point `x₀` such
> that `deg_Y Q(x₀,Y,Z) = bY` and `Q(x₀,Y,Z)` is squarefree in `Y`.

Everything below marked **Lean** is a machine-checked, `sorry`-free theorem in this repository
(axioms `propext`, `Classical.choice`, `Quot.sound` only). Everything marked **exact
computation** is a deterministic finite-field calculation in `analysis/` — exact arithmetic,
no sampling where stated, but *not* Lean-verified. Everything marked **empirical** is a
randomised search.

---

## ND∃ STATUS: **REFUTED**

Refuted by an explicit, **scalable**, Lean-verified family: the **spike lines**. The
refutation applies verbatim at both BCHKS prize schedules, so the conditional
`+10.62 / +40.85` bits are **not** obtainable on this route as stated.

The same family also refutes every weaker hypothesis introduced during this mission:
(SF∃) "some admissible interpolant is separable in `Y`", (CO∃) "two coprime admissible
interpolants exist", (GCD-SEP∃) "the gcd of the interpolation space is squarefree".

### The counterexample family (Lean)

Fix a domain `D`, an evaluation point `i ∈ D`, a scalar `a ≠ 0`, and polynomials `p₀, p₁` of
degree `< k`. The **spike line** is

```
f₀(x) = p₀(x) + a·[x = i]        (RequestProject/.../SpikeLineCounterexample.lean, spikeF0)
f₁(x) = p₁(x) − a·[x = i]        (spikeF1)
```

* **`spikeLine_isBad_one`** (Lean): if `k + 1 ≤ |D|` then `γ = 1 ∈ Bad`, so `Bad ≠ ∅`.
  Witness `S = D`: the point `f₀ + f₁ = p₀ + p₁` of the line is *exactly* a codeword on all of
  `D`, while `f₀` itself is not close to the code on `S` — the only candidate is `p₀`, from
  which it differs at `i`. Hence the line is not uniformly close on `S`.
* **`spikeLine_sq_dvd`** (Lean): the formal line agrees with the *codeword line*
  `p = p₀ + Z·p₁` on `D \ {i}`, i.e. on `|D| − 1` points. Whenever
  `k ≤ L`, `L ≤ m(|D| − 1)` and `L − k ≤ (m − 1)(|D| − 1)`, the Guruswami–Sudan double-root
  lemma applied over the domain `F[Z]` forces `(Y − p)² ∣ Q` for **every** admissible
  interpolant `Q` — not for one canonical choice, for the whole space.
* **`spikeLine_not_separableInY`** (Lean): consequently no admissible interpolant of a spike
  line is separable in `Y`; `Disc_Y Q ≡ 0`, so `Q(x₀,Y,Z)` has a repeated root at *every*
  evaluation point `x₀` and over every extension.
* **`sfExists_fails`**, **`ndExists_fails_rho_half`**, **`ndExists_fails_rho_quarter`** (Lean):
  the resulting refutations, the last two instantiated at the prize schedules.

The technical ingredient is a version of the GS root-finding and double-root lemmas over a
**domain** with unit pairwise differences of agreement points
(`GS.eval_eq_zero_of_agreement_domain`, `GS.sq_dvd_of_agreement_domain`); this is what lets the
argument run over `F[Z]` — i.e. for the *formal* line, uniformly in `Z` — rather than one
specialisation at a time.

---

## SMALLEST TESTED BAD LINE

Exact computation, `analysis/nd_exists_adversarial_gcd.py`:

```
F = GF(101),  D = {0,…,5}  (n = 6),  k = 1,  e = 2,  schedule m = 2, L = 6
one-spike line  f₀ = a·δ_i,  f₁ = −a·δ_i :  Bad ≠ ∅,
gcd of the interpolation space has Y-degree 2 and is NOT squarefree, SF∃ = False.
```

This is the smallest instance in which the mechanism was observed; it is the instance that
revealed the family. The earlier, more elaborate certificate is retained below.

## SMALLEST COUNTEREXAMPLE

Minimal form of the family: `p₀ = p₁ = 0`, `a = 1`, any `i ∈ D`, i.e.
`f₀ = δ_i`, `f₁ = −δ_i`. This is exactly the instantiation used by the Lean theorem
`sfExists_fails`.

## SCALABLE: **YES**

The two schedule inequalities `L ≤ m(|D| − 1)` and `L − k ≤ (m − 1)(|D| − 1)` are satisfied
with an enormous margin at both prize schedules (`|D| = 2²⁰`, `|D| − 1 = 1 048 575`):

```
ρ = 1/2 :  L = 642 769 488   ≤  866·1 048 575 = 908 065 950
           L − k = 642 245 200 ≤  865·1 048 575 = 907 017 375
ρ = 1/4 :  L = 403 177 215   ≤  768·1 048 575 = 805 305 600
           L − k = 402 915 071 ≤  767·1 048 575 = 804 257 025
```

These are exactly the hypotheses of `ndExists_fails_rho_half` /
`ndExists_fails_rho_quarter`, discharged by `norm_num` inside Lean. So the KILL is not a
small-field or low-surplus artefact: it survives at the prize parameters, at any field size,
and at any dimension surplus.

**This retires the earlier "shape surplus `s ≥ 2` ⇒ (ND∃)" heuristic**, which was based on the
`s = 1` certificate below and on a sweep that never contained a spike line. The true driver of
the failure is not the surplus but **proximity of the formal line to a codeword line**: any
line agreeing with a codeword line off a single point kills every interpolant simultaneously,
however large the interpolation space is.

## DIMENSION OF INTERPOLATION SPACE

Irrelevant to the KILL — that is the point. The obstruction is a divisibility statement that
holds for the *entire* kernel, of whatever dimension. Recorded values from the exact
computations: `dim_F I = 42` for the `GF(101)` certificate below (out of 736 unknowns), and
`4.24·10¹⁴` surplus unknowns at the prize schedule `ρ = 1/2` — neither helps.

## DEGREE-DEFECT LOCUS

Mode A of GATE 3 (**every** interpolant has `deg_Y Q < bY`) does occur in the small exact
certificate (`max_Q deg_Y Q = 2 < bY = 3`), but it is **not** the fatal mode:

* **Lean** `lineInterpolant_natDegree_pos`: if `L ≤ m·|D|` then every admissible interpolant
  has `deg_Y Q ≥ 1`, so degree failure can never be total;
* **Lean** `epsMCAmax_le_disc_of_bad_flex` / `epsMCAmax_le_of_schedule_separable`: the whole
  ε-MCA chain runs with the *actual* `Y`-degree `b` (`1 ≤ b ≤ bY`) and the certified constant
  `(2bY − 1)·dZ` is unchanged.

So only mode B, **squarefree failure**, matters — and mode B is what the spike family
realises, unconditionally.

## DISCRIMINANT LOCUS

For a spike line, `I ⊆ V(Disc_Y)` with an explicit reason: every `Q ∈ I` is divisible by
`(Y − (p₀ + Z p₁))²` in `F(Z,X)[Y]`. This is the strongest possible answer to GATE 7 — the GS
interpolation kernel of a bad RS line **can** be a linear subspace of the discriminant
hypersurface, and there is a one-line algebraic reason for it.

Supporting exact computation (`analysis/nd_exists_kill_certificate.py`), retained:

```
F = GF(101),  D = {0,1,2,3,4},  k = 2,  e = 1,  m = 2,  L = 7,  bY = 3,  dZ = 45
admissibility:  L = 7 < m(n − e) = 8;   5·C(3,2)·(dZ+bY+1) = 735 < 16·(dZ+1) = 736
line f₀ = [46,8,100,99,45], f₁ = [88,75,84,4,97],  badSet = {33}
dim_F I = 42,  max deg_Y = 2,  Disc_Y Q = q₁² − 4q₀q₂ = 0 identically for all Q ∈ I
  (verified on a basis of 42 elements and, by polarisation of the quadratic form Disc_Y,
   on all 861 pairs — exact, not sampled)
```

## GENERIC-LINE ESCAPE: **NO**

GATE 4 (generic linear combination) is settled, and it fails for spike lines: `D_{x₀}(λ) ≡ 0`
for every `x₀` and every pencil, because the obstruction is a *common repeated factor* of the
whole space, not a coincidence at finitely many `λ`.

The positive half of GATE 4 was nevertheless proved in full generality, in Lean, over an
arbitrary field and with no algebraic closure; it is still valid mathematics, just with a
hypothesis that spike lines violate:

* **Lean** `card_pencil_degenerate_le`: for coprime `f, g`, at most `deg(f g′ − f′ g)` values
  of `λ` make `f + λg` non-separable.
* **Lean** `card_pencil_common_le` / `card_pencil_nonCoprime_le`: at most `deg G` values of
  `λ` make `f + λg` share a factor with a fixed `G ≠ 0`.
* **Lean** `exists_separableInY_of_separable_gcd`, `exists_separableInY_of_gcd_separable`: if
  two admissible interpolants have a **squarefree gcd** in `F(Z,X)[Y]`, then all but at most
  `3·bY` scalars `λ` make `Q₁ + λQ₂` admissible and separable. Needs only `bY < char F` and
  `3bY < |F|`.

GATE 5 (characteristic) is therefore not the issue: with `bY = 1225` resp. `1537` and a prime
field of size `≥ 2¹⁶⁰`, `bY < char F`, so inseparability is equivalent to a repeated factor —
and the spike line supplies a genuine repeated factor, not a Frobenius power.

GATE 6 is answered **yes** in the strongest sense: an interpolation space can consist entirely
of multiples of a fixed square, so no perturbation `Q₀² + λR` escapes.

## GATE 8 / dimension surplus

Definitively insufficient. Recorded exact values:

```
formal-line surplus, ρ = 1/2 :  519 870 790 369 444 800 unknowns
                                519 446 693 491 507 200 conditions,  surplus ≈ 4.24·10¹⁴
GS shape surplus s = #{(a,b) : a + k·b < L} − n·C(m+1,2)
  ρ = 1/2 :  394 334 425 888 − 393 646 964 736 = 687 461 152
  ρ = 1/4 :  310 244 669 438 − 309 640 298 496 = 604 370 942
```

and the spike family is degenerate at *every one* of these surpluses.

## EXACT SURVIVING LEMMA

The separability route is dead as a *universal* statement over lines, but the counterexamples
are highly structured, and they are structured in a way that makes them harmless. The
surviving reduction is a **dichotomy**:

> **(DICH)** Let `f₀, f₁` be a formal RS line with `Bad ≠ ∅`. Either
>
> * **(near)** the line agrees with some codeword line `p₀ + Z·p₁` (`deg p₀, p₁ < k`) on more
>   than `|D| − e′` points for a suitable `e′`, in which case `Bad` is small *directly*; or
> * **(far)** the line is not near any codeword line, and then some admissible interpolant is
>   separable in `Y`, so `epsMCAmax_le_of_schedule_separable` applies unchanged.

The **(near)** half is already proved for the counterexample family itself:

* **Lean** `spike_badSet_eq_singleton`: for `f₀ = a·δ_i`, `f₁ = −a·δ_i` with `a ≠ 0` and
  `k + e + 1 ≤ |D|`, the bad set is **exactly** the singleton `{1}`;
* **Lean** `spike_epsMCA_eq`: hence `ε_mca = 1/|F|` for these lines — the smallest value any
  nonconstant line can have.

So the lines that kill the separability route are precisely the lines for which the MCA bound
is trivially optimal. That is the reason to expect (DICH) to be provable, and it is the
strongest available evidence that the KILL is a defect of the *proof strategy*, not of the
Johnson-radius statement.

Only the **(far)** half is open, and it now carries an extra usable hypothesis — a *lower*
bound on the distance from the formal line to the codeword-line variety — which the previous
formulations (ND∃)/(SF∃)/(CO∃)/(GCD-SEP∃) did not have and which is exactly what the spike
counterexample destroys. Note that (DICH) is genuinely weaker than (ND∃): it does not claim a
separable interpolant for *every* bad line, only for those bounded away from the codeword-line
variety.

The already-proved half of the chain is untouched:
`epsMCAmax_le_of_schedule_separable`, `epsMCAmax_le_disc_of_bad_flex`,
`lineInterpolant_natDegree_pos`, `threshold_rho_half_bchks_*`,
`threshold_rho_quarter_bchks_*` remain `sorry`-free theorems; only their hypotheses are now
known to be unsatisfiable in the form stated.

## JOHNSON CONSEQUENCE

**None, currently.** The Johnson-radius certificates in `NDExistsReduction.lean`,
`PencilEscape.lean` and `GcdPencilEscape.lean` are true implications whose hypotheses (ND∃),
(SF∃), (CO∃), (GCD-SEP∃) are now **known false at the prize schedules**. They therefore no
longer support a Johnson-radius claim. The unconditional part of the project is unchanged:

```
UD frontier          δ = (1 − ρ)/2      PROVED, unconditional
Johnson frontier                        NOT supported by this route
```

## EXPECTED BIT GAIN

**0 as of now** on this route. The previously quoted **+10.62 bits** (`ρ = 1/2`) and
**+40.85 bits** (`ρ = 1/4`) at `t = 128` (radius increase `+0.041916` resp. `+0.124022`)
remain the *value* of the Johnson frontier, but they are no longer reachable through any of
the four hypotheses examined in this mission. They become available again only if (DICH), or
some other bypass of the near-codeword-line lines, is proved.

## DECISION

* Note that the counterexamples are **harmless lines** (`ε_mca = 1/|F|`, Lean-verified): the
  failure is a failure of the discriminant proof strategy on a measure-zero, explicitly
  describable family, not evidence against the Johnson-radius bound itself.
* **Stop** all work on "one separable / coprime / squarefree-gcd interpolant" statements. They
  are refuted, at the prize schedules, by a family that is trivial to write down. Any future
  proposal of this shape must first be tested against `f₀ = δ_i`, `f₁ = −δ_i`.
* The single next mission, if the Johnson frontier is to be pursued, is **(DICH)**: prove that
  lines *near* the codeword-line variety have small bad sets by a direct argument (the spike
  case is already essentially a one-line computation), and re-attempt separability only for
  lines *far* from it. The distance parameter must be chosen so that the two halves overlap.
* Record explicitly that the mechanism is geometric, not arithmetic: it is insensitive to
  field size, characteristic, interpolation dimension, and shape surplus.

---

## Artefacts

Lean (all `sorry`-free, all built, axioms `propext`/`Classical.choice`/`Quot.sound`):

* `RequestProject/Root/CodingTheory/SpikeLineCounterexample.lean` — **the KILL**: GS root
  finding and double-root lemma over a domain; spike lines; `Bad ≠ ∅`; `(Y − p)²` divides
  every admissible interpolant; refutation of (SF∃)/(ND∃) at both prize schedules; and the
  exact bad set (`{1}`) and exact `ε_mca` (`1/|F|`) of the counterexample lines.
* `RequestProject/Root/CodingTheory/SquareSpanObstruction.lean` — the square-span mechanism in
  the abstract (`not_separableInY_of_sq_dvd`, `not_ndExists_of_forall_sq_dvd`).
* `RequestProject/Root/CodingTheory/NDExistsReduction.lean` — degree defect is never total;
  flexible-degree ε-MCA chain; reduction to (SF∃).
* `RequestProject/Root/CodingTheory/PencilEscape.lean` — pencil theorem for coprime pairs.
* `RequestProject/Root/CodingTheory/GcdPencilEscape.lean` — general pencil counting lemma;
  escape modulo a squarefree common factor.

Exact / exploratory computation (`analysis/`, Python, **not** Lean-verified):

* `nd_exists_interpolation_space.py` — bad sets and formal-line interpolation matrices over
  GF(q), exact kernels.
* `nd_exists_deep_probe.py`, `nd_exists_admissible_sweep.py`, `nd_exists_gcd_sweep.py` —
  GATE 1/2 sweeps over admissible schedules.
* `nd_exists_counterexample_probe.py` — structure of the degenerate space.
* `nd_exists_kill_certificate.py` — exact certificate `Disc_Y ≡ 0` on a whole 42-dimensional
  interpolation space.
* `nd_exists_surplus_scan.py`, `nd_exists_low_surplus_probe.py` — shape-surplus scan
  (superseded as a criterion; retained as data).
* `nd_exists_adversarial_gcd.py` — the adversarial search that produced the spike line.
