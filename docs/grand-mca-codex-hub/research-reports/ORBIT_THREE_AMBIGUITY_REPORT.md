# The `d = 3` Frobenius-orbit case: locus barrier and ambiguity dichotomy

Status legend: **[MC]** machine-checked Lean theorem (no `sorry`, axioms
`propext / Classical.choice / Quot.sound` only), **[EX]** exhaustive small-model
computation, **[SA]** sampled small-model computation, **[CB]** conjectural bridge.

Deployed calibration constants (KoalaBear row):

```
p  = 2130706433 = 2^31 - 2^24 + 1        F = F_{p^6},  H = mu_{2^21}
n  = 2^21, k = 2^20, e = 981104          a = n - e = 1116048,  t = a - k = 67472
B* = 274980728111395087 = floor(|F| / 2^128)
p^2 + p + 1 = 4539909905758289923        B*/(p^2+p+1) = 0.0605696443...
p + 1       = 2130706434
```

Continuation of `ORBIT_THREE_RESOLUTION_REPORT.md`.  That report closed with a proposed
"next object": bound the number of *close directions* (or of common-support planes) inside
the rational 3-space and compare it with `B*`.  Section 2 below shows that this object can
never work.  Section 3 gives the replacement, which does.

---

## 1. Exact small-model computation

Two scripts, both exact over small prime fields (`analysis/orbit3_plane_census.py`,
`analysis/orbit3_plane_search.py`).  For a 3-dimensional space `U <= F_q^D` given by a
`3 x n` generator matrix, with `a = n - e` and excess `t = a - k`, they compute

* `closeProj(U)`  — the number of projective directions `[lam]` of `PG(U)` whose word is
  within distance `e` of `RS_k(D)`;
* `planeAll(U)`   — the number of planes `W < U` contained in `ker psi_S` for some support
  `S` with `|S| >= a` (syndrome rank `<= 1`);
* `planeExact(U)` — the number of planes `W < U` with `W = ker psi_S` exactly (syndrome rank
  *exactly* one).  This is the quantity an officially bad challenge injects into: badness
  forces a support on which a whole rational plane is explained **and** the ambient 3-space
  is not.

Findings (reproducible by running the scripts):

| `q` | `n` | `k` | `e` | `a` | `t` | max `planeExact` | `C(n,a)` |
|----|----|----|----|----|----|----|----|
| 5 | 4 | 1 | 2 | 2 | 1 | 6 **[EX]** | 6 |
| 5 | 4 | 2 | 1 | 3 | 1 | 4 **[EX]** | 4 |
| 7 | 6 | 2 | 3 | 3 | 1 | 20 **[SA]** | 20 |
| 7 | 6 | 3 | 2 | 4 | 1 | 15 **[SA]** | 15 |
| 5 | 4 | 1 | 1 | 3 | 2 | 2 **[EX]** | – |
| 7 | 6 | 2 | 2 | 4 | 2 | 4 **[SA]** | – |
| 7 | 6 | 3 | 1 | 5 | 2 | 2 **[SA]** | – |
| 7 | 6 | 2 | 1 | 5 | 3 | 1 **[SA]** | – |

Two robust patterns:

1. **At excess `t = 1` the maximum of `planeExact` equals `C(n, a)` and is independent of
   `q`.**  Every support of the exact size `a` can carry its own rank-one plane, and nothing
   more.  This is exactly the mechanism of the `k = 1`, `e = |D| - 2` sharpness family of
   `OrbitThreeSharpness.lean`.
2. **At `t = 2` the count collapses to `<= 4`, at `t = 3` to `<= 1`.**  The danger in `d = 3`
   is entirely concentrated at tiny excess.

The deployed row has `t = 67472`, i.e. very far from the dangerous regime — but the census
gives no `q`-uniform bound, so it cannot by itself settle the deployed case.  It did,
however, motivate both results below.

---

## 2. Barrier: the close-direction locus carries no information

**[MC] `Root.CodingTheory.locus_barrier`, `Root.CodingTheory.KoalaRow.deployed_locus_barrier`**
(`RequestProject/Root/CodingTheory/OrbitThreeLocusBarrier.lean`).

Take the *monomial* 3-space, `u_j = ` the words of `1, X, X^2`, inside any rate `k >= 3`.
Then, at **every** radius:

* `closeDirSet` is maximal: **all** `p^3 - 1` nonzero rational directions carry a word within
  the radius — 100 % of `PG(2,p)`;
* every plane of the 3-space is commonly correctable on every support;
* yet `badSet = {}` and `goodCovSet = {}`.

The witness is instantiated in the deployed field with Frobenius-orbit dimension exactly
three (`KoalaRow.deployed_locus_barrier`, using `coeffA` / `coeffA_independent` of
`KoalaBearOrbitThreeWitness.lean`).

**Consequence.**  Any argument of the shape "a Prize-breaking `d = 3` pencil would need more
than `X` close rational directions / commonly-correctable planes, and `X > B*` is impossible"
is *unconditionally* dead: the extremal configuration attains 100 % of the plane while being
perfectly Prize-safe.  The proximity clause of `goodCovSet` is free; **only** the exactness
clause `¬ LineCloseOn` — syndrome rank exactly one, i.e. the ambient 3-space is *not*
explained — can carry information.

This retires the object proposed in `ORBIT_THREE_RESOLUTION_REPORT.md` §4, and with it
outcome (3) of the task statement in the form originally envisaged: the locus of rational
covectors cannot be pushed below `B*` by counting closeness.

---

## 3. The `d = 3` ambiguity dichotomy

The conditional theorem `card_badSet_le_of_rigid_orbit3` gives `#Bad <= e + 2` under a
*global* hypothesis `hrigid`: one single codeword triple `g` explains every bad hyperplane.
That hypothesis is unverifiable in practice and, at the deployed radius, provably
unavailable pairwise (`KoalaBearRigidOrbit3.deployed_no_pairwise_rigidity`: two witness
supports meet in `n - 2e = 134944 < k` points).

**[MC] `Root.CodingTheory.card_badSet_le_ambiguity`**
(`RequestProject/Root/CodingTheory/OrbitThreeAmbiguity.lean`).  Unconditionally, with
`q = #Fix(sigma)`:

```
#Bad * (q - 1)  <=  (e + q + 3) * (q - 1)  +  #ambigSet * (q + 1) .
```

Here `ambigSet` is the set of nonzero rational (`sigma`-fixed) directions `lam` for which the
rational word `sum_j lam_j u_j` has **two distinct** codewords of degree `< k` within
distance `e`: genuine list-decoding failure, not mere proximity.

So the global rigidity hypothesis is replaced by a local, meaningful one.  Either the bad set
is capped at `e + q + 3` (Prize-safe on the deployed row by a factor `> 2^36`), or the
rational 3-space contains a large ambiguous locus.

### Proof architecture

All pieces are in `OrbitThreeAmbiguity.lean` and `CrossThree.lean`.

* `exists_perp_basis_coords` (`CrossThree.lean`) — explicit **linear** coordinates on the
  plane `c^perp`: indices `j1 != j2` and vectors `A, B` with `A j1 = 1, A j2 = 0, B j1 = 0,
  B j2 = 1`, `sigma`-fixed whenever `c` is, such that every `nu ⊥ c` equals
  `nu j1 . A + nu j2 . B`.
* `exists_transversal` — a rational `Z ⊥ c'` with `c . Z != 0`, obtained from those
  coordinates.
* `exists_global_interp` — **propagation.**  Two code-good covectors `c, c'` whose
  intersection direction `c x c'` is *unambiguous* force one codeword triple `g` explaining
  the whole plane `c^perp` on `S` **and** the whole plane `c'^perp` on `S'`.  The triple is
  built as `g_j = [j = j1] PA + [j = j2] PB + c_j R` with a correction polynomial `R`
  calibrated on the transversal.
* `dev_dir_of_clean` — **rigidity transfer.**  Any further code-good covector `c''` outside
  the pencil of `c, c'`, all of whose rational directions are unambiguous, satisfies the
  `hrigid` relation for that same `g`: on its support the deviation `u(x) - g(x)` points
  along `c''`.  The proof uses `nu_1 = c x c''`, `nu_2 = c' x c''` and the identity
  `(c x c'') x (c' x c'') = det(c,c',c'') . c''` (`cross3_cross3_cross3`).
* `card_le_of_pairwise_nonprop` — pairwise non-proportional nonzero rational vectors inside a
  rational plane satisfy `#T * (q - 1) <= q^2 - 1`, i.e. at most `q + 1` of them.
* `isAmbig_smul` / `smul_mem_ambigSet` — ambiguity is invariant under scaling by a nonzero
  rational scalar, which is what makes the incidence double count between dirty challenges
  and ambiguous directions work.
* Assembly: split the bad set into the exceptional challenge (`<= 1`, by
  `exceptional_subsingleton`), the *dirty* challenges (whose covector annihilates some
  ambiguous direction; controlled by the double count) and the *clean* ones; the clean part
  splits again into the pencil line (`<= q + 1`) and the rigid remainder (`<= e + 1`, by
  `card_le_succ_radius_of_rigid` applied to the `g` produced above).

### Deployed form

**[MC] `Root.CodingTheory.KoalaRow.prizeBreaking_forces_ambiguity`,
`prizeBreaking_ambiguity_lower_bound`, `prizeBreaking_ambiguity_projective`,
`ambiguity_fraction_of_line`**
(`RequestProject/Root/CodingTheory/KoalaBearOrbitThreeAmbiguity.lean`).

On the deployed row, at any radius `e <= n = 2^21`, a `d = 3` pencil with
`#Bad > B*` satisfies

```
274980725978591499 * (p - 1)  <=  #ambigSet * (p + 1)
```

hence

```
#ambigSet >= 274980725720479240  >=  128000000 * (p - 1) .
```

Because ambiguity is scale invariant, the ambiguous locus is a union of punctured rational
lines through the origin, so this reads as **more than `1.28 * 10^8` ambiguous points of
`PG(2,p)`** — approximately `1.29 * 10^8`, i.e. again about `1/17`, but now of `p + 1`, the
size of a **line** of `PG(2,p)` (`ambiguity_fraction_of_line`), rather than of the whole
plane.

---

## 4. Where this leaves the `d = 3` gate

* Outcome (4) of the task statement is achieved for the route that was on the table:
  §2 is a **machine-checked barrier** showing that no bound on the close-direction locus, and
  no bound on the number of commonly-correctable planes, can eliminate `d = 3`.  The 6.05 %
  figure of the plane is not the obstruction; the obstruction is exactness.
* Outcome (3) is achieved in the corrected form: §3 derives a genuinely new, unconditional
  relation on the rational covectors of the orbit 3-space.  It does not push the *close*
  locus below `B*` (§2 forbids that), but it pushes the requirement from a plane-sized
  proximity statement to a line-sized **two-codeword** statement.
* Outcome (1) — `d = 3` Prize-safe, gate upgraded to `d >= 4` — is **not** achieved and is
  now reduced to a sharply stated question:

  > **[CB] Open.** Can a rational 3-space over `F_{p^6}` with `D = mu_{2^21}`, `k = 2^20`,
  > `e <= 2^21` have `>= 1.28 * 10^8` projective rational directions at which the
  > `RS_k(D)` list of radius `e` has size `>= 2`?

  At the deployed excess `t = 67472` the Johnson/Guruswami–Sudan radius is far below `e`, so
  ambiguity is not a priori excluded pointwise; what is now needed is a bound on the number
  of ambiguous directions *inside one 3-space*, i.e. a list-size statement for a
  two-dimensional family of words rather than for a single word.  This is the first
  formulation of the `d = 3` problem in which the required object is a **pair** of codewords,
  which is what makes list-decoding machinery (rather than pure incidence counting)
  applicable.
* Outcome (2) — a genuine `d = 3` counterexample scaling to the deployed row — remains
  unfound; the small-model census of §1 indicates that the known sharpness mechanism lives at
  excess `t <= 1` and does not scale to `t = 67472`.

## 5. Files

| file | content |
|---|---|
| `analysis/orbit3_plane_census.py` | exhaustive/sampled census of `closeProj`, `planeAll`, `planeExact` |
| `analysis/orbit3_plane_search.py` | hill-climbing search for maximal `planeExact` |
| `RequestProject/Root/CodingTheory/CrossThree.lean` | `dot3`/`cross3` algebra, perp-basis coordinates |
| `RequestProject/Root/CodingTheory/OrbitThreeLocusBarrier.lean` | §2, the locus barrier |
| `RequestProject/Root/CodingTheory/OrbitThreeAmbiguity.lean` | §3, the dichotomy |
| `RequestProject/Root/CodingTheory/KoalaBearOrbitThreeAmbiguity.lean` | §3, deployed numbers |
