# FREE-CHALLENGE RESIDUAL INCIDENCE LOCUS — deep mission report

**Mission.** Study the free-challenge residual incidence object intrinsically and decide
whether it yields a theorem, an obstruction or a reduction for MCA / Grand MCA.  Do not
restrict to proving the conjectured inequality `Σ_i (c_i − 1) ≤ 2κ − 1`.

**Status of everything below.** Section §I–§II, §IV, §V, §VII, §VIII, §X contain
paper-level derivations (elementary linear algebra and Schubert calculus); §III, §VI, §IX
contain *exact finite-field measurements* (integer arithmetic mod a prime — no floating
point, no sampling error in the verified claims).  Reproduction: `analysis/fcri_lib.py`,
`analysis/fcri_counterexample.py`, `analysis/fcri_reanalyse.py`,
`analysis/fcri_verify_record.py`, `analysis/fcri_frontier.py`, `analysis/fcri_exhaust.py`,
`analysis/fcri_lean_bridge_check.py`, `analysis/fcri_cashout.py`, data in
`analysis/fcri_data/`.

**Lean.**  The stop rule forbids Lean *unless* one of A–D occurs.  Outcome D occurred (a
scalable counterexample), so exactly that one object was formalised: §XII records the
machine-checked file `RequestProject/Root/CodingTheory/CommonWindowPencil.lean`, which
proves the counterexample family and the resulting lower bound `ε_mca ≥ (e+1)/|F|` with no
`sorry` and no new axioms.  Everything else below remains paper-level or experimental.

**Notation** (the project's).  `D ⊆ F_q^*`, `|D| = n`, `C = RS_k(D)`, `κ = n − k`,
`c = n − k − e`, `δ = e/n`, `ρ = k/n`.  A line is a pair of words `(f₀,f₁)`.
`IsCloseOn k S f` = `f` agrees on `S` with a polynomial of degree `< k`.
`IsBad k e f₀ f₁ γ` = `∃ S, |S| ≥ n − e`, `f₀+γf₁` close on `S`, and the whole line is
**not** close on `S`.  By `line_closure` the last clause is equivalent to
`¬ IsCloseOn k S f₁`, so **the FULL-MCA clause is part of `IsBad` itself, per challenge**.
Windows: `S_i` a maximal agreement window of `f₀+γ_i f₁`, `Z_i = D∖S_i`, `c_i = |S_i|−k`,
`A_i = ∏_{z∈Z_i}(X−z)`, `R_i = A_i·F[X]_{<c_i} ⊆ P = F[X]_{<κ}`, `V_i = R_i^⊥`.

---

## THE 17 REQUESTED ITEMS — SHORT ANSWERS

| # | item | answer |
|---|---|---|
| 1 | canonical object | line ↔ 2-plane in `V = F^D/C`; incidence with the arrangement of error subspaces `L_Z`; = Schubert intersection in `Gr(2,κ)`; = rank locus of a linear pencil `Σγ_iB_i` |
| 2 | exact quantifiers | `∀` instance `∃!` line; `∀` bad `γ` the incidence holds with **its own** window; all bad `γ` sit on **one** line simultaneously |
| 3 | BadMCA bridge | valid and simultaneous, with no witness-choice ambiguity (§IV); the *regular* restriction is what breaks simultaneity |
| 4 | why `c_i − 1` | Schubert codimension of "a line meets a codim-`c_i` subspace"; the saved unit **is** the free challenge `γ_i` (position of the intersection point on the line).  Uniform for unequal `c_i` |
| 5 | falsification size | 18 certified counterexample rows (`n = 10 … 1024`); 543 stored regular families re-analysed; 370 new certified regular families from ≈`10^6` gauge-reduced challenge vectors in the pencil form; **13 fully exhaustive sweeps over *every* MCA line** (`q ≤ 11`, `n ≤ 8`, ≈`4.4·10^6` lines carrying a bad challenge, `analysis/fcri_data/exhaust.json`); 6 independent re-verifications of the Lean instance against the faithful `IsBad` scan |
| 6 | max `E` | unbounded: `E = Σ(c_i−1) − (2κ−1) = (e+1)(c−1) − (2κ−1) = Θ(n²)`; `E ≥ 48 384` verified at `n = 1024`; `E ≥ 2^36` at the prize row |
| 7 | counterexample | **YES** — the *common-window pencil*, exact, scalable, strictly inside unique decoding; now also a **Lean theorem** (`free_challenge_cap_fails`) |
| 8 | dimension / codimension | `dim Gr(2,κ) = 2κ−4`; each window costs exactly `c_i − 1`; expected `dim = 2κ−4−Σ(c_i−1)`; in challenge space codim `Σc_i − 2κ + 1` inside an `(m−2)`-dimensional gauge-reduced space |
| 9 | exceptional components | two: (a) *pair components* — all `Z_i` inside one `(e+1)`-set (this is the counterexample and it is exactly `MCAPairCover`); (b) *window-growth degenerations* on the boundary of a stratum (the observed `+1` over the Schubert count) |
| 10 | canonical ideal | maximal minors of the linear pencil `N(γ) = Σ_i γ_i B_i` (`Σ_i B_i = 0`); for `Σc_i = 2κ` a **single** polynomial `det N(γ)`, homogeneous of degree `κ` and affine-gauge invariant |
| 11 | relations | see the table in §VII — `SAME OBJECT` as the stacked residual matrix `M`, `PROJECTION` of the Welch–Berlekamp pencil, `DEGENERATION` to `MCAPairCover`, `INDEPENDENT` of grading/quotient sectors |
| 12 | strongest true inequality | unrestricted: **none** beyond the trivial `Σ(c_i−1) ≤ m(κ−1)`.  Regular: `Σ_i (c_i−1) ≤ 2κ−3`, in **913/913** certified regular families (543 stored + 370 newly generated) and attained; the Schubert count `2κ−4` is exceeded, always by exactly `+1`, in 10 of them |
| 13 | `#Bad` consequence | the cap would give `#Bad ≤ 4` at `δ=1/4`; the exact counterexample gives `#Bad ≥ e+1 = 2^18` at the same row — the cap is off by `2^16`.  The regular version bounds only the regular stratum, by `O(1)` |
| 14 | target-row consequence | at `n=2^20, k=2^19` all radii give a cap value `3…20`, i.e. `ε_mca ≤ 2^-183.9…2^-181.6`, ≈`0.000000` bits of protocol gain (cf. `KOALAIRS12_PRIZE_GAP_AUDIT.md`); the *radius window*, not the constant, is what could reach the score |
| 15 | new invariants | the challenge space of a fixed `(f₁, windows)` is a **linear** subspace `G(u) ⊆ F^m` containing `1`; `Σ_i B_i = 0` (gauge); `regular ⟺ R_i∩R_j = 0`; `regular ⟹ 2e ≥ κ`; `w = dim ΣR_i = κ` in 543/543 records; rank-deficiency frequency `≈ q^{-t}` |
| 16 | status | **KILL** for the conjectured cap (stop-rule outcome D, and the kill is now formalised — §XII); **PROMISING** for the regular-stratum version (not prize-sufficient on its own, and not yet READY-FOR-LEAN) |
| 17 | one next lemma | §XVII — the *regular charging lemma* (pairwise transversality + the pencil), stated there in full |

---

## I. THE CANONICAL OBJECT

### I.0 Elimination of everything that is not needed

Start from the raw MCA variables `f₀,f₁ ∈ F^D`, `γ₁..γ_m ∈ F`, windows `S_i`, the
interpolating polynomials `p_i` of degree `< k`, and the residual words.  Three
eliminations are forced:

1. **`p_i` and the residuals are redundant.**  `f₀+γ_if₁` is close on `S_i` iff the class
   of `f₀+γ_if₁` in `V := F^D/C` is represented by a word supported in `Z_i = D∖S_i`.
2. **`f₀,f₁` only matter modulo `C`.**  All predicates (`IsCloseOn`, `IsBad`) are invariant
   under adding codewords, so the state space is `V × V`, `dim V = κ`, not `F^D × F^D`.
3. **The parameterisation `γ` is a gauge.**  `(f₀,f₁) ↦ (af₀+bf₁, cf₀+df₁)` is invisible to
   the geometry and moves `γ` by a Möbius transformation; the subgroup fixing the marked
   direction `[f₁]` is the affine group `γ ↦ aγ+b`.

What is left is the **canonical object**:

> Let `V = F^D/C ≅ F^κ`.  For `Z ⊆ D` with `|Z| ≤ κ` let `L_Z := (F^Z + C)/C ⊆ V`; because
> `C` is MDS, `dim L_Z = |Z|`.  An MCA line is a **2-plane** `L̄ = ⟨[f₀],[f₁]⟩ ⊆ V` with a
> **marked point** `[f₁] ∈ P(L̄)`; `γ` is bad at radius `e` iff the point `[f₀+γf₁]` of the
> projective line `P(L̄)` lies on some `L_Z` with `|Z| ≤ e` and `[f₁] ∉ L_Z`.
>
> **FREE-CHALLENGE RESIDUAL INCIDENCE LOCUS** := the locus of 2-planes meeting the
> subspaces `L_{Z_1},…,L_{Z_m}` in `m` *distinct* points, no one of which is the marked
> point.

This is the smallest object retaining exactly the `BadMCA` information: the `γ_i` are not
extra variables, they are the *coordinates of the intersection points* in the marked
affine chart of `P(L̄)`.

### I.1 Affine formulation

`(φ₀,φ₁) ∈ P^* × P^* ≅ F^{2κ}` (syndromes; `P^* ≅ V`), `γ ∈ F^m`:

```
Inc_aff = { (φ₀,φ₁,γ) : R_i(φ₀ + γ_i φ₁) = 0 for all i,  R_iφ₁ ≠ 0 for all i,  γ_i distinct }.
```

`Σ_i c_i` bilinear equations in `2κ + m` unknowns.  Contains the 4-dimensional `GL₂` gauge
orbit of every solution.

### I.2 Projective formulation

`Inc ⊆ Gr(2,V) × (P^1)^m`, or after eliminating the (determined) intersection points,

```
Inc = ⋂_{i=1}^m σ(L_{Z_i}),      σ(K) := { L ∈ Gr(2,V) : L ∩ K ≠ 0 },
```

an intersection of `m` special Schubert varieties, intersected with the open condition
"the `m` intersection points are pairwise distinct".  This is the natural home of the
object: `σ(K)` is the classical variety of *lines meeting a linear subspace*.

### I.3 Determinantal formulation

Stack the residual bases: `R ∈ F^{(Σc_i)×κ}`, blocks `R_i`.  With
`Γ(γ) = diag(γ_i·I_{c_i})`,

```
M(γ) = [ R | Γ(γ)R ] ∈ F^{(Σc_i) × 2κ},     Inc_aff = { (φ,γ) : M(γ)·(φ₀,φ₁)ᵀ = 0 }.
```

`γ` is in the image of the projection iff `rank M(γ) ≤ 2κ − 1`.

### I.4 Module / subspace formulation

`N_i := R_i ∩ L̄^⊥ ⊆ P`.  Under FULL-MCA `dim N_i = c_i − 1` exactly (`R_i ⊆ ψ_i^⊥` and
`R_i ⊄ ψ_j^⊥` for `j ≠ i`, else `f₁` would be close on `S_i`).  So the object is:

```
m subspaces N_i ⊆ L̄^⊥  (dim κ−2)  with dim N_i = c_i − 1,
N_i ⊆ R_i = A_i F[X]_{<c_i},  and  Σ_i N_i ⊆ L̄^⊥.
```

The failure of the naive bound `Σ(c_i−1) ≤ κ−2` is precisely the **syzygy module**
`{(h_i) : Σ_i A_i h_i = 0, deg h_i < c_i}`.

### I.5 Elimination onto challenge space (the working form)

Let `Q` be a basis of the left null space of `R` (`QR = 0`), and
`B_i := Q[:,\text{block } i]·R_i`.  Eliminating `φ₀`:

```
N(γ) := Q Γ(γ) R = Σ_i γ_i B_i ,      N(γ)·φ₁ = 0 .
```

**`N` is a linear pencil in the challenges**, of size `(Σc_i − κ) × κ`, and

```
Σ_i B_i = Q R = 0 ,
```

so `N(γ+b·1) = N(γ)` and `N(λγ) = λN(γ)`: the pencil is invariant under exactly the affine
gauge.  The projected locus is

```
BadLocus(Z₁..Z_m) = { γ mod (γ ↦ aγ+b) : rank N(γ) < κ },
```

a **rank-deficiency locus of a gauge-invariant linear matrix pencil**, verified numerically
(`Σ B_i = 0` and the codimension law, §V).

---

## II. WHY `c_i − 1` AND NOT `c_i` — THE EXACT MECHANISM

Fix the 2-plane `L̄`.  The condition contributed by window `i` is `L̄ ∩ L_{Z_i} ≠ 0`, i.e.
`L̄ ∈ σ(L_{Z_i})`.  `L_{Z_i}` has codimension `c_i` in `V`.  The Schubert variety of lines
of `P(V) = P^{κ−1}` meeting a fixed linear subspace of codimension `c_i` has

```
codim σ(L_{Z_i}) = c_i − 1     in     Gr(2,κ)  (dim 2κ−4).
```

**The saved dimension is the position of the intersection point along the line** — and in
the MCA dictionary that position *is* the challenge `γ_i`.  Concretely: imposing
`φ₀+γφ₁ ∈ L_{Z_i}` for a *frozen* `γ` is `c_i` conditions; letting `γ` move restores one
dimension, because the incidence point is free to slide along `P(L̄)`.

This is a **Schubert/incidence effect**, not parameter counting, and it is the answer to
the mission's list:

* not projectivisation (that is a further, global, `−3`, see §V);
* not a pencil symmetry, syzygy or hidden gauge specific to `M31`/Mersenne;
* it is the free scalar `γ_i`, but in its correct geometric role: the intersection
  point of a line with a subspace, whose *position* costs nothing.

**Unequal `c_i`.**  Nothing in the argument couples the windows: the codimension of
`σ(L_{Z_i})` is `c_i − 1` for each `i` separately, so the `−1` is per window and is
independent of the other `c_j`.  This is confirmed experimentally on families with
unequal profiles (e.g. `c = (12,15,12,12,12,12)` at `n=48`, and profiles
`(4,3,3,3,3,3)`, `(6,5,4,4,4,4)`, … in `analysis/fcri_frontier.py`).

**Two exact structural consequences** (elementary, proved here, worth keeping):

* `dim (R_i ∩ R_j) = max(0, |S_i∩S_j| − k)`.  Hence
  **regularity `|S_i∩S_j| ≤ k` ⟺ pairwise transversality `R_i ∩ R_j = 0`**.
* `|S_i∩S_j| ≥ |S_i|+|S_j|−n ≥ n−2e`, so regularity forces `n−2e ≤ k`, i.e.
  **`2e ≥ κ`: the regular branch is empty below the unique-decoding radius.**

---

## III. AGGRESSIVE FALSIFICATION — THE CAP IS FALSE

### III.1 The common-window pencil (counterexample family)

Fix `D, k, e` with `c = n−k−e`.  Split `D = T ⊔ Y`, `|T| = n−e−1 = k+c−1`, `|Y| = e+1`.
Put

```
f₀ = u₀ ,  f₁ = u₁      both supported on Y,      u₁(x) ≠ 0 for all x ∈ Y,
γ_x := −u₀(x)/u₁(x)     pairwise distinct  (x ∈ Y).
```

Then for each `x ∈ Y`:

* `f₀+γ_x f₁` vanishes on `S_x := T ∪ {x}`, i.e. agrees there with the **zero** codeword,
  and `|S_x| = n−e`;
* `f₁` agrees with no degree-`<k` polynomial on `S_x` (it vanishes on `T`, `|T| ≥ k`, so
  the only candidate is `0`, and `f₁(x) ≠ 0`);
* hence `IsBad k e f₀ f₁ γ_x` holds, with `c_x = |S_x| − k = c` (`= c` exactly when
  `e < c`, i.e. strictly inside unique decoding, where the maximal window is unique);
* `dist(f₁,C) = e+1 > e`, so **the line has no correlated agreement at radius `e`**: this
  is a genuine MCA instance, not a degenerate one.

Therefore `m = e+1` distinct FULL-MCA bad challenges with maximal windows and

```
Σ_i (c_i − 1) = (e+1)(c−1)      vs      2κ − 1 = 2(e+c) − 1 ,
E = (e+1)(c−1) − (2κ−1) > 0    as soon as   e(c−3) > c .
```

### III.2 Exact verification

`analysis/fcri_counterexample.py`, output `analysis/fcri_data/counterexample.log`.
Every row has `2e < κ` (**strictly inside the unique-decoding radius**, hence far inside
Johnson).  Badness is checked against the `IsBad` predicate itself; maximal windows are
computed by Berlekamp–Welch (exact in this regime) and, for `n ≤ 18`, cross-checked by
brute-force enumeration of *all* admissible windows.

| n | k | e | c | κ | q | ρ | δ | m | c_i | Σ(c_i−1) | 2κ−1 | **E** |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 1 | 2 | 7 | 9 | 17 | 0.100 | 0.200 | 3 | 7 | 18 | 17 | **+1** |
| 11 | 1 | 3 | 7 | 10 | 17 | 0.091 | 0.273 | 4 | 7 | 24 | 19 | **+5** |
| 15 | 6 | 4 | 5 | 9 | 17 | 0.400 | 0.267 | 5 | 5 | 20 | 17 | **+3** |
| 16 | 6 | 4 | 6 | 10 | 29 | 0.375 | 0.250 | 5 | 6 | 25 | 19 | **+6** |
| 21 | 8 | 5 | 8 | 13 | 37 | 0.381 | 0.238 | 6 | 8 | 42 | 25 | **+17** |
| 25 | 10 | 6 | 9 | 15 | 43 | 0.400 | 0.240 | 7 | 9 | 56 | 29 | **+27** |
| 30 | 14 | 7 | 9 | 16 | 59 | 0.467 | 0.233 | 8 | 9 | 64 | 31 | **+33** |
| 32 | 16 | 4 | 12 | 16 | 97 | 0.500 | 0.125 | 5 | 12 | 55 | 31 | **+24** |
| 64 | 32 | 8 | 24 | 32 | 193 | 0.500 | 0.125 | 9 | 24 | 207 | 63 | **+144** |
| 128 | 64 | 16 | 48 | 64 | 257 | 0.5 | 0.125 | 17 | ≥48 | ≥799 | 127 | **≥+672** |
| 256 | 128 | 32 | 96 | 128 | 521 | 0.5 | 0.125 | 33 | ≥96 | ≥3135 | 255 | **≥+2880** |
| 512 | 256 | 64 | 192 | 256 | 1031 | 0.5 | 0.125 | 65 | ≥192 | ≥12415 | 511 | **≥+11904** |
| 1024 | 512 | 128 | 384 | 512 | 2053 | 0.5 | 0.125 | 129 | ≥384 | ≥49407 | 1023 | **≥+48384** |

18/18 rows violate the cap; all are `FULL-MCA`, all windows maximal (verified up to
`n = 64`; for the four largest rows each of the `e+1` challenges is verified individually,
so the listed `Σ` is a lower bound and `E` only grows).

**Smallest counterexample found: `n = 10, k = 1, e = 2, q = 17`, `E = +1`.**  At fixed
rate and radius `E = Θ(n²)`.

### III.3 What the previous searches missed, and why

Every counterexample is **irregular**: `|S_i ∩ S_j| = |T| = n−e−1 > k`.  The whole previous
campaign (495 witnesses, annealing, quarter-pairs, maximiser) enforced regularity
`max_{i<j}|S_i∩S_j| ≤ k` as a standing hypothesis, and the mission statement dropped it.
By §II, regularity is impossible below the unique-decoding radius, so in the entire
unique-decoding regime the "regular free-challenge cap" says **nothing at all**, while the
common-window pencil says `#Bad ≥ e+1`.

Other classes explored and their outcome (all negative for the cap *with* regularity):

* gauge-reduced sweep of challenge space in the pencil form (`fcri_frontier.py`) for
  profiles with `Σc_i = 2κ … 2κ+4` at `(n,k,e) = (12,3,6), (16,4,8), (16,6,7)`, two
  primes — 370 certified regular families, best margin `−2` against `2κ−1` (§VI);
* re-analysis of all 543 stored window families of the previous mission
  (`fcri_reanalyse.py`);
* unequal-`c_i` profiles, maximal windows recomputed from the reconstructed `f₀,f₁` in
  every case.

### III.4 Fully exhaustive sweeps (every MCA line, small parameters)

`analysis/fcri_exhaust.py` enumerates, in the quotient picture of §I.4, **every** MCA line
up to the gauge group (`f₁`-direction a projective point of `V`, `f₀` modulo `⟨f₁⟩`), for
all radii `1 ≤ e < κ`, and records both `Σ = Σ(c_i−1)` over the *whole* bad family and
`Σ_reg`, its maximum over pairwise-regular subfamilies.  Result (13 rows, ≈`4.4·10⁶` lines
carrying at least one bad challenge, `analysis/fcri_data/exhaust.json`):

| `q` | `n` | `k` | `κ` | `e` | `max Σ` | `2κ−1` | `max Σ_reg` | `2κ−4` |
|---|---|---|---|---|---|---|---|---|
| 5 | 5 | 2 | 3 | 1,2 | 2 | 5 | 2 | 2 |
| 7 | 6 | 2 | 4 | 1 | 4 | 7 | 3 | 4 |
| 7 | 6 | 2 | 4 | 2,3 | 6 | 7 | 3 | 4 |
| 7 | 6 | 3 | 3 | 1,2 | 2 | 5 | 2 | 2 |
| 7 | 7 | 3 | 4 | 1 | 4 | 7 | 3 | 4 |
| 7 | 7 | 3 | 4 | 2,3 | 6 | 7 | 3 | 4 |
| 11 | 8 | 4 | 4 | 1 | 4 | 7 | 3 | 4 |
| 11 | 8 | 4 | 4 | 2,3 | **7** | 7 | **4** | 4 |

Two things follow, and they are consistent with §III.1–III.2 rather than in tension with
it:

1. For `κ ≤ 4` the cap `2κ−1` is **true and attained** (`Σ = 7 = 2κ−1` at `q=11, n=8,
   k=4`).  This is why every earlier small-scale search saw the cap survive: the
   counterexample needs `(e+1)(κ−e−1) > 2κ−1`, whose smallest solution is `κ = 9`,
   `e = 2` — out of exhaustive reach in the quotient enumeration (`q^{2κ−2}` lines).
2. In every exhausted row `Σ_reg ≤ 2κ−4`, the Schubert count, with equality attained —
   further support for the regular statement of item 12.

Finally, `analysis/fcri_lean_bridge_check.py` rebuilds the *Lean* instance of §XII over
`GF(q)` and re-runs the faithful `IsBad` scan on it: for
`(q,n,k,e) ∈ {(17,10,1,2), (17,12,2,2), (23,14,3,3), (29,16,4,3), (29,20,5,4),
(37,24,6,5)}` the bad set is exactly the predicted block `Y` (`#Bad = e+1`), every window
is a **maximum**-agreement window of size `n−e`, and `E = +1, +2, +7, +9, +21, +37`
respectively, all with `2e < κ`.

---

## IV. QUANTIFIER / PROJECTION AUDIT

**The implication `γ ∈ BadMCA ⇒ γ occurs in the incidence locus` is valid, and it is
simultaneous.**  In detail:

1. `IsBad k e f₀ f₁ γ` gives `∃S`, `|S| ≥ n−e`, `f₀+γf₁` close on `S`, line not close on
   `S`.  By `line_closure` the last clause is `¬IsCloseOn k S f₁`.
2. Let `p` be the codeword witnessing closeness on `S` and let `S^max` be its full
   agreement set (`S ⊆ S^max`).  Then `f₁` is **still** not close on `S^max`, because
   closeness on a set implies closeness on every subset.  So *enlarging the window never
   destroys the FULL-MCA clause* — the maximal-window normalisation is free.
3. `c_γ := |S^max| − k ≥ c ≥ 1`, and `Z_γ = D∖S^max` has `|Z_γ| ≤ e`.
4. In `V = F^D/C`: `[f₀+γf₁] ∈ L_{Z_γ}` and `[f₁] ∉ L_{Z_γ}`.  This is exactly one
   incidence of the canonical object.
5. **Simultaneity.**  All bad challenges of one instance refer to the *same* pair
   `(f₀,f₁)`, hence to the *same* 2-plane `L̄` and the same marked point.  There is no
   choice of "which line" and no per-challenge existential that could be incompatible: the
   window `Z_γ` is attached to `γ` alone.  Distinct `γ` automatically give distinct
   windows (if `S_i = S_j` then `(γ_i−γ_j)f₁` would be close on it, contradicting FULL-MCA).
   So the whole bad set can be charged in one incidence system.
6. **Residual multi-valuedness, and it is harmless.**  A coset may contain several
   minimum-weight representatives; then several maximal windows exist for the same `γ`.
   `c_γ` is nevertheless well defined (`= κ − minweight` restricted to windows on which
   `f₁` is not close), and any choice yields a valid incidence.  Different choices change
   the point of `Gr(2,κ)`'s Schubert conditions but not the statistic.
7. **What is *not* transportable.**  The *regularity* hypothesis is a property of the
   *family*, not of individual challenges.  A single MCA instance can (and, by §III,
   generically does) have a bad set that is nowhere regular.  Charging the whole bad set
   by a regular cap is therefore **invalid**; one must first split the bad set:

```
Bad = Bad_reg ⊔ Bad_pair,     γ,γ' pair-related  :⟺  |S_γ ∩ S_{γ'}| ≥ k+1
                                              ⟺  f₁ is close on S_γ ∩ S_{γ'}
                                              ⟺  a codeword PAIR explains both.
```

The pair-related classes are exactly the objects of `MCAPairCover` /
`AffineFactorSplit`; the incidence cap (if true) bounds only an *independent set* in the
pair-relation graph.  **This is the exact logical bridge, and the exact obstruction.**

---

## V. GEOMETRY OF THE LOCUS

Ambient and expected numbers, for a fixed window profile `(c_1,…,c_m)`:

| quantity | value |
|---|---|
| ambient (Grassmann form) | `dim Gr(2,κ) = 2κ − 4` |
| ambient (affine form) | `2κ + m` |
| ambient (challenge form, gauge-reduced) | `m − 2` |
| codimension of one incidence | `c_i − 1` (Schubert), equivalently `c_i` conditions minus the free `γ_i` |
| codimension of the projected locus in challenge space | `t := Σ_i c_i − 2κ + 1` |
| expected dimension of `Inc ⊆ Gr(2,κ)` | `2κ − 4 − Σ_i (c_i − 1)` |
| expected dimension of the gauge-reduced challenge locus | `m − 2 − t = 2κ − 3 − Σ(c_i−1)` |
| generic fibre of `Inc_aff → Inc` | `4` (the `GL₂` gauge) |
| generic fibre over a point of the challenge locus | `1` (the scaling of `φ₁`; `φ₀` is then determined, since `ker R = 0` whenever `w = κ`) |
| degree of the projection onto `γ`-space | `1` on the regular branch (γ determines `L̄` uniquely) |

The two expected dimensions differ by `1` because the marked point `[f₁]` is a free extra
parameter of the challenge picture that cannot rescue an empty `Inc`; the **binding**
count is therefore the Grassmann one:

```
   nonempty (generic strata)   ⟹   Σ_i (c_i − 1) ≤ 2κ − 4 .
```

**Measured.**  `Σ B_i = 0` and the codimension law were verified directly: for
`(n,k,e,q) = (12,3,6,13)` with six windows and `t = 1`, an exhaustive gauge-reduced sweep
found `616` rank-deficient challenge vectors out of `7920`, i.e. a fraction
`0.0778 ≈ 1/13 = q^{-t}` — a codimension-1 hypersurface, exactly as predicted.

**Nature of the failure locus.**  Determinantal *plus* exceptional components:

* the **determinantal / Schubert branch**: `rank N(γ) < κ` for the linear pencil, an
  intersection of special Schubert varieties, of the expected codimension in every case
  measured;
* **exceptional pair components**: all `Z_i` contained in a common set `Y` of size `e+1`
  (the counterexample of §III).  Then the whole configuration lives inside `L_Y` (dim
  `e+1`) and the Schubert count in `Gr(2,κ)` is irrelevant, because the line and *all*
  subspaces degenerate into a small common ambient.  These components are irregular by
  construction and are precisely the `MCAPairCover` stratum;
* **window-growth degenerations**: the closure of the stratum of a profile
  `(c_1,…,c_m)` meets deeper strata where some window grows.  This is what produces the
  single observed `+1` over the Schubert bound (§VI): a family seeded with profile
  `(12,12,12,12,12,12)` (`Σ(c_i−1) = 66 ≤ 68`) realised the profile
  `(12,15,12,12,12,12)` (`Σ(c_i−1) = 69 > 68`).

**Singular locus / components.**  On the regular branch with `w = dim Σ_iR_i = κ`
(543/543 measured records) the kernel of `N(γ)` is 1-dimensional at a generic point of the
locus; higher corank is the leave-one-out degeneracy `⋂_{j≠i}V_j ≠ 0` identified by the
previous mission, and every such solution violates FULL-MCA on `m−1` windows — i.e. the
singular locus of the incidence variety is exactly the non-FULL-MCA locus.

---

## VI. THE STRONGEST TRUE STATEMENT

The unrestricted statistic is unbounded (§III), so the only surviving statements carry
regularity, i.e. live at radii `δ ≥ (1−ρ)/2`.

**Evidence base.**  543 stored regular FULL-MCA families with maximal windows
(`fcri_reanalyse.py`), spanning `n = 8 … 512`, 32 parameter rows, both on and below
Johnson, plus the new exhaustive pencil sweeps.  For every one of them:

```
       Σ_i (c_i − 1)  −  (2κ − 4)   ∈  {−13, −9, −5, −4, −3, −2, −1, 0, +1}
       counts:                          1    1    1    2   12  392  74  59   1
```

* `Σ(c_i−1) ≤ 2κ−1` (conjecture): margin `≤ −2` everywhere; **never within 2 of the cap**;
* `Σ(c_i−1) ≤ 2κ−4` (Schubert/expected): attained `59` times, exceeded **once**, by `+1`;
* `Σ(c_i−1) ≤ 2κ−3`: **never exceeded**;
* the weaker radius-level form `m·(c−1) ≤ 2κ−1` (which is what a `#Bad` bound needs):
  margin `≤ −3` everywhere.

**Second, independent evidence base (completed after the first draft).**  The pencil-form
campaign `fcri_frontier.py` finished: **370 freshly generated, certified regular FULL-MCA
families** over four parameter rows (`q=13,n=12,k=3,e=6`: 75; `q=37,n=12,k=3,e=6`: 160;
`q=17,n=16,k=4,e=8`: 59; `q=17,n=16,k=6,e=7`: 76), each with windows recomputed from the
reconstructed `f₀,f₁` and re-checked against the FULL-MCA predicate
(`analysis/fcri_data/frontier.json`, log `frontier.log`).  Margins:

```
       Σ_i (c_i − 1)  −  (2κ − 4)   ∈  {−4, −3, −2, −1, 0, +1}
       counts:                          5   15  172  96  73   9
```

so `2κ−4` is attained 73 times and exceeded 9 times, always by exactly `+1`; the best
margin against the conjectured cap is `−2` (`n=16, k=4, e=8, q=17, Σ = 21 = 2κ−3`).  The
`+1` excess is therefore *not* an isolated accident of the single stored record: it recurs
in three independent parameter rows, always with value exactly `+1`, and never twice.
Combining the two bases (543 stored + 370 new = 913 certified regular families):
**`Σ(c_i−1) ≤ 2κ−3` holds in 913/913 cases and is attained; `Σ(c_i−1) ≤ 2κ−2` was never
needed, and `2κ−1` was never approached closer than `−2`.**

The single `+1` record (`n=48, k=12, e=24, q=193, m=6, Σ=69, κ=36`) was re-certified from
scratch (`fcri_verify_record.py`): distinct challenges ✓, windows are genuine agreement
sets ✓, `|S_i| ≥ n−e` ✓, FULL-MCA ✓, maximal for their own codeword ✓, regular
(`maxint = 12 = k`) ✓, `w = κ = 36` ✓, `R_i` pairwise transverse ✓.  Its excess over the
Schubert count is entirely explained by window growth (§V).

**Strongest statement supported by all data:**

```
(REG-CAP)   If γ_1..γ_m (m ≥ 2) are distinct bad challenges of one line at radius e,
            with maximal windows S_i, c_i = |S_i| − k, and the family is REGULAR
            (|S_i ∩ S_j| ≤ k for i ≠ j, equivalently R_i ∩ R_j = 0), then

                       Σ_i (c_i − 1)  ≤  2κ − 3 ,

            and Σ_i (c_i − 1) ≤ 2κ − 4 whenever no window exceeds its stratum
            (i.e. for the profile that the incidence stratum was cut out with).
```

Weaker, more robust, and sufficient for counting:

```
(REG-COUNT) regular  ⟹  m ≤ (2κ−3)/(c−1) + 1 = O(1) at fixed rate and radius.
```

Neither is proved.  Both are consistent with every exact measurement in this project.

---

## VII. RELATION TO THE EXISTING PROJECT OBJECTS

| object | relation | justification |
|---|---|---|
| stacked residual matrix `M` (`REGULAR_RANK_CAP_KILL_REPORT`) | **SAME OBJECT**, different coordinates | `M(γ) = [R \| Γ(γ)R]`; the incidence locus is `{rank M(γ) ≤ 2κ−1}`; §I.3 |
| Welch–Berlekamp pencil `u₀+γu₁` | **PROJECTION** | WB works with a *fixed* codeword pair; the incidence object is the WB degeneracy after eliminating the codewords.  A WB minor is one equation of the ideal of §VIII |
| `W_can` / subresultants (`SubresultantCore`) | **SPECIAL CASE** — the `m = 1`, `T = k` layer | the subresultant/gcd degeneracy is exactly the condition that *one* window is larger than `k`; it cuts out one factor of the incidence ideal, not the whole locus |
| syndrome / Hankel matrices | **SAME OBJECT** (dual coordinates) | `R_i` is the shortened dual code of `S_i`; the rows of `M` are syndrome functionals |
| `codewordLocus` | **DEGENERATION** | the sublocus where some `Z_i = ∅` (`c_i = κ`); this forces `m = 1` (see §X.4) |
| `AffineFactorSplit` | **DEGENERATION / same stratum** | the fibre of bad challenges over one codeword pair; this is the exceptional pair component of §V, which the counterexample realises |
| projective residual locus | **SAME OBJECT** | the projectivised form §I.2 |
| support-overlap geometry | **SAME OBJECT** in the discrete direction | `|S_i∩S_j| ≤ k ⟺ R_i∩R_j = 0`; the set-family Johnson bound bounds `m` from the same data |
| graded / quotient sectors | **INDEPENDENT** | the sector decomposition acts on `P` and is orthogonal to the incidence structure; the counterexample is nongraded and the incidence picture never uses `h \| n` |
| `MCAPairCover` | **COMPLEMENTARY** — the two halves of the bad set | §IV.7: `Bad = Bad_reg ⊔ Bad_pair`; the incidence object controls `Bad_reg`, `MCAPairCover` controls `Bad_pair` |
| `MCALowerBound` (`blockWord`) | **WEAKER SIBLING** | `blockWord` needs a fibre of size `≥ n−e`, hence at most `1/(1−δ)` bad challenges; the common-window pencil of §III gives `e+1` at the same radius, with the same `IsBad` predicate |

**Theorem reuse.**  Nothing new is needed for the pair branch: `card_badPairSet_le` and
`card_badSet_le_pairCover` already cover it.  What the incidence object could contribute
is exactly the *residual* (regular) term, which is currently the unproved part.

---

## VIII. CANONICAL POLYNOMIAL / IDEAL

For a fixed window profile the canonical ideal is

```
I(Z_1..Z_m) := ideal of maximal (κ×κ) minors of the linear pencil  N(γ) = Σ_i γ_i B_i ,
               Σ_i B_i = 0 ,   N of size (Σc_i − κ) × κ .
```

* `BadLocus ⊆ V(I)`, with equality on the FULL-MCA open part;
* `I` is homogeneous of degree `κ` and invariant under the affine gauge `γ ↦ aγ+b`;
* when `Σc_i = 2κ` the pencil is square and `I = (det N(γ))`: **one polynomial**, of degree
  `κ` in `m` variables, cutting out the free-challenge locus of that profile;
* the number of generators is `C(Σc_i−κ, κ)`, so the "single polynomial" form is available
  exactly on the `Σc_i = 2κ` stratum, which is the extremal stratum of the count.

For a **fixed MCA instance** (which is what a `#Bad` bound needs) the corresponding object
is *not* this pencil but the Welch–Berlekamp ideal: with `u_γ = f₀+γf₁`,

```
I_MCA(γ) = ideal of maximal minors of  WB(γ) ∈ F^{n×(k+2e+1)},
           WB(γ)[x, j] = u_γ(x)x^j   (j ≤ e)  |  −x^j  (j < k+e).
```

Each generator has degree `≤ e+1` in `γ`, so **`BadMCA ⊆ V(I_MCA)` with
`deg = e+1 = O(n)`** whenever some maximal minor is not identically zero — which happens
exactly below the forcing barrier `k+2e+1 ≤ n`, i.e. `δ ≤ (1−ρ)/2`.  The counterexample of
§III shows this degree bound is **tight**: it realises `e+1` distinct roots.  Above the
barrier the ideal is identically zero and the object degenerates — that, and not the
counting, is where the difficulty lives.

---

## IX. PRIZE CASH-OUT (derived, not assumed)

Row: `n = 2^20`, `k = 2^19`, `κ = 2^19`, `2κ−1 = 1 048 575`, `|F| = KoalaBear.Ext6`,
`log₂|F| = 185.9321` (`KOALAIRS12_PRIZE_GAP_AUDIT.md`).  `c = κ − e`.  The conversion
`#Bad ≤ ⌊(2κ−1)/(c−1)⌋` follows from `c_i ≥ c` and the cap; it is exact, not asymptotic
(`analysis/fcri_cashout.py`):

| radius | `e` | `c` | cap `#Bad ≤` | `ε_mca ≤` | **true `#Bad ≥ e+1`** |
|---|---:|---:|---:|---:|---:|
| `δ = 1/4` (project baseline, = UD) | 262144 | 262144 | 4 | `2^-183.93` | `2^18.00` |
| safe Johnson `(1−ρ)/3` | 174762 | 349526 | 3 | `2^-184.35` | `2^17.42` |
| Johnson `1−√ρ` | 307120 | 217168 | 4 | `2^-183.93` | `2^18.23` |
| `δ = 0.30` | 314572 | 209716 | 5 | `2^-183.61` | `2^18.26` |
| `δ = 0.35` | 367001 | 157287 | 6 | `2^-183.35` | `2^18.49` |
| `δ = 0.40` | 419430 | 104858 | 10 | `2^-182.61` | `2^18.68` |
| `δ = 0.45` | 471859 | 52429 | 20 | `2^-181.61` | `2^18.85` |

Three conclusions:

1. **The cap contradicts an exactly verified lower bound at the prize row itself.**  At
   `δ = 1/4` it predicts `#Bad ≤ 4`; the common-window pencil produces `#Bad ≥ 262 145`
   at exactly that `(n,k,e)`.  No repair by restricting the radius is possible: the
   counterexample exists at *every* radius with `c ≥ 2`.
2. **The counting side was never the bottleneck.**  Even `#Bad = e+1 = 2^18` is `2^39.9`
   below the Grand-MCA budget `2^57.93`, and by the audit the MCA constant is worth
   `0.000000` bits at the audited score.  What reaches the score is the **radius window**
   in which a theorem is valid, not the constant.
3. Consequently a free-challenge theorem is prize-relevant **only** if it extends the
   valid radius window (e.g. past `(1−ρ)/2` or past Johnson), not if it shrinks the
   constant.

---

## X. DISCOVERY MODE — INVARIANTS THAT SURVIVED EVERY EXAMPLE

1. **The challenge space is linear.**  Fix the windows and `f₁` (i.e. `u = Rφ₁`).  Then
   ```
   G(u) = { γ ∈ F^m : Γ(γ)u ∈ Im R } = { γ : Σ_i γ_i B_i φ₁ = 0 }
   ```
   is an `F`-**linear subspace** of `F^m` containing `1 = (1,…,1)`.  Bad configurations
   exist iff `dim G(u) ≥ 2`, and then the admissible challenge vectors form a linear
   space, not merely an algebraic set.  (Immediate consequence: the set of *challenge
   differences* of one instance and one window family is closed under `F`-linear
   combinations — a strong rigidity that no earlier project object exposed.)
2. **`Σ_i B_i = 0`** — the affine gauge is visible as a linear relation among the pencil
   coefficients.  Verified exactly on every family generated.
3. **`w = dim Σ_i R_i = κ` in 543/543 stored records** — the residual spaces always span
   the whole syndrome space; the refined cap `2(w−2)` therefore never beats `2κ−4` in
   practice.
4. **`c_i = κ` forces `m = 1`.**  If some window is all of `D` then `f₀+γ_if₁ ∈ C`, so
   `f₀ ≡ −γ_i f₁ mod C`, and every other bad challenge `γ_j` would give
   `(γ_j−γ_i)f₁ ≡ ε_j` supported in `Z_j`, i.e. `f₁` close on `S_j` — contradiction.
5. **Regularity ⟺ pairwise transversality of the residual modules**, and
   **regularity ⟹ `2e ≥ κ`** (§II).  Both are exact, elementary and previously unrecorded.
6. **Rank-deficiency frequency `≈ q^{-t}`** with `t = Σc_i − 2κ + 1`: measured
   `616/7920 = 0.0778` vs `1/13 = 0.0769` at `t = 1`.  The locus behaves like a generic
   determinantal variety of the expected codimension, which is why the counting heuristic
   is accurate on the regular branch and useless on the pair branch.
7. **Cross-ratio rigidity.**  The `m` challenges are `m` marked points on `P(L̄)` plus the
   marked direction `[f₁]`; cross-ratios of quadruples are invariants of the incidence
   configuration modulo the whole gauge.  On the pair branch they are *not* free: in the
   common-window pencil `γ_x = −u₀(x)/u₁(x)` is the image of the "spurious value map",
   so the challenge set is a projective image of a subset of `D`.
8. **Window growth is the only observed way to exceed the Schubert count** (one instance
   in 543, by exactly `+1`).

---

## XI. WHAT THIS MEANS FOR THE ROUTE

* The free-challenge residual incidence locus is a *correct and clean* description of the
  MCA failure geometry — it is the right object, and it explains the `−1` exactly.
* But the inequality proposed for it is false, by a classical, exactly reconstructible
  family, at every size and inside unique decoding.
* What survives is a statement about the **regular stratum only**, which is empty below
  unique decoding and which — by §IV.7 — cannot charge the bad set of an instance on its
  own.  It is worth having only in combination with `MCAPairCover`, where it would replace
  the currently unproved residual term by `O(1)`.
* The prize does not need a better constant; it needs a larger radius window.  The
  incidence object does not, by itself, extend the radius window.

**STATUS: KILL** for `Σ(c_i−1) ≤ 2κ−1`.  **PROMISING** (not prize-sufficient alone, not
ready for Lean) for the regular-stratum version.  No Lean is recommended for *proving* the
cap or the regular cap — the former is false and the latter is not yet a theorem.  The one
durable Lean artifact of this mission is therefore the counterexample family itself
(stop-rule outcome D), now formalised in §XII; it also sharpens the project's existing
`MCALowerBound` from `Θ(1)` to `e+1` bad challenges.

---

## XII. THE LEAN ARTIFACT (stop-rule outcome D)

The counterexample — and only the counterexample — has been formalised, in
`RequestProject/Root/CodingTheory/CommonWindowPencil.lean` (no `sorry`; axioms
`propext, Classical.choice, Quot.sound` only).  It is stated with the project's own MCA
definitions (`IsCloseOn`, `LineCloseOn`, `IsBad`, `badSet`, `epsMCA`, `epsMCAmax` from
`RequestProject/Root/CodingTheory/MCA.lean`), so no new formalisation of "badness" is
involved and the bridge of §IV is literal.

The instance is the common-window pencil written in its cleanest form: split `D = T ⊍ Y`
with `|Y| = e+1` and take

```
u₁ := 1_Y          (maskWord)                 u₀ := −x·1_Y      (tunedWord)
S_y := T ∪ {y}     (commonWindow),  y ∈ Y
```

so that the bad challenges are literally the *evaluation points* of the block `Y`.  Main
declarations:

| name | statement |
|---|---|
| `isCloseOn_commonWindow` | `u₀ + y·u₁` vanishes on `S_y`, hence is close there (with `p = 0`) |
| `not_isCloseOn_maskWord` | `u₁` is close on `S_y` for no polynomial of degree `< k` (uses `|T| ≥ k`) |
| `not_lineCloseOn_commonWindow` | hence the whole line is not `S_y`-close |
| `isBad_commonWindow` | `IsBad k e u₀ u₁ (y : F)` for every `y ∈ Y` |
| `card_le_card_badSet_commonWindow` | `|Y| ≤ #badSet k e u₀ u₁` |
| `succ_div_card_le_epsMCAmax` | `(e+1)/|F| ≤ ε_mca(C,e)` whenever `k + e + 1 ≤ |D|` |
| `free_challenge_cap_fails` | `e+1` distinct bad challenges with windows of size `|D|−e` and `Σ_i (|S_i| − k − 1) > 2(|D|−k) − 1` whenever `(e+1)(|D|−k−e−1) > 2(|D|−k)−1` |
| `card_le_two_mul_of_regular_windows` | a regular pair of windows forces `κ ≤ 2e`: the regular cap is vacuous strictly inside unique decoding |

Two remarks on faithfulness.

* `free_challenge_cap_fails` uses the windows `S_y` of size `|D|−e`, which are *at most*
  the maximal windows; since enlarging a window only increases `|S_i| − k − 1`, the
  refutation does not depend on window maximality.  (Maximality is nevertheless confirmed
  exactly, in `analysis/fcri_lean_bridge_check.py`.)
* `succ_div_card_le_epsMCAmax` strictly strengthens the project's previous unconditional
  lower bound `1/|F|` (`MCALowerBound.one_div_card_le_epsMCAmax`).  The earlier
  construction charged pairwise **disjoint** fibres of a colouring, of which at most
  `|D|/(|D|−e)` can be large enough; the common-window pencil charges `e+1` windows sharing
  one common block — the irregular overlap pattern `|S_i ∩ S_j| = |D|−e−1 > k` that §III.3
  identifies as the reason all earlier searches missed the counterexample.

---

## XVII. EXACTLY ONE NEXT LEMMA

```
LEMMA (regular charging lemma — pencil form).

Let (f0,f1) be a line, e a radius, and let gamma_1 < ... < gamma_m be distinct bad
challenges with maximal windows S_i, Z_i = D \ S_i, c_i = |S_i| - k >= 1, such that the
family is REGULAR:            |S_i n S_j| <= k          for all i != j.
Equivalently R_i n R_j = 0, where R_i = A_{Z_i} F[X]_{<c_i} <= P = F[X]_{<kappa}.

Let R be the stacked matrix of the R_i, Q a basis of its left null space, and
N(gamma) = sum_i gamma_i B_i,  B_i = Q[:,block i] R_i,  sum_i B_i = 0.

Then rank N(gamma) < kappa, and consequently

                      sum_i (c_i - 1)  <=  2*kappa - 3 .
```

Why this one, and not the original cap: it is the *only* form that survives §III (the
unrestricted cap is dead), it is exactly the statement the `MCAPairCover` composition is
missing, its hypothesis is now understood structurally (`regular ⟺ pairwise transverse
residual modules`, and `regular ⟹ 2e ≥ κ`), and its proof obligation is a clean, purely
linear-algebraic one: bound the rank-deficiency locus of a gauge-invariant linear pencil
whose blocks are pairwise transverse residual modules of an MDS code.  The constant `−3`
(rather than `−4`) is forced by the window-growth degeneration, which is realised.

*Remark (Lean).*  The one statement here that is finished mathematics, and that would
strengthen an existing Lean theorem, is the counterexample:

```
THEOREM (common-window pencil).  For every D, k, e with c = n-k-e >= 1 and q > e+1,
there are words f0, f1 with dist(f1, RS_k(D)) = e+1 (so the line has no correlated
agreement at radius e) and e+1 distinct challenges gamma with IsBad k e f0 f1 gamma,
each with a window of size exactly n-e.   Hence  eps_mca >= (e+1)/|F|,
and  sum_i (c_i - 1) >= (e+1)(c-1),  which exceeds 2*kappa-1 for e(c-3) > c.
```
