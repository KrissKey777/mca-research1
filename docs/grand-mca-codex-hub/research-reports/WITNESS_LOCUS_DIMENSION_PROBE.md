# WITNESS_LOCUS_DIMENSION_PROBE

**Mission (v2): does the MCA witness locus have a genuine low-dimensional structure that can be
converted into a non-Johnson bound on the bad set?**

Constraints respected: no Lean file created or modified, no axiom, no `sorry`/`admit`, no
Johnson/list-size argument, no reopening of support geometry / occupancy / κ-charging, no broad
sweep (only the recorded small families), exact integer arithmetic modulo a prime throughout, no
floating-point rank or dimension computation. One measurement script was needed and created:
`analysis/witness_locus_dimension_probe.py`, transcript
`analysis/witness_locus_dimension_probe_output.txt`.

---

## 0. Answer, in one page

**DECISION: OUTCOME A — a canonical low-dimensional reduction exists**, but *not* the one the
mission's `R1` asked about. The witness locus is **not** contained in an affine plane
(refuted: `dim aff` reaches `k+1 = 4` in the data). What exists instead is a canonical
**quotient**, defined by the dual space of the code, which is injective on every witness selection
*for free* and through which the whole MCA direction inclusion survives:

> for every linear functional `λ` on the ambient space,
> `π_λ : F × C → F²`, `π_λ(γ,c) = (γ, λ(c))`.

Since the points of a witness selection have pairwise **distinct first coordinates**, every `π_λ`
is injective on it — no genericity, no arbitrary coordinate choice, no loss of points. Directions
map to directions, and `D(B) ⊆ L(f₁,2e)` projects to `D_λ(B) ⊆ λ(L(f₁,2e))`. That is precisely the
"`R3` direction-counting quotient" the mission demanded, and it is enough to feed Rédei/Szőnyi.

Combining it with Szőnyi's direction theorem gives the target dichotomy in exact form:

> **Dichotomy (derived here).** Either every witness selection is collinear — equivalently (proved
> below) the witnesses are unique and all bad witnesses lie on a *single codeword line*, the
> classical pencil/zero-locus case — or
>
> ```
> |B| ≤ 2·|λ(L(f₁,2e))| − 3 ≤ 2·|L(f₁,2e)| − 3        (for a suitable functional λ)
> ```

This is **linear** in the list size, against the project's existing capacity-free bound
`|B| ≤ κ_max + |L|(|L|−1)`, which is **quadratic**, and it uses no capacity at all. Zero violations
in 211/211 non-collinear instances; 14 collinear instances violate it, which is exactly why the
first branch of the dichotomy is not removable.

Honest limitation, stated up front: on the recorded micro-instances (`p ≤ 19`) the new bound is
true but **vacuous**, because there `|λ(L)| ≥ (p+3)/2` always, so `2|λ(L)|−3 ≥ p ≥ |B|` holds for
free. Its content lies in the regime the project actually targets (`p = 2³¹−1`, list size ≪ `p`),
and its sharpness cannot be improved: an actual MCA configuration in the data **attains** the
Rédei–Megyesi extremum `|D| = (|B|+3)/2` with `|B| = p = 7`.

**One recommended next mission: OUTCOME A ⇒ "RÉDEI–SZŐNYI MCA DIRECTION BOUND"**, in the sharpened
form isolated in §11 (the object to bound is `min_λ |λ(L)|`, not `|L|`).

---

## 1. The two objects, kept apart

| object | definition | canonical? |
| --- | --- | --- |
| `W_full` | `{ (γ,c) : γ ∈ B, c an admissible witness for γ }` | yes, once "admissible" is fixed |
| `W_s` | `{ (γ,c_γ) : γ ∈ B }` for a selection `s` choosing one witness per bad `γ` | no — depends on `s` |

Both conventions of "admissible" used in the project are measured separately: the recorded
degeneracy filter, and the unfiltered one (`every codeword within distance e`). Every statement
below says which object it is about, and every selection-level statement is quantified over
**all** selections (enumerated exhaustively: `324 / 324` instances).

**The distinction is not cosmetic.** In 6 instances `dim aff(W_full) > max_s dim aff(W_s)`: the
union of the fibres is *strictly* higher-dimensional than any single selection. Smallest example:
`RAND[7,3]/F7`, `e = 2`, `|B| = 3`, witness multiplicities `(2,2,3)`,
`f₀ = (0,0,0,3,1,0,2)`, `f₁ = (0,0,0,1,1,0,0)`, degeneracy filter — every selection spans a plane
(`dim 2`), while `dim aff(W_full) = 3`. And in 40 instances one selection is collinear while
another is not, so "the witness geometry" is genuinely selection-dependent.

---

## 2. Measurement setup

Recorded families only (`RS[4,2]/F5 … RS[7,3]/F11`, plus the non-RS controls `RAND[6,3]/F5`,
`RAND[7,3]/F7`, `RAND[6,2]/F11`), both witness conventions, gap regime `2e ≥ w`, `2e+2w ≥ d`,
instances with `|B| ≥ 3`: **324 instances**, ranges `p ≤ 19`, `n ≤ 7`, `k ≤ 3`, `|B| ≤ 11`,
`|L| ≤ 131`. Witness selections enumerated **exhaustively** in all 324 (the fibre products were
below the cap). All arithmetic exact.

---

## 3. PHASE I — exact dimension audit, and three dimension theorems

### D1 (structural identity) — **PROVED**

For any base point `γ₀ ∈ B` and any selection `s`, with `q_{0j} = (c_j − c_0)/(γ_j − γ_0)`:

```
dim aff(W_s) = 1 + dim aff{ q_{0j} : j ≠ 0 } .
```

*Proof.* `P_j − P_0 = (γ_j − γ_0)·(1, q_{0j})`, and `γ_j ≠ γ_0`, so the difference space is spanned
by the vectors `(1, q_{0j})`; the rank of a family `(1,x_j)` is `1 + dim aff{x_j}`. ∎

Checked on all `324 / 324` instances, over every selection. This identity is what makes the whole
probe meaningful: *the affine geometry of the witness locus and the geometry of the secant
direction set are the same object, shifted by one dimension.*

### D2 (dimension is bounded by the code, not by the block length) — **PROVED**

```
dim aff(W_s) ≤ min( |B| − 1 , k + 1 ),      dim aff(W_full) ≤ k + 1 ,     k = dim C .
```

*Proof.* `W ⊆ F × C`, an affine space of dimension `1 + k`; and `m` points span at most `m−1`. ∎

Checked `324 / 324`; the bound `k+1` is **attained** in 73 instances. So the witness locus *is*
intrinsically low-dimensional — but low relative to the **code dimension**, not to 2. In
particular the mission's `H1` has a positive but *`|B|`-independent* answer: `d₀ = k+1`.

### D3 (the collinear branch is rigid) — **PROVED**

For `|B| ≥ 3` the following are equivalent for a selection `s`:
`dim aff(W_s) = 1` ⟺ `|D(W_s)| = 1` ⟺ all witnesses of `s` lie on one **codeword line**
`g′(γ) = a + γq` with `a, q ∈ C`.
Moreover, if **every** selection is collinear then the witness of each bad `γ` is **unique** and
`W_full = W_s` is that single line.

*Proof of the last clause.* Suppose `γ₀` had two witnesses `c ≠ c′`. The other `|B| − 1 ≥ 2` points
are distinct and span a unique line `ℓ`; both completions are collinear, so `(γ₀,c), (γ₀,c′) ∈ ℓ`.
But `ℓ` contains two points with distinct abscissae, hence meets the fibre `{γ₀} × C` in at most one
point, so `c = c′`. The equivalences follow from D1 (`dim = 1 ⟺ dim aff Q = 0 ⟺ |Q| = 1`) and from
`a = c_{γ₀} − γ₀q ∈ C`. ∎

Data: `113 / 324` instances are collinear for every selection, and in **all 113** every witness is
unique (`0/113` with a multiple fibre) — exactly as the proof predicts.

---

## 4. PHASE II — H1 … H4

| hypothesis | verdict | evidence |
| --- | --- | --- |
| **H1** `|B|` large ⇒ `dim aff(W_s) ≤ d₀` | **True but for a trivial reason — d₀ = k+1 (PROVED, D2), independent of `|B|`.** Large `|B|` does **not** push the dimension down. | `|B| ≥ 9`: `dim = 4 = k+1` throughout; the largest instance `|B| = 11` still has `dim = 4` |
| **H2** for fixed `d ≥ 2`, `|D(W_s)|` grows with `|B|` | **EMPIRICALLY SUPPORTED, and PROVED in the sharper form `|D| ≥ (|B|+3)/2`** (§6-§7, via Szőnyi). Growth is *not* monotone in `d`. | at `d = 4`: `min|D| = 4, 10, 7, 20, 20, 27, 11` for `|B| = 5,6,7,8,9,10,11` |
| **H3** `dim = 1` ⟺ all witnesses on one line | **PROVED, and strictly more than the tautology** (D3): it forces witness *uniqueness* and a **codeword** line, i.e. a genuine MCA pencil member | `113/113` |
| **H4** large `|B|`, large `dim`, small `|D|` simultaneously | **REFUTED in the strong form `|D| ≥ |B|`** (18 counterexamples), **CONFIRMED SHARP at the Rédei level**: `|D|` can be as small as `⌈(|B|+3)/2⌉`, never smaller (0 violations) | smallest/strongest: see §9 |

`H2/H4` together are the real content: `|D|` cannot be small, but the exact floor is the
*Rédei–Megyesi value*, not `|B|`.

---

## 5. PHASE III — which finite-geometric model the configurations follow

Over a maximal-dimension selection per instance:

| type | count |
| --- | --- |
| simplex-like (`d = |B| − 1`, points in general position) | 113 |
| dimension-saturated (`d = k+1 < |B|−1`, forced by the code) | 43 |
| collinear (`d = 1`) | 113 |
| intermediate | 55 |

Direction-multiplicity profiles (number of pairs realising each direction) show two distinct
regimes, both present at `|B| = 11`, `d = 4`:

* *near-generic*: `profile = [3,3,3,3,3,3,3,2,2,1,1,1,…]`, `|D| = 39`, largest collinear subset 3;
* *Rédei-like*: `profile = [21,3,1,1,1,…]`, `|D| = 33`, largest collinear subset **7** — a big
  sub-line plus a few off-line points, which is exactly the shape of the classical Rédei extremal
  configurations (a `Rédei blocking set` arises from a large collinear part plus few extra points).

So the correct model is neither "cap" nor "grid": it is **line-plus-few-points / simplex mixture**,
which is the model Rédei-type theorems were designed for.

---

## 6. PHASE IV — R1 / R2 / R3

**R1 (exact affine embedding in dimension ≤ 2): REFUTED.** Only `207 / 324` instances have every
selection planar; `206 / 324` for `W_full`. Explicit failure: `RS[6,3]/F11`, `e = 2`, `|B| = 11`,
`dim aff(W_s) = 4`. The witness locus is genuinely `(k+1)`-dimensional. (Note the two counts
differ — one instance has all selections planar while `W_full` is not; §1.)

**R2 / R3 (canonical direction-counting quotient): ESTABLISHED.**

> **Q (quotient lemma) — PROVED.** For `λ` in the dual `(Fⁿ)*` put `π_λ(γ,c) = (γ, λ(c))`. Then
> 1. `π_λ` is **injective on every** `W_s`, unconditionally, because the first coordinates `γ` are
>    pairwise distinct — no genericity assumption, no point collisions, `|π_λ(W_s)| = |B|`;
> 2. `π_λ` is affine, hence maps the secant of `P_i,P_j` to the secant of their images; the image
>    secant is never vertical, and its direction is the affine slope `λ(q_ij) ∈ F`;
> 3. therefore `D_λ(B) := λ(D(B))` satisfies `|D_λ(B)| ≤ |D(B)|` (directions can merge, never
>    split) and, by the secant lemma, `D_λ(B) ⊆ λ(L(f₁,2e))`;
> 4. if `W_s` is non-collinear then `|D(B)| ≥ 2` (by D1) and some `λ` — a coordinate functional
>    suffices — separates two directions, so `π_λ(W_s)` is a non-collinear `|B|`-point set of
>    `AG(2,p)`.

"Remain distinguishable" is thus given a precise and *minimal* meaning: the quotient need not
preserve `q` as a vector (impossible, as the mission notes); it must only preserve (i) the points,
(ii) enough of the direction set to be non-degenerate, and (iii) the MCA membership
`q ∈ L`, which it does in the projected form `λ(q) ∈ λ(L)`. The quotient is canonical as a
*family* indexed by the dual space `C*`; no arbitrary single coordinate is privileged, and the
bound below is obtained by **optimising over `λ`**, which is itself an intrinsic operation.

Measured: a non-collinear planar image exists in `211 / 211` instances that have a non-collinear
selection — exactly as the lemma predicts.

---

## 7. PHASE VI — the Rédei/Szőnyi gate, hypothesis by hypothesis

**Theorem used (literature).** *Rédei–Megyesi / Szőnyi direction theorem.* Let `p` be a **prime**
and let `U` be a set of `k` points of the affine plane `AG(2,p)` with `k ≤ p`, not all collinear.
Then `U` determines at least `(k+3)/2` directions (points of the line at infinity `PG(1,p)`).
References: L. Rédei, *Lückenhafte Polynome über endlichen Körpern* (1970) (the `k = p` case, with
Megyesi); T. Szőnyi, *On the number of directions determined by a set of points in an affine Galois
plane*, J. Combin. Theory Ser. A **74** (1996), 358–361 (the extension to `k ≤ p`). The statement is
quoted as recorded in the literature and is **not** re-proved here.

| theorem object | MCA object | hypothesis verified? |
| --- | --- | --- |
| prime field `F_p` | the MCA base field | **yes** for `M31 = F_{2³¹−1}` and for every probed instance. **Obstruction for extension fields**: over `F_{p^h}` the `(k+3)/2` bound is false in general (the Ball–Blokhuis–Brouwer–Storme–Szőnyi hierarchy replaces it), so the bridge is prime-field-only |
| `k`-point set of `AG(2,p)` | `π_λ(W_s)`, `k = |B|` | **yes** — injectivity is free (Q.1), so exactly `|B|` points |
| `k ≤ p` | `B ⊆ F_p` | **yes**, always |
| not all collinear | `W_s` non-collinear + `λ` separating | **yes** in the non-collinear branch (Q.4); **fails** in the collinear branch, which is why the dichotomy has two arms |
| "direction" = point of `PG(1,p)` | affine slope `λ(q_ij)`; no vertical direction occurs | **yes** (Q.2) |
| conclusion `#directions ≥ (k+3)/2` | `|λ(D(B))| ≥ (|B|+3)/2` | consistent in `211 / 211` instances, `0` violations, and **attained** (§9) |

**Resulting inequality (the bridge).**

```
(|B|+3)/2  ≤  |λ(D(B))|  ≤  |λ(L(f₁,2e))|  ≤  |L(f₁,2e)|
⟹  |B| ≤ 2·min_λ |λ(L(f₁,2e))| − 3   ≤   2·|L(f₁,2e)| − 3 .
```

Status: **PROVED conditional on the quoted Szőnyi theorem** (everything on the MCA side — Q.1–Q.4,
D1–D3, the secant lemma — is proved here or already in the project); **not formalised** (the mission
forbids Lean); **0 violations** in `211/211` non-collinear instances and `0` violations of the
projected form.

---

## 8. The resulting `|B|` bound, and comparison with all existing bounds

| bound | form | branch | comment |
| --- | --- | --- | --- |
| κ-charging (project, proved, Lean) | `|B| ≤ Σ_{q∈L} κ(q)`, capacities `κ(q) ≤ chargeCap(e,d(f₁,q))` | all | capacity-dependent |
| capacity-free (project, proved) | `|B| ≤ κ_max + |L|(|L|−1)` | all | **quadratic** in `|L|` |
| packing / occupancy (project, proved) | per-pencil `|class(q)| ≤ cap(e,d(f₁,q))` | all | frozen here |
| **this report** | `|B| ≤ 2·min_λ|λ(L)| − 3 ≤ 2|L| − 3` | non-collinear only | **linear** in `|L|`, capacity-free, Johnson-free, list-size-machinery-free |
| this report | collinear arm: witnesses unique, all on one codeword line `a+γq`; then `|B|·(n−e−z) ≤ |supp(f₁−q)| ≤ 2e` whenever `n−e−z ≥ 1`, where `z = #{i : (f₀−a)_i = (f₁−q)_i = 0}`; if `n−e−z ≤ 0` the whole line is `e`-close and `|B|` is unbounded (the known degenerate case) | collinear only | `0` violations in the `82` non-degenerate collinear instances; `31` degenerate |

So in the non-collinear branch the new bound improves the capacity-free bound from `|L|²` to
`2|L|`, and beats the charging bound whenever the mean capacity exceeds 2.

**Where it is vacuous (measured, not guessed).** `|B| ≤ p` is free, so the bound says something
only when `2|λ(L)| − 3 < p`, i.e. `|λ(L)| < (p+3)/2`. In the probed micro-instances
`min_λ |λ(L)|` equals `p` itself in nearly every case (e.g. `11` at `p = 11` with `|L| = 128`; best
observed `10 < 11` at `RS[7,3]/F11`), so **every probed verification of the bound is non-vacuous
only as a consistency check of the direction inequality, not of the `|B|` bound**. This is a
property of `p ≤ 19` toy instances, where the radius-`2e` ball already contains a constant fraction
of the code; the bound's content is in the project's actual regime (`p = 2³¹−1`, list size
polynomial in `n` and ≪ `p`).

---

## 9. Strongest counterexamples / extremal configurations found

1. **Refutes any MCA-specific improvement of Szőnyi** (and refutes `|D| ≥ |B|`):
   `RS[6,3]/F7`, `e = 2`, unfiltered witnesses, `f₀ = (0,0,0,6,3,1)`, `f₁ = (0,0,0,5,6,2)`,
   `|B| = 7 = p` (every parameter is bad), and a non-collinear selection — of affine dimension
   exactly **2**, i.e. genuinely planar — with `|D| = 5 = (p+3)/2` exactly, direction multiplicity
   profile `[6,6,3,3,3]`, largest collinear subset of size 4, and all five directions inside `L`
   (`|L| = 71`). This is an actual MCA witness configuration realising the **Rédei–Megyesi
   extremum**, verified by an isolated recomputation (last block of the transcript, all 64
   selections enumerated). The bridge is therefore sharp: no bound better than `|B| ≤ 2|D| − 3`
   is available from direction counting alone, and the "line-plus-few-points" model of §5 is
   realised exactly.
2. **Refutes `R1` (planarity)**: `RS[6,3]/F11`, `e = 2`, `|B| = 11`, `dim aff(W_s) = 4 = k+1`.
3. **Refutes conflating `W_full` with `W_s`**: `RAND[7,3]/F7`, `e = 2`, `|B| = 3`,
   `f₀ = (0,0,0,3,1,0,2)`, `f₁ = (0,0,0,1,1,0,0)`: every selection is planar, `W_full` is not.
4. **Shows the collinear arm cannot be dropped**: 14 instances (all with `dim = 1`) satisfy
   `|B| > 2|L| − 3`; e.g. `RS[5,2]/F5`, `e = 1`, `|B| = 5`, `|L| = 1`.
5. **Shows the collinear arm can be unbounded**: 31 instances with `n − e − z ≤ 0`, where the whole
   codeword line is `e`-close and `|B|` is limited only by `|F|`.

---

## 10. Status classification

| statement | status |
| --- | --- |
| D1 `dim aff(W_s) = 1 + dim aff(Q_{γ₀})` | **PROVED** (+ `324/324` exact checks) |
| D2 `dim aff(W_s) ≤ min(|B|−1, k+1)`, `dim aff(W_full) ≤ k+1` | **PROVED** (attained in 73 instances) |
| D3 collinear ⟺ `|D| = 1` ⟺ one codeword line; all-selections-collinear ⇒ unique witnesses | **PROVED** (+ `113/113`) |
| Q quotient lemma (`π_λ` injective, direction-preserving, `D_λ ⊆ λ(L)`) | **PROVED** (+ `211/211`) |
| H1 large `|B|` forces small dimension | **REFUTED** as stated; true only in the `|B|`-independent form `d ≤ k+1` |
| H4 large `|B|` + large `dim` + `|D| < |B|` | **CONFIRMED** (18 instances) — so no `|D| ≥ |B|` theorem |
| `|D| ≥ (|B|+3)/2` for non-collinear MCA configurations | **PROVED conditional on Szőnyi**; `0/211` violations; **sharp** (§9.1) |
| `|B| ≤ 2 min_λ |λ(L)| − 3 ≤ 2|L| − 3` in the non-collinear branch | **PROVED conditional on Szőnyi**; `0/211` violations; **vacuous on the probed micro-instances** |
| collinear branch `|B|(n−e−z) ≤ |supp(f₁−q)|` (when `n−e−z ≥ 1`) | **EMPIRICALLY SUPPORTED** (`0/82` violations); a one-line zero-counting proof is expected but was not written out here |
| planar embedding `R1` | **REFUTED** |
| arbitrary affine configurations realisable (universality, OUTCOME C) | **OPEN** — not decided by this probe; the Rédei-extremal realisation of §9.1 is evidence *for* substantial realisability, but the `(k+1)`-dimension ceiling of D2 is a genuine obstruction to full universality |
| Rédei applicability over extension fields `F_{p^h}` | **INVALID** — the `(k+3)/2` bound is prime-field-specific |

---

## 11. The single recommended next mission

**OUTCOME A ⇒ NEXT MISSION: "RÉDEI–SZŐNYI MCA DIRECTION BOUND".**

But with the target sharpened by what this probe found, because the naive form is provably vacuous
on small fields and the sharpening is where the remaining mathematics is:

> **Objective.** Make `|B| ≤ 2·min_λ |λ(L(f₁,2e))| − 3` non-vacuous, i.e. bound the *projected*
> Hamming ball. Concretely: for `L = { q ∈ C : wt(f₁ − q) ≤ 2e }`, prove an upper bound on
> `min_{λ ∈ C*} |λ(L)|` in terms of `e`, `n`, `k` (**not** `p`), and show it is `< (p+3)/2` in the
> MCA regime. Every `q ∈ L` agrees with `f₁` outside a set of size `≤ 2e`, so a functional
> supported on coordinates where the ball is thin should have a very small image; the question is
> whether such a `λ` always exists and how small `|λ(L)|` can be forced to be.
>
> Secondary deliverables of the same mission: (a) discharge the collinear arm with the explicit
> zero-counting proof so the dichotomy is complete and unconditional on that side; (b) decide
> whether the Szőnyi hypothesis `|B| ≤ p` can be traded for the `k ≤ p` regime of the
> higher-dimensional theory when `|B| > p` cannot occur anyway.

Explicitly **not** recommended: returning to κ, to occupancy, or to three-point secant identities.
Formalisation in Lean should be opened only after (a) — at that point the statement
"non-collinear witness selection ⇒ `|B| ≤ 2|L| − 3`" becomes a self-contained theorem whose only
external input is the cited Szőnyi bound.
