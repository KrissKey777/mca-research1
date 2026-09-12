# JOHNSON DECISIVE GATE — FORCED DEGENERACY ABOVE K\*

Mission: resolve exactly one question — **can an admissible GS interpolation space
above K\* be forced into a common repeated-factor locus, and can such a family
carry a large Bad set?**

No Lean was added (per mission scope). Everything below is exact integer /
GF(p) computation plus symbolic algebra. Scripts and raw logs:

| file | role |
|---|---|
| `analysis/forced_degeneracy_above_kstar.py` | exact threshold arithmetic (GATES 2, 4, 5) + score correction |
| `analysis/fd_thresholds_output.txt` | its output |
| `analysis/fd_core.py` | exact GF(p) linear algebra, F[X][Y] arithmetic, module gcd, exact Bad set |
| `analysis/fd_models.py`, `analysis/fd_experiments.py` | scaled small models M1–M6 and experiments A–D |
| `analysis/fd_sharpness.py`, `analysis/fd_sharpness_output.txt` | predicted vs measured multiplicity (185 cells) |
| `analysis/fd_adversarial.py`, `analysis/fd_kill.py`, `analysis/fd_kill*_output.txt` | GATE 7 adversarial solve-for-a-kill |
| `analysis/fd_anatomy.py` | anatomy of a single instance |
| `analysis/fd_envelope.py`, `analysis/fd_envelope_output.txt` | GATE 1 taxonomy items 2–5 |

---

## 0. SCORE CORRECTION (mandated)

At ρ = 1/2 the relevant external frontier is δ = 1/4. Recomputed exactly:

* Johnson target radius δ_J = 0.291916; frontier δ = 0.25;
* **gain at 128 queries = +10.620 bits over δ = 1/4.**

The figure +27.745 bits is the gain relative to the weaker *local* certified
radius 0.177124 and is **not** a frontier gain; it is not used anywhere below.
(For the record, at ρ = 1/4 the same computation gives δ_J = 0.499022 and
+74.515 bits over δ = 1/4.)

---

## 1. SETUP AND THE ONE IDENTITY EVERYTHING RESTS ON

Schedule (ρ = 1/2): n = 2²⁰, k = 524288, e = 306096, **t = 742480**, m = 866,
L = 642769488, b_Y = 1225, d_Z = 1318349.
dim V = 394 334 425 888, conditions = 393 646 964 736, **surplus = 687 461 152 > 0**.

    V = { Q : wdeg_(1,k) Q ≤ L−1, deg_Y Q ≤ b_Y },
    I = { Q ∈ V : ord ≥ m at every line point (x, f₀(x) + Z f₁(x)), x ∈ D }.

**SHEAR IDENTITY.** Let c ∈ K[X], deg c = K, K_eff = max(K,k),
W_K = L−1+(K_eff−k)·b_Y. The substitution Y ↦ Y+c preserves the
(1,K_eff)-weighted filtration in both directions, so in the (Y−c)-adic expansion
Q = Σ_j p_j·(Y−c)^j of any Q ∈ V one has, exactly,

    deg p_j ≤ W_K − K_eff·j.

If the line lies on the curve Y = c(X) at s of the n points (agreement locus S),
order-m vanishing forces E_S^{(m−j)_+} | p_j. Hence

> **(FORCE_r)**  W_K − K_eff·j < s·(m−j) for all j < r
> ⟹ (Y−c)^r divides **every** admissible Q.

This implication is unconditional (no genericity). s = n is the known
"curve-line" family; **s < n is the partial-curve family this mission isolates.**

**Escape identity.** For r = 1 the expected-dimension escape condition is
*exactly* the complement of (FORCE_1): symbolically,
dim V − dim box(L−1−K, b_Y−1) = L − k·b_Y + K·b_Y versus s·m.

---

## 2. GATE 1 — THE EXACT FAILURE OBJECTS (kept separate)

The primary object is the gcd/content of the **whole module** I, not of one Q.
The five items were tested separately in exact small models.

1. **Common factor H.** Occurs. Whenever (FORCE_1) holds, the module gcd is
   nontrivial; measured gcd was always exactly (Y−c)^r, never larger.
2. **Common square H².** Occurs, precisely in the (FORCE_2) cells.
3. **Common factor of Q and ∂_Y Q** (i.e. every interpolant inseparable).
   Occurs, and in every tested instance it coincided with case 2 — the
   inseparability came from the module's own common square.
4. **Common factor only after specialisation x = x₀.** Vacuous as a separate
   mechanism: in every model and every line (including 40 random control
   lines), *all* n specialisations already had a repeated factor, so this test
   never separates lines. It is not a usable failure object.
5. **Varying repeated factors with a common algebraic envelope**, i.e. every
   Q ∈ I inseparable while the module gcd is trivial.
   **ENVELOPE CASES FOUND: 0** (M1 and M4, `fd_envelope_output.txt`, covering
   random lines, spike lines, all partial-curve cells, and two-curve lines).
   Every observed all-inseparable line had a nontrivial *module* gcd.

Also proved (structural, rigorous): **any common factor of a nonzero
interpolation module must vanish at ≥ 1 interpolation point** — otherwise
I = H·I′ ⊆ H²·I″ ⊆ … is an infinite descent inside a finite-dimensional space,
forcing I = 0.

---

## 3. GATE 2 — CROSSING K\*

Exact maximisation of the curve degree K over **all** s ≤ n subject to (FORCE_r):

| r | max K with forced (Y−c)^r, ρ = 1/2 | vs t = 742480 | ρ = 1/4 (t = 525313) |
|---|---|---|---|
| 1 | 740 857 | < t, margin 1623 | 523 776 (margin 1537) |
| 2 | **740 605** | < t, margin 1875 | 523 434 (margin 1879) |
| 3 | 740 354 | < t, margin 2126 | 523 092 (margin 2221) |

General common factor H with deg_Y H = h (expected-dimension cap, r = 2):
max over h is **740 820 < t** (worst case h = 1; strictly decreasing in h;
0 for h ≥ 50). At ρ = 1/4: 523 775 < t.

**The repository's K\* = 740 604 is the same threshold under a conservative
(K+1)-weight convention; the sharp value is K\*+1 = 740 605.** The apparent
"one step above K\*" is an indexing artefact, not a new mechanism.

**Why this is not an accident.** (FORCE_1) needs W_K < s·m ≤ n·m, i.e.
K ≤ k + (n·m − L)/b_Y, and

    k + (nm − L)/b_Y  <  t   ⟺   k·n < t²   ⟺   Johnson.

Numerically k+(nm−L)/b_Y = 740857.25 and k·n/t = 740431.81, both < t = 742480;
the margin (t²−k·n)/t = 2048.2. **Forced degeneracy and the Johnson condition
are the same inequality.**

### The honest gap (this is the real content of GATE 2)

(FORCE_r) is *sufficient*. The table above caps only degeneracies produced by
that mechanism. Two counting attempts at the **converse** were made:

* **box variant.** Cutting I out of V_S (the s curve conditions) leaves
  codim_{V_S} I ≤ (n−s)·C(m+1,2), and forcing kills the slots j < r, giving
  Σ_{j<r} slot_dim(j) ≤ (n−s)·C(m+1,2). This is fully rigorous **only for
  K ≤ k**, where the shear preserves V exactly; for K > k the sheared box
  strictly contains V, the slots are over-counted and the resulting cap is a
  heuristic. It reproduces 740 605 at s = n, and is toothless for s < n
  (max over s: K ≤ 160 737 263 ≫ t, attained at s = 1).
* **sound sub-box variant.** The sub-box {deg p_j ≤ L−1−K·j} demonstrably maps
  into V for every K, but under-counts so badly that the condition is vacuous
  (no finite cap).

**Conclusion: counting alone gives no sound upper bound on K once K > k.**
The sub-t conclusion for degeneracies not produced by (FORCE_r) rests on the
sharpness of (FORCE_r), which is verified in 185 exact cells but not proved.
This is the next bottleneck.

---

## 4. GATE 3 — THE LARGE-Bad CONDITION

A degenerate interpolation space is not by itself a counterexample. For every
forced-degeneracy construction the **complete** Bad set was computed exactly, by
enumerating all witness sets of size ≥ t (closeness gives at most one γ per
witness set; LineCloseOn ⟺ both high parts vanish).

**The danger window.** The Bezout harmlessness argument needs s − e > K. The
region where degeneracy is forced but Bezout is silent is nonempty at both prize
schedules (it is empty whenever 2t ≥ k+n; here 2t = 1 484 960 < k+n = 1 572 864):

| schedule | widest window | size |
|---|---|---|
| ρ = 1/2 | K = 524 287: s ∈ [742 480, 830 383] | 87 904 values |
| ρ = 1/4 | K = 262 143: s ∈ [525 313, 785 406] | 260 094 values |

This window is the genuinely new object found by this mission: **forced
degeneracy is not confined to the harmless full curve-line family.**

**Measured Bad sets in the window** (GATE 7 solves, never samples, for lines
that are forced-degenerate *and* carry prescribed bad challenges whose witness
sets deliberately leave S):

| model | n | k | t | danger cell (K,s) | max #Bad | FATAL | \|N_G\| | gcd deg_Y |
|---|---|---|---|---|---|---|---|---|
| M1 | 9 | 2 | 5 | (2, 6) | 6 | **1** | 6 | 2 |
| M3 | 11 | 3 | 7 | — (window empty) | ≤ 1 (all rigid) | 1 | — | — |
| M4 | 12 | 3 | 7 | (3, 8) | 7 | **1** | 8 | 2 |
| M5 | 15 | 4 | 9 | (4, 10) | 8 | **1** | 10 | 2 |
| M6 | 18 | 5 | 11 | (5, 12) | 9 | **1** | 12 | 2 |

*FATAL* = bad challenges all of whose witness sets lie inside N_G (the locus
swallowed by the repeated part), i.e. invisible to the annihilator repair.
Outside the window every witness set of size ≥ t must meet S in > K points, so
**no** bad challenge can leave the agreement locus: all are rigid.

Full curve lines (s = n) reproduce the known picture: gcd = (Y−c)³, every Q
inseparable, N_G = D, **#Bad = 1**. Random-line control: 0/40 degenerate, all
with #Bad = 0.

**Scaling.** #Bad grows slowly and linearly: 6, 7, 8, 9 at n = 9, 12, 15, 18 —
exactly n/3 + 3 in all four models, with |N_G| = s and the number of FATAL
challenges **exactly 1 in every instance found**. B_prize = 2^57.93. Nothing
here approaches it, and the fatal part does not grow at all.

**Verdict: HARMLESS.**

---

## 5. GATE 4 — STRUCTURAL CLASSIFICATION

Every forced degeneracy observed, and every one produced by (FORCE_r), has the
same structural source: the coefficient line lies on a low-degree algebraic
curve a + Z·b of X-degree K at s points. In exact models the measured module gcd
was **always** exactly (Y−c)^r for that very curve — never a factor of a
different shape, never a strictly larger gcd (185 cells). Together with the
ENVELOPE count of 0, this supports the implication

    common repeated factor  ⟹  low-complexity algebraic line/curve structure.

And that structure does bound Bad, by the following rigorous statement.

> **RIGID BRANCH ≤ 1.** Suppose K < t and every witness set of a bad γ lies
> inside the agreement locus S. Then |W| ≥ t > K, and a + γ·b agrees with the
> degree-<k polynomial p_γ on more than K points while their difference has
> degree ≤ max(K, k−1); hence a + γ·b = p_γ, i.e. deg(a+γ·b) < k. This can hold
> for at most one γ (two would make the line itself a codeword line, and then no
> bad γ exists at all). **#Bad ≤ 1.**

Since forcing implies K < t (Section 3), the rigid branch is unconditionally
harmless. The measured FATAL count of exactly 1 in the danger window is precisely
this bound being attained — and this is **not** an accident:

> **FATAL ≤ 1.** Suppose the module gcd is a power of (Y − c), c = a + Z·b.
> Then G vanishes at the line point (x, f₀(x)+Z f₁(x)) exactly when the line
> meets the curve at x, i.e. **N_G = S**. A FATAL challenge is by definition one
> all of whose witness sets lie inside N_G = S, which is the hypothesis of RIGID
> BRANCH ≤ 1. Hence **at most one FATAL challenge**, whatever s, K and n are.

The measurements confirm N_G = S exactly (|N_G| = 6, 8, 10, 12 at s = 6, 8, 10,
12), and FATAL = 1 in every instance found. The only loophole is a module gcd
with an *extra* factor beyond the (Y−c)-power; in 185 exact cells no such extra factor
ever appeared.

---

## 6. GATE 5 — ANNIHILATOR FAMILY

**Constructed symbolically (on paper), not formalized.** Let

    G := gcd(Q, ∂_Y Q)  (primitive in F[Z][X][Y]; deg_Z G ≤ d_Z by Gauss),
    U := Q / G          (squarefree part).

For a bad γ: GS root-finding (L ≤ m·t) gives (Y − p_γ) | Q_γ; the second stage
(L − k ≤ (m−1)·t, tight with equality at both schedules) upgrades this to
(Y − p_γ)² | Q_γ. Then exactly one of:

* **(a)** U_γ is non-squarefree ⟹ γ is a root of Res_Y(U, ∂_Y U)|_{x₀},
  of degree ≤ (2b_Y − 1)·d_Z, plus ≤ 2d_Z for leading-coefficient/content terms;
* **(b)** (Y − p_γ) | G_γ ⟹ w_x(γ) = 0 for every x ∈ S_γ, where
  w_x(Z) := G(Z, x, f₀(x) + Z f₁(x)) has degree ≤ d_Z + b_Y — so γ is annihilated
  unless S_γ ⊆ N_G;
* **(c)** S_γ ⊆ N_G — the rigid case, ≤ 1 challenge by Section 5.

The construction needs Q chosen generically in a pencil so that its repeated part
equals the module's forced common factor; the repository already supplies
`card_pencil_degenerate_le` (≤ 3b_Y bad λ).

**Exact budget.**

    B = n·(d_Z + b_Y) + (2b_Y − 1)·d_Z + 2·d_Z + 1

| schedule | B | log₂ B |
|---|---|---|
| ρ = 1/2 | 1 386 904 900 024 | **2^40.3350** |
| ρ = 1/4 | 1 245 024 911 257 | 2^40.1793 |

| challenge field | budget B_max = \|F\|/2^128 | fits? | ε_mca |
|---|---|---|---|
| KoalaBear sextic (actual) | 2^57.9321 | **YES** | ≤ 2^−145.5971 (ρ=1/2), 2^−145.7528 (ρ=1/4) |
| artificial \|F\| ≥ 2^160 | 2^32.0000 | **NO** | — |

So the repair is affordable in the real field and only fails under the
artificial simplification, exactly as suspected.

---

## 7. GATE 6 — THE CANDIDATE DICHOTOMY

    For every line L:
      (generic branch)  the GS interpolation module escapes repeated-factor
                        degeneracy  ⟹  root/discriminant counting, B = 2^40.34;
      (rigid branch)    the module is forced degenerate  ⟹  the line lies on a
                        curve a + Z·b of degree K < t at s ≥ … points, and
                        every bad challenge invisible to the annihilator family
                        is rigid  ⟹  #Bad ≤ 1.

Status of the two branches:

* **rigid branch:** the "#Bad ≤ 1 given K < t" step is **proved** (Section 5);
  "forced ⟹ K < t" is proved *for degeneracies produced by (FORCE_r)* and is
  equivalent to Johnson; the general converse is **open**.
* **generic branch:** the annihilator family is derived symbolically but the
  pencil/generic-Q step and the uniformity at the Johnson target are **not**
  proved.

**Therefore this is a candidate, not a theorem.** It survives the adversarial
gate, which is what was asked.

---

## 8. GATE 7 — CHEAPEST KILL: RESULT

Target: a line with K ≥ K\*, whole module forced degenerate, not reducible to the
harmless curve-line structure, and #Bad large.

* K ≥ K\* with forced degeneracy: **not found, and provably impossible via
  (FORCE_r)** — every forced factor has K ≤ 740 605 < t = 742 480.
* Forced degeneracy outside the harmless full-curve family: **found** (the
  danger window, Section 4) — this part of the kill succeeds.
* Large Bad on that family: **failed**. Max #Bad = 9 at n = 18, growing exactly
  like n/3 + 3, with **exactly one FATAL challenge in every single instance**
  (as it must be, by the FATAL ≤ 1 theorem). Nothing scales toward
  B_prize = 2^57.93.

**No kill.**

---

## REQUIRED OUTPUT

**FORCED DEGENERACY ABOVE K\*:** **NO** (in the operative sense). Every forced
common factor has curve degree ≤ 740 605 < t = 742 480; the sharp threshold
equals the repository's K\* up to a one-step weight convention (K\*+1). *Caveat:*
this is proved for degeneracy produced by the shear criterion (FORCE_r); a
converse ruling out other mechanisms above K\* is **UNKNOWN** — counting alone
gives no sound cap for K > k.

**SMALLEST INSTANCE:** model M1 (n = 9, k = 2, e = 4, t = 5, m = 4, L = 20,
b_Y = 9) over GF(999983), D = {1,…,9}, cell K = 2, s = 6 — a *partial* curve line
inside the danger window.

**COMMON MODULE FACTOR:** (Y − c(X)) with c = a + Z·b the interpolating curve of
X-degree K; the gcd of the whole module was always exactly a power of this single
factor, never anything else, and never larger than predicted at r = 1.

**REPEATED MULTIPLICITY:** 2 in the danger window (3 for full curve lines, where
the criterion permits r = 3); at the prize schedule r = 2 up to K = 740 605 and
r = 3 up to K = 740 354.

**STRUCTURAL SOURCE:** the coefficient line lies on the low-degree algebraic
curve a + Z·b at s points, with W_K − K_eff·j < s·(m−j) for j < r. Nothing else
produced degeneracy in any experiment; in particular **no envelope case exists**
(0 found).

**MAX #Bad:** 9 (measured, n = 18). Growth exactly n/3 + 3 across
n = 9, 12, 15, 18. FATAL (invisible to the repair) = **1** in every instance.
Full curve lines: 1.

**SCALABLE:** yes as a *family* (the window has 87 904 values of s at ρ = 1/2),
but #Bad scales only linearly in n and FATAL does not scale at all.

**HARMLESS / DANGEROUS:** **HARMLESS.** #Bad ≪ B_prize = 2^57.93 by orders of
magnitude, and the fatal part is bounded by a theorem, not an observation:
whenever the module gcd is a power of (Y − c) one has N_G = S, so every FATAL
challenge is rigid and **FATAL ≤ 1** for all n, K, s.

**ANNIHILATOR FAMILY CONSTRUCTED:** **YES** (symbolically, on paper; not
formalized, as instructed).

**EXACT B:** 1 386 904 900 024 = 2^40.3350 (ρ = 1/2); 1 245 024 911 257 =
2^40.1793 (ρ = 1/4).

**ACTUAL-FIELD MCA BUDGET:** KoalaBear sextic → B_max = 2^57.9321, **fits**,
ε_mca ≤ 2^−145.5971. Under the artificial |F| ≥ 2^160 simplification B_max = 2^32
and it does **not** fit — that hypothesis must be dropped, not the construction.

**ESCAPE/STRUCTURE DICHOTOMY SURVIVES:** **YES.** Both branches produce a
prize-sufficient B (2^40.34 generic / ≤ 1 rigid). It is a candidate, not a
theorem: one step in each branch is unproved.

**JOHNSON CONSEQUENCE:** the Johnson repair is **not killed**. Better: the
mechanism that would kill it (forced degeneracy at K ≥ t) is *equivalent* to the
failure of Johnson, k·n < t². Degeneracy and Johnson are the same inequality.

**GAIN OVER δ = 1/4:** **+10.620 bits** at 128 queries (ρ = 1/2). Not +27.745,
which is measured against the weaker local radius 0.177124.

**DECISION:** **REDUCE.** Not KILL (no counterexample), not yet PROVE/FORMALIZE
(two unproved steps).

**NEXT SINGLE BOTTLENECK:** the **converse of the forcing criterion** —
prove that a forced common repeated factor implies curve degree
K ≤ k + (n·m − L)/b_Y (equivalently: that the module escapes whenever the
expected dimension permits it). Counting alone provably cannot do this for
K > k; it needs a genuine non-vanishing/genericity argument for the sheared
image of V. Secondary: the pencil step making a chosen interpolant's repeated
part equal the module's forced common factor, and the h ≥ 2 (higher Y-degree)
common-factor case, currently covered only by an expected-dimension cap.

---

## HONESTY CAVEATS

1. **No Lean was added this session** (mission scope). No claim here is
   machine-checked; the arithmetic and the small-model algebra are exact
   computations, the structural statements are paper proofs.
2. (FORCE_r) is rigorous only as a **sufficient** condition. Its sharpness is
   experimental: 185 cells (M1 40, M2 40, M3 45, M4 60) with **3 mismatches**,
   all of the form "measured multiplicity = predicted + 1" at boundary cells
   (M2 K=3,s=8; M4 K=4,s=10; M4 K=5,s=12). **No cell ever had a forced factor
   where the criterion predicted none** — excess forcing occurred only at r ≥ 2.
3. Small-model Z-handling uses random specialisations Z = z₀; ranks are generic
   for all but finitely many z₀, and several z₀ were used per verdict.
4. The general-common-factor cap (deg_Y H = h ≥ 2) is an **expected-dimension**
   bound, not a proof.
5. The GATE 7 search is exhaustive only over the enumerated witness-set
   combinations (up to N = 8 prescribed bad challenges, 60 combinations each);
   it *solves* the interpolation constraints rather than sampling, but a larger
   #Bad in some unexplored corner of the same cells is not excluded.
