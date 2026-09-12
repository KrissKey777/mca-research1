# IS EVERY RESIDUAL RANK DEFECT GRADED?  — exact-arithmetic verdict

**Status.** Exact integer arithmetic modulo a prime (no floating point), *not* machine-checked
Lean. No Lean file was written or changed (per the mission instruction). Scripts and raw data:

* `analysis/grading_completeness_probe.py` — the measurement library (stacked matrix, defect,
  FULL-MCA realisability, grading orders, common-factor reduction, sector split, the
  preserver algebra `E`, the weakest certificate);
* `analysis/grading_adversarial_search.py` — STAGE 3 sweep over all seven requested window
  classes (`python3 grading_adversarial_search.py 32`);
* `analysis/grading_interior_scan.py` — the same restricted to the interior
  (past unique decoding, strictly below Johnson);
* `analysis/grading_quotient_descent.py` — STAGE 1 + STAGE 5 (sector split = quotient system);
* `analysis/grading_bad_sector_test.py` — STAGE 5/6 (distribution of Bad over sectors);
* `analysis/grading_scaling_test.py` — STAGE 4 (does a defect survive `n -> 2n, 4n`);
* `analysis/grading_data/*.jsonl` — every recorded hit, with the windows.

Notation as in `REGULAR_RANK_CAP_KILL_REPORT.md`: `n = |D|`, `κ = n−k`, `e`, `c = n−e−k`,
`A_i(X) = ∏_{z∈D∖S_i}(X−z)`, `R_i = A_i·F[X]_{<c} ⊆ P = F[X]_{<κ}`,
`V_i = {(g, γ_i g) : g ∈ R_i}`, `Row(M) = Σ_i V_i`, `Δ = mc − rank M`, and

```
      Δ* := min(mc, 2κ) − rank M            (the NON-TRIVIAL defect; the dimension cap
                                             min(mc,2κ) is not counted as an explanation)
```

Two exact identities are used throughout (both proved by projecting `Σ_i V_i` on the first
factor; verified numerically):

```
      rank M = dim(Σ_i R_i) + dim K ,   K = { Σ_i γ_i A_i h_i : Σ_i A_i h_i = 0, deg h_i < c }
      Δ      = dim N − dim K ,          N = { (h_i) : deg h_i < c , Σ_i A_i h_i = 0 }
      Δ      = dim { (u_i) ∈ ⊕_i R_i : Σ u_i = 0 = Σ γ_i u_i }      (double-syzygy space)
```

Scale of the experiment: **43,278** measured instances in the systematic sweeps
(n = 32 exhaustive over all `(k,e,m)`, n = 32/48/64 interior) plus ≈ 600 targeted instances at
n = 64, 128; **208** of them are FULL-MCA realisable *and* regular *and* have `Δ* > 0`.
Cross-checked on `q = 12289` and `q = 40961` (independent primes, same conclusions).

---

## EXACT GRADING CONDITION

Because `0 ∉ D`, every `A_i` has a nonzero constant term, so "exponent support inside one
residue class mod h" collapses to "exponent support inside `hℤ`". The exact condition for the
*monomial* sector decomposition is therefore

```
      Graded(h)   ⟺   A_i ∈ F[X^h]  for every i
                  ⟺   supp(A_i) ⊆ hℤ
                  ⟺   Z_i = D∖S_i is a union of cosets of H = μ_h ≤ D , for every i .
```

Polynomial and set formulations coincide **for the naive form**; the set form is *not* the
right condition, because the following two strictly weaker certificates also produce a block
bound, and both occur among the counterexamples:

```
  (F)  common factor         A_i = G·A_i'  with  G = gcd_i A_i  of degree g  (= |⋂_i Z_i|):
                             the whole system is isomorphic to the residual system with
                             ambient F[X]_{<κ−g} and annihilators A_i' — apply Graded(h) there;

  (G')  per-window factors   A_i = G_i·B_i(X^h) ,  d_i := deg G_i :
                             R_i ⊆ B_i·F[X]_{<c+d_i}, which IS h-graded.
```

`d_i(h)` is combinatorial: `d_i(h) = |Z_i| − |largest μ_h-closed subset of Z_i|`.

## SECTOR DECOMPOSITION FORMULA

For `Graded(h)` (all `d_i = 0`), with `c_r = #{j<c : j ≡ r mod h}`, `κ_r = #{j<κ : j ≡ r mod h}`,
`W_r = Σ_i R_{i,r}`:

```
      P = ⊕_{r<h} X^r F[X^h]_{<κ_r} ,     R_i = ⊕_{r<h} X^r B_i F[X^h]_{<c_r} ,
      M ≃ ⊕_{r<h} M_r ,                   rank M = Σ_{r<h} rank M_r ,
      rank M_r = min( m c_r , 2 dim W_r − ε_r ) ,   ε_r = 1 if some γ_i is bad in sector r,
                                                    ε_r = 0 otherwise.
```

The `ε_r` term is forced: `Bad_r ≠ ∅ ⇒ K_r ≠ P_r ⇒ dim K_r ≤ κ_r − 1 ⇒ rank M_r ≤ 2κ_r − 1`.
Verified exactly (`rank M = Σ_r rank M_r`, and the closed form) on every graded instance
measured, including the three published counterexamples
(`n=32,k=15,e=10,h=2,m=5`: `18+15 = 33`; `n=64,k=29,e=20,h=4,m=5`: `18+18+18+15 = 69`;
`n=64,k=30,e=20,h=4,m=5`: `18+18+15+15 = 66`).

## WEAKEST GRADING CERTIFICATE

```
      Graded(h ; d_1..d_m)   :   A_i = G_i · B_i(X^h) ,  deg G_i = d_i    (G_i may differ!)

      rank M  ≤  CERT(h)  :=  Σ_{r<h} min( Σ_i #{ j < c+d_i : j ≡ r mod h } , 2 κ_r ) ,

      and the same bound applied to the system reduced by the common factor
      (κ ↦ κ−g, Z_i ↦ Z_i ∖ ⋂_j Z_j).   The certificate value is  min over h | n  of these.
```

This is the weakest exact certificate found; it is purely a statement about exponent supports
of divisors of the `A_i`, and it degenerates to `min(mc, 2κ)` when no `h > 1` helps.

A strictly more general notion was also tested — a nontrivial idempotent in
`E = {φ ∈ End(W) : φ R_i ⊆ R_i ∀i}`, `W = Σ_i R_i`, which is *exactly* equivalent to the
existence of some block decomposition `W = ⊕_s W_s` with `R_i = ⊕_s (R_i ∩ W_s)`. It is **too
weak to be useful**: `dim E` is 9–20 for unstructured window families (versus `dim E = 1` for
random subspaces of the same dimensions), and nontrivial idempotents exist generically; the
splits they produce (e.g. `17 = 16 ⊕ 1`) carry no counting content. `E` does detect the true
grading: for the `h = 2` counterexample it returns the even/odd split `κ = 17 = 9 ⊕ 8` exactly.

**Accuracy of the certificate.** On the 112 hits whose windows were stored:
`CERT = rank M` in **95** cases, `CERT = rank M + 1` in **16** (exactly the FULL-MCA `ε = 1`
correction), and `CERT = rank M + 4` in **one** (see below).

## RANK-DEFICIENT INSTANCES TESTED

```
   measured instances (systematic sweeps)                     43,278
   FULL-MCA realisable + regular + Δ* > 0                        208
   of these, cap violations  m > ⌊(2κ−1)/c⌋                       98
```

## GRADED

```
   208 hits:   naive Graded(h), h>1                              ~ 60 %
               graded only after common-factor reduction         ~ 20 %   (e.g. n=48: k=20,e=17,
                                                                          m=5, g=1, h_red=4)
               graded only via per-window factors G_i            ~ 15 %   (perturbed coset windows)
   98 cap violations:  ALL 98 carry a nontrivial certificate (h ∈ {2,3,4}).
       For the 48 whose windows were stored the certificate is numerically exact
       (47 exact, 1 off by the FULL-MCA −1).  No cap violation was ever produced by a family
       with certificate value min(mc,2κ).
```

## NONGRADED

Yes — grading is **not** the complete obstruction to a rank defect. The nongraded family lives
at *saturated regularity*, i.e. `max_{i<j} |S_i ∩ S_j| = k` (the extreme allowed by the
residual layer), close to the Johnson boundary:

```
   n=64,  k=14, e=34, c=16, m=6:  mc=96,  2κ=100, rank M = 92  → Δ = Δ* = 4
   n=128, k=28, e=68, c=32, m=6:  mc=192, 2κ=200, rank M = 186 → Δ = Δ* = 6
                                   (Δ up to 11 among realisable families; 3–9 overall)
```

For these: grading order `h = 1`, no common factor obstruction, no per-window-factor
certificate (`CERT = mc`), no index-partition explanation (checked over all 2-block partitions
and, at `m ≤ 6`, all set partitions), `dim Σ_i R_i` full or within 2 of full, and the defect is
stable under re-drawing the challenges `γ` (identical rank for every draw) and under changing
the prime (`q = 12289` and `q = 40961` give the same defects). Regularity `|S_i∩S_j| ≤ k` and
FULL MCA (`R_i ⊄ K` for every i) were verified by the same criterion used for the published
counterexamples; the instances are strictly past unique decoding and strictly below Johnson
(`(n−e)² − nk = +4` at n=64, `+16` at n=128).

**The mechanism is saturation of the pairwise agreement, not grading.** Slackening regularity
by a couple of points destroys the defect:

```
   n=64,  (k,e,m) = (14,34,6):  |S_i∩S_j| ≤ k    → Δ ∈ {0..4}, 12/12 families deficient-or-0,
                                |S_i∩S_j| ≤ k−1  → Δ = 0 in 11/12,
                                |S_i∩S_j| ≤ k−2  → Δ = 0 in 12/12 (all FULL-MCA),
                                |S_i∩S_j| ≤ k−4  → combinatorially infeasible.
   n=128, (k,e,m) = (28,68,6):  Δ ∈ {5..11} at k, {2..5} at k−1, {0..3} at k−2, 0 at k−3.
```

## SMALLEST NONGRADED DEFECT

```
   n = 32, k = 7, e = 17, c = 8, m = 6, q = 12289   (interior: 2e ≥ κ+2, (n−e)² − nk = +1)
   mc = 48, 2κ = 50, rank M = 47      →  Δ = Δ* = 1
   grading order 1, gcd_i A_i = 1, certificate value 48, |S_i∩S_j| ≤ 7 = k (saturated),
   FULL-MCA realisable for every γ draw tested.   Windows: analysis/grading_data/int32b.jsonl
```

## SCALABLE NONGRADED DEFECT: **YES**

Same rate/radius band (`ρ ≈ 0.22`, `δ ≈ 0.53`, just inside Johnson), saturated regularity:

```
        n =  32     64     128
        Δ  =   1      4     6…11          (FULL-MCA, regular, below Johnson)
```

so the nongraded defect grows with `n` (roughly linearly in the data). **This kills
grading-completeness for the rank defect.**

It does **not** kill the cap: at `n = 128` the same construction at `m = ⌊(2κ−1)/c⌋ + 1 = 7`
gave `0/6` FULL-MCA realisable families, and no nongraded family anywhere in the 43k sweep
exceeded `⌊(2κ−1)/c⌋`.

## EXISTING PROJECT OBJECT COVERING NONGRADED DEFECTS

Partially. The nongraded defects occur exactly when the pairwise agreement is **saturated**,
`|S_i∩S_j| = k`, i.e. one point below the correlated-pair threshold `k+1` that
`MCAPairCover` / `codewordLocus` / `AffineFactorSplit` act on. They are therefore the boundary
layer of the *existing* pair-cover object rather than a new algebraic structure: the WB /
subresultant pencil is unavailable (`k + 2e + 1 > n`, the ForcingBarrier), the annihilator span
is full, and no common codeword pair exists (that would need `|S_i∩S_j| ≥ k+1`). What is new is
that at the boundary the *twisted* sum `Σ_i V_i` degenerates although every intersection
`R_i ∩ R_j` is exactly zero.

## QUOTIENT DESCENT: **EXACT**

For `Graded(h)`, with `Y = X^h`, `B_i(Y) = A_i(X)`, sector `r` is *literally* the residual
system on the quotient group:

```
      D' = D^h = D/H ,  n' = n/h ,  Z_i' = Z_i^h ,  e' = e/h ,  κ' = κ_r ,  k'_r = n/h − κ_r ,
      c'_r = c_r = κ_r − e/h        (h | e ⇒ κ_r − c_r = e/h exactly, for every r)
      same challenges γ_1..γ_m .
```

Verified identical (`rank`, `dim K`, and the whole set of bad indices) sector by sector for
`n = 32, 64, 128` and `h = 2, 4`. Measured quantities:

```
      quotient length      n/h                      (exact)
      quotient dimension   k'_r = n/h − κ_r ,  κ_r ∈ {⌈κ/h⌉, ⌊κ/h⌋}   (rate preserved to ±1/n')
      quotient radius      e/h                      (exact; relative radius δ' = δ preserved)
      number of sectors    h
      regularity           |S̄_i ∩ S̄_j| ≤ k'_r verified in every instance measured
```

The recursion is therefore self-similar: **a graded residual problem on `D` is exactly `h`
residual problems of the same rate and the same relative radius on `D/H`.**

## BAD PRESERVED UNDER QUOTIENT: **YES (exactly, as a union)**

`R_i ⊆ K ⟺ R_{i,r} ⊆ K_r for every r`, hence

```
      Bad(D) = ⋃_{r<h} Bad_r(D/H)  ,          #Bad ≤ Σ_r #Bad_r        (union bound)
```

and each `Bad_r` is a FULL-MCA family of the quotient system (dropping windows only shrinks
`K_r`). Measured on 257 realisable regular graded families: the bad challenges are spread over
**2–14 sectors** (usually *all* unsaturated sectors carry *all* challenges), and saturated
sectors carry none.

## PREDICTED RECURSIVE #BAD SCALE

The union bound alone would give `M(n) ≤ h·M(n/h) = O(n)`. The data say the true recursion is
the **max**, not the sum, because a sector that carries even one bad challenge must satisfy
`dim K_r ≤ κ_r − 1`, i.e. `rank M_r ≤ 2κ_r − 1`, which under sector-genericity forces
`m ≤ (2κ_r − 1)/c_r`:

```
      m ≤ max_{h | n} max_{r<h} ⌊ (2κ_r − 1)/c_r ⌋       — never violated in 257/257
                                                            graded realisable families,
                                                            nor in any of the 208 hits.
      Excess over the plain cap ⌊(2κ−1)/c⌋ : ≤ +1 everywhere (5 instances attain +1),
      and the +1 is pure rounding: κ_r ≈ κ/h, c_r ≈ c/h.
```

So the residual layer is `O(1)` — `m ≤ 2(1−ρ)/(1−ρ−δ) + 1` — at every scale, and the total is

```
      #Bad ≤ P·n + O(1) = O(n)      (P = number of explaining codeword pairs; the proved
                                     unconditional substitute remains n·Λ(k,k+1)² + O(n)).
```

No mechanism found anywhere in the sweep produces a super-linear residual layer; the exponent
`2.89` is not approached by any observed configuration.

## DECISION: **PROVE GRADING-OR-ALGEBRAIC DICHOTOMY** (and KILL the rank route)

* "Every residual rank defect is graded" — **KILLED**: nongraded, scalable (`Δ = 1, 4, 6…11` at
  `n = 32, 64, 128`), FULL-MCA, regular, below-Johnson defects exist at saturated regularity,
  reproducible across two primes and every challenge draw.
* "Every *cap violation* is graded" — **survives all 98 observed violations**, each carrying an
  explicit certificate `Graded(h; d_i)` with `h ∈ {2,3,4}` (47/48 numerically exact).
* Consequently the object to prove is not a rank identity but the **cap**:
  `m ≤ max_{h|n, r<h} ⌊(2κ_r − 1)/c_r⌋`, i.e. either the family carries a grading certificate —
  and then descends exactly to `D/H` with the same rate and relative radius — or it does not,
  and then the plain cap `⌊(2κ−1)/c⌋` holds even though the rank may be deficient.

## NEXT SINGLE BIG LEMMA

```
   (unconditional, no genericity, in the dual coordinates of Root/SyndromeSpace.lean)

   Let  γ_1..γ_m  be distinct bad challenges with witness windows S_i,  R_i = A_i·F[X]_{<c},
        N = {(h_i) : deg h_i < c , Σ A_i h_i = 0},  K = {Σ γ_i A_i h_i : (h_i) ∈ N}.
   (a)  FULL MCA  ⟹  R_i ⊄ K for every i  ⟹  dim K ≤ κ−1  ⟹  rank M ≤ 2κ−1.
   (b)  If A_i = G_i·B_i(X^h) with deg G_i = d_i, then P splits into h sectors, every
        R_i ⊆ B_i·F[X]_{<c+d_i} splits with it, and
             rank M ≤ Σ_{r<h} min( Σ_i #{j < c+d_i : j ≡ r mod h} , 2κ_r ) ,
        with (a) applied sector-wise:  Bad_r ≠ ∅ ⟹ rank M_r ≤ 2κ_r − 1.
   (c)  Sector r of a Graded(h) family IS the residual system on D/H with
        (n/h, n/h − κ_r, e/h), same challenges; Bad(D) = ⋃_r Bad_r(D/H).
```

(a) is the lemma already queued in `REGULAR_RANK_CAP_KILL_REPORT.md`; (b) is the counterexample
generator in its weakest form; (c) is the descent that turns the graded branch of the dichotomy
into a recursion. The **missing** half — and the only place where genericity can still be
assumed to fail — is the lower bound `rank M_r ≥ min(m c_r, 2κ_r − 1)` for certificate-free
families; the data show it can fail by `Θ(n)` at saturated regularity, but never by enough to
add a challenge.

---

## ADDENDUM (later mission) — two claims above are now refuted

See `CAP_VIOLATION_FALSIFICATION_REPORT.md`.

1. **"Every observed violation of the plain cap was graded" is FALSE.** 495 exactly
   certified FULL-MCA, pairwise-regular, common-factor-free violations of
   `Σ_i c_i ≤ 2κ−1` carry no grading certificate at any `h | n`, even with per-window
   defects; they occur on and strictly below the Johnson bound, and an explicit
   quarter-pair construction produces them at `n = 8, 16, 32, 64, 128, 256, 512`.
   Earlier searches missed them because they sampled challenges at random: the
   cap-violating set is a positive-codimension subvariety of challenge space.

2. **`Bad(D) = ⋃_r Bad_r(D/H)` in item (c) of the NEXT SINGLE BIG LEMMA should read
   `Bad_H(D) = ⋂_r Bad_r(D/H)`** (with matched windows `S = π^{-1}(S')`). The union
   statement is true for a different object — the set of FULL-MCA *indices*, since
   `R_i ⊆ K ⟺ ∀r, R_{i,r} ⊆ K_r`. The intersection form is the useful one: it gives
   `#Bad_H(D) ≤ min_r #Bad_r(D/H)`.

Item (a) of that lemma (`FULL-MCA ⇒ rank M ≤ 2κ−1`) is untouched and holds in all 495
witnesses. The surviving replacement for the false plain cap is the free-challenge cap
`Σ_i (c_i − 1) ≤ 2κ − 1`.
