# FALSIFY-FIRST: the regular rank cap `m(n−e−k) ≤ 2(n−k)` on the smooth domain

**Status of this note.** It is an *exact-arithmetic* investigation (integer arithmetic modulo a
prime, no floating point), not a Lean theorem. Nothing in the Lean development was changed and
nothing here is machine-checked. Scripts:

* `analysis/smooth_rank_cap_kill.py` — the stacked matrix in both coordinate systems, and the
  exact FULL-MCA realisability criterion;
* `analysis/smooth_rank_cap_search.py` — the structured search that found the counterexample;
* `analysis/smooth_rank_cap_witness.py` — explicit witnesses, verified against the *definition*
  of `Root.CodingTheory.IsBad` by brute force (interpolate on the window, compare on the window);
* `analysis/smooth_rank_cap_probe.py` — the sector prediction and the max-`m` probe;
* `analysis/smooth_rank_cap_structure.py` — STEP 4 structure detection.

Notation as in `NONJOHNSON_INTERIOR_MEASUREMENT.md`: `n = |D|`, `k`, radius `e`,
`c := n − e − k`, `κ := n − k`, `ρ = k/n`, `δ = e/n`; `C = RS_k(D)`, `C^⊥` its dual;
window `S_i = D ∖ Z_i`, `|Z_i| = e`.

---

## STEP 1 — EXACT STACKED MATRIX

For a window `S` put `w^S_x := (∏_{y∈S, y≠x}(x−y))^{-1}` (the GRS multipliers of the shortened
code `RS_k|S`). Then `f|S` extends to a codeword of degree `< k` **iff**

```
      σ_S(f)_t  :=  Σ_{x∈S} w^S_x · x^t · f(x)  =  0        for  t = 0, …, |S|−k−1 .
```

**EXACT STACKED MATRIX.** `M ∈ F^{(m·c) × 2n}`, rows indexed by `(i,t)`, `1 ≤ i ≤ m`,
`0 ≤ t < c`, columns split into an `f₀`-block and an `f₁`-block of `n` columns each:

```
      M[(i,t), (0,x)]  =  1_{x∈S_i} · w^{S_i}_x · x^t
      M[(i,t), (1,x)]  =  γ_i · 1_{x∈S_i} · w^{S_i}_x · x^t
                                                          M · (f₀ , f₁)ᵀ = 0 .
```

Row `(i,t)` is exactly `σ_{S_i}(f₀ + γ_i f₁)_t = 0`.

**Dual-polynomial form (the one used in all computations).** Under `C^⊥ ≅ P := F[x]_{<n−k}`,
`g ↦ (v_x g(x))_x`, the row space of `M` is

```
      Row(M)  =  Σ_{i=1}^m  { (g , γ_i g) : g ∈ R_i } ⊆ P ⊕ P ,
      R_i     =  A_i · F[x]_{<c} ,      A_i(x) = ∏_{z ∈ Z_i} (x − z) ,   dim R_i = c ,
```

so `M` is equivalent to an `mc × 2(n−k)` matrix (verified: `check_rank_agreement`). In
particular `ker M ⊇ C × C` (dim `2k`), whence **`rank M ≤ 2(n−k)` unconditionally**.

**REQUIRED RANK.** The cap is *exactly* the full-row-rank statement

```
      rank M  =  m·c  =  m(n − e − k) .                                        (RANK)
```

Combined with `rank M ≤ 2(n−k)` it gives `m(n−e−k) ≤ 2(n−k)`.

**Precise corrected version.** FULL MCA forces `ker M ⊋ C × C`, i.e. `rank M ≤ 2(n−k) − 1`, so
the honest form of the claim is

```
      (RANK)  ⟹   m(n − e − k)  ≤  2(n − k) − 1 ,
```

and the *bound* one actually wants is `m ≤ ⌊(2(n−k) − 1)/c⌋`.

**MCA-SPECIFIC HYPOTHESES** (as opposed to "arbitrary subsets `S_i`"):

| # | hypothesis | source | load-bearing? |
|---|---|---|---|
| H1 | `σ_{S_i}(f₀ + γ_i f₁) = 0` | `IsCloseOn` clause of `IsBad` (with `|S_i| ≥ n−e`) | defines `M` |
| H2 | **`σ_{S_i}(f₁) ≠ 0` for every `i`** | `¬ LineCloseOn S_i f₀ f₁` clause of `IsBad` — *this is the whole FULL-MCA content* | **yes — decisive (STEP 3)** |
| H3 | the `γ_i` are pairwise distinct | counting distinct bad challenges | makes `V_i ∩ V_j = 0` automatic |
| H4 | `|S_i| = n − e` exactly | worst case of `|S_i| ≥ n − e` (larger windows give larger `c_i ≥ c`) | conservative |
| H5 | `f₁` is not a codeword | else `badSet = ∅` (`badSet_eq_empty_of_direction_codeword`) | needed only to have `m ≥ 1` |

Not from MCA: **regularity** `|S_i ∩ S_j| ≤ k` is an extra combinatorial restriction that
defines the residual (`|T| = k`) layer — it prevents two-point interpolation from producing a
common codeword pair. And, crucially, **(RANK) itself is not an MCA hypothesis**: it is a
genericity property of the evaluation points (STEP 2).

Given H1–H3, `(f₀,f₁)` is equivalent to a pair of functionals `(λ₀,λ₁)` on `P` with
`λ₀ + γ_i λ₁ ∈ W_i := Ann(R_i)` and `λ₁ ∉ W_i`; i.e. **a 2-plane `Λ = ⟨λ₀,λ₁⟩ ⊆ P^*` meeting
each `W_i` in a line `≠ ⟨λ₁⟩`**. With
`N := {(h_i) : deg h_i < c, Σ A_i h_i = 0}` and `K := {Σ γ_i A_i h_i : (h_i) ∈ N}` one gets the
exact criterion used throughout below (`mca_realisable`):

```
      a FULL-MCA family with windows {S_i} and challenges {γ_i} exists
                     ⟺        R_i ⊄ K   for every i          (|F| > m).
```

---

## STEP 2 — HIGHER-ORDER-MDS COMPARISON

`dim Σ_i R_i = (n−k) − dim ⋂_i span{ ev_z : z ∈ Z_i }` — the right-hand intersection is
*literally* the quantity whose genericity defines higher-order MDS / GM-MDS for the sets `Z_i`.
But (RANK) does not ask for that: it asks that the **twisted** subspaces
`V_i = {(g, γ_i g) : g ∈ R_i} ⊆ C^⊥ ⊕ C^⊥` be in direct sum. Since `Σ_i R_i` lives in an
`(n−k)`-dimensional space while `Σ_i V_i` lives in a `2(n−k)`-dimensional one, (RANK) permits
`mc` up to `2(n−k)` where plain MDS(m) for the `R_i` would force `mc ≤ n−k`.

```
RELATION TO MDS(m):   SAME AS HIGHER-ORDER MDS, in twisted (doubled) form —
                      strictly weaker than plain MDS(m) for the R_i in C^⊥,
                      and NOT MCA-specific.
```

Consequences, all confirmed below: (RANK) is a statement about the *evaluation points*, it is
implied by (and only by) a genericity property of the `Z_i`, it is neither implied by nor
implies FULL MCA, and — like higher-order MDS — **it is false on structured (smooth) domains**.

---

## STEP 3 — SMOOTH-DOMAIN KILL TEST

Domain: the project's smooth domain, `D` = multiplicative subgroup of order `n = 2^ν` of `F_q^*`
or a coset of one (`q = 12289`, cross-checked `q ∈ {40961, 2^31−2^27+1}`; no dependence on `q`).
Only quotient / subcoset / symmetric window patterns were used; random search is the baseline.

### 3a. The mechanism (proved by hand, then measured)

If every `Z_i` is a union of cosets of the subgroup `H ≤ D` of order `h`, then
`A_i(x) = B_i(x^h)`, so `M` is **block diagonal over the `h` residue sectors of the degree**:

```
      rank M  =  Σ_{r<h} rank M_r ,       rank M_r ≤ min( m·c_r , 2·κ_r ) ,
      c_r = #{ j < c : j ≡ r (mod h) } ,  κ_r = #{ j < n−k : j ≡ r (mod h) } .
```

Each sector is *the same problem on the quotient group* `D/H`. Measured: the inequality is an
equality (`rank = pred`) in **every** instance tested. Because `Σ_r 2κ_r = 2(n−k)` but the two
caps `m c_r` and `2κ_r` bind unevenly across sectors, the total can fall strictly below both
`mc` and `2(n−k)` — which is exactly what a bad family needs.

### 3b. Pure coset windows (`h = e`) — deficient but **killed by FULL MCA**

`Z_i` = `m` disjoint cosets of the subgroup of order `e` gives `A_i = x^e − b_i`, and for `c ≤ e`
one computes `rank M = c·min(m,4)`: massively deficient for `m ≥ 5`
(e.g. `n=256, k=194, e=32, m=8`: `rank = 120` vs `mc = 240`, `2(n−k) = 124`).
**But every kernel element has `σ_{S_i}(f₁) = 0` for all `i`.** Proof: `λ ∈ W_i` reads
`λ_{e+j} = b_i λ_j (j < c)`, so the conditions say
`λ₀_{e+j}·1 + λ₁_{e+j}·γ_i − λ₀_j·b_i − λ₁_j·(b_iγ_i) = 0` for all `i`; as soon as the vectors
`(1, γ_i, b_i, b_iγ_i)` span `F⁴` (`m ≥ 4`, generic), all four coordinates vanish, hence
`λ₁ ∈ W_i` for every `i`. Measured: 0/200 kernel vectors satisfy MCA on even one window.
So H2 is genuinely load-bearing and this route does **not** kill the cap.

### 3c. Symmetric / sub-coset windows — the **cap does fall**

Take `h` a *proper* divisor of `e` (`h = 2`: `Z_i` closed under `x ↦ −x`). Then the sector split
above is uneven and a genuine FULL-MCA family exceeds the cap. Verified end-to-end against the
definition of `IsBad` (interpolate on the window; check closeness of `f₀+γ_if₁`, and failure of
closeness for `f₀` and `f₁` separately):

| q | n | k | e | c | 2(n−k) | h | m | m·c | rank M | sector pred | δ | interior `2e−(n−k)` | `(n−e)²−nk` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 12289 | 32 | 15 | 10 | 7 | 34 | 2 | **5** | **35 > 34** | 33 | 33 | 0.3125 | 3 | +4 |
| 12289 | 64 | 29 | 20 | 15 | 70 | 4 | **5** | **75 > 70** | 69 | 69 | 0.3125 | 5 | +80 |
| 12289 | 64 | 30 | 20 | 14 | 68 | 4 | **5** | **70 > 68** | 66 | 66 | 0.3125 | 6 | +16 |

All three rows are **strictly above unique decoding** (`2e ≥ n−k+2`), **strictly below the
Johnson radius** (`(n−e)² > nk`), and **regular** (measured pairwise `|S_i ∩ S_j| ∈ {24,28} ≤ k`
at `n=64`, and `≤ k−1` in every row, so the family is regular in both conventions). All `m` challenges are brute-force certified bad, and no
window carries a correlated pair. The same parameters with *unstructured* regular windows give
`rank M = 2(n−k)` and **no** realisable family at `m = 5` (0/6 … 0/12 trials), i.e. the cap holds
there — the violation is created by the smooth structure, not by the parameters.

```
SMOOTH COUNTEREXAMPLE FOUND:  YES   (FULL MCA + regular + m(n−e−k) > 2(n−k),
                                     and simultaneously rank M < m(n−e−k))
```

### 3d. How far does it scale?

The mechanism is available at every size: instances with sector-corrected cap
`> ⌊2(n−k)/c⌋` and rate `ρ ∈ [0.45,0.55]` exist for `n = 32, 64, 128, 256, 1024, 4096`
(1, 4, 8, 16, 30, 19 of them respectively, e.g. `n=4096, k=1935, e=1280, h=64`).
**But the excess is always
exactly `+1`:** in the whole scan the sector-corrected cap never exceeded
`⌊2(n−k)/c⌋ + 1` at rate ≈ 1/2, and the probe confirms `m = cap+1` realisable, `m = cap+2` not
(`rank M` saturates at `2(n−k)`), matching the sector prediction exactly.

```
SCALABLE:  YES for the falsification (the +1 violation persists at fixed rate and radius,
           n = 32 … 4096) — NO for any growth: the excess stays +1, m = O(1) throughout,
           and at the cash-out parameters the mechanism is blocked outright (STEP 5).
```

The blocking rule is a divisibility fact: if `h | n` and `h | k` (so `h | κ`) and `h | |Z_i|`
(so `h | c`), then `c_r = c/h` and `κ_r = κ/h` for every sector, hence
`2κ_r/c_r = 2κ/c` and the sector correction is *vacuous*. The counterexamples all need
`κ` or `c` **not** divisible by `h` — i.e. `k` not a multiple of the symmetry order.

---

## STEP 4 — IF RANK FAILS, TEST STRUCTURE

Tested on the verified `n=32, k=15, e=10, m=5` instance (`smooth_rank_cap_structure.py`):

| detector | verdict |
|---|---|
| `WelchBerlekampPencil` (`wbDet`) | **unavailable**: a maximal minor needs `k+2e+1 ≤ n`, here `36 > 32` — the `ForcingBarrier`. Every interior instance is past it. |
| `SubresultantCore` / `GcdPencilEscape` | live on the same WB pencil / interpolant pencil, so equally unavailable in the interior; no degenerate gcd is exhibited by the instance. |
| affine / common factor (`AffineFactorSplit`, `MCAPairCover`) | **no**: the 10 challenge pairs induce **10 distinct** codeword pairs, with common agreement `|T| = 12` or `14`, i.e. **strictly below `k = 15`**. No pair explains two challenges, so the structured layer is empty and `F ≤ n` has nothing to act on. |
| `codewordLocus` | not triggered — there is no repeated interpolant part here; the instance is a pure syndrome-geometry object. |
| annihilator family — *span* | **no**: `dim span{A_i} = 5 = m`, full. The naive "annihilator degeneracy" detector does not see it. |
| annihilator family — *grading* (new) | **YES**: every `A_i` is a polynomial in `x^h` (`h = 2` resp. `4`); the deficiency equals the sector prediction `Σ_r min(mc_r, 2κ_r)` in every instance measured. |

```
RANK FAILURE ⇒ EXISTING STRUCTURE:  NO
     (⇒ NEW structure: the H-grading of the windows / sector split of the syndrome space,
      which is not one of the objects currently in the development)
```

---

## STEP 5 — CASH-OUT at `n = 2²⁰`, `k = 2¹⁹`

`κ = 2(n−k)/2 = 2¹⁹`, `2(n−k) = 2²⁰`. Sector-corrected cap = maximum over all window sizes
`z ≤ e` and all `h | gcd(n,z)` of `max_{r : c_r ≥ 1} ⌊(2κ_r − 1)/c_r⌋` (computed exactly):

| radius | `e` | `c` | `2(n−k)/c` | plain cap `⌊2(n−k)/c⌋` | sector-corrected cap |
|---|---|---|---|---|---|
| `δ = 1/4 + 2⁻²⁰` | 262145 | 262143 | 4.0000153 | 4 | **4** (attained only at `h = 1`) |
| safe Johnson `δ = 1 − √ρ` | 307120 | 217168 | 4.8284 | 4 | **4** |

The corrected cap coincides with the plain cap here because `k = 2¹⁹` makes `h | κ` and `h | c`
for every admissible symmetry order `h`, which annihilates the sector correction (§3d).

```
RESULTING m CAP AT 1/4:            m ≤ 4
RESULTING m CAP AT SAFE JOHNSON:   m ≤ 4
```

**#Bad scale.** With `AffineFactorSplit.card_badPairSet_le` (`F ≤ n`, proved) and the residual
layer capped at `m ≤ 4`:

```
      #Bad  ≤  P · F  +  m   ≤  P · n  +  4 ,
```

`P` = number of distinct codeword pairs with `|T| ≥ k+1` that actually explain a challenge.
So the total is `O(n)` — in fact `≤ 4n + 4` — **as soon as `P = O(1)`**; the measurement puts
`P ≤ 6` on every interior row tested, but the only *proved* substitute today is the list size in
`MCAPairCover.card_badSet_le_pairCover` (`#Bad ≤ n·Λ(k,τ)² + O(n)`). No polynomial in `n` other
than the linear one appears: the residual layer contributes `O(1)`, each pair contributes `≤ n`.

```
RESULTING #BAD SCALE:   4n + 4  (i.e. O(n))  conditional on P = O(1);
                        unconditionally still n·Λ(k,k+1)² + O(n).
```

---

## RETURN

```
EXACT STACKED MATRIX:
    M ∈ F^{mc × 2n},  rows (i,t), i ≤ m, t < c := n−e−k,  columns (f0-block | f1-block):
        M[(i,t),(0,x)] = 1_{x∈S_i}·w^{S_i}_x·x^t ,   M[(i,t),(1,x)] = γ_i·1_{x∈S_i}·w^{S_i}_x·x^t
        w^{S}_x = (∏_{y∈S, y≠x}(x−y))^{-1} ;         M·(f0,f1)ᵀ = 0 .
    Dual form: Row(M) = Σ_i {(g, γ_i g) : g ∈ A_i·F[x]_{<c}} ⊆ (F[x]_{<n−k})²,
               A_i = ∏_{z∈D∖S_i}(x−z).

REQUIRED RANK:
    rank M = m(n−e−k)   (full row rank).  Since ker M ⊇ C×C, rank M ≤ 2(n−k) always, and
    FULL MCA forces ker M ⊋ C×C, so the corrected consequence is
        m(n−e−k) ≤ 2(n−k) − 1 .

MCA-SPECIFIC HYPOTHESES:
    H2  σ_{S_i}(f1) ≠ 0 for every i   (= ¬LineCloseOn S_i, the "no correlated pair on the
        witness window" clause of IsBad) — decisive, it kills the coset-window collapse;
    H1  σ_{S_i}(f0+γ_i f1) = 0 with |S_i| ≥ n−e;   H3 γ_i pairwise distinct;
    H5  f1 not a codeword.
    NOT from MCA: regularity |S_i ∩ S_j| ≤ k (a combinatorial layer definition), and — above
    all — the independence/genericity (RANK) itself.

RELATION TO MDS(m):
    SAME AS HIGHER-ORDER MDS (twisted/doubled form: the V_i = {(g,γ_i g) : g ∈ R_i} must have
    generic minimal intersection in C^⊥⊕C^⊥); strictly weaker than plain MDS(m) for the R_i;
    independent of MCA.  Hence not MCA-specific, and it fails on structured domains.

SMOOTH COUNTEREXAMPLE FOUND: YES
    q=12289, D = subgroup of order 32, k=15, e=10, c=7, m=5 negation-closed windows:
    m·c = 35 > 34 = 2(n−k), rank M = 33; all 5 challenges brute-force IsBad; regular;
    2e−(n−k)=3 (strict interior);  (n−e)²−nk = +4 (strictly below Johnson).
    Also n=64: (k,e,h,m) = (29,20,4,5) with 75 > 70, and (30,20,4,5) with 70 > 68.

SCALABLE: YES for the falsification, NO for growth
    the +1 violation exists at n = 32 … 4096 at fixed rate/radius, but the excess over
    ⌊2(n−k)/c⌋ never exceeded +1 anywhere, and it is blocked when h | (n−k) and h | c.

RANK FAILURE ⇒ EXISTING STRUCTURE: NO
    WB pencil unavailable past the forcing barrier (k+2e+1 > n); no common codeword pair
    (all induced |T| = 12,14 < k = 15); span{A_i} full.  The deficiency is detected only by a
    NEW object: the H-grading of the windows (sector split of the syndrome space).

RESULTING m CAP AT 1/4:            4
RESULTING m CAP AT SAFE JOHNSON:   4
RESULTING #BAD SCALE:              ≤ 4n + 4 = O(n) given P = O(1) explaining pairs;
                                   unconditionally n·Λ(k,k+1)² + O(n) (already proved).

DECISION:  KILL the rank-cap route as stated  →  PROVE DICHOTOMY (graded form).
    The literal theorem "regular FULL-MCA ⇒ rank M = m(n−e−k)" and its corollary
    "m(n−e−k) ≤ 2(n−k)" are both FALSE on the smooth domain.  What survives, and matches
    every measurement, is the graded statement plus the divisibility side condition that
    holds at the cash-out parameters.

NEXT SINGLE LEMMA:
    (Lean, in the dual coordinates of Root/SyndromeSpace.lean; no genericity assumed)
        Let R_i ⊆ C^⊥ be the shortened dual of S_i, N = {(h_i) : Σ A_i h_i = 0, deg h_i < c},
        K = { Σ γ_i A_i h_i : (h_i) ∈ N }.  If γ_1..γ_m are distinct bad challenges with
        witness windows S_i and the line satisfies FULL MCA, then
              R_i ⊄ K   for every i,
        and consequently rank M ≤ 2(n−k) − 1;  if moreover the twisted family
        {(g,γ_i g) : g ∈ R_i} is in direct sum then m(n−e−k) ≤ 2(n−k) − 1.
    This isolates exactly the FULL-MCA hypothesis (H2), is true as stated, and makes the
    now-refuted genericity hypothesis explicit instead of hiding it.
    Immediately afterwards: the H-grading lemma  rank M = Σ_{r<h} rank M_r  for H-closed
    windows (unconditional, one page), which is the counterexample generator and the reason
    the direct-sum hypothesis cannot be dropped.
```
