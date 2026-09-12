# STRENGTH_GATE_REPORT

Decisive strength gate on the conditional projected‑Rédei bound

```
R(n,e) = 2·C(n−1, 2e−1) − 1 .
```

Arithmetic/asymptotic triage only. No Lean file was created or modified, no theorem was
searched for or proved, no literature was consulted, no parameter sweep was run.

---

## TARGET

Recovered from the project sources (not from the prompt).

**Bad set and ε_mca** (`Root/CodingTheory/MCA.lean`, `AlphabetMCA.lean`):

```
badSet k e f₀ f₁ = { γ ∈ F : IsBad k e f₀ f₁ γ } ,
epsMCA k e f₀ f₁ = |badSet k e f₀ f₁| / |F|                      (uniform γ ∈ F)
epsMCAmax k e D  = max over lines (f₀,f₁) of epsMCA k e f₀ f₁ .
```

**Strong MCA** (`Root/CodingTheory/GG25LiteralMCA.lean`, `StrongMCA`, and proved equivalent to
GG25 Def. 2.8, `strongMCA_iff_GG25MCA`):

```
StrongMCA C δ err  ⟺  ∀ e ≤ δ·n, ∀ (u₀,u₁) :  |badSet C e u₀ u₁| / |F| ≤ err .
```

So the **conversion is exact and multiplication‑free**:

```
#Bad ≤ B   ⟹   ε_mca ≤ B/|F| ;      security condition:   B ≤ err·|F| .        (1)
```

**Target parameters** (`SOTA_PLAN.md` §2, §4; `RESULTS.md` §28, §31; `DISCREPANCIES.md` O21,
O22, O27): ordinary Reed–Solomon,

```
n = |D| = 2²⁰ ,   ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16} ,   err = ε_mca = 2⁻¹²⁸ ,
usable field sizes  |F| ∈ [2¹²⁸, 2²⁵⁶]   (proved certificates sit at 2¹²⁸…2¹⁶⁰;
                                          2⁶⁴ is proved unsatisfiable, O22).
```

Open band the gate is about (SOTA_PLAN §2): at ρ = 1/2 no sub‑exponential‑field certificate
exists for `δ ∈ (1/6, 1−√ρ ≈ 0.2929)`.

**Validity regime of R(n,e)** (`ARISTOTLE_SUMMARY.md` P1/P2, `PROJECTED_REDEI_CLAIMS.md` §4.2):
MDS/RS, `F` **prime**, non‑collinear witness selection, and

```
k + 2e ≤ n   ⟺   δ ≤ (1−ρ)/2 ,                                                (2)
```

with `M*_L ≤ 1 + C(n−1,2e−1)` and Szőnyi `|B| ≤ 2M*_L − 3` quoted, not proved.

---

## SUBSTITUTION

Insert `R(n,e)` into (1):

```
PASS(n,k,e,|F|,err)   ⟺   2·C(n−1, 2e−1) − 1  ≤  err·|F|  = 2⁻¹²⁸·|F| ,        (3)
```

equivalently, in bits, with `T = log₂(err·|F|) = log₂|F| − 128`:

```
1 + log₂C(n−1,2e−1)  ≤  log₂|F| − 128 .                                        (4)
```

Margin (bits): `M = (log₂|F| − 128) − log₂R(n,e)`.

---

## PHASE BOUNDARY

Rigorous brackets (`(m/r)^r ≤ C(m,r) ≤ (em/r)^r`; `2^{mH(r/m)}/(m+1) ≤ C(m,r) ≤ 2^{mH(r/m)}`):

```
(2e−1)·log₂((n−1)/(2e−1))        ≤  log₂C(n−1,2e−1)  ≤  (2e−1)·log₂(e·(n−1)/(2e−1))   (5)
(n−1)H(2δ') − log₂ n             ≤  log₂C(n−1,2e−1)  ≤  (n−1)H(2δ'),   δ' = (2e−1)/(2(n−1)) (6)
```

Two regimes, exactly separated:

* **constant radius** `e = O(1)`: `R = Θ(n^{2e−1})`, so by (5)

```
PASS  ⟺  (2e−1) ≲ (log₂|F| − 129)/log₂ n .                                     (7)
```

* **proportional radius** `e = δn`, `δ = Θ(1)`: by (6)

```
log₂R = n·H(2δ) ± O(log n) ,   PASS ⟺ log₂|F| ≥ 128 + n·H(2δ) .                (8)
```

Since (2) forces `0 < 2δ ≤ 1−ρ < 1`, `H(2δ) > 0` is bounded away from 0, hence

```
required log₂|F| = Θ(n) ,   while available log₂|F| ≤ 256 .                    FAIL.
```

Phase boundary at `n = 2²⁰`, `err = 2⁻¹²⁸` (exact integers):

| e | log₂R | PASS at \|F\| = 2¹⁶⁰ (T=32) | PASS at \|F\| = 2²⁵⁶ (T=128) |
|---|---|---|---|
| 1 | 21.00 | yes | yes |
| 2 | 58.42 | no | yes |
| 3 | 94.09 | no | yes |
| 4 | 128.70 | no | **no** |
| 5 | 162.53 | no | no |

```
e*(2²⁰, 2¹⁶⁰) = 1 ,   e*(2²⁰, 2²⁵⁶) = 3 ,   i.e. δ* ≈ 3·2⁻²⁰ ≈ 2.9·10⁻⁶ .
```

Target δ is `≈ 0.17–0.47`; the boundary is at `δ ≈ 3·10⁻⁶`. Five orders of magnitude.

---

## TARGET‑REGIME RESULT

`n = 2²⁰`, `err = 2⁻¹²⁸`. `δ_max = (1−ρ)/2` is the top of regime (2); `δ = (1−ρ)/3` is the
top of the already‑proved `#Bad ≤ e+1` row.

| ρ | δ | log₂R | log₂ \|F\| needed | margin at \|F\| = 2²⁵⁶ | class |
|---|---|---|---|---|---|
| 1/2 | 1/6 = 0.1667 | 962 891 | 963 019 | −962 763 | catastrophic |
| 1/2 | 1/4 = 0.2500 | 1 048 566 | 1 048 694 | −1 048 438 | catastrophic |
| 1/4 | 1/4 | 1 048 566 | 1 048 694 | −1 048 438 | catastrophic |
| 1/4 | 3/8 = 0.3750 | 850 677 | 850 805 | −850 549 | catastrophic |
| 1/8 | 0.2917 | 1 027 457 | 1 027 585 | −1 027 329 | catastrophic |
| 1/8 | 0.4375 | 569 960 | 570 088 | −569 832 | catastrophic |
| 1/16 | 0.3125 | 1 000 787 | 1 000 915 | −1 000 659 | catastrophic |
| 1/16 | 0.46875 | 353 666 | 353 794 | −353 538 | catastrophic |

Deficit `≈ n·H(2δ) − 128 = Θ(n)` bits, i.e. `10⁵–10⁶` bits everywhere in the target regime.

**Vacuity.** `badSet ⊆ F` gives `#Bad ≤ |F|` for free. Hence R is not merely insufficient but
**logically vacuous** whenever `log₂|F| ≤ log₂R`, i.e. for every field with
`|F| < 2^{353 666}` at the mildest row above and `|F| < 2^{1 048 566}` at ρ = 1/2, δ = 1/4.
At all usable field sizes (`≤ 2²⁵⁶`) R states nothing.

**Two further hard blocks, independent of the arithmetic.**

1. Regime (2) is `δ ≤ (1−ρ)/2`, and `(1−ρ)/2 ≤ 1−√ρ` for all ρ (⟺ `(1−√ρ)² ≥ 0`). So R can
   **never** reach the post‑Johnson band, which is the project's actual frontier.
2. R requires `F` prime (`PROJECTED_REDEI_CLAIMS.md` §2.4 refutes the `F_p`‑linear route over
   `F_{p^m}`). The flagship M31 setting uses `F_{(2³¹−1)^m}`, non‑prime, where the mechanism
   does not apply at all.

---

## COMPARISON WITH OLD BOUND

Proved, unconditional, same or larger regime:

```
#Bad ≤ e + 1                  (card_badSet_le_succ_radius,  3e < n−k+1)
#Bad ≤ n                      (card_badSet_le,              3e < d)
#Bad ≤ max(C(n,e), e)         (card_badSet_le_choose_radius, 2e + k ≤ n, every radius)
#Bad ≤ C(n,k+1)/C(n−e−1,k)    (card_badSet_le_circuit)
```

Bit comparison at `n = 2²⁰`:

| ρ, δ | log₂(e+1) | log₂C(n,e) | log₂R |
|---|---|---|---|
| 1/2, 1/6 | 17.4 | 681 587 | 962 891 |
| 1/2, 1/4 | 18.0 | 850 677 | 1 048 566 |
| 1/4, 3/8 | 18.6 | 1 000 786 | 850 677 |
| 1/8, 0.4375 | 18.8 | 1 036 716 | 569 960 |
| 1/16, 0.46875 | 18.9 | 1 045 609 | 353 666 |

Exact crossover with the binomial bound:

```
R ≤ C(n,e)  ⟺  H(2δ) ≤ H(δ)  ⟺  2δ ≥ 1 − δ  ⟺  δ ≥ 1/3   (feasible only if ρ < 1/3).      (9)
```

* Against `#Bad ≤ e+1` (the row that actually certifies `2⁻¹²⁸` at `|F| ≥ 2¹⁴⁶`): R is worse
  by `≈ 10⁶` bits. No improvement, at any ρ, δ.
* Against `#Bad ≤ max(C(n,e),e)`: R is **worse** for `δ < 1/3` (all of ρ ≥ 1/3), and better by
  `n(H(δ) − H(2δ))` bits only for `δ > 1/3`, i.e. up to `6.9·10⁵` bits at ρ = 1/16 — an
  improvement *between two bounds that are both `Θ(n)` bits above the 128‑bit budget*.
* Against `#Bad ≤ n` (20 bits, valid for `3e < d`): R is worse by `≈ 10⁶` bits.

So in the target regime projected‑Rédei **does not improve the relevant exponent**; where it
does improve `C(n,e)` (`δ > 1/3`, low rate) the improvement is irrelevant to security.

---

## REQUIRED IMPROVEMENT

Required bound from (1): `B_required = 2⁻¹²⁸·|F|`.

```
|F| = 2¹⁴⁶ ⟹ B_req = 2¹⁸ ;   |F| = 2¹⁶⁰ ⟹ B_req = 2³² ;   |F| = 2²⁵⁶ ⟹ B_req = 2¹²⁸ .
```

Gap at the flagship point `n = 2²⁰, ρ = 1/2, δ = 1/4, |F| = 2¹⁶⁰`:

```
R / B_req = 2^{1 048 566 − 32} = 2^{1 048 534}  ≈ 2^{n} .
```

Deficit scale: `Θ(n)` bits — **exponential improvement required**, not `0`, not `O(1)`, not
`O(log n)`. Concretely the replacement theorem must deliver

```
#Bad  ≤  poly(n)      (any bound O(n^c) with c·20 ≤ log₂|F| − 128 suffices; c ≤ 1.6 at 2¹⁶⁰)
```

in place of `exp(Θ(n))`. Corollaries for research planning:

* Improving the constant `2` in `2C(n−1,2e−1)−1`, or the `−1`/`−3` slack, buys **1 bit**:
  pointless.
* Improving the Szőnyi direction constant `(k+3)/2` to `c·k` buys `log₂(1/c)` bits: pointless.
* The entire deficit sits in the *input* to the Rédei step, `M*_L ≤ 1 + C(n−1,2e−1)`; a
  Rédei‑type route becomes viable only with `M*_L = poly(n)`, i.e. a projected‑list bound that
  is polynomial, not binomial. That is an exponential strengthening of P2, not a tweak.
* The needed strength is already realised by the counting route in the sub‑band
  `3e < n−k+1` (`#Bad ≤ e+1`, 18 bits). The genuinely open sub‑band inside regime (2) is
  `(n−k)/3 ≤ e ≤ (n−k)/2`, i.e. `δ ∈ (0.1667, 0.25]` at ρ = 1/2, where any `poly(n)` bound
  would close the certificate — and where R gives `2^{10⁶}`.

---

## VERDICT

**C — FUNDAMENTALLY INSUFFICIENT.**

```
deficit  = n·H(2δ) − (log₂|F| − 128) = Θ(n) bits ≈ 3.5·10⁵ … 1.05·10⁶ bits at n = 2²⁰ ;
required = exponential improvement (exp(Θ(n)) → poly(n)) ;
R is vacuous (weaker than #Bad ≤ |F|) for every |F| ≤ 2²⁵⁶ at target parameters ;
R does not improve the best proved bound in the target regime (worse than e+1 by ≈10⁶ bits,
worse than C(n,e) for δ < 1/3) ;
R's regime δ ≤ (1−ρ)/2 ≤ 1−√ρ cannot reach the post‑Johnson frontier ;
R needs F prime, excluding the M31‑extension flagship field.
```

Do **not** formalise Rédei–Szőnyi to complete the chain. Do not spend effort on the
constant `2`.

---

## NEXT MISSION

Per the deficit rule (`Θ(n)` bits ⇒ change of theory, not local strengthening):

1. The target object is a **polynomial** bound on `#Bad` (or on `M*_L`) in the open band
   `(n−k)/3 ≤ e ≤ (n−k)/2` at ρ ≥ 1/3, where the proved counting row stops and the binomial
   rows are `Θ(n)` bits too weak. The measured obstruction recorded in the project
   (`MCA_ROUTE_DECISION.md`: correlated agreement extracted from *two* line points costs
   radius `2e`; the `2e = n−k` witness with `#Bad = |D|`) is what must be bypassed.
2. Any candidate mechanism should be gated by the same arithmetic **before** formalisation:
   accept only if it yields `log₂(#Bad) ≤ log₂|F| − 128` with `log₂|F| ≤ 256`, i.e.
   `#Bad ≤ 2¹²⁸`, at `n = 2²⁰`.
3. The projected‑Rédei line of work (P1/P2 list and multiplicity bounds) stays as proved
   combinatorics; it is not a security certificate and should not be quoted as one.

*Numbers above: exact integers for `e ≤ 6`; `lgamma`‑evaluated `log₂C` and the rigorous
entropy brackets (5)–(6) for `e = Θ(n)`. Rounded to the digits shown; every margin is
negative by `> 3·10⁵` bits, far outside any evaluation error.*
