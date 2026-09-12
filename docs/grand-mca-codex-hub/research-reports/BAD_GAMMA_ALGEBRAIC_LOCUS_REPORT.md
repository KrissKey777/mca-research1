# BAD_GAMMA_ALGEBRAIC_LOCUS_REPORT

Scope: no Lean file created or modified, no axiom, no `sorry`, no sweep. Labels:
**LEAN** = kernel-checked in this repository (name given); **PROVED** = complete paper proof
in this document; **CHECKED** = exact finite-field arithmetic on the instances listed in §7;
**OPEN**. Notation: `n = |D|`, `k`, radius `e`, `Close = {γ : f₀+γf₁ is e-close to RS[k] on D}`,
`Bad = badSet k e f₀ f₁`, `P_e = {Λ ∈ F[X] : deg Λ ≤ e}`. Throughout `k + 2e ≤ n`.

**DECISION: B — a canonical subresultant/local divisor suffices.** The rank route (A) is
*false* in the singular branch; the first true condition is a gcd/divisibility condition, and it
is captured exactly by one canonical polynomial `W(Z)` of degree `≤ (k+1)ν+1 = O(ne)`.

---

## 1. EXACT Bad / Close / WB RELATIONS

`M(Z)` = WB pencil (`wbRow`), rows `x ∈ D`, columns `(e+1)` locator + `(k+e)` numerator,
row `x` = `Λ(x)(f₀x + Z f₁x) − Q(x)`. Only the `e+1` locator columns carry `Z`, linearly.
Write `N_γ = {Λ ∈ P_e : Λ·(f₀+γf₁) interpolates some Q, deg Q < k+e, on D}` (the locator part
of `ker M(γ)`; `Q` is determined by `Λ` because `k+e ≤ n`). Known chain:

| implication | verdict |
|---|---|
| `γ ∈ Bad ⇒ γ ∈ Close` | **SUFFICIENT, not equivalent** (LEAN: `IsBad` contains `IsCloseOn`; `Bad ⊊ Close` in general) |
| `γ ∈ Close ⇒ N_γ ≠ 0` | **NECESSARY, not sufficient** (LEAN `exists_wbPair_of_isCloseOn`; converse fails: `wbDet_eq_zero_of_rationalLine` + `not_isCloseOn_of_not_dvd`) |
| `γ ∈ Close ⇔ some `0 ≠ Λ ∈ N_γ` has `Q = Λ·p`, `deg p < k`` | **EQUIVALENT** (LEAN `wbPair_eq_mul_of_isCloseOn`, `isCloseOn_of_wbPair_mul`; needs `k+2e ≤ n`) |
| `γ ∈ Close ⇒ *every*` `0 ≠ Λ ∈ N_γ` has `Q = Λ·p_γ`, `deg p_γ < k` | **EQUIVALENT** (PROVED, cross-product `wbPair_cross`: `L·Q = Λ·L·p` has degree `≤ k+2e−1 < n` and vanishes on `D`) |

The last line is the whole leverage: in the unique-decoding regime *closeness is a property of
the parameter, not of the chosen kernel vector*.

## 2. REGULAR CONTROL CASE (why `e+1`)

If `M(Z)` has full column rank over `F(Z)`, some maximal minor `P(Z) ≢ 0`. `γ ∈ Close ⇒ N_γ ≠ 0
⇒ rank M(γ) < k+2e+1 ⇒ P(γ) = 0`. `Z` sits only in the `e+1` locator columns and only linearly,
so `deg P ≤ e+1` (LEAN `natDegree_wbDet_le`), whence `Close ⊆ V(P)` and `#Close ≤ e+1`
(LEAN `card_badSet_le_of_wbDet_ne_zero`). **The locus is `V(P)`; the budget is the dimension
`e+1` of the locator space.** Any singular theory must replace `P`.

## 3. GENERIC RANK DROP GATE — route A is FALSE

Singular branch: `𝒦 = ker M(Z)` over `F[Z]` is free of rank `r ≥ 1`; generic rank is
`r' = k+2e+1−r`. Test of `γ ∈ Close ⇒ rank M(γ) < r'`:

* **FALSE.** In both project witnesses `dim N_γ = r = 1` for *every* `γ ∈ F` (CHECKED:
  `GapWitness` `F₅, n=4, k=2, e=1`, all 5 parameters; `StrictWindowWitness`
  `F₁₁, n=8, k=3, e=2`, all 11 parameters), while `#Close = 4` in both. So the `r`-th
  determinantal divisor `D_det` is a unit, `V(D_det) = ∅`, and `Bad ⊄ V(D_det)`.

Rank data is exhausted by the *global* kernel; bad parameters in the singular branch cost no
extra rank. Route A is dead — not for degree reasons but for containment reasons.

## 4. FIRST TRUE ALGEBRAIC CHARACTERISATION (case B: gcd / divisibility)

Let `v = (Λ(Z,X), Q(Z,X)) ∈ 𝒦` have **minimal** `Z`-degree `ν := deg_Z Λ`.

* **Primitivity (PROVED).** `Λ(γ,·) ≠ 0` for every `γ ∈ F̄`. Indeed `Λ(γ,·) = 0` means
  `(Z−γ) ∣ Λ`; then `Q(γ,·)` vanishes on `D` and has `deg_X < k+e ≤ n`, so `Q(γ,·) = 0`,
  `(Z−γ) ∣ Q`, and `v/(Z−γ) ∈ 𝒦` contradicts minimality.
* **Exact locus (PROVED).** Let `T_Λ(Z)` be the `(k+e) × k` matrix of multiplication by `Λ` on
  `F[X]_{<k}` (entries of `Z`-degree `≤ ν`), and `Q(Z)` the coefficient column of `Q`
  (`Z`-degree `≤ ν+1`). Then

      γ ∈ Close  ⟺  rank [ T_Λ(γ) | Q(γ) ] ≤ k
                 ⟺  Λ(γ,·) ∣ Q(γ,·) with quotient of degree < k.

  (`⇒` by §1 line 4 applied to `Λ(γ,·) ≠ 0`; `⇐` because `Q(γ)=Λ(γ)p` makes `f₀+γf₁` agree with
  `p` off the `≤ e` roots of `Λ(γ,·)`.) Define the **canonical divisor**

      W(Z) := gcd of the (k+1)×(k+1) minors of [ T_Λ(Z) | Q(Z) ]   (a subresultant-type
                                                                    polynomial of Λ and Q).

  Then `Bad ⊆ Close = V(W)` whenever `W ≢ 0`, with **no support enumeration** anywhere.
* **The degenerate case is exactly correlated agreement (PROVED).** `W ≡ 0` ⟺ `Q = Λ·P` in
  `F(Z)[X]` with `deg_X P < k`. Minimality of the denominator plus `deg_X < k ≤ n−e` forces
  `P ∈ F[Z][X]`, and comparing `Z`-degrees on `S = {x : Λ(Z,x) ≢ 0}` (`|D∖S| ≤ e`) gives
  `P = p₀ + Z p₁`, `f₀|_S = p₀|_S`, `f₁|_S = p₁|_S`: correlated agreement at radius `e`
  (the hypothesis of LEAN `wbDet_eq_zero_of_correlatedAgreement`).

So the dichotomy is: **correlated agreement, or `Close` is the zero set of one explicit
univariate polynomial.**

## 5. GLOBAL vs LOCAL DATA

* **Global (one item only).** A minimal-degree kernel vector and its index `ν = ε₁`, the first
  Kronecker/Forney minimal index of `𝒦`. `ν ≤ e` (coefficients `Λ_0,…,Λ_ν` of a minimal vector
  are `F`-independent in `P_e`). No further minimal-basis data is used.
* **Local.** `m_γ := ord_{Z=γ} W ≥ 1` for `γ ∈ Close`.
* **Conservation.** `Σ_{γ∈Close} m_γ ≤ deg W ≤ (k+1)ν + 1`. The regular branch is the case
  `𝒦 = 0`, `W := P`, `deg W ≤ e+1` — the two branches are one statement with two budgets.
* **Defect theorem (PROVED).** `ν ≥ 1 ⇒ k+3e ≥ n+1`. Proof: a minimal chain `(Λ₀,Λ₁)` gives
  `G := Λ₀²Q₂ + Λ₁²Q₀ − Λ₀Λ₁Q₁` vanishing on all of `D` with `deg G ≤ k+3e−1`; if `k+3e ≤ n`
  then `G ≡ 0`, and with `d = gcd(Λ₀,Λ₁)`, `Λ₀ = da`, `Λ₁ = db` one gets `a ∣ Q₀`, `b ∣ Q₂`,
  `Q₁ = aB + bA`, hence `d f₀ ≡ A` and `d f₁ ≡ B` on *all* of `D` (the middle equation covers
  the zeros of `a` and of `b`) — a kernel vector of index `0`, contradiction.
  Consequently, in the deep interior `k+3e ≤ n` the singular branch has `ν = 0`,
  `deg W ≤ 1`, and `#Close ≤ 1`: the pencil route re-proves `#Bad ≤ e+1` there
  *unconditionally*, matching the existing `card_badSet_le_succ_radius`.

## 6. CANONICAL DEGREE BUDGET AND STRENGTH GATE

    #Bad ≤ #Close ≤ deg W ≤ (k+1)·ν + 1 ≤ (k+1)e + 1 = O(ne),   ν ≤ min(e, ...) ,
    ν = 0  ⇒  #Close ≤ 1;   regular branch  ⇒  #Close ≤ e+1.

Budget contains no `C(n,Θ(e))`, no `2^{Θ(n)}`, no list size `|L|`. Strength gate at
`k+2e ≤ n`, `e = Θ(n)`: budget `O(n²)`, i.e. `ε_mca ≤ O(n²)/|F|` — at `n = 2²⁰` that is
`≈ 2⁴¹ ≪ 2¹²⁸`. **Passes.** The mechanism is valid up to *and including* the wall `k+2e = n`
(the cross-product argument needs only `k+2e−1 < n`); it dies at `k+2e = n+1`, where unique
decoding is lost and `Q = Λp_γ` may fail.

## 7. FALSIFICATION

| test (exact arithmetic) | outcome |
|---|---|
| `Close = V(W)` on both project witnesses | exact, parameter by parameter (5/5 and 11/11) |
| `Close = V(W)` on 97 generated singular lines (`n = 6,8`, `k = 1,2,3`, `e = 1,2,3`) | 97/97, no mismatch |
| `#Close ≤ (k+1)ν+1` on 475 generated singular non-CA lines | 0 violations |
| `k+3e ≤ n ⇒ ν = 0` | 395/395 generated singular lines, plus **exhaustive** over all `5⁸` lines at `F₅, n=4, k=1, e=1` (3625 singular, all `ν = 0`) |
| `ν ≥ 1` instances | occur only when `k+3e > n`; both project witnesses have `ν = 1` and sit at `k+3e = n+1` |
| wall `k+2e = n` (`F₅…F₁₇`, `n=4,k=2,e=1`), max `#Close` over non-CA lines | `4` for every field size — **does not scale with `|F|`**, so no `#Bad = Θ(|F|)` family |
| tightness | `GapWitness` attains `#Close = 4 = (k+1)ν+1` exactly |

What the witnesses kill: **the rank/determinantal route (Bad containment)**, not the degree
budget and not the containment `Bad ⊆ V(W)`. No counterexample to §4 or §6 was found.

## 8. ONE NEXT THEOREM

> **(Singular WB locus.)** Let `k + 2e ≤ n`, `𝒦 ≠ 0`, and let `(Λ,Q)` be a kernel vector of
> minimal `Z`-degree `ν`. Then either `f₀,f₁` have correlated agreement at radius `e`, or
> `W ≢ 0` and `Bad ⊆ Close = V(W)`, so `#Bad ≤ (k+1)ν + 1`.

Formalisation order (each piece is small and self-contained): (i) primitivity of a minimal
kernel vector; (ii) `Close = {γ : Λ(γ) ∣ Q(γ), deg quotient < k}` from the existing cross
lemma; (iii) `W ≡ 0 ⇒ correlated agreement`; (iv) the degree bound `deg W ≤ (k+1)ν+1`.
Then the defect theorem `ν ≥ 1 ⇒ k+3e ≥ n+1` of §5 upgrades the interior `k+3e ≤ n` to an
unconditional `#Bad ≤ e+1` with no pencil hypothesis at all.
