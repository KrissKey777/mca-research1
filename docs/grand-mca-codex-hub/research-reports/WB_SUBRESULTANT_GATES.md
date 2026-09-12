# WB_SUBRESULTANT_GATES

Four gates on the canonical subresultant mechanism `Bad ⊆ Close ⊆ V(W)`, `deg W = poly(n,k,e)`.
No Lean file was created or modified; no axiom, no `sorry`; no broad sweep; `P1/P2` untouched.

**Labels.** **PROVED** = complete paper proof, given here. **CHECKED** = exact finite‑field
arithmetic on the small instances listed in §5 (prime fields `F₅ … F₁₃`, no floating point).

**Setting.** `D ⊆ F`, `|D| = n`; `f₀, f₁ : D → F`; radius `e`; rate parameter `k`; standing
hypothesis **`k + 2e ≤ n`** (unique‑decoding window; the mechanism is claimed only here).
`Close = {γ ∈ F̄ : f₀ + γ f₁ is e‑close on D to some p, deg p < k}`; `Bad = badSet k e f₀ f₁`
with `Bad ⊆ Close` already kernel‑checked in the project.
`M(Z)` = WB pencil: rows `x ∈ D`, columns `(e+1)` locator + `(k+e)` numerator, row `x` equal to
`Λ(x)(f₀(x) + Z f₁(x)) − Q(x)`; only the `e+1` locator columns carry `Z`, and linearly.
`𝒦 ⊆ F[Z]^{k+2e+1}` = its right kernel over `F[Z]`, i.e. pairs `(Λ(Z,X), Q(Z,X))` with
`deg_X Λ ≤ e`, `deg_X Q < k+e`, and `Λ(Z,x)(f₀(x)+Zf₁(x)) = Q(Z,x)` for all `x ∈ D`.
Assume `𝒦 ≠ 0` (the singular branch; the regular branch is the old `deg P ≤ e+1` statement) and
let `v = (Λ,Q) ∈ 𝒦 ∖ 0` have minimal `Z`‑degree `ν = deg_Z Λ`.
`T_Λ(Z)` = `(k+e) × k` matrix of multiplication by `Λ` on `F[X]_{<k}`; `Q(Z)` = coefficient column
of `Q`; `W(Z) := gcd` of the `(k+1)`‑minors of `[ T_Λ(Z) | Q(Z) ]`.
Since `F[Z]` is a PID, `V(W) = {γ : all (k+1)-minors vanish at γ}` whenever `W ≢ 0`.

---

## 1. GATE 1 — SPECIALISATION: **EQUALITY**

**(1a) Primitivity (PROVED).** `Λ(γ,·) ≠ 0` for every `γ ∈ F̄`. If `π(Z)` irreducible divides all
`X`‑coefficients of `Λ`, then `Q(Z,x) ≡ 0 mod π` for `x ∈ D`, and `deg_X Q < k+e ≤ n` forces
`π ∣ Q`; then `v/π ∈ 𝒦` has `Z`‑degree `< ν`. Contradiction. In particular the specialised pair
`(Λ(γ,·), Q(γ,·))` is a **nonzero** kernel vector of `M(γ)` — the locator never dies.

**(1b) `γ ∈ Close ⟹ W(γ) = 0` (PROVED).** Let `p`, `deg p < k`, agree with `f₀+γf₁` off
`E ⊆ D`, `|E| ≤ e`, and `L = ∏_{x∈E}(X−x)`. For `x ∈ D`,
`Λ(γ,x)·L(x)·p(x) = L(x)·Q(γ,x)`; both sides have `deg_X ≤ e + e + k − 1 = k+2e−1 < n`, so
`L·Q(γ) = L·Λ(γ)·p` identically, and `L ≠ 0` gives `Q(γ) = Λ(γ)·p`. Hence `Q(γ)` lies in the
column span of `T_Λ(γ)`, `rank[T_Λ(γ)|Q(γ)] ≤ k`, all `(k+1)`‑minors vanish, `W(γ) = 0`.
This is the only place where `k+2e ≤ n` is used.

**(1c) `W(γ) = 0 ⟹ γ ∈ Close` (PROVED — no spurious zeros).** By (1a) `Λ(γ,·) ≠ 0`, so
multiplication by `Λ(γ,·)` is injective and `T_Λ(γ)` has full rank `k` **even when its `X`‑degree
drops**. Therefore `rank[T_Λ(γ)|Q(γ)] ≤ k` is *equivalent* to `Q(γ) = Λ(γ)·p` with `deg p < k`
(the column span is exactly `Λ(γ)·F[X]_{<k}`, which is what excludes the "quotient of degree `k`"
failure mode). Then for every `x ∈ D` with `Λ(γ,x) ≠ 0` we get `(f₀+γf₁)(x) = p(x)`, and
`#{x : Λ(γ,x) = 0} ≤ deg_X Λ(γ,·) ≤ e`. Hence `γ ∈ Close`.

**Tracking the specialisation.** `Λ(γ,X) ≠ 0` always; its `X`‑degree *does* drop for some `γ`
(CHECKED: in 28 of 40 sampled singular instances, 35 parameters in total), and `deg_X Q(γ,·)`
drops with it; but the drop is a *common* drop of the whole column block, so `T_Λ(γ)` keeps rank
`k` and no rank loss occurs without divisibility — none of those 35 drop‑parameters was a spurious
zero of `W`. Extra factors appear only in the minors themselves (the gcd `W` is typically much
smaller than a single minor, see §4).

**RECORD: `EQUALITY`** — `Bad ⊆ Close = V(W)` whenever `W ≢ 0` (outcome A, stronger than the
required containment B). CHECKED: 56 singular non‑CA instances over `F₅, F₇, F₁₁, F₁₃` with
`(n,k,e)` in `{(4,2,1),(4,1,1),(5,1,2),(6,2,2),(7,3,2),(9,3,3)}`: `Close = V(W)` parameter by
parameter, 0 mismatches.

## 2. GATE 2 — `W ≡ 0`: **A and B simultaneously (no hierarchy needed)**

`W ≡ 0` ⟺ all `(k+1)`‑minors vanish identically ⟺ `Q = Λ·P` with `P ∈ F(Z)[X]`, `deg_X P < k`.

**(2a) `P` is polynomial (PROVED).** If `π(Z)` irreducible divides a denominator of `P`, then
`π ∣ Λ·P̃` with `π ∤ P̃`, so `π ∣ Λ`, contradicting (1a). Hence `P ∈ F[Z][X]`.

**(2b) `W ≡ 0 ⟹ every parameter is close` (PROVED, option A).** For each `γ ∈ F̄`,
`Q(γ) = Λ(γ)P(γ)` with `deg_X P(γ) < k` and `Λ(γ) ≠ 0`, so `γ ∈ Close` by (1c). Thus
`Close = F̄` and the divisor statement is vacuous but never *wrong*.

**(2c) `W ≡ 0` ⟺ correlated agreement at radius `e` (PROVED, option B).** Let
`S = {x ∈ D : Λ(Z,x) ≢ 0}`; `|D∖S| ≤ e` (the excluded `x` are common roots of the `X`‑coefficients
of `Λ`, a nonzero polynomial family of degree `≤ e`). On `S`, `Q = ΛP` gives
`P(Z,x) = f₀(x) + Z f₁(x)`. Writing `P = Σ_j Z^j P_j`, `deg P_j < k`: `P_j|_S = 0` for `j ≥ 2` and
`|S| ≥ n − e ≥ k`, so `P = p₀ + Z p₁` with `f₀|_S = p₀|_S`, `f₁|_S = p₁|_S` — correlated agreement
of `f₀, f₁` at radius `e`. Conversely correlated agreement puts every `γ` in `Close`, hence
`V(W) = F̄` by (1b), hence `W ≡ 0` (a nonzero polynomial has finitely many roots).

**RECORD: classification A ∧ B.** `W ≡ 0` ⟺ all parameters close ⟺ `f₀,f₁` have correlated
agreement at radius `e`. Neither C nor D is needed: no higher subresultant/Fitting descendant has
to be invoked, because the degenerate branch is exactly the branch the correlated‑agreement
dichotomy already handles. CHECKED: `W ≡ 0` occurred in 4 random singular instances and in all
625 multi‑minimal instances of the exhaustive family of §5; in every one of them the instance was
correlated‑agreeing and `Close = F_p`; conversely no `W ≢ 0` instance was correlated‑agreeing.

## 3. GATE 3 — CANONICITY: **locus canonical; presentation canonical in rank 1**

**(3a) Containment holds for *every* kernel vector (PROVED).** For arbitrary `0 ≠ u = (Λ',Q') ∈ 𝒦`
and `γ ∈ Close`: if `Λ'(γ,·) ≠ 0`, the argument (1b) applies verbatim and `W_u(γ) = 0`; if
`Λ'(γ,·) = 0` then also `Q'(γ,·) = 0` and the whole matrix vanishes at `γ`. So
`Close ⊆ V(W_u)` unconditionally, with equality exactly when `u` is primitive (1c). In particular
`V(W₁) = V(W₂) = Close` and `rad(W₁) = rad(W₂) = ∏_{γ∈Close}(Z−γ)` for any two primitive kernel
vectors — **the locus is canonical by theorem, not by luck**.

**(3b) Rank 1 ⟹ `W` itself is canonical (PROVED).** If `𝒦` has rank 1, then every `u ∈ 𝒦`
satisfies `β u = α v` for some `α,β ∈ F[Z]`; any irreducible `π ∣ β` would divide `Λ` by (1a)'s
argument, so `u = c(Z)·v`, i.e. `𝒦 = F[Z]·v`. Then `W_u = c^{k+1}·W`, and `u` is primitive iff
`c ∈ F^×`. Hence all primitive kernel vectors give the *same* `W` up to a nonzero scalar.
`dim K_min > 1` therefore requires `rank 𝒦 ≥ 2`.

**(3c) The canonical object when `dim K_min > 1`.** Take

    I_bad := ideal of F[Z] generated by all (k+1)-minors of [T_Λ'(Z) | Q'(Z)],
             over all 0 ≠ (Λ',Q') ∈ 𝒦        (equivalently: over an F[Z]-basis of 𝒦),
    W_can := the monic generator of I_bad  (F[Z] is a PID).

By (3a), `V(W_can) = Close`, `W_can ∣ W` for the minimal `v`, so `deg W_can ≤ deg W ≤ (k+1)ν+1`.
`W_can` involves no choice at all: the locus *and* the budget are canonical, only the presentation
of a single `W` could be non‑canonical.

**CHECKED.** Exhaustive over the whole family `F₅, n = 4, k = 2, e = 1` (all `5⁸ = 390 625` pairs
`(f₀,f₁)`): `dim K_min > 1` occurs for exactly 625 lines, and every one of them is
correlated‑agreeing, where `W₁ = W₂ = 0` for all choices. Randomised hunt (≈ 30 000 further lines):
3 instances with `dim K_min = 2` and no correlated agreement (two with `F₅,(n,k,e)=(5,1,2)`, one
with `F₇,(6,2,2)`); in each of them **all `p²−1` nonzero combinations of the two minimal vectors produce
literally the same monic `W`** (e.g. `W = Z+2`, `V(W) = Close = {3}`). No instance of
`W₁ ≁ W₂` was found; the theorem guarantees at least `V(W₁) = V(W₂)` and `rad W₁ = rad W₂`.

## 4. GATE 4 — DEGREE BUDGET: **EXACT, `B = (k+1)ν + 1`**

Column‑by‑column `Z`‑degrees of `[T_Λ(Z) | Q(Z)]` (size `(k+e) × (k+1)`):

| column | content | `deg_Z` |
|---|---|---|
| `j = 0 … k−1` | the `X`‑coefficients `λ_0(Z),…,λ_e(Z)` of `Λ`, shifted by `j` | `≤ ν` |
| `j = k` | coefficient column of `Q` | `≤ ν+1` |

The last line is PROVED: for each `x`, `Λ(Z,x)(f₀(x)+Zf₁(x))` has `Z`‑degree `≤ ν+1`, and `Q` is
the unique interpolant of `deg_X < k+e ≤ n` of these values, whose coefficients are `F`‑linear in
them. Expanding a `(k+1)`‑minor along the last column: each term is (`k`‑minor of `T_Λ`, degree
`≤ kν`) × (entry of `Q`, degree `≤ ν+1`), so

    deg_Z (every (k+1)-minor) ≤ kν + ν + 1 = (k+1)ν + 1 = B,     deg W ≤ deg W_can ≤ B.

**Bound on `ν` (PROVED).** Cramer: pick a maximal nonsingular `ρ×ρ` submatrix of `M(Z)`
(`ρ = rank_{F(Z)} M`) plus one further column; the resulting kernel vector has entries equal to
`ρ`‑minors, and `Z` occurs linearly in only `e+1` columns, so `ν ≤ e+1`. At the wall `k+2e = n` a
direct count (unknowns `(d+1)(e+1)` versus syndrome conditions `(d+2)(n−k−e) = (d+2)e`) gives a
kernel vector already at `d = e`, so `ν ≤ e`. In the deep interior `k+3e ≤ n` the project's defect
theorem gives `ν = 0`, hence `deg W ≤ 1` and `#Close ≤ 1`.

**Classification: EXACT.** `B = (k+1)ν + 1`, hence

    #Bad ≤ #Close ≤ deg W ≤ (k+1)ν + 1 ≤ (k+1)(e+1) + 1 = O(ne) = O(n²)  —  polynomial.

CHECKED: 0 violations in all 60 singular instances; the per‑minor bound is *attained*
(`max deg minor = (k+1)ν+1`: `7` at `k=2,ν=2`; `9` at `k=3,ν=2`; `13` at `k=3,ν=3`), and the
budget for `W` itself is attained by the `n=4, k=2, e=1` family, where `deg W = 4 = (k+1)ν+1` and
`#Close = 4`. In all sampled instances `deg W = #Close` (so `W` is squarefree there and the local
multiplicities `ord_{Z=γ} W` are `1`); no super‑polynomial behaviour anywhere.

## 5. INSTANCES USED, AND LIMITS

Exact arithmetic over prime fields, `Close` computed by exhaustive decoding (all `p^k` codewords),
correlated agreement by intersecting the two decoding lists. Families: exhaustive `F₅, n=4, k=2,
e=1` (390 625 lines); ≈ 60 000 further random lines over `F₅ … F₁₃` with
`(n,k,e) ∈ {(4,1,1),(4,2,1),(5,1,2),(6,2,2),(7,1,3),(7,3,2),(8,2,3),(9,3,3)}`, all inside
`k+2e ≤ n`; every singular line among them (60 fully analysed, plus the 628 multi‑minimal /
degenerate ones) was tested for Gates 1–4. Checks are over the prime field; the proofs of §1–§4 are
over `F̄`.

**Where the mechanism dies.** Only the hypothesis `k+2e ≤ n` is essential: at `k+2e = n+1` step
(1b) loses the degree room `k+2e−1 < n`, unique decoding is lost, and `Q(γ) = Λ(γ)p` may fail — so
`Close ⊆ V(W)` is not claimed there. Inside the window, including the wall `k+2e = n`, no failure
mode was found.

## 6. DECISION

> **A. CANONICAL SUBRESULTANT THEOREM CERTIFIED.**
>
> Let `k + 2e ≤ n` and `𝒦 ≠ 0`, and let `W_can` be the monic generator of `I_bad`. Then either
> `f₀, f₁` have correlated agreement at radius `e` — equivalently `W_can ≡ 0`, equivalently every
> parameter is close — or
>
>     Bad ⊆ Close = V(W_can) = Supp(D_bad),   deg W_can ≤ (k+1)ν + 1 ≤ (k+1)(e+1) + 1 = O(ne),
>
> with `ν ≤ e` at the wall and `ν = 0` (hence `#Close ≤ 1`) whenever `k+3e ≤ n`.

Gate 1 returned `EQUALITY` (strictly stronger than the required containment), Gate 2 returned
`A ∧ B` (no hierarchy needed), Gate 3 returned a canonical locus and budget with `W_can` as the
canonical presentation, Gate 4 returned `EXACT` with `B = (k+1)ν+1`. Outcome A justifies
formalisation; the natural order is (i) primitivity of a minimal kernel vector, (ii)
`Close = {γ : Λ(γ) ∣ Q(γ), quotient degree < k}`, (iii) `W ≡ 0 ⟹ correlated agreement`,
(iv) `deg W ≤ (k+1)ν+1`.
