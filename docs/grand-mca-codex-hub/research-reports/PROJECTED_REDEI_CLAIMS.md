# PROJECTED_REDEI_CLAIMS

**Mission: resolve Claim A and Claim B for the projected Rédei mechanism. Nothing else.**

Constraints respected: no Lean file created or modified, no axiom, no `sorry`/`admit`, no
formalisation, no proof of Rédei–Szőnyi, no Johnson/list-size argument, no κ-charging, no
occupancy/support geometry, no broad empirical scan, **no new script** (none was necessary: both
claims are settled by exact proofs, and the one counterexample below is a three-point hand
computation in `F₄`).

---

## 0. Verdict, in one page

| claim | status |
| --- | --- |
| **Claim A** — `D(S_λ) ⊆ λ(L(f₁,2e))` for every admissible witness selection and every functional `λ` | **PROVED** — under the *exact* hypothesis that `λ` is **`F`-linear** (`F` = the field the parameters `γ` live in), which over a prime field is the same as additive. |
| **Claim A for merely `F_p`-linear `λ` over `F = F_{p^m}`, `m > 1`** | **REFUTED** — smallest counterexample: `F = F₄`, three points, `λ =` Frobenius (§2.4). |
| **Claim B** — a non-collinear witness selection admits a functional `λ` with `S_λ` non-collinear | **PROVED**, in the strongest form: the admissible set is exactly `C^∨ ∖ Ann(V_W)` with `V_W ≠ 0`; it is nonempty over *any* field, needs no primality, no `|B| ≤ p`, no MCA structure, and is already realised by a **coordinate** functional (§3). |
| conditional projected bound `|B| ≤ 2·M*_L − 3` | **justified**, conditional only on the cited Szőnyi theorem (§4). |
| replacing `M*_L` by `min_λ |λ(L)|` | **REFUTED, decisively**: `λ = 0` is always inadmissible and gives `|λ(L)| = 1`, so the unrestricted minimum is `1` and the "bound" would read `|B| ≤ −1` (§4.3). The distinction the mission insisted on is not a scruple; it is the difference between a theorem and a false statement. |

**Recommended next step: SUCCESS A — "PROJECTED HAMMING-BALL GEOMETRY", i.e. bound `M*_L`.** (§5)

---

## 1. Setting and notation, fixed once

* `F` a field, `A` an `F`-vector space (the alphabet; `A = F` in the ordinary RS case), `ι` a finite
  index set, `C ⊆ (ι → A)` an `F`-submodule (the code), `k = dim_F C`.
* `f₀, f₁ : ι → A`, `e ∈ ℕ`, and the list `L = L(f₁,2e) = { q ∈ C : wt(f₁ − q) ≤ 2e }`.
* `B ⊆ F` the bad set: for each `γ ∈ B` there is an *admissible witness* `c_γ ∈ C` with
  `d(f₀ + γ f₁, c_γ) ≤ e` (equivalently an agreement set `S_γ` with `|S_γ| ≥ |ι| − e`).
  A *witness selection* is `W_s = { (γ, c_γ) : γ ∈ B } ⊆ F × C`, one witness per bad parameter.
* Secant slopes: for `γ ≠ γ'` in `B`, `q_{γγ'} = (γ − γ')⁻¹ (c_γ − c_{γ'}) ∈ C`, and
  `D(B) = { q_{γγ'} : γ ≠ γ' ∈ B }`.
* **Secant lemma (already proved in the project**, `hammingDistance_slope_le` + `slope_mem` in
  `RequestProject/Root/CodingTheory/ListGeometrySlopeBound.lean`**):** `D(B) ⊆ L(f₁,2e)`.
* For a linear functional `λ : C → F`, `π_λ(γ,c) = (γ, λ(c))`, `S_λ = π_λ(W_s) ⊆ F²`, and
  `D(S_λ) ⊆ PG(1,F)` is the set of directions determined by `S_λ`.
* Throughout, "collinear" means "contained in one affine line" of the ambient affine space
  (`F × C` for `W_s`, `F²` for `S_λ`). Any set of `≤ 2` points is collinear, so the hypothesis
  "`W_s` non-collinear" already forces `|B| ≥ 3`.

---

## 2. CLAIM A

### 2.1 Statement proved

> **Theorem A (projected secant containment).** Let `W_s` be any witness selection and let
> `λ : C → F` be any map that is (i) additive and (ii) `F`-homogeneous, i.e. an `F`-linear
> functional on `C`. Then
>
> ```
> D(S_λ) = { λ(q) : q ∈ D(B) } = λ(D(B)) ⊆ λ(L(f₁,2e)) ,
> ```
>
> and no direction of `S_λ` is the vertical direction `∞ ∈ PG(1,F)`. In particular
> `|D(S_λ)| ≤ |λ(L(f₁,2e))| ≤ |L(f₁,2e)|`.

### 2.2 Proof

Let `γ ≠ γ'` in `B` and let `P = (γ, λ(c_γ))`, `P' = (γ', λ(c_{γ'}))` be the corresponding points
of `S_λ`.

1. **The two points are distinct and the secant is not vertical.** Their first coordinates are
   `γ ≠ γ'`. (This is also why `π_λ` is injective on `W_s`, hence `|S_λ| = |B|`; `S_λ` is a genuine
   set, no multiplicities, for *every* `λ` — no genericity is used.)
2. **The direction of the secant is `λ(q_{γγ'})`.** The direction is the affine slope
   `(λ(c_γ) − λ(c_{γ'})) · (γ − γ')⁻¹`. By additivity, `λ(c_γ) − λ(c_{γ'}) = λ(c_γ − c_{γ'})`; by
   `F`-homogeneity, `(γ − γ')⁻¹ λ(c_γ − c_{γ'}) = λ((γ − γ')⁻¹ (c_γ − c_{γ'})) = λ(q_{γγ'})`.
   Both directions of the identity are used, so `D(S_λ) = λ(D(B))` exactly — not merely `⊆`.
3. **Containment.** `q_{γγ'} ∈ C` (`slope_mem`) and `wt(f₁ − q_{γγ'}) ≤ 2e`
   (`hammingDistance_slope_le`, applicable because both witnesses are admissible and `γ ≠ γ'`), so
   `q_{γγ'} ∈ L(f₁,2e)` and therefore `λ(q_{γγ'}) ∈ λ(L(f₁,2e))`. ∎

### 2.3 Weakest assumptions on `λ` — exactly what is used

* `λ` need only be defined on `C` (not on all of `ι → A`), and only on the `F`-span of
  `D(B) ∪ L(f₁,2e)`.
* `λ` must be **additive** and **`F`-homogeneous**. Homogeneity is used exactly once, in step 2,
  and only for the scalars `(γ − γ')⁻¹`, `γ,γ' ∈ B`. So the truly minimal hypothesis is:
  `λ` additive and `λ(t·x) = t·λ(x)` for all `t` in the multiplicative group generated by
  `{ (γ−γ')⁻¹ : γ ≠ γ' ∈ B }`.
* `λ` must be **`F`-valued** (into the same field the abscissae live in) — otherwise `S_λ` is not a
  subset of an affine plane over `F` and "direction" has no meaning.
* **Nothing else.** No injectivity, no non-vanishing, no genericity, no relation to `f₀,f₁,e`, no
  primality of `|F|`, no bound on `|B|`, no non-collinearity. Claim A is unconditional in `λ`
  beyond linearity, and holds verbatim for `F_{p^m}` and for the folded (`A ≠ F`) setting.
* The witness selection may be arbitrary (any one witness per bad parameter); Claim A is *not*
  selection-dependent, and it also holds for the full fibre set `W_full`, since step 2 only ever
  looks at one pair at a time. What is selection-dependent is Claim B, not Claim A.

### 2.4 The hypothesis is sharp: `F_p`-linear is not enough over `F_{p^m}`

Take `F = F₄ = {0,1,ω,ω²}`, `ω³ = 1`, `ω² = ω + 1`, `A = F`, `C = F` (one coordinate), and
`λ : F₄ → F₄`, `λ(x) = x²` (Frobenius). `λ` is additive and `F₂`-linear, but **not** `F₄`-linear.
Take `B = {0, 1, ω}` with witnesses `c_0 = 0`, `c_1 = 1`, `c_ω = 0`.

| pair | secant slope `q` in `C` | `λ(q)` | direction of the projected pair |
| --- | --- | --- | --- |
| `0,1` | `1` | `1` | `1` |
| `0,ω` | `0` | `0` | `0` |
| `1,ω` | `1/(1−ω) = 1/ω² = ω` | `ω²` | `(1−0)/(1−ω) = ω^{-2} = ω` |

So `D(B) = {0,1,ω}` while `D(S_λ) = {0,1,ω}` is **not** contained in `λ(D(B)) = {0,1,ω²}`:
the projected direction `ω` is missing (`ω ≠ ω²`). Step 2 of the proof genuinely breaks, and with it
the only route to containment in `λ(L)` for any `L` with `λ(L) = λ(D(B))`.

**Consequence for Part VI of the parent plan (recorded here only to keep the logical separation
clean, not pursued):** over `F_{p^m}` the projection must be taken with an `F_{p^m}`-linear
functional, landing in `AG(2,p^m)`, where the `(k+3)/2` direction bound is false in general. The
tempting fix "project `F_p`-linearly to `AG(2,p)` and use the prime-field theorem" is precisely what
§2.4 refutes. Extension fields therefore remain **OPEN** and logically separate.

**Status of Claim A: PROVED** for `F`-linear `λ`; **REFUTED** for merely `F_p`-linear `λ` over
non-prime `F`.

---

## 3. CLAIM B

### 3.1 The collinearity criterion (both sides)

Fix `γ₀ ∈ B` and write, for `γ ∈ B ∖ {γ₀}`, `q_γ = q_{γγ₀} = (γ − γ₀)⁻¹(c_γ − c_{γ₀})`, so that

```
(γ, c_γ) − (γ₀, c_{γ₀}) = (γ − γ₀)·(1, q_γ) ,        γ − γ₀ ≠ 0 .        (★)
```

> **Lemma B1.** `W_s` is collinear ⟺ the family `(q_γ)_{γ ≠ γ₀}` is constant.
> **Lemma B2.** For `F`-linear `λ : C → F`, `S_λ` is collinear ⟺ the family `(λ(q_γ))_{γ ≠ γ₀}` is
> constant.

*Proof.* Both are the same computation, in `F × C` and in `F × F` respectively. (⇐) is immediate
from (★): all points lie on the line through `(γ₀,c_{γ₀})` with direction `(1,q)`. (⇒) if all points
lie on a line `{(γ₀,c_{γ₀}) + t·(a,b)}`, then for `γ ≠ γ₀` the first coordinate gives `t_γ a =
γ − γ₀ ≠ 0`, so `a ≠ 0`; rescaling the direction vector we may take `a = 1`, whence `t_γ = γ − γ₀`
and `c_γ − c_{γ₀} = (γ − γ₀) b`, i.e. `q_γ = b` for all `γ`. The projected statement is the case
`C := F`, `c := λ(c)`, using Claim A step 2 (`λ(q_γ)` is the projected slope). ∎

Note this reproves, and makes precise, the identity `dim aff(W_s) = 1 + dim aff{q_γ}` (D1 of the
previous report) — but nothing below needs the dimension formula, only Lemmas B1/B2.

### 3.2 The theorem

> **Theorem B (non-collinear projection lemma).** Let `F` be any field, `V` any `F`-vector space,
> `B ⊆ F` finite, and `(c_γ)_{γ ∈ B} ⊆ V` a family with `W = {(γ,c_γ)} ⊆ F × V` **not collinear**.
> Put
>
> ```
> V_W = span_F { q − q' : q, q' ∈ D(W) }   ( = span_F { q_γ − q_{γ'} : γ,γ' ≠ γ₀ } , any base γ₀ ),
> Λ(W) = { λ ∈ V^∨ : S_λ is non-collinear } .
> ```
>
> Then `V_W ≠ 0` and
>
> ```
> Λ(W) = V^∨ ∖ Ann(V_W)  ≠  ∅ .
> ```
>
> Moreover, if `V ⊆ (ι → A)` is a space of `A`-valued words, `Λ(W)` already contains a functional of
> the *coordinate* form `λ = μ ∘ ev_x` with `x ∈ ι` and `μ ∈ A^∨`; for `A = F` a plain coordinate
> evaluation `λ = ev_x` suffices. If `F = F_q` and `dim_F V = k < ∞`, then
>
> ```
> |Λ(W)| = q^k − q^{k−r} ≥ q^{k−1}(q−1) ,      r = dim_F V_W ≥ 1 .
> ```

*Proof.* By Lemma B1, non-collinearity of `W` means the family `(q_γ)` is not constant, so there are
`γ₁,γ₂` with `v := q_{γ₁} − q_{γ₂} ≠ 0`; hence `V_W ≠ 0`, and `r = dim V_W ≥ 1`.

By Lemma B2, `S_λ` is collinear ⟺ `λ(q_γ)` is constant ⟺ `λ(q_γ − q_{γ'}) = 0` for all
`γ,γ'` ⟺ `λ` vanishes on the spanning set of `V_W` ⟺ `λ ∈ Ann(V_W)`. (The base point `γ₀` is
immaterial: if `λ(q_γ)` is constant `= m` for one base point then, writing
`c_γ − c_{γ'} = (γ − γ₀)q_γ − (γ' − γ₀)q_{γ'}`, one gets `λ(q_{γγ'}) = m` for *all* pairs, so
`span{q − q' : q,q' ∈ D(W)}` is annihilated too; conversely trivially.) This proves
`Λ(W) = V^∨ ∖ Ann(V_W)`.

Nonemptiness: `v ≠ 0` in the `F`-vector space `V`, so `{v}` extends to a basis and the dual
coordinate `λ` of `v` in that basis is a linear functional with `λ(v) = 1 ≠ 0`, i.e.
`λ ∉ Ann(V_W)`. (For finite-dimensional `V`, or for `V ⊆ (ι → A)` with `ι` finite, this needs no
choice.) Concretely for `V ⊆ (ι → A)`: `v ≠ 0` means `v_x ≠ 0` for some `x ∈ ι`, and then some
`μ ∈ A^∨` has `μ(v_x) ≠ 0`; `λ = μ ∘ ev_x` restricted to `V` works. For `A = F` take `μ = id`.

Counting: `Ann(V_W)` is a subspace of `V^∨` of dimension `k − r`, so
`|Λ(W)| = q^k − q^{k−r}`, minimal at `r = 1`. ∎

### 3.3 What Theorem B does and does not need

* **Not needed:** primality of `|F|`; `|B| ≤ |F|`; finiteness of `F` or of `V`; any MCA structure
  (`f₀, f₁, e`, admissibility, the code being RS or even a code); the value of `k`; genericity.
  Theorem B is pure linear algebra and is therefore automatically valid for the actual MCA witness
  configurations, for arbitrary finite-dimensional `C` over `F_p`, for `|B| ≤ p` and for `|B| > p`,
  and for `p = 2,3,5,…` alike — the five sub-questions of the parent plan's Part I(B) all have the
  same answer, and none of them needs a threshold on `p`.
* **Needed and unremovable:** `W_s` non-collinear. This is necessary as well as sufficient: if
  `W_s` is collinear then `q_γ ≡ q` and `λ(q_γ) ≡ λ(q)` for every `λ`, so *every* projection is
  collinear (Lemma B2) and `Λ(W_s) = ∅`. Hence the dichotomy has two genuine arms; Claim B closes
  exactly the non-collinear one and cannot be pushed further.
* **The stronger reading is the one proved.** The mission warned that the naive statement
  "`λ(W)` is not a single point" is too weak. Indeed that weaker statement is about `V_W' =
  span{c − c'}`, whereas the correct object is `V_W = span{q − q'}`, the span of *slope
  differences*. Theorem B is stated and proved for the correct object: it delivers non-collinearity
  in `F²`, not mere distinctness. (Distinctness is free anyway, by Claim A step 1.)
* **A canonical finite "projection cover" already exists**, so the mission's contingency SUCCESS C
  is not needed: the `|ι|·(dim A)`-element family of coordinate functionals contains an admissible
  `λ` whenever one exists. This makes `Λ(W_s)` effectively computable without searching `C^∨`.

**Status of Claim B: PROVED**, in the weakest-hypothesis form of Theorem B. No counterexample
exists (an alleged one would contradict a two-line linear-algebra argument).

---

## 4. Is the conditional projected bound now justified?

### 4.1 Assembling

Let `p` be prime, `F = F_p`, `W_s` a non-collinear witness selection, `|B| ≤ p` (automatic, as
`B ⊆ F_p`). Let `λ ∈ Λ(W_s)`, which is nonempty by Theorem B. Then:

* `S_λ ⊆ AG(2,p)` is a **set** of exactly `|B| ≤ p` points (Claim A step 1);
* `S_λ` is **not collinear** (definition of `Λ(W_s)`, Theorem B);
* every direction determined by `S_λ` is an affine slope, and lies in `λ(L(f₁,2e))` (Theorem A);
* the direction count of the cited theorem is over `PG(1,p)`, and `∞ ∉ D(S_λ)`, so every counted
  direction is an element of `λ(L(f₁,2e)) ⊆ F_p`.

Quoting (not proving, per the mission) the Rédei–Megyesi/Szőnyi direction theorem — *for `p` prime
and a non-collinear set of `k ≤ p` points of `AG(2,p)`, at least `(k+3)/2` directions are
determined* — we obtain

```
(|B| + 3)/2  ≤  |D(S_λ)|  ≤  |λ(L(f₁,2e))| ,      i.e.      |B| ≤ 2·|λ(L(f₁,2e))| − 3 ,
```

for **every** admissible `λ`, hence for the best one.

### 4.2 The conditional theorem

> **Conditional Projected Rédei Bound.** Let `p` be prime, `C ⊆ F_p^ι` a code, `f₀,f₁,e` as above,
> and let `W_s` be a non-collinear witness selection over the bad set `B`. Define the intrinsic
> quantity
>
> ```
> M*_L(W_s) = min { |λ(L(f₁,2e))| : λ ∈ Λ(W_s) }        (the min is over a nonempty set, Thm B).
> ```
>
> Then, conditional on the quoted Szőnyi theorem and on nothing else,
>
> ```
> |B| ≤ 2·M*_L(W_s) − 3 .
> ```

Everything on the MCA side of this statement is now proved: Claim A (§2), Claim B (§3), the secant
lemma (project, Lean), the hypothesis audit (§4.1, and §7 of `WITNESS_LOCUS_DIMENSION_PROBE.md`).
The single external input is the Szőnyi bound, quoted from the literature and *not* re-proved here,
as instructed. The statement is **not** formalised (the mission forbids Lean), and it is **not**
claimed unconditionally.

### 4.3 Why `min` over *all* `λ` is not merely "too strong" — it is false

`λ = 0` is a linear functional with `|λ(L)| = 1`, and it is inadmissible (`0 ∈ Ann(V_W)`). Hence
`min_{λ ∈ C^∨} |λ(L)| = 1` **always**, and the substituted inequality would read `|B| ≤ −1`. So the
restriction of the minimum to `Λ(W_s)` is not a matter of taste: `M*_L` is the only correct object,
and any future statement must carry the admissibility side condition. More generally, the whole
subspace `Ann(V_W)` (of index `p^r`, `r = dim V_W ≥ 1`) consists of functionals that collapse
directions, and the minimum over it is meaningless.

Two further honest caveats, so that the bound is not over-read:

* `M*_L` depends on the selection `W_s` (through `Λ(W_s)`), not only on `B` and `L`. A
  selection-free version requires either quantifying over selections (take the *best* non-collinear
  selection, which only strengthens the bound) or proving that `V_{W_s}` is selection-independent —
  not established.
* On the recorded micro-instances (`p ≤ 19`) the bound is true but vacuous, since there
  `M*_L ≥ (p+3)/2` in nearly every case; this was measured in the previous report and is not
  re-measured here. Its content lies entirely in the regime `|λ(L)| ≪ p`.

---

## 5. Recommended next step (exactly one)

**SUCCESS A: both claims hold, so the next mission is "PROJECTED HAMMING-BALL GEOMETRY".**

Objective: bound `M*_L` — i.e. bound `|λ(L(f₁,2e))|` for functionals `λ` that are *admissible* —
in terms of `n = |ι|`, `e`, `k`, the support of `f₁` and the interaction between `supp(λ)` and the
ball, **not** in terms of `p`; and decide when `M*_L < (p+3)/2`, which is exactly the threshold of
non-vacuity. The two structural facts proved here are what make that mission well-posed:

* by Theorem B, admissibility is a *linear* condition (`λ ∉ Ann(V_W)`, a subspace of index `p^r`),
  so one is minimising `|λ(L)|` over a set of density `1 − p^{−r} ≥ 1 − 1/p` — an optimisation over
  almost all functionals, not over a thin exceptional set;
* by Theorem B again, coordinate functionals `ev_x` are admissible for at least one `x ∈ ι`, giving
  an immediate first estimate `M*_L ≤ min_{x admissible} |{ q_x : q ∈ L }| ≤ |L|` and, more
  usefully, `|ev_x(L)| ≤ 1 + #{ q ∈ L : q_x ≠ f₁(x) }`, which is small at coordinates where the
  radius-`2e` ball is thin. Making this quantitative is the concrete first task.

Two deliverables should be carried along, but are secondary: (a) the exact collinear arm (the
`|B|·(n−e−z) ≤ 2e` zero-count sketched in the previous report, to be written out in full so the
dichotomy is complete); (b) keeping the extension-field case flagged **OPEN**, with §2.4 as the
recorded obstruction.

Explicitly not recommended: re-opening κ-charging, occupancy, Johnson/list-size, or a broad scan;
and no Lean formalisation until (a) is closed and `M*_L` is understood — at that point the
statement of §4.2 becomes a self-contained theorem whose only external input is the cited Szőnyi
bound.

---

## 6. Status table

| item | status |
| --- | --- |
| Claim A, `λ` an `F`-linear functional on `C` (`F`-valued) | **PROVED** (§2.2); identity `D(S_λ) = λ(D(B))`, containment in `λ(L)` |
| weakest hypotheses on `λ` | additive + homogeneous for the scalars `(γ−γ')⁻¹`; `F`-valued (§2.3) |
| Claim A for `F_p`-linear but not `F`-linear `λ` over `F = F_{p^m}` | **REFUTED**, minimal counterexample `F₄`, `|B| = 3` (§2.4) |
| Claim B | **PROVED** (Theorem B, §3.2), no primality, no `|B| ≤ p`, no MCA input |
| structure of the admissible set `Λ(W_s)` | `= C^∨ ∖ Ann(V_W)`, size `p^k − p^{k−r}`, `r ≥ 1` (§3.2) |
| existence of a canonical projection cover | **PROVED**: coordinate functionals suffice (§3.2) |
| collinear selections | **no admissible `λ` exists** — necessary and sufficient (§3.3); the second arm of the dichotomy is unavoidable |
| conditional bound `|B| ≤ 2·M*_L − 3` | **justified conditional on Szőnyi only** (§4.2); not formalised |
| `M*_L` replaced by `min_λ |λ(L)|` | **REFUTED** (`λ = 0` gives `1`, bound would read `|B| ≤ −1`) (§4.3) |
| extension fields `F_{p^m}` | **OPEN**, with §2.4 as an explicit obstruction to the naive route |
| Szőnyi direction theorem itself | quoted from the literature, **not proved here** (out of scope by mission) |
