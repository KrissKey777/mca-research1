# MINIMAL_CHARGING_THEOREM

**Extraction round.** No Lean file was created or modified, no axiom was added, no `sorry`/`admit`
was written, no Johnson/list-size statement was used, no support/occupancy/rank invariant was
reopened, no broad scan was run. The only computations performed are exact finite checks of the
*derived* lemmas of §4–§6 (integers mod p, no floats); they were run outside the repository and are
**not** evidence for anything: every statement labelled PROVED below carries a complete
human-checkable proof in this document.

Status labels used throughout:

* **PROVED** — complete proof given here (paper-level, Lean pending);
* **REFUTED** — explicit counterexample given here;
* **CHECKED** — exact finite verification only, no proof (never used to support a claim);
* **OPEN** — neither.

---

## 0. Executive answer to the question that was asked

> *Is `Σ_q κ(q)` only a crude union bound, or does it hide a stronger intersection phenomenon?*

**It is a union bound, and we can now say exactly how crude it is.** Precisely (all PROVED, §3–§5):

1. The charging construction is not a bound at all but a **partition**. After basing at one point
   `p₀ = (γ₀,c₀)` of the *tube* `T = {(γ,c) ∈ F×C : wt(f₀+γf₁−c) ≤ e}`, the pencil of affine
   `C`-lines through `p₀` partitions `T ∖ ({γ₀}×C)`, and `B` is the image of `T` under the
   projection to the parameter axis. **T2 is an identity, not an inequality:**
   `B = ⋃_{q∈L} Γ(u_q,q)`.
2. The passage from T2 to T1 loses exactly the **decoding multiplicity**:
   `Σ_{q∈L}(|Γ(u_q,q)|−1) = Σ_{γ∈B∖{γ₀}} N(γ)`, where `N(γ) = #(Ball(f₀+γf₁,e) ∩ C)`.
   Hence the *exact* form of T3 is the identity
   `|B| = 1 + Σ_{q∈L}(|Γ(u_q,q)|−1) − Σ_{γ∈B∖{γ₀}}(N(γ)−1)`.
3. Consequently the "based capacity sum" equals `|T| − N(γ₀) + 1`: it is **literally the
   fibre-counting bound** `|π(T)| ≤ |T|` corrected by the base fibre. All of its non-triviality
   sits in the two *external* estimates: `|Γ| ≤ κ(q) ≤ chargeCap(e, d(f₁,q))` (a Hamming counting
   lemma, §6) and the size of `L`.
4. **The mission's T3 target — an unconditional geometric `Δ > 0` — is impossible** (§7,
   REFUTED): by (2), `Δ = Σ(N(γ)−1)`, and `Δ = 0` on every instance with `2e < d(C)`, where the
   based bound is an *equality*. Any genuine improvement must reduce the index set `L` or the
   capacities, not the overlap.
5. The pairwise intersection question has a sharp answer (§5): overlap forces `wt(q−q′) ≤ 2e`
   *and* non-unique decoding at the overlap point; a **universal constant `C(e)` does not exist**
   (REFUTED, explicit counterexample with `|Γ_q ∩ Γ_{q′}| = |F|`); under the single
   hypothesis `d(f₁,q) + d(f₁,q′) > 2e` one has the second-order counting theorem
   `|Γ_q ∩ Γ_{q′}| ≤ chargeCap(2e, d(f₁,q)+d(f₁,q′))`, obtained by applying the *first-order*
   lemma to the doubled configuration — this is the hierarchy Phase V asked for.
6. A genuinely different, field-free and Johnson-free constraint does exist (§8): the witness
   points form a **point set in `F×C` all of whose determined directions lie in `L`**, whence
   `|B| ≤ κ_max + |L|(|L|−1)`. Incomparable with T1 (better only when capacities are large and
   the list is short).

The mechanism is therefore **not** Hamming-specific and **not** RS-specific: §3–§4 use no weight
at all (any closeness predicate), §2 uses only subadditivity + invariance under nonzero scalars,
and Hamming enters **only** in the capacity estimate of §6.

---

## 1. The minimal configuration and the minimal hypotheses

### 1.1 Data

| object | requirement actually used |
| --- | --- |
| `F` | a field. Finiteness only where a cardinality is written (§4, §6, §8). |
| `V` | an `F`-vector space (for §6 also: `V = A^ι`, `ι` finite, `A` an `F`-vector space, coordinatewise). |
| `C ⊆ V` | an `F`-**subspace** (closure under subtraction and under scalar multiplication is all that is used; a submodule over a field is enough). No dimension, no generator matrix, no evaluation structure. |
| `f₀,f₁ ∈ V` | arbitrary. `f₁ ∉ C` is *not* assumed. |
| `e` | an element of `ℕ` used only through the predicate below. |
| `wt : V → ℕ` | see (W1)–(W2). |

Write the parameter line `g(γ) := f₀ + γ f₁`, and

```
P(x)      :⇔  wt(x) ≤ e                       (the closeness predicate)
B         := { γ ∈ F : ∃ c ∈ C, P(g(γ) − c) }         (the bad set = project `badSet`)
N(γ)      := #{ c ∈ C : P(g(γ) − c) }                 (local decoding multiplicity)
T         := { (γ,c) ∈ F × C : P(g(γ) − c) }          (the tube)
L         := { q ∈ C : wt(f₁ − q) ≤ 2e }
Γ(u,q)    := { γ ∈ F : P( (f₀−u) + γ(f₁−q) ) }        (u,q ∈ C)
κ(q)      := max_{u ∈ C} |Γ(u,q)|
```

The project's `badSet C e f₀ f₁` is exactly `B` (no degeneracy filter is present in the Lean
sources; the filter used in earlier *experiments* only shrinks `B`, and every statement below is
monotone under passing to a subset of `B`, except the two *identities*, which need the full `B`).

### 1.2 Weight axioms

* **(W1) subadditivity** `wt(x+y) ≤ wt(x) + wt(y)`;
* **(W2) invariance under nonzero scalars** `wt(λx) = wt(x)` for `λ ≠ 0`. Only the inequality
  `wt(λx) ≤ wt(x)` (`λ ≠ 0`) is used; applied to `λ` and `λ⁻¹` it forces equality, so (W2) is not
  a strengthening. `wt(−x) = wt(x)` is the case `λ = −1`; nonnegativity and `wt 0 = 0` are never
  used.
* **(W3) coordinate structure** `V = A^ι`, `wt(x) = #{i : x_i ≠ 0}`. **Used only in §6 and §5.2.**

Which part of the mechanism needs what:

| statement | needs |
| --- | --- |
| pencil identity `B = ⋃_q Γ(u_q,q)` (§3, §4) | **nothing about `wt`** — holds for an arbitrary predicate `P` on `V` |
| multiplicity identity (§4) | arbitrary `P`; finiteness of `C` |
| secant lemma `q ∈ L` (§2) | (W1) + (W2) |
| pairwise disjointness criterion (§5.1) | (W1) + (W2) |
| capacity estimates `κ ≤ chargeCap`, second-order bound (§5.2, §6) | (W3) |
| directions bound (§8) | (W1)+(W2), plus finiteness for counting |

**(W2) is the one substantive restriction.** It holds for the Hamming weight, for the rank metric
(`rank(λM) = rank M`), and for every "projective" weight (a weight that factors through
`(V∖0)/F^×`, i.e. a gauge on the projective space). It **fails** for norms over `ℝ`/`ℂ`; there the
mechanism survives in scaled form, see §2.2.

---

## 2. The secant lemma (Lemma A) — PROVED

> **Lemma A.** Assume (W1),(W2). Let `γ ≠ γ₀` in `F`, `c,c₀ ∈ C` with `wt(g(γ)−c) ≤ e` and
> `wt(g(γ₀)−c₀) ≤ e`. Then `q := (γ−γ₀)⁻¹(c−c₀) ∈ C` and `wt(f₁ − q) ≤ 2e`, i.e. `q ∈ L`.

*Proof.* `q ∈ C` because `C` is a subspace. Compute in `V`:

```
(γ−γ₀)(f₁ − q) = (γ−γ₀)f₁ − (c−c₀) = (g(γ) − c) − (g(γ₀) − c₀).
```

By (W2) with `λ = −1` and (W1), the right-hand side has weight `≤ 2e`. By (W2) with
`λ = (γ−γ₀)⁻¹`, `wt(f₁−q) = wt((γ−γ₀)(f₁−q)) ≤ 2e`. ∎

Nothing else is used: no minimum distance, no relation between `e`, `|ι|` and `|F|`, no RS
structure, no bound on `|L|`, no finiteness. The hypothesis is *exactly* (W1)+(W2).

**Corollary A′ (all secants, not only those through the base point).** For *any* two elements of
`B` with *any* choice of witnesses, the secant direction lies in `L`. This is what makes §8 work.

### 2.2 The general-metric version (what happens without (W2))

Let `d` be a translation-invariant metric on `V` and let
`σ(λ) := sup_{x≠0} d(λx,0)/d(x,0) ∈ (0,∞]` be its scaling modulus. The same computation gives

> **Lemma A_σ.** `d(f₁, q) ≤ σ((γ−γ₀)⁻¹) · 2e`.

For Hamming/rank, `σ ≡ 1` and one recovers Lemma A. For a norm over `ℝ`, `σ(λ) = |λ|`, so the
statement becomes `‖f₁ − q‖ ≤ 2e/|γ−γ₀|`: the pencil radius shrinks with the distance to the base
point, so the theory persists but `L` must be replaced by a *filtration* `L(r)` of nested
neighbourhoods. This is the honest general-metric form; the "single radius `2e`" statement is
equivalent to projective invariance of the weight. **PROVED**, same proof.

---

## 3. The pencil lemma (Lemma B) and the covering (Lemma C) — PROVED, and purely affine

Fix `γ₀ ∈ B` with a witness `c₀`, and for `q ∈ C` put `u_q := c₀ − γ₀ q ∈ C`. Two *identities* in
`V` (no weight, no inequality, no hypothesis at all beyond `C` being a subspace):

```
(f₀ − u_q) + γ₀ (f₁ − q) = g(γ₀) − c₀                                   (B1)
(f₀ − u_q) + γ  (f₁ − q) = g(γ)  − (c₀ + (γ−γ₀) q)                      (B2)
```

> **Lemma B.** `γ₀ ∈ Γ(u_q,q)` for **every** `q ∈ C` — the sets `Γ(u_q,q)` form a pencil through
> the base point. If moreover `γ ∈ B∖{γ₀}` has witness `c` and `q = (γ−γ₀)⁻¹(c−c₀)`, then
> `c₀+(γ−γ₀)q = c` and hence `γ ∈ Γ(u_q,q)`.

*Proof.* (B1) with `P(g(γ₀)−c₀)`; (B2) with `P(g(γ)−c)`. ∎

The geometric content, stated once and for all:

> **Lemma C (pencil covering).** In the affine space `F × C`, the "non-vertical" lines
> `Λ_q := {(γ, u_q+γq) : γ ∈ F}`, `q ∈ C`, are exactly the lines through `p₀=(γ₀,c₀)` other than
> `{γ₀}×C`, and they **partition** `(F×C) ∖ ({γ₀}×C)`: every point `(γ,c)` with `γ ≠ γ₀` lies on
> `Λ_q` for the unique `q = (γ−γ₀)⁻¹(c−c₀)`. Moreover `Γ(u_q,q) = π_F(Λ_q ∩ T)` and
> `B = π_F(T)`.

*Proof.* `(γ,c) ∈ Λ_q ⇔ c = c₀+(γ−γ₀)q ⇔ q = (γ−γ₀)⁻¹(c−c₀)` for `γ ≠ γ₀`; and
`π_F(Λ_q∩T) = Γ(u_q,q)` is (B2). ∎

**This is the whole "charging map".** The map `φ : B∖{γ₀} → Σ_q (Γ(u_q,q)∖{γ₀})`,
`γ ↦ (q(γ), γ)`, of the previous round is the composition "choose a witness, then apply the
partition of Lemma C, then project". Its injectivity is the tautology "the second coordinate is
`γ`"; the mathematical content is Lemma B (membership) + Lemma A (the index `q` lies in `L`).
The object being injected is a *point of the tube*, and the target is *the partition of the tube by
the pencil*: `φ` is the restriction to a section of the canonical map `T ∖ ({γ₀}×C) → Σ_q Λ_q∩T`.

---

## 4. The exact candidate theorem

> **Theorem 1 (pencil identity; T2 is an equality).** *(PROVED; needs only: `C` a subspace,
> `B ≠ ∅`; for the restriction of the index set to `L` also (W1),(W2).)* Let `γ₀ ∈ B` with witness
> `c₀`. Then
> ```
> B = ⋃_{q ∈ L} Γ(u_q, q),        and   γ₀ ∈ Γ(u_q,q) for all q ∈ C,
> ```
> and moreover `Γ(u_q,q) = {γ₀}` for every `q ∈ C ∖ L`.

*Proof.* `⊇`: if `γ ∈ Γ(u_q,q)` then `u_q+γq ∈ C` is a witness for `γ`, so `γ ∈ B`. `⊆`: `γ₀ ∈ B`
by assumption and lies in every `Γ(u_q,q)` by Lemma B; for `γ ∈ B∖{γ₀}` pick a witness `c`, put
`q := (γ−γ₀)⁻¹(c−c₀)`; then `q ∈ L` by Lemma A and `γ ∈ Γ(u_q,q)` by Lemma B. Last claim: if
`γ ∈ Γ(u_q,q)∖{γ₀}` then `c := u_q+γq` is a witness for `γ` with
`(γ−γ₀)⁻¹(c−c₀) = q`, so Lemma A gives `q ∈ L`. ∎

> **Theorem 2 (multiplicity identity; the exact T3).** *(PROVED; additionally `C` finite.)* With
> the notation above,
> ```
> Σ_{q ∈ L} ( |Γ(u_q,q)| − 1 )  =  Σ_{γ ∈ B∖{γ₀}} N(γ)  =  |T| − N(γ₀),
> ```
> and therefore
> ```
>      |B|  =  1 + Σ_{q ∈ L} ( |Γ(u_q,q)| − 1 )  −  Σ_{γ ∈ B∖{γ₀}} ( N(γ) − 1 ).      (★)
> ```

*Proof.* Double count `I := {(q,γ) : q ∈ C, γ ∈ Γ(u_q,q), γ ≠ γ₀}`. Fibre over `q`: `|Γ(u_q,q)|−1`
by Lemma B, and it is `0` for `q ∉ L` by Theorem 1. Fibre over a fixed `γ ≠ γ₀`: the map
`q ↦ u_q + γq = c₀ + (γ−γ₀)q` is a bijection `C → C` (affine with invertible linear part
`γ−γ₀ ≠ 0`), and `γ ∈ Γ(u_q,q)` says precisely that its value is a witness for `γ`; so the fibre
has size `N(γ)`, which is `0` unless `γ ∈ B`. The second equality is `|T| = Σ_{γ} N(γ)`. (★)
follows since `|B|−1 = Σ_{γ∈B∖{γ₀}} 1`. ∎

> **Corollary 3 (the theorem in the form asked for: T1).** *(PROVED.)* For `B ≠ ∅` and any base
> point,
> ```
> |B| ≤ 1 + Σ_{q ∈ L} ( |Γ(u_q,q)| − 1 ) ≤ 1 + Σ_{q ∈ L} ( κ(q) − 1 ),
> ```
> with equality in the first inequality **iff** `N(γ) = 1` for every `γ ∈ B∖{γ₀}` (unique decoding
> away from the base point).

> **Corollary 4 (what the based sum really is).** `1 + Σ_{q∈L}(|Γ(u_q,q)|−1) = |T| − N(γ₀) + 1`.
> The based-capacity bound is the fibre-counting bound `|π_F(T)| ≤ |T| − (N(γ₀)−1)`.

Corollary 4 is the honest verdict on the discovery: *the sum over the pencil carries no information
beyond the size of the tube.* Everything non-trivial must come from bounding `|Γ|` (§6) or `|L|`.

---

## 5. Pairwise intersections

### 5.1 The disjointness criterion — PROVED

> **Lemma 5.** *(needs (W1),(W2).)* Let `q ≠ q′ ∈ C` and `γ ∈ Γ(u_q,q) ∩ Γ(u_{q′},q′)` with
> `γ ≠ γ₀`. Then
> 1. `wt(q − q′) ≤ 2e`; in particular `Γ(u_q,q) ∩ Γ(u_{q′},q′) ⊆ {γ₀}` whenever `wt(q−q′) > 2e`;
> 2. `N(γ) ≥ 2`.
>
> Conversely, `Γ(u_q,q) ∩ Γ(u_{q′},q′) ∖ {γ₀} = {γ ≠ γ₀ : both c₀+(γ−γ₀)q and c₀+(γ−γ₀)q′ are
> witnesses for γ}`.

*Proof.* The two witnesses `c = c₀+(γ−γ₀)q`, `c′ = c₀+(γ−γ₀)q′` are distinct (as `γ≠γ₀`, `q≠q′`),
which is (2); and `c − c′ = (γ−γ₀)(q−q′)` has weight `≤ 2e` by (W1), hence `wt(q−q′) ≤ 2e` by (W2),
which is (1). ∎

> **Corollary 6 (unique-decoding regime).** If `V = A^ι` with Hamming weight and the minimum
> distance of `C` satisfies `2e < d(C)`, then the sets `Γ(u_q,q)∖{γ₀}`, `q ∈ L`, are pairwise
> disjoint and (★) is an **equality with zero deficit**:
> `|B| = 1 + Σ_{q∈L}(|Γ(u_q,q)|−1)`.

### 5.2 No universal constant `C(e)` — REFUTED

> **Counterexample 7.** Take any field `F`, `V = F³`, `C = {(a,0,0) : a ∈ F}`, `e = 2`,
> `f₀ = 0`, `f₁ = (0,0,1)` (so `f₁ ∉ C`), `γ₀ = 0`, `c₀ = 0`. Then `q = (0,0,0)` and
> `q′ = (1,0,0)` both lie in `L` (`wt(f₁−q)=1`, `wt(f₁−q′)=2`), `u_q = u_{q′} = 0`, and for every
> `γ`, `wt(γ(f₁−q)) = 1 ≤ e` and `wt(γ(f₁−q′)) = 2 ≤ e`. Hence
> `Γ(u_q,q) = Γ(u_{q′},q′) = F` and `|Γ(u_q,q) ∩ Γ(u_{q′},q′)| = |F|`, unbounded in terms of `e`.
> (Verified exactly for `F = F₁₁`: `|Γ∩Γ′| = 11 = |B|`.)

So the Phase-IV wish "`|Γ_q ∩ Γ_{q′}| ≤ C(e)` for `q ≠ q′`" is **false unconditionally.** The
counterexample is not an artefact: by Lemma 8 below, an unbounded `Γ` occurs **iff** a pencil line
lies entirely inside the ball, which requires two codewords within `e` of `f₁`, i.e. `d(C) ≤ 2e`.
The correct statement is the dichotomy of §6.

### 5.3 The second-order theorem: intersections are first-order objects one level up — PROVED

> **Theorem 9 (doubling).** *(Hamming; `V = A^ι`.)* For `q,q′ ∈ C` put `v = f₁−q`, `v′ = f₁−q′`,
> and consider in `V ⊕ V` (index set `ι ⊔ ι`, Hamming weight = sum of the two weights) the affine
> line
> ```
> γ ↦ A + γ V,    A := (f₀−u_q, f₀−u_{q′}),   V := (v, v′).
> ```
> Then `Γ(u_q,q) ∩ Γ(u_{q′},q′) ⊆ Λ := {γ : wt_{V⊕V}(A+γV) ≤ 2e}`, and Lemma 8 applied to `Λ`
> gives, whenever `wt(v) + wt(v′) > 2e`,
> ```
> |Γ(u_q,q) ∩ Γ(u_{q′},q′)| ≤ chargeCap( 2e , d(f₁,q) + d(f₁,q′) ).
> ```
> More generally, for `q_1,…,q_k` the `k`-fold intersection embeds in the first-order set of the
> `k`-fold configuration `(V^k, Σ-weight, radius ke, direction (v_1,…,v_k))`, giving
> `|⋂_{j} Γ(u_{q_j},q_j)| ≤ chargeCap(ke, Σ_j d(f₁,q_j))` when `Σ_j d(f₁,q_j) > ke`.

*Proof.* `wt(x) ≤ e ∧ wt(y) ≤ e ⇒ wt(x)+wt(y) ≤ 2e`, and the pair of the two error vectors is
`A+γV` by (B2) applied twice. Then apply Lemma 8. ∎

This answers Phase V structurally: **the hierarchy exists and is self-similar** — "second-order
object" is not a new invariant `κ(q,q′)` but the *same* first-order line-in-a-ball object for the
diagonal configuration in `V⊕V` at radius `2e`. (CHECKED exactly on 500k+ pairs from small random
linear and RS codes over `F₅,F₇,F₁₁`: no violation; the bound is strictly better than the trivial
`e+1` on ~90% of the pairs. This is a check of a proved lemma, not evidence.)

---

## 6. Where Hamming actually enters: the line-in-a-ball counting lemma — PROVED

> **Lemma 8 (dichotomy for one pencil line).** Let `V = A^ι` with Hamming weight, `a,v ∈ V`,
> `v ≠ 0`, `S = supp(v)`, `s = |S|`, `m = wt(a|_{ι∖S})`, and `Λ = {t ∈ F : wt(a+tv) ≤ e}`. For
> `i ∈ S` let `t_i` be the unique scalar with `(a+t_iv)_i = 0` if it exists (`t_i = −a_i/v_i` in the
> scalar case) and put `z(t) = #{i ∈ S : (a+tv)_i = 0}`. Then
> ```
> wt(a+tv) = m + s − z(t),      Λ = { t : z(t) ≥ m+s−e },      Σ_t z(t) ≤ s.
> ```
> Hence the **dichotomy**: either `m+s ≤ e`, and `Λ = F` (the whole line lies in the ball), or
> `|Λ| ≤ s/(m+s−e) ≤ s/(s−e) = chargeCap(e,s)`-type bound; in particular `|Λ| ≤ e+1`.

*Proof.* Immediate from the coordinate description; `Σ_t z(t) ≤ s` because each `i ∈ S`
contributes to at most one `t`. ∎

> **Corollary 10.** `κ(q) ≤ chargeCap(e, d(f₁,q))` for every `q` with `d(f₁,q) > e`, and
> `Γ(u_q,q) = F` is possible only when `d(f₁,q) + m ≤ e`. Consequently T1 implies the project's
> already-formalised `card_badSet_le_sum_chargeCap`, which explains the measured comparison
> (κ-charge never worse, usually strictly better) without any new invariant.

**This lemma is the only Hamming-specific ingredient of the entire theory.** For an abstract
weight satisfying (W1)+(W2), Theorems 1, 2, Lemma A and Lemma 5 remain valid verbatim, and Lemma 8
must be *assumed* in the form "either the line is contained in the ball, or `|Λ| ≤ cap(e,·)`". For
the rank metric the analogue of Lemma 8 is **OPEN** (a pencil of matrices `A+tV` of bounded rank —
this is a genuinely different, and interesting, question).

---

## 7. T1 / T2 / T3 — the exact comparison, and why T3 as posed is impossible

```
        |B|
   =    | ⋃_{q∈L} Γ(u_q,q) |                                   (T2 — IDENTITY, Thm 1)
   =    1 + Σ_{q∈L}(|Γ(u_q,q)|−1) − Σ_{γ∈B∖{γ₀}}(N(γ)−1)       (exact T3, Thm 2)
   ≤    1 + Σ_{q∈L}(|Γ(u_q,q)|−1)                              (union bound)
   ≤    1 + Σ_{q∈L}(κ(q)−1)                                    (T1)
   ≤    max(1, Σ_{q∈L} chargeCap(e,d(f₁,q)))                   (project's proved bound)
```

The three losses are now named:

| step | exact loss | geometric meaning |
| --- | --- | --- |
| exact T3 → union bound | `Σ_{γ∈B∖{γ₀}} (N(γ)−1)` | total excess decoding multiplicity along the line |
| union bound → T1 | `Σ_{q∈L}(κ(q)−|Γ(u_q,q)|)` | difference between the *based* line through `(γ₀,c₀)` and the best line of slope `q` |
| T1 → chargeCap bound | `Σ_{q∈L}(chargeCap−κ)` | slack of the counting Lemma 8 |

> **Proposition 11 (no unconditional `Δ`).** *(REFUTED-type result, PROVED.)* There is no
> nonnegative quantity `Δ` depending only on the pencil configuration, positive whenever
> `|L| ≥ 2`, such that `|B| ≤ 1 + Σ_{q∈L}(|Γ(u_q,q)|−1) − Δ` holds unconditionally: by (★) the
> maximal admissible `Δ` **equals** `Σ_{γ∈B∖{γ₀}}(N(γ)−1)`, which is `0` whenever every bad
> parameter decodes uniquely — in particular on **every** instance with `2e < d(C)`
> (Corollary 6), a regime that certainly contains instances with `|B| ≥ 2` and `|L| ≥ 2` (take
> `e = 1` and any code of minimum distance `≥ 3`: `L = Ball(f₁,2) ∩ C` easily has two elements,
> since `wt(q−q′) ≤ 4` is compatible with `d ≥ 3`). Unique decoding was also the generic situation
> in the tested families (equality in 3221/3296 instances of the previous round).
> **Forced overlap of pencils is therefore equivalent to forced non-unique decoding, and cannot be
> derived from the incidence geometry alone.**

This closes Phase IV/VI in the negative for the *based* sum, and redirects the search: the only
available improvements are (i) restricting `L` to the realised directions `Q`, (ii) sharpening
`κ`, (iii) a bound of a completely different shape, such as §8.

---

## 8. The geometry of the direction set `Q` (Phase VII) — PROVED, field-free

Choose one witness `c_γ` for each `γ ∈ B` and set `P := {(γ,c_γ) : γ ∈ B} ⊆ F × C`, a set of `|B|`
points with pairwise distinct first coordinates. By Corollary A′ **every direction determined by
`P` lies in `L`** — a constraint that does not involve `f₀` at all.

> **Theorem 12 (two-base-point incidence bound).** *(PROVED; any field, any `dim C`.)* Let
> `D ⊆ L` be the set of directions determined by `P` and `|B| ≥ 2`. Fix `x ≠ y ∈ P`, let `d₀` be
> their direction and `ℓ` their joining line. Then the map `z ↦ (dir(x,z), dir(y,z))` is injective
> on `P ∖ ℓ` with values in the off-diagonal of `D × D`, hence
> ```
> |B| ≤ |P ∩ ℓ| + |D|(|D|−1) ≤ κ(d₀) + |L|(|L|−1) ≤ (e+1) + |L|(|L|−1)
> ```
> (the last step under the non-degeneracy hypothesis of Lemma 8).

*Proof.* Two non-vertical lines with distinct directions `d₁ ≠ d₂` meet in at most one point:
`a₁+γd₁ = a₂+γd₂` forces `γ(d₁−d₂) = a₂−a₁`, and `γ ↦ γ(d₁−d₂)` is injective. If
`dir(x,z) = dir(y,z)` then `x,y,z` are collinear, i.e. `z ∈ ℓ`. Points of `P∩ℓ` lie in the pencil
member of direction `d₀` based at `x`, so `|P∩ℓ| ≤ κ(d₀)`. ∎

Comparison with T1 (`≈ |L|·(κ̄−1)`): Theorem 12 is better exactly when `|L| ≲ κ̄`, i.e. for short
lists with large capacities; in the regime of the previous round (`κ̄ ≈ 1.6`, `|L|` up to 136) it is
much worse. It is nevertheless the first bound in this project that is *quadratic in the list and
independent of the capacities*, and it uses neither Johnson nor RS nor the field size.

> **Remark 13 (the Rédei–Szőnyi route — OPEN, literature-dependent).** Over a **prime** field, a
> `k`-point set of `AG(2,p)` with `k ≤ p` is either collinear or determines at least `(k+3)/2`
> directions (Rédei's theorem and its extension to `k<p`). Projecting `P` by a linear functional
> `λ : C → F` (the projection is non-collinear for some `λ` unless `P` itself is collinear) would
> give the *linear* bound `|B| ≤ 2|D| − 3 ≤ 2|L| − 3` unless `B` is a single pencil member (in
> which case `|B| ≤ κ`). Two caveats: (i) the statement is prime-field specific — over `F_{q₀²}` a
> subplane gives `k = q₀²` points with only `q₀+1` directions, and Theorem 12 is then sharp in
> order of magnitude; (ii) no Rédei-type theorem is in Mathlib, so this route costs a full
> formalisation of a nontrivial external theorem. It does **not** beat T1 in the measured regime.

> **Remark 14 (three-point relation).** For `γ,γ′,γ″ ∈ B` with witnesses, the three secant
> directions satisfy `(γ′−γ₀)q′ = (γ−γ₀)q + (γ′−γ)r`, i.e. `q′` is the affine combination
> `αq + (1−α)r`, `α = (γ−γ₀)/(γ′−γ₀)`. So `Q ∪ (all secants)` is closed under a prescribed system
> of affine relations *and* contained in the ball `L`. Exploiting this ("many directions in a small
> Hamming ball satisfying many affine relations") is, in our judgement, the best next theorem to
> attack; see §11.

---

## 9. Does anything depend on Reed–Solomon? — No

Explicit audit of every statement above:

* **RS structure:** used nowhere. `C` is an arbitrary `F`-subspace throughout. (Consistent with the
  previous round's random-linear-code families, but here it is a matter of proof, not of data.)
* **Minimum distance:** used only in Corollary 6 (`2e < d(C)`) and mentioned in §5.2 as the
  condition making Counterexample 7 possible. Nowhere else.
* **Relations between `e`, `n`, `|F|`, `|L|`:** used nowhere.
* **Field:** arbitrary in §1–§8 except where cardinalities are summed (finiteness of `C`, `F`) and
  in Remark 13 (prime field, and that remark is OPEN).
* **Hamming:** only Lemma 8, Corollary 10, Theorem 9, Corollary 6 (via `d(C)`). The charging
  mechanism itself (Theorems 1, 2) needs **no weight whatsoever**: it holds for an arbitrary
  subset `Ball ⊆ V` in place of `{x : wt x ≤ e}`.
* **Alphabet:** `A` may be any `F`-vector space (the project's `AlphabetMCA` generality), since
  Lemma 8 only uses "a coordinate is zero or not".

Domain of validity of the mechanism, in increasing order of hypothesis:

| level | hypotheses | valid results |
| --- | --- | --- |
| 0 | `C` subspace, arbitrary closeness predicate | Lemma B, Lemma C, Theorem 1 (without `q∈L`), Theorem 2, Corollary 4 |
| 1 | + (W1),(W2) | Lemma A, `Γ_q={γ₀}` off `L`, Theorem 1, Lemma 5, Theorem 12 |
| 1′ | + translation-invariant metric with modulus `σ` | Lemma A_σ (scaled pencil radius) |
| 2 | + (W3) Hamming/coordinates | Lemma 8, Corollary 10, Theorem 9, T1, project bound |
| 3 | + minimum distance `2e<d` | Corollary 6 (exact equality, zero deficit) |

---

## 10. What remains before Lean, and the recommended Lean statement

The mathematics is now stable. A formalisation mission should implement exactly the following
modular skeleton (naming suggestions only; all of it is `Ball`-agnostic except the last file).

1. **`PencilCore`** — `variable {F V} [Field F] [AddCommGroup V] [Module F V] (C : Submodule F V)`
   `(Ball : Set V)` `(f₀ f₁ : V)`; definitions `g`, `B`, `Γ`, `u_q`, `N`;
   `lemma base_mem_pencil : γ₀ ∈ Γ (u q) q` (B1) and `lemma charged_mem_pencil` (B2).
   *No weight, no finiteness.* Difficulty: trivial (`module`/`abel` after unfolding).
2. **`SecantLemma`** — abstract weight class with (W1),(W2) (Mathlib's `hammingNorm` satisfies
   both: `hammingNorm_add_le`… plus `hammingNorm_smul` for `λ ≠ 0`; check the exact names), then
   Lemma A. Difficulty: low.
3. **`PencilIdentity`** — Theorem 1 as a `Finset`/`Set` equality. Needs `Fintype F` for the
   `Finset` version. Difficulty: low–medium (the `⊇` direction needs the witness construction).
4. **`MultiplicityIdentity`** — Theorem 2 by `Finset.sum_comm`/`Finset.card_eq_sum_card_fiberwise`
   over `I ⊆ C ×ˢ F`. The only real work is the bijection `q ↦ c₀+(γ−γ₀)q` on the fibre over `γ`
   (`Equiv` from `Units.smul` + translation). Difficulty: medium. **This is the main new theorem.**
5. **`ChargingTheorem`** — Corollary 3 (T1) and Corollary 4; and the comparison
   `κ(q) ≤ chargeCap e (d f₁ q)` (Corollary 10) linking to the existing
   `ChargingCapacity.card_badSet_le_sum_chargeCap`. Difficulty: medium (Lemma 8 is the work; part
   of it already exists in `card_le_chargeCap`).
6. **`PencilIntersection`** (optional) — Lemma 5, Corollary 6, Theorem 9. Difficulty: medium; the
   doubling in Theorem 9 needs `ι ⊕ ι` and `hammingNorm` on a sum type.
7. **`DirectionsBound`** (optional) — Theorem 12. Difficulty: medium, purely combinatorial.

Open points that a Lean round does **not** need to resolve, and must not silently assume:

* whether `L` can be replaced by the realised set `Q` with a computable description — **OPEN**;
* a rank-metric analogue of Lemma 8 — **OPEN**;
* Rédei/Szőnyi (Remark 13) — **OPEN**, external, not in Mathlib;
* any improvement of the form "`Δ > 0` unconditionally" — **REFUTED**, do not attempt.

---

## 11. Final report (the requested 10 items)

1. **Core theorem discovered.** The charging map is the projection of the *partition of the tube
   `T = {(γ,c) : c ∈ C, g(γ)−c ∈ Ball}` by the pencil of affine `C`-lines through one of its
   points*. Its two exact expressions are Theorem 1 (`B = ⋃_{q∈L} Γ(u_q,q)`) and Theorem 2
   (`Σ_{q∈L}(|Γ(u_q,q)|−1) = Σ_{γ∈B∖{γ₀}} N(γ) = |T| − N(γ₀)`), whence the identity (★).
   **PROVED.**
2. **Minimal hypotheses.** `C` an `F`-subspace and *nothing else* for Theorems 1(core), 2;
   subadditivity + invariance of the weight under nonzero scalars for the secant lemma and for the
   restriction of the index set to `L`; the coordinate (Hamming) structure **only** for the
   capacity estimates. No RS, no minimum distance, no `e`–`n`–`|F|` relation, no list bound.
   **PROVED** (audit in §9).
3. **Geometric interpretation.** `B = π_F(T)`; a pencil of lines through a point covers everything
   except the vertical line through that point; `Γ(u_q,q)` is the parameter set of the pencil
   member `Λ_q`, i.e. `π_F(Λ_q ∩ T)`, and simultaneously the *level set of the coincidence
   multiplicity* `z(t) ≥ m+s−e` of an affine line in `V` (Lemma 8). The overlap multiplicity of the
   pencil arrangement is exactly the local decoding multiplicity `N(γ)`, independent of the base
   point.
4. **Charging lemma.** Lemma A + Lemma B + Lemma C of §2–§3; the injected object is a point of the
   tube, the target is the fibre decomposition of the tube by the pencil; injectivity is a
   tautology, membership is the content. **PROVED.**
5. **Intersection/union theorem.** Union: Theorem 1, an *identity*. Intersection: Lemma 5
   (overlap ⟹ `wt(q−q′) ≤ 2e` and `N ≥ 2`), Corollary 6 (`2e<d(C)` ⟹ pairwise disjoint away from
   `γ₀`, and (★) is an equality), Theorem 9 (second-order counting bound
   `chargeCap(2e, d(f₁,q)+d(f₁,q′))`, and its `k`-fold version). **PROVED.**
6. **Strongest new bound.** The exact identity (★) — strictly stronger than T1 and T2, and it
   *implies* both. Plus the incomparable capacity-free bound `|B| ≤ κ_max + |L|(|L|−1)`
   (Theorem 12).
7. **Counterexamples to stronger conjectures.** (a) `|Γ_q ∩ Γ_{q′}| ≤ C(e)` is **false**
   (Counterexample 7: intersection `= F`); (b) an unconditional geometric deficit `Δ>0` in T3 is
   **impossible** (Proposition 11): the maximal `Δ` equals `Σ(N(γ)−1)`, which vanishes whenever
   decoding is unique, e.g. always when `2e < d(C)`.
8. **Lean status.** Nothing formalised in this round by design (FREEZE respected: no Lean file
   touched, no axiom, no `sorry`, no `admit`, the existing project is untouched and still builds as
   before). §10 gives the modular skeleton, per-file difficulty, and the exact statements.
9. **What remains genuinely open.** (i) A description of the realised direction set `Q` better than
   `Q ⊆ L`; (ii) the geometry of `Q`: many directions inside a Hamming ball of radius `2e` obeying
   the affine relations of Remark 14 — is `|Q|` forced to be small, or forced to be spread?
   (iii) a Rédei-type direction theorem usable here (prime fields only, not in Mathlib);
   (iv) a rank-metric analogue of Lemma 8; (v) whether `|T|` itself admits a bound not going
   through list sizes.
10. **Best next theorem to attack.** *The direction–ball theorem*: let `Q ⊆ C` be a set of secant
    directions of a `|B|`-point graph set, all lying in `Ball(f₁,2e) ∩ C`, and closed under the
    three-point affine relation of Remark 14. Prove a nontrivial lower bound on `|Q|` in terms of
    `|B|` (Rédei-type, but field-free), or exhibit a subfield-plane style construction showing the
    quadratic bound of Theorem 12 is sharp. This is the only route left that can beat T1 in the
    regime that matters (`|L|` large, `κ` small), and it is Johnson-free and RS-free by
    construction.

### Level attained, honestly

* Level 1 is **exceeded**: the charging theorem is not merely correct, it is an *identity*, and its
  deficit is exactly characterised.
* Level 2 is **attained**: the mechanism is proved for an arbitrary closeness predicate over an
  arbitrary field and subspace, and for arbitrary metrics with a scaling modulus (§2.2, §9).
* Level 3 is **attained in the negative direction that matters**: the union geometry is fully
  understood (T2 is an equality), and the hoped-for improvement of the κ-bound by overlap is
  *proved impossible* (Proposition 11) — with the second-order intersection theorem (Theorem 9)
  as the constructive residue.
* Levels 4–5 are **not attained**; §11.10 states the precise question whose answer would give them.
