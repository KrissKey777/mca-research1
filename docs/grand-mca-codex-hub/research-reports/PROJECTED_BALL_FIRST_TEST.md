# PROJECTED HAMMING BALL — FIRST DECISIVE TEST

**Mission: one question only.** Does the projected Hamming ball `λ(L(f₁,2e))` have
intrinsically smaller size than `F_p` for an *admissible* functional `λ`?

Constraints respected: **no Lean file created or modified**, no axiom, no `sorry`/`admit`, no
formalisation, no proof of Rédei–Szőnyi, no Johnson/list-size search, no κ redevelopment, no broad
scan. One small exact-arithmetic check was written (`analysis/projected_ball_first_test.py`,
transcript `analysis/projected_ball_first_test_output.txt`, runtime 72 s, Python integers mod a
prime, **no floats**); every statement labelled PROVED below carries a complete human-checkable
proof and does not rest on the computation.

---

## 0. Answer, in one page

> ### **CASE A — structural compression exists, and it is exactly the interpolation regime.**

| # | statement | label |
| --- | --- | --- |
| 1 | **Level 1 (ambient ball, `C = F_p^n`).** For `e ≥ 1` and *every* nonzero `λ`, `λ(L) = F_p`. No dependence on `|supp λ|`, no threshold in `p`. | **PROVED** (§2) |
| 2 | **The general obstruction.** If some `q₀ ∈ C`, `0 ≠ v ∈ C` satisfy `d(f₁,q₀) + wt(v) ≤ 2e`, the whole line `q₀ + F_p v` lies in `L`; then `λ(L) = F_p` for every `λ` with `λ(v) ≠ 0`. If the space `N` spanned by such `v` contains `V_W`, then `M*_L = p` — *every* admissible `λ` is full. For MDS/RS codes with `d(f₁,C) + d ≤ 2e` this holds unconditionally, so there the projected route is quantitatively dead. | **PROVED** (§3) |
| 3 | **Compression is nevertheless real.** `\|λ(L)\| =` number of cosets of `ker λ` meeting `L`, hence `M*_L ≤ min(\|L\|, p)`; and the *support* refinement `M*_L ≤ 1 + min_{x ∈ supp V_W} m_x ≤ 1 + ⌊2e·\|L\| / \|supp V_W\|⌋`, `m_x = #{q ∈ L : q_x ≠ f₁(x)}`. | **PROVED** (§4, §5) |
| 4 | **A `p`-independent bound exists — exactly in the interpolation regime `2e ≤ n−k` (MDS).** There the error supports `supp(f₁−q)`, `q ∈ L`, are distinct and form an antichain, so `\|L\| ≤ Σ_{i≤2e} C(n,i) ≤ 2ⁿ` and `m_x ≤ Σ_{i≤2e} C(n−1,i−1) ≤ 2^{n−1}`, both free of `p`. Hence `M*_L ≤ 1 + 2^{n−1} = F(n,e)`, and `\|B\| ≤ 2·F − 3`, independent of `p`. | **PROVED** (§6) |
| 5 | **Yes, `\|λ(L)\| < p` really happens in a genuine MCA instance.** Smallest one found: `RS[4,2]/F₅`, `e = 1`, `f₀ = (0,0,1,0)`, `f₁ = (0,0,0,1)`, `B = {0,2,4}`, admissible `λ = ev` on the second pivot coordinate: `λ(L) = {0,2,4}`, `M*_L = 3 < 5 = p`, and the projected Rédei bound is **attained**: `\|B\| = 3 = 2·3 − 3`. | **PROVED** (explicit, §7) |
| 6 | **Exhaustive-per-instance measurement (81 443 non-collinear witness selections, `p ≤ 13`, `C^∨` enumerated in full).** `M*_L < p` in 993 records and `M*_L = p` in 80 450 — and the split is *exactly* the regime split: all 993 compressing records satisfy `2e ≤ n−k`, and **none** of the 80 441 records with `2e > n−k` compresses at all. Every bound of items 3–4 held with **0 violations**, as did the Rédei consistency `\|B\| ≤ 2M*_L − 3`. | **EMPIRICALLY SUPPORTED** (§8) |
| 7 | A universal `p`-independent bound `\|λ(L)\| ≤ F(n,e)` valid for *every* code and *every* nonzero `λ` | **REFUTED** — item 1 and item 2 give counterexamples with `\|λ(L)\| = p` for arbitrarily large `p` at fixed `n,e` (§2, §3). |

**Bottom line.** The projected-ball route is *not* quantitatively empty, but its content is confined
to a sharply delimited regime. Outside `2e ≤ n−k` the projected ball is full and the mechanism only
reproduces `|B| ≤ 2p − 3`; inside it, `M*_L` is bounded by a quantity depending only on `n, e, k`
(and, more finely, on `|supp V_W|`), so `|B|` inherits a **`p`-free** bound. That is the theorem the
mission was looking for, together with the exact obstruction that limits it.

---

## 1. Notation, fixed once (unchanged from `PROJECTED_REDEI_CLAIMS.md`)

* `p` prime, `F = F_p`, `ι = {1,…,n}`, `C ⊆ Fⁿ` a linear code, `k = dim C`, `d = d(C)`.
* `f₀,f₁ ∈ Fⁿ`, `e ∈ ℕ`, `w = d(f₁,C)`, and
  `L = L(f₁,2e) = { q ∈ C : wt(f₁ − q) ≤ 2e }` (so `L ≠ ∅ ⟺ w ≤ 2e`).
* `H_{2e} = { z ∈ Fⁿ : wt(z) ≤ 2e }`, so `L = C ∩ (f₁ + H_{2e})`.
* `B ⊆ F` the bad set, `W_s = {(γ,c_γ)}` a witness selection, `q_{γγ'} = (γ−γ')⁻¹(c_γ−c_{γ'})` the
  secant slopes, `D(B) ⊆ L` (project's secant lemma), `V_W = span{ q − q' : q,q' ∈ D(W_s) }`.
* `λ : C → F` linear, `Λ : Fⁿ → F` any linear extension of `λ` (exists, and `λ(L)` does not depend
  on the choice, since `L ⊆ C`). `supp Λ = { x : Λ(e_x) ≠ 0 }`, `s = |supp Λ|`.
* **Admissibility** (proved earlier, Theorem B of `PROJECTED_REDEI_CLAIMS.md`):
  `S_λ = {(γ,λ(c_γ))}` is non-collinear `⟺ λ|_{V_W} ≠ 0`; for a coordinate functional
  `ev_x` this reads `x ∈ supp V_W := ⋃_{v ∈ V_W} supp v`.
* `M*_L(W_s) = min { |λ(L)| : λ|_{V_W} ≠ 0 }`.
* `m_x = #{ q ∈ L : q_x ≠ f₁(x) }` (the *activity* of coordinate `x` on the list).

---

## 2. Normal form and Level 1 — the ambient ball is always full

### 2.1 Normal form (PROVED, trivial but it fixes the object)

For any linear extension `Λ`,

```
λ(L) = Λ(f₁) + Λ(A),        A = A_λ(2e) = (C − f₁) ∩ H_{2e} = { q − f₁ : q ∈ L } .
```

So `λ(L)` is a translate of the image of the *admissible error set* `A`, and only `A` matters. The
three data the mission asked to separate enter as follows: `f₁` only through the translate `Λ(f₁)`
and through which errors are admissible (`A` depends on the coset `f₁ + C`); `supp λ` through
`Λ(A)`; `ker λ` through the fibres (§4); `C` through the constraint `q ∈ C`. `λ(L)` is in general
**not** an interval, not a subgroup and not a ball — §7 shows `λ(L) = {0,2,4} ⊆ F₅`, which is none
of these (it is not closed under addition, and it is a translate of `{0,2,4}`, a set of three
values with two distinct gaps in cyclic order).

### 2.2 Theorem 1 (Level 1) — **PROVED**

> Let `C = Fⁿ`, `e ≥ 1` and `λ ≠ 0`. Then `λ(L(f₁,2e)) = F_p`; in particular `|λ(H_{2e})| = p`
> for every nonzero `λ`, irrespective of `s = |supp λ|`, of `n`, and of `p`.
> If `2e = 0`, then `|λ(L)| = 1`.

*Proof.* Pick `x ∈ supp Λ` and put `a = Λ(e_x) ≠ 0`. For every `t ∈ F` the word
`q = f₁ + t a^{-1} e_x` has `wt(f₁ − q) ≤ 1 ≤ 2e`, so `q ∈ L`, and `λ(q) = Λ(f₁) + t`. As `t` runs
over `F` we obtain all of `F`. ∎

**Consequences demanded by Parts III, VI, VII of the parent plan.**

* Regime C (`s ≤ 2e`) and Regime D (`s > 2e`) have the *same* answer at Level 1: full. The exact
  dependence of `|λ(H_{2e})|` on `(p, s, 2e)` is therefore: `p` if `2e ≥ 1` and `s ≥ 1`, else `1`.
  There is **no** threshold and **no** extremal support pattern to find — the hoped-for
  "`λ(H_{2e}) = F_p` only for large support" phenomenon does not exist.
* The strong hope of Part VII — a universal `p`-independent bound `|λ(L)| ≤ F(n,e)` for every
  nonzero `λ` — is **REFUTED** already at `n = 1`, `e = 1`, `C = F_p`. A single-coordinate
  functional does give `λ(L) = F_p` as soon as one coordinate can be moved freely inside the ball.
  This is the fundamental obstruction the mission asked to record; §3 is its exact code-level form.
* Measured control (transcript, LEVEL 1 block): for `(p,n,e) ∈ {(5,3,1),(7,2,1),(5,2,2),(3,3,1),
  (7,3,1)}` the minimum of `|λ(ball)|` over **all** nonzero `λ` and three random `f₁` equals `p` in
  every case.

---

## 3. The exact obstruction inside a code (Level 2) — Theorem 2

The Level-1 proof used only one thing: a *line* through the ball. Inside a code the same mechanism
survives verbatim, and it is the only source of fullness we could not remove.

> ### Theorem 2 (line criterion). **PROVED**
> Suppose there are `q₀ ∈ C` and `v ∈ C ∖ {0}` with `d(f₁,q₀) + wt(v) ≤ 2e`. Then
> `q₀ + F·v ⊆ L`; consequently `|L| ≥ p` and, for every `λ` with `λ(v) ≠ 0`, `λ(L) = F_p`.

*Proof.* `wt(f₁ − q₀ − t v) ≤ wt(f₁ − q₀) + wt(t v) ≤ d(f₁,q₀) + wt(v) ≤ 2e`, and `q₀ + tv ∈ C`.
So the whole line is in `L`, and `λ(q₀ + tv) = λ(q₀) + t λ(v)` runs over `F` when `λ(v) ≠ 0`. ∎

> ### Theorem 2′ (fullness for *admissible* `λ`). **PROVED**
> Let `N = span{ v ∈ C ∖ {0} : ∃ q₀ ∈ C, d(f₁,q₀) + wt(v) ≤ 2e }`. If `V_W ⊆ N`, then
> `M*_L(W_s) = p`: **every** admissible `λ` has a full projected ball.

*Proof.* Admissible means `λ|_{V_W} ≠ 0`; since `V_W ⊆ N`, `λ|_N ≠ 0`, so `λ(v) ≠ 0` for at least
one generator `v` of `N`, and Theorem 2 gives `λ(L) = F_p`. ∎

> ### Corollary 2″ (RS/MDS form). **PROVED**
> Let `C` be Reed–Solomon (`k ≥ 1`, `n ≥ k`) and `d(f₁,C) + d ≤ 2e`, `d = n−k+1`. Then
> `M*_L(W_s) = p` for every witness selection: the projected Rédei bound degenerates to
> `|B| ≤ 2p − 3` and carries no information.

*Proof.* Take `q₀` a nearest codeword; every minimum-weight `v` satisfies
`d(f₁,q₀) + wt(v) = w + d ≤ 2e`, so all minimum-weight codewords lie in `N`. RS codes are spanned
by minimum-weight codewords: with evaluation points `α_1,…,α_n`, the polynomials
`P_j(X) = ∏_{i ≤ k, i ≠ j}(X − α_i)`, `j = 1,…,k`, have degree `k−1 < k`, exactly `k−1` roots among
the evaluation points, hence weight `n−k+1 = d`; and the matrix `(P_j(α_i))_{i,j ≤ k}` is diagonal
with nonzero diagonal, so the `P_j` are independent and span `C`. Thus `N = C ⊇ V_W`, and
Theorem 2′ applies. ∎
*(Checked numerically as well: for `RS[4,2]/F₅`, `RS[5,2]/F₅`, `RS[6,2]/F₇`, `RS[6,3]/F₇`,
`RS[6,2]/F₁₁`, `RS[6,2]/F₁₃`, `RS[7,3]/F₁₁` the minimum-weight codewords have rank exactly `k`.)*

**Reading.** Fullness is *not* an accident of small primes: it is forced whenever the ball around
`f₁` is wide enough to contain a whole codeword line, i.e. `2e ≥ w + d`. This is the exact
frontier; §6 shows the complementary regime behaves in the opposite way.

---

## 4. Fibre (coset) description — what compression can possibly mean

> ### Theorem 3. **PROVED**
> Let `λ ≠ 0` and `K = ker λ ⊆ C` (a hyperplane of `C`). Then `|λ(L)|` equals the number of cosets
> of `K` meeting `L`. Consequently:
> 1. `q,q' ∈ L` collide `⟺ q − q' ∈ K` and `wt(q−q') ≤ 4e`; so if `K` contains no nonzero
>    codeword of weight `≤ 4e`, then `λ` is **injective** on `L` and `|λ(L)| = |L|`;
> 2. `|λ(L)| ≥ |L| / h_λ`, where `h_λ = max_{coset} |L ∩ (q + K)|`;
> 3. `|L| ≥ 2` forces `d ≤ 4e` (the difference of two list elements is a nonzero codeword of
>    weight `≤ 4e`).

*Proof.* (fibres) The fibre of `v ∈ λ(L)` is `L ∩ (q_v + K)` for any `q_v ∈ L` with `λ(q_v) = v`;
distinct values give distinct cosets. (1) `wt(q−q') ≤ wt(q−f₁) + wt(f₁−q') ≤ 4e`. (2) and (3) are
immediate. ∎

Theorem 3 says precisely where compression can come from: **only** from low-weight codewords that
`λ` kills. It also gives the intrinsic lower bound `M*_L ≥ |L| / h`, `h = max` number of list
elements in one affine hyperplane of `C` — so no bound of the form `M*_L ≤ o(|L|)` can hold for
lists in general position.

---

## 5. The support bound — the one place where admissibility helps

> ### Theorem 4 (coordinate/support bound). **PROVED**
> For every `x ∈ ι`: `|ev_x(L)| ≤ 1 + m_x`. More generally, for every `λ`,
> `|λ(L)| ≤ 1 + #{ q ∈ L : supp(f₁−q) ∩ supp Λ ≠ ∅ }`.
> Moreover `Σ_{x ∈ ι} m_x = Σ_{q ∈ L} wt(f₁ − q) ≤ 2e·|L|`, hence for every `S ⊆ ι`
> `min_{x ∈ S} m_x ≤ ⌊ 2e·|L| / |S| ⌋`.

*Proof.* All `q ∈ L` with `q_x = f₁(x)` contribute the single value `f₁(x)`; the remaining `m_x`
elements contribute at most `m_x` values. The general form is the same argument with
`Λ(q − f₁) = 0` whenever `supp(q−f₁) ∩ supp Λ = ∅`. The identity is double counting of the pairs
`(x,q)` with `q_x ≠ f₁(x)`, and the inequality is `wt(f₁−q) ≤ 2e`. ∎

> ### Theorem 5 (joint optimisation: admissible support bound). **PROVED**
> Let `W_s` be a non-collinear witness selection. Then
>
> ```
> M*_L(W_s)  ≤  1 + min_{x ∈ supp V_W} m_x  ≤  1 + ⌊ 2e·|L| / |supp V_W| ⌋ ,
> ```
>
> and since every nonzero `v ∈ V_W ⊆ C` has `wt(v) ≥ d`, also `M*_L ≤ 1 + ⌊2e·|L| / d⌋`
> unconditionally. In particular `M*_L < |L|` as soon as `|supp V_W| > 2e·|L|/(|L|−1)`,
> i.e. essentially as soon as `|supp V_W| > 2e`.

*Proof.* By Theorem B of the previous report, `ev_x` is admissible exactly for `x ∈ supp V_W`
(non-collinearity of `W_s` guarantees `V_W ≠ 0`, so this set is nonempty). Apply Theorem 4 with
`S = supp V_W`. ∎

This is the exact answer to Parts VIII–X: the admissibility constraint is a *linear* one
(`λ|_{V_W} ≠ 0`), it never helps make `λ(L)` smaller than the unrestricted optimum — the
unrestricted optimum is the useless value `1` (a `λ` annihilating `span(L−L)`), which is why the
minimisation must be constrained — but it costs *little*: one may always stay inside the
`|supp V_W|`-element family of coordinate functionals, and the averaging above then buys the factor
`2e/|supp V_W|` over the trivial estimate `|L|`. The only intrinsic parameter of `V_W` that enters
is its **support size**, not its dimension, not its generalized Hamming weights.

---

## 6. The regime where the projection is genuinely `p`-free

> ### Theorem 6 (interpolation regime). **PROVED**
> Let `C` be MDS (any `k` coordinates determine a codeword — e.g. Reed–Solomon) and assume
> `2e ≤ n − k`. Then the map `q ↦ E_q := supp(f₁ − q)` is **injective** on `L`, and
> `{E_q : q ∈ L}` is an **antichain** of subsets of size `≤ 2e`. Consequently
>
> ```
> |L|  ≤  Σ_{i=0}^{2e} C(n,i)  ≤  2ⁿ ,        m_x  ≤  Σ_{i=1}^{2e} C(n−1,i−1)  ≤  2^{n−1} ,
> ```
>
> and therefore, for any non-collinear witness selection,
>
> ```
> M*_L(W_s)  ≤  1 + min_{x ∈ supp V_W} m_x  ≤  1 + 2^{n−1}  =:  F(n,e,k) ,
> ```
>
> a bound **independent of `p`**. Combined with the (quoted) Rédei–Szőnyi theorem as in
> `PROJECTED_REDEI_CLAIMS.md` §4.2, `|B| ≤ 2F − 3`, again independent of `p`.

*Proof.* If `E_q = E_{q'}` then `q` and `q'` agree with `f₁`, hence with each other, outside a set of
size `≤ 2e`, i.e. on at least `n − 2e ≥ k` coordinates; by the MDS property `q = q'`. For the
antichain property: for `q ≠ q'`, `q − q'` is a nonzero codeword supported in `E_q ∪ E_{q'}`, so
`|E_q ∪ E_{q'}| ≥ d = n−k+1 > n−k ≥ 2e ≥ |E_q|`, whence `E_{q'} ⊄ E_q` and symmetrically. The
counting bounds follow (`m_x` counts list elements whose error support contains `x`). ∎

**This is the positive answer to the mission's question.** With `n, k, e` fixed and `p → ∞`, the
list, and hence every projection of it, stays bounded by a constant, while `p` grows without bound:
the compression is unbounded and structural, not numerical.

**Sharpness (measured, exact).** `RS[6,2]`, `e = 2` (`2e = 4 = n−k`), 40 random `f₁` per prime:

| `p` | `max |L|` | bound `C(n,2e)` | `max_x m_x` | `C(n−1,2e−1)` | `max_x |ev_x(L)|` | `max_λ |λ(L)|` |
| --- | --- | --- | --- | --- | --- | --- |
| 11 | 15 | 15 | 10 | 10 | 10 | 11 |
| 13 | 15 | 15 | 10 | 10 | 11 | 13 |
| 17 | 15 | 15 | 10 | 10 | 11 | 15 |
| 19 | 15 | 15 | 10 | 10 | 11 | 15 |
| 23 | 15 | 15 | 10 | 10 | 11 | 15 |
| 29 | 15 | 15 | 10 | 10 | — | — |

The saturation at `15` and `10`, **independent of `p` from `p = 17` on**, shows that the crude
`2ⁿ`/`2^{n−1}` bounds are in this instance realised at the tighter values `C(n,2e)` and
`C(n−1,2e−1)`, and that both are attained: the coordinate bound `1 + C(n−1,2e−1) = 11` is sharp,
and the general-`λ` bound `|L| = 15` is sharp. Coordinate functionals are strictly better than
general ones here (`11 < 15`) — exactly the gain Theorem 5 predicts, of size `≈ 2e/n = 2/3`.
For `RS[7,2]/F₁₃`, `e = 2` (`2e = 4 < n−k = 5`) the same measurement gives `max|L| = 4`,
`max_x m_x = 3`: far below the combinatorial bound, and again `p`-free.
Label of the exact extremal values `C(n,2e)` / `C(n−1,2e−1)`: **EMPIRICALLY SUPPORTED**
(the proved statement is the weaker `Σ_{i≤2e}` / antichain bound).

**Consistency with §3.** In the interpolation regime `2e ≤ n−k = d−1 < d ≤ w + d`, so Theorem 2's
hypothesis fails for *every* pair `(q₀,v)` — no codeword line fits in the ball. The two regimes are
disjoint, and §8 shows that, on all instances measured, they exhaust the possibilities.

---

## 7. The smallest exact MCA instance with `|λ(L)| < p`, and sharpness of the whole chain

Exhaustive search over `RS[4,2]/F₅` (`e = 1`, all `f₀,f₁` coset representatives, all witness
selections, all `25` functionals of `C^∨`) gives as the smallest projected ball:

```
p = 5,  C = RS[4,2] on {1,2,3,4},  d = 3,  e = 1,  2e = 2 = n − k   (interpolation regime)
f₀ = (0,0,1,0),   f₁ = (0,0,0,1),   w = d(f₁,C) = 2
B  = {0, 2, 4},                     |B| = 3
witnesses:  c₀ = (0,0,0,0),  c₂ = (4,0,1,2),  c₄ = (0,3,1,4)
L  = { (0,0,0,0), (0,2,4,1), (2,0,3,1), (3,4,0,1) },            |L| = 4
secant slopes:  q₂₀ = (2,0,3,1),  q₄₀ = (0,2,4,1)   (distinct ⇒ W_s non-collinear)
admissible λ = ev₂ (second pivot coordinate):
        λ(L) = {0, 2, 4},          M*_L = 3 < 5 = p
```

* `M*_L = 3 < p = 5`: **`|λ(L)| < p` is possible in a genuine MCA configuration** — the central
  question of the mission is answered affirmatively, with an explicit witness.
* `|B| = 3 = 2·M*_L − 3`: the projected Rédei bound is **attained exactly**. Together with the
  earlier `RS[6,3]/F₇` instance attaining the Rédei–Megyesi direction extremum, this makes the
  chain `B → S_λ → D(S_λ) → λ(L)` sharp at both ends on actual MCA data; no constant in it can be
  improved without extra hypotheses. Label: **PROVED (explicit instance)**.
* `λ(L) = {0,2,4}` is neither a subgroup, nor an interval, nor a ball: the warning in Part I of the
  parent plan was justified.

---

## 8. Exhaustive measurement (Level 2/3), and what it says

`analysis/projected_ball_first_test.py`, families `RS[4,2]/F₅`, `RS[4,3]/F₅`, `RS[5,2]/F₅`,
`RS[5,3]/F₅`, `RS[6,2]/F₇`, `RS[6,3]/F₇`, `RS[5,2]/F₁₁`, `RS[6,2]/F₁₃` plus two **non-RS** random
linear codes `RAND[6,3]/F₅`, `RAND[7,3]/F₇`. For every instance with `|B| ≥ 3` and every
non-collinear witness selection (capped at 64 per instance) the *entire* dual `C^∨` (`p^k`
functionals) was enumerated and `|λ(L)|` computed exactly. **81 443 records.**

| measurement | result |
| --- | --- |
| bound violations for `M* ≤ min(|L|,p)`, Theorem 5 (both forms), Theorem 6 counting, and Rédei consistency `2M*−3 ≥ |B|` | **0 / 81 443** each |
| `M*_L < p` | 993 |
| `M*_L = p` | 80 450 |
| `M*_L < |L|` | **81 443 / 81 443** (the projection always compresses strictly below the list size) |
| `M*_L < min(|L|,p)` | 993 |
| all 993 compressing records satisfy `2e ≤ n−k` | yes (993 / 993) |
| records with `2e > n−k` that compress | **0 / 80 441** |
| records with `w + d ≤ 2e` (Theorem 2′ hypothesis for RS) that are full | 50 / 50 |
| unrestricted `min_{λ≠0} |λ(L)| = 1` (i.e. `L` inside a hyperplane of `C`) | 1 record — a reminder that the unrestricted minimum is meaningless |
| admissible minimum `≥ 2` always | yes |

**Interpretation, stated carefully.**

* The measured families live at `p ≤ 13` with lists that are typically much larger than `p`
  (up to `|L| = 76` at `RS[6,3]/F₇`); that is precisely the regime `2e > n−k` where §3 proves
  fullness. So the 98.8 % fullness rate is *not* evidence against compression — it is a measurement
  of how much of the micro-instance corpus lies in the dead regime.
* The clean 993/0 split along `2e ≤ n−k` is the empirical face of Theorems 2′ and 6. Labelled
  **EMPIRICALLY SUPPORTED** as a characterisation (the two proved theorems give the two
  implications only in their stated forms, which do not quite meet).
* The claim `M*_L < |L|` in *all* records is stronger than anything proved here; the proved
  statement is `M*_L ≤ min(|L|,p)` plus Theorem 5. Labelled **EMPIRICALLY SUPPORTED, OPEN**.

---

## 9. Symbolic comparison with the existing MCA bounds

With `F_coord = 1 + min_{x ∈ supp V_W} m_x` (Theorem 5) and, in the interpolation regime,
`F_comb = 1 + Σ_{i≤2e} C(n−1,i−1)` (Theorem 6):

| bound | form | `p`-dependence |
| --- | --- | --- |
| trivial | `|B| ≤ p` | yes |
| previous projected bound | `|B| ≤ 2|L| − 3` | through `|L|` |
| **new (this report)** | `|B| ≤ 2·F_coord − 3 = 2·min_{x∈supp V_W} m_x − 1` | through `m_x` only |
| **new, interpolation regime** | `|B| ≤ 2·F_comb − 3`, e.g. `≤ 2ⁿ − 1` | **none** |
| capacity-free packing bound | `|B| ≤ κ_max + |L|(|L|−1)` | through `κ_max ≤ p` |
| κ-charging bound | `|B| ≤ 1 + Σ_{q∈L}(κ(q)−1)` | through `κ(q) ≤ p` |

Strict improvement over `2|L| − 3` holds iff `min_{x ∈ supp V_W} m_x < |L| − 1`, and is *guaranteed*
by the averaging whenever `|supp V_W| > 2e·|L|/(|L|−1)`. Concretely, at `RS[6,2]`, `e = 2`,
`p ≥ 17`: `2|L| − 3 = 27` versus `2·11 − 3 = 19`. Against the κ-bounds no numerical comparison is
made here (κ is frozen by the mission); the structural difference is that the new bound is
`p`-free in the interpolation regime whereas `κ(q)` is not bounded independently of `p`.

---

## 10. Labels

| statement | label |
| --- | --- |
| normal form `λ(L) = Λ(f₁) + Λ((C−f₁) ∩ H_{2e})` | PROVED |
| Level 1: `λ(H_{2e}) = F_p` for all `λ ≠ 0`, `e ≥ 1`; no dependence on `|supp λ|` | PROVED |
| universal `p`-independent bound for arbitrary `λ` and arbitrary `C` | REFUTED |
| line criterion (Theorem 2) and admissible fullness (Theorem 2′) | PROVED |
| RS corollary: `w + d ≤ 2e ⇒ M*_L = p` | PROVED |
| coset/fibre description; injectivity when `ker λ ∩ C_{≤4e} = 0`; `M*_L ≥ |L|/h` | PROVED |
| support bound `M*_L ≤ 1 + min_{x ∈ supp V_W} m_x ≤ 1 + ⌊2e|L|/|supp V_W|⌋` | PROVED |
| interpolation regime: injective error supports, antichain, `p`-free `|L|`, `m_x`, `M*_L` | PROVED |
| exact extremal values `C(n,2e)`, `C(n−1,2e−1)` in that regime | EMPIRICALLY SUPPORTED |
| explicit MCA instance with `M*_L = 3 < p = 5` and `|B| = 2M*_L − 3` (sharp) | PROVED |
| "compression happens **iff** `2e ≤ n−k`" | EMPIRICALLY SUPPORTED (both proved implications are one-sided) |
| `M*_L < |L|` always | OPEN (0 counterexamples in 81 443 records) |
| whether the new bound beats the κ-bounds numerically | OPEN (not compared; κ frozen) |
| extension fields `F_{p^m}` | OPEN (obstruction recorded earlier) |

---

## 11. Classification and the single next step

### **CASE A — strong, structural compression.**

`|λ(L)| < p` is possible for admissible `λ` (explicit instance, §7), and in the interpolation
regime `2e ≤ n−k` the projected ball is bounded by a quantity **independent of `p`** (§6), so the
compression is unbounded as `p` grows. The mechanism is: the code constraint makes the error
support `supp(f₁−q)` a *faithful label* of `q`, the labels are `≤2e`-sets, and a coordinate
functional only sees the labels containing its coordinate — a `2e/n` fraction of them.

Two honest limitations, both proved rather than guessed:

1. outside that regime — precisely when a codeword line fits inside the ball, `w + d ≤ 2e` — every
   admissible `λ` is full and the projected route yields nothing beyond `|B| ≤ 2p−3` (§3);
2. inside it, the gain over the already known `|B| ≤ 2|L|−3` is the factor `≈ 2e/|supp V_W|`, not
   an order of magnitude. The bound is sharp (§6, §7), so this factor cannot be improved by a
   better choice of `λ`.

**Next mission (exactly one): CANONICAL DUAL-SEPARATION / PROJECTED-BALL THEOREM, restricted to the
interpolation regime `2e ≤ n−k`.** Concretely: determine the exact extremal function
`Φ(n,k,e) = max |L|` and `Φ_x(n,k,e) = max_x m_x` for MDS codes in that regime (the data say
`C(n,2e)` and `C(n−1,2e−1)`), then state and prove

```
either  W_s is collinear (the one-pencil arm, unchanged),
or      |B| ≤ 2·(1 + Φ_x(n,k,e)) − 3 ,     independent of p ,
```

and only then formalise — the statement is by then self-contained apart from the quoted
Rédei–Szőnyi direction theorem. Do **not** spend further effort on the regime `2e ≥ w + d`:
Theorem 2′ closes it.

---

## 12. Artifacts

* `analysis/projected_ball_first_test.py` — the exact check (Level 1, the `RS[5,1]/F₅` fullness
  example, the exhaustive Level 2/3 sweep over `C^∨`, the interpolation-regime table).
* `analysis/projected_ball_first_test_output.txt` — saved exact transcript.

No Lean source was created or modified; no axiom, `sorry` or `admit` was introduced anywhere.
