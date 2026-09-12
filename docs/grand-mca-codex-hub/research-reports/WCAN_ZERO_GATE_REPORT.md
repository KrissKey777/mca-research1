# W_can = 0 — adversarial closure gate

Status tags used below: **PROVED** (symbolic argument, valid for the stated regime; paper, no
Lean), **EXACT-CHECKED** (verified on the explicitly listed finite instances only),
**CONJECTURE**, **OPEN**. No Lean file was modified in this mission.

---

## 1. EXACT BRANCH

Frozen objects (exactly as in `RequestProject/Root/CodingTheory/MCA.lean` and
`.../SubresultantCore.lean`). `F` a field, `D ⊆ F` finite, `n := |D|`, `k ≥ 1`, `e ≥ 0`,
`f₀, f₁ : D → F`, `g_γ := f₀ + γ f₁`.

* `IsCloseOn k S f` : `∃ p ∈ F[X], deg p < k, f = p on S`.
* `Close(γ)` (`IsCloseToCode k e g_γ`) : `∃ S ⊆ D, |S| ≥ n − e, IsCloseOn k S g_γ`.
* `LineCloseOn k S f₀ f₁` : `∀ γ ∈ F, IsCloseOn k S g_γ`.
* `Bad(γ)` (`IsBad k e f₀ f₁ γ`) : `∃ S ⊆ D, |S| ≥ n − e, IsCloseOn k S g_γ` **and**
  `¬ LineCloseOn k S f₀ f₁`.  `Bad := badSet k e f₀ f₁ ⊆ F` — **counted over `F`**.
* WB kernel, `ν`, minors, `I_can`, `W_can` : as in `SubresultantCore.lean`
  (`IsWBKernel`, `nu`, `subresDet`, `canIdeal`, `W_can`).
* **CA(r)** ("correlated agreement at radius `r`") : `∃ S* ⊆ D, |S*| ≥ n − r` and
  `p₀, p₁ ∈ F[X]` of degree `< k` with `f₀ = p₀` and `f₁ = p₁` on `S*`.

Distinction kept throughout: `Close_F = F` (all rational parameters close) is **weaker** than
`Close_{F̄} = F̄`; only the latter is equivalent to `W_can = 0`
(`SUBRESULTANT_DEPENDENCY_AUDIT.md`, §"Correlated branch"; the converse direction uses
`|F̄| = ∞`). `Bad ⊆ Close` always, but `Close = F` does **not** give `Bad = F`, and it is exactly
this gap that the mission asks to quantify.

Certified starting point taken as given (PAPER in the audit, one direction Lean-anchored):

> under `k + 2e ≤ n`, `k ≥ 1`, `𝒦 ≠ 0`:  `W_can = 0 ⇔ Close_{F̄} = F̄ ⇔ CA(e)`.

Remark (**PROVED**, not previously recorded): in the window `k + 2e ≤ n` the kernel is never
zero. Over `F(Z)` the WB system has `(e+1) + (k+e) = k+2e+1 > n` unknowns and `n` equations, so a
nonzero solution exists; clearing denominators gives `0 ≠ (Λ,Q) ∈ 𝒦`. Hence `𝒦 ≠ 0` is automatic
and the dichotomy `W_can = 0` / `W_can ≠ 0` is exhaustive.

Standing hypotheses of everything below: `k ≥ 1`, `k + 2e ≤ n` (interior **or** wall), CA(e).

---

## 2. CATASTROPHE GATE

**No catastrophic family exists in this branch — this is proved, not merely unfound.** Section 5
gives `#Bad ≤ e` for *every* parameter set satisfying the standing hypotheses, so no family
(interior or wall, `e = Θ(n)` or not) can reach `Ω(|F|)`, super-polynomial, or even
super-linear-in-`e` growth. The catastrophe search of Gate A therefore terminates negatively for a
structural reason, and the four construction routes A4.1–A4.4 all collapse into the normal form of
§3: a common locator is *forced*, so "families where the locator varies essentially with `γ`" do
not exist inside the branch.

What *is* attainable is the exact maximum, by a scalable symbolic family (**PROVED**):

> `F_m` any field with `|F_m| ≥ n_m`; `D_m ⊆ F_m`, `|D_m| = n_m → ∞`; `k_m ≥ 1`;
> `e_m := ⌊(n_m − k_m)/2⌋ = Θ(n_m)`; `E_m ⊆ D_m` with `|E_m| = e_m`; pick distinct
> `γ_x ∈ F_m (x ∈ E_m)`. Set `f₀ := 0` and `f₁ := 0` off `E_m`, and `f₁(x) := 1`,
> `f₀(x) := −γ_x` for `x ∈ E_m`.

Then CA(e) holds with `S* = D_m \ E_m`, `p₀ = p₁ = 0`, hence `W_can = 0`; and by the criterion of
§4, `Bad = {γ_x : x ∈ E_m}`, i.e. `B_m = e_m = Θ(n_m)`. Choosing `n_m − k_m` even gives the
**wall** `k + 2e = n`, odd gives the **interior** `k + 2e = n − 1`; the family and the count are
identical in both cases. Classification in the mission's scale: **SMALL — `Θ(e)`**, and
`#Bad/|F| ≤ e/|F|`, which is the shape the MCA statement wants. Nothing here falsifies MCA.

Interior vs wall: the two regimes are *not* separated in this branch. The only place where the
regime is load-bearing is the unique-decoding inequality `k + 2e ≤ n` itself, which holds with
equality on the wall and is used only through "`n − 2e ≥ k`".

---

## 3. CORRELATED NORMAL FORM

**Lemma 0 (splitting).** `LineCloseOn k S f₀ f₁ ⇔ IsCloseOn k S f₀ ∧ IsCloseOn k S f₁`.
(⇐ is Lean `line_closure`; ⇒ takes `γ = 0` and `γ = 1` and subtracts.) **PROVED**

**Lemma 1 (unique decoder).** If `k + 2e ≤ n` and `p, q` of degree `< k` each agree with the same
word on a set of size `≥ n − e`, then `p = q` (they agree on `≥ n − 2e ≥ k` points). **PROVED**

**Lemma 2 (rigidity of the correlated pair).** Under CA(e) and `k + 2e ≤ n` the pair `(p₀, p₁)` is
unique; put `a := f₀ − p₀`, `b := f₁ − p₁` on `D` and `E := {x ∈ D : (a(x), b(x)) ≠ (0,0)}`. Then
`E ⊆ D \ S*`, so `|E| ≤ e`, and `S*` may be taken `= D \ E`. **PROVED**

So the normal form forced by `W_can = 0` is
`f₀ = p₀ + a`, `f₁ = p₁ + b` with `deg p_i < k` and `supp(a) ∪ supp(b) = E`, `|E| ≤ e`.

**Common locator (answers B1/B2/B3).** Let `Λ_E := ∏_{x∈E}(X − x) ∈ F[X]`, `deg Λ_E = |E| ≤ e`,
and `P := p₀ + Z p₁`. Then for every `x ∈ D`

  `Λ_E(x) · (f₀(x) + Z f₁(x)) = Λ_E(x) · P(x)`,

i.e. `(Λ, Q) := (Λ_E, Λ_E·P)` is a WB kernel element with `deg_X Λ ≤ e`,
`deg_X Q ≤ |E| + k − 1 < k + e`, and **`deg_Z Λ = 0`**. Consequences (**PROVED**):

* `A f₀ = P₀`, `A f₁ = P₁` on `D` with `A := Λ_E` (`deg ≤ e`), `P₀ := Λ_E p₀`, `P₁ := Λ_E p₁`
  (`deg < k + e`): the common-denominator/common-locator representation is *forced*, with exact
  degree bounds — it does not have to be assumed.
* `W_can = 0 ⇒ ν = 0`: the branch is exactly the `Z`-constant-locator branch.
* The `γ`-dependence of the witness is *not* essentially variable: the agreement set of `g_γ` is
  `A_γ = D \ {x ∈ E : a(x) + γ b(x) ≠ 0}` and its locator `∏_{x∈E, a(x)+γb(x)≠0}(X−x)` is a
  **divisor of the single fixed `Λ_E`**. The canonical parameter space controlling the variation is
  the finite set of subsets of `E`, and it is non-constant only at the `≤ e` parameters of §4.

No bounded-rank / Schubert / determinantal machinery was needed; the escalation rule was not
triggered.

---

## 4. BAD CHARACTERISATION

**Theorem (exact criterion).** Assume `k ≥ 1`, `k + 2e ≤ n`, CA(e), with `a, b, E` as in Lemma 2.
Then, for `γ ∈ F`,

  `γ ∈ Bad ⇔ ∃ x ∈ E : a(x) + γ b(x) = 0`,

equivalently `Bad = { −a(x)/b(x) : x ∈ E, b(x) ≠ 0 }`. **PROVED**

*Proof.* (⊇) Given such an `x` (necessarily `b(x) ≠ 0`, else `a(x) = 0` and `x ∉ E`), take
`S := S* ∪ {x}`, `|S| ≥ n − e`. Then `g_γ = p₀ + γp₁` on `S*` and also at `x`, since
`g_γ(x) − (p₀+γp₁)(x) = a(x) + γb(x) = 0`; so `IsCloseOn k S g_γ`. If `f₁` agreed with some
`r₁`, `deg r₁ < k`, on `S`, then `r₁ = p₁` on `S*` (`|S*| ≥ n − e ≥ k`), hence `r₁ = p₁`, whereas
`f₁(x) − p₁(x) = b(x) ≠ 0`. So `¬ LineCloseOn k S f₀ f₁` by Lemma 0, i.e. `γ ∈ Bad`.

(⊆) Let `γ ∈ Bad` with witness `S`, `|S| ≥ n − e`, `g_γ = q` on `S`, `deg q < k`. Since
`p_γ := p₀ + γp₁` agrees with `g_γ` on `S*`, Lemma 1 gives `q = p_γ`. If `f₀ = r₀` on `S` with
`deg r₀ < k`, then `r₀ = p₀` on `S ∩ S*`, a set of size `≥ (n−e) + (n−e) − n = n − 2e ≥ k`, so
`r₀ = p₀`; likewise for `f₁`. Hence by Lemma 0, `¬ LineCloseOn k S f₀ f₁` forces some `x ∈ S ∩ E`.
For that `x`, `a(x) + γb(x) = g_γ(x) − p_γ(x) = q(x) − p_γ(x) = 0`. ∎

Monotonicity remark used implicitly: `¬LineCloseOn` is inherited upwards along `S ⊆ S'`, so the
maximal witness `A_γ` is the optimal adversarial choice; the criterion is therefore an
*equivalence*, not a one-sided implication.

So the additional condition distinguishing `Bad` from merely `Close` is completely explicit:
**`γ` resurrects an error position** — some position of the correlated error support `E` is healed
by the specific combination `a + γb`, and healing a position of `E` breaks correlation because the
`(p₀,p₁)` pair is rigid.

EXACT-CHECKED corroboration (brute force over *all* subsets `S` with `|S| ≥ n−e` and all `γ`,
directly from the Lean definitions): `F = 𝔽₁₁`, `D = {0,…,8}` (`n = 9`), interior `(k,e) = (2,3)`
and wall `(k,e) = (3,3)`, six pseudo-random correlated instances each, plus the designed instance
with ratios `{8,9,10}`: computed `Bad` equals the predicted set in all 13 instances. Outside the
window (`(k,e) = (4,3)`, `k+2e = 10 > n`) the criterion demonstrably fails (extra bad parameters
appear, and `#Bad = 4 > e` occurs), which shows `k + 2e ≤ n` is load-bearing rather than cosmetic.

---

## 5. SCALE

**Upper bound (PROVED).** Under `k ≥ 1`, `k + 2e ≤ n`, `W_can = 0` (hence CA(e)):

  `#Bad = #{ −a(x)/b(x) : x ∈ E, b(x) ≠ 0 } ≤ |E| ≤ e`.

**Lower bound (PROVED).** The family of §2 attains `#Bad = e` for every `n`, on the wall and in
the interior. Hence `max #Bad = e` exactly in this branch (for `|F| ≥ e`), and the branch is
`Θ(e)`, i.e. strictly *better* than the generic bound `(k+1)e + 1` of the `W_can ≠ 0` branch.

**Consequence for the dichotomy (PROVED, paper level).** Combining with the certified
`W_can ≠ 0` branch and with the remark of §1 that `𝒦 ≠ 0` is automatic: for `k ≥ 1` and
`k + 2e ≤ n`, *unconditionally* (no `W_can ≠ 0` hypothesis)

  `#Bad ≤ max{ e, (k+1)e + 1 } = (k+1)e + 1`,   so   `ε_mca ≤ ((k+1)e+1)/|F|`.

This removes hypothesis `hW : W_can ≠ 0` from the Lean statement
`Root.CodingTheory.Subresultant.badSet_card_le_poly` at paper level; the Lean statement itself was
not touched, as mandated.

**Robustness (PROVED).** If one only wants to assume the weaker CA(2e) (the radius produced by the
two-point correlated-agreement lemma `correlated_agreement_of_two`, `|S*| ≥ n − 2e`), the same
argument works under the stricter slack `k + 3e ≤ n` and yields `#Bad ≤ 2e`. The step that needs
the slack is `q = p_γ` (`|A_γ ∩ S*| ≥ n − 3e ≥ k`).

**Residual (OPEN, outside the mission's window).** For `k + 2e > n` (beyond unique decoding) the
criterion is false and `#Bad > e` occurs already at `n = 9`; nothing here is claimed there.

---

## 6. DECISION

**B — POLYNOMIAL CLOSURE.**

The exceptional branch is closed: `W_can = 0` (equivalently `Close_{F̄} = F̄`, equivalently CA(e))
implies `#Bad ≤ e` under `k ≥ 1`, `k + 2e ≤ n`, with an *exact* characterisation of `Bad` (§4) and
a matching `Θ(n)`-scale family showing `e` is attained. The bound is linear, not merely
polynomial, and it is better than the bound in the generic branch; therefore the target MCA
inequality is *not* threatened by the correlated branch, and no repair of MCA is needed.

Caveats, stated plainly: the input `W_can = 0 ⇒ CA(e)` is PAPER-level in this repository (audited,
one direction Lean-anchored, not machine-checked); the new results of §§3–5 are PAPER-level too
(no Lean changes were permitted in this mission) and are additionally EXACT-CHECKED on the 13
instances listed in §4. The natural next Lean target, if the branch is ever to be machine-checked,
is the pair "Lemma 0 + Lemma 1 + the exact criterion of §4", none of which needs subresultants at
all — only the unique-decoding inequality and rigidity of the correlated pair.
