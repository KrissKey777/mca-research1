# MDS SUPPORT–ANTICHAIN AUDIT

**Mission.** Settle one lemma before anything larger: for an `[n,k]` MDS code `C` and
`L = L(f₁,2e) = { q ∈ C : wt(f₁ − q) ≤ 2e }`, is `q ↦ E(q) = supp(f₁ − q)` injective, and is
`{E(q)}` an antichain? Plus the exact threshold, the coordinate bound `m_x ≤ C(n−1,2e−1)`, and the
MDS/RS separation.

**Constraints respected.** No Lean file created or modified; no axiom; no `sorry`/`admit`; no
Johnson argument, no κ-charging, no broad scan, no new mechanism. One tiny exact-arithmetic check
(`analysis/mds_support_antichain_check.py`, integers mod `p` only, runtime ≈ 20 s) guards the worked
examples; every statement labelled **PROVED** below carries a complete human-checkable proof and
does not depend on that computation.

---

## 0. Verdict

| # | statement | label |
| --- | --- | --- |
| 1 | The three candidate thresholds `2e ≤ n−k`, `2e < d`, `2e < n−k+1` are **the same inequality** for MDS codes and integers `e`. The intrinsic hypothesis is `2e < d`; MDS enters only through `d = n−k+1`. | **PROVED** (§1) |
| 2 | `q ↦ E(q)` is injective on `L`. Stronger and cleaner: *for every `S ⊆ ι` with `|S| ≤ d−1` there is at most one `q ∈ C` with `supp(f₁−q) ⊆ S`.* Uses only linearity and `2e < d` — **not** MDS. | **PROVED** (§2) |
| 3 | `{E(q) : q ∈ L}` is an antichain. It is *not* a consequence of injectivity; it is the same one-line argument at strength `⊆` instead of `=`, and it is subsumed by the strictly stronger **union law** `|E(q) ∪ E(q')| ≥ d` for `q ≠ q'`. | **PROVED** (§3) |
| 4 | The union law is equivalent to: the *agreement* sets `A(q) = ι ∖ E(q)` have `|A(q)| ≥ n−2e` and pairwise `|A(q) ∩ A(q')| ≤ n−d` ( `= k−1` for MDS). So the list is a **packing**, strictly more than an antichain. | **PROVED** (§3.2) |
| 5 | `m_x ≤ C(n−1, 2e−1)` for every MDS code in the regime (`e ≥ 1`). Proof by two complementary branches (LYM on the antichain; injection into `k`-subsets of an information set). | **PROVED** (§4) |
| 6 | The same two-branch argument upgrades the previous list bound `Σ_{i≤2e} C(n,i)` to the single binomial `|L| ≤ C(n,2e)`, and `2^{n−1} → C(n−1,2e−1)`. | **PROVED** (§4.3) |
| 7 | **Equality.** Both bounds are attained **iff `2e = n−k` and `f₁` is a deep hole** (`d(f₁,C) = n−k`); then, exactly, `|L| = C(n,k) = C(n,2e)` and `m_x = C(n−1,k) = C(n−1,2e−1)` for *every* `x`. In the interior `2e < n−k` both bounds are **strict** (never attained). | **PROVED** (§5) |
| 8 | Attainability is realised: `RS[4,2]/F₅`, `RS[5,3]/F₅` (full length `n=p`), `RS[6,2]/F₁₁`, `RS[7,3]/F₁₁` with `f₁ = (α^k)_{α}` all meet equality. This confirms the previously *empirically supported* values `C(n,2e)`, `C(n−1,2e−1)` and now **explains** them. | **PROVED** (explicit, §5.3) |
| 9 | "The antichain claim is false" | **REFUTED** — the claim is true, and true for a strictly weaker hypothesis than the one used. |
| 10 | Sharpness of the threshold: at `2e ≥ d` injectivity and the antichain both fail; minimal counterexamples `[2,1]/F₃` (both fail) and `[2,1]/F₂` (antichain fails, injectivity survives). | **PROVED** (§1.2) |

**Bottom line.** The lemma the previous report used is correct, but it was stated with an
unnecessarily *specialised* hypothesis (MDS) and an unnecessarily *weak* conclusion (antichain
⇒ `Σ_{i≤2e} C(n,i)`, `2^{n−1}`). The correct hypothesis is `2e < d`; the correct conclusion is the
union law, which yields the exact extremal values `C(n,2e)` and `C(n−1,2e−1)`, both attained
exactly at the boundary `2e = n−k` on deep holes. The previously measured saturation
(`|L| = 15`, `max_x m_x = 10` at `RS[6,2]`, `e = 2`) is now a **theorem with an equality
characterisation**, not a measurement.

---

## 1. STEP 1 — the exact threshold

Notation as in `PROJECTED_BALL_FIRST_TEST.md` §1: `ι = {1,…,n}`, `C ⊆ F^n` linear of dimension `k`
and minimum distance `d`, `f₁ ∈ F^n` **arbitrary** (not assumed to be a codeword),
`L = L(f₁,2e) = { q ∈ C : wt(f₁ − q) ≤ 2e }`, `E(q) = supp(f₁ − q)`, `A(q) = ι ∖ E(q)`,
`m_x = #{ q ∈ L : q_x ≠ f₁(x) } = #{ q ∈ L : x ∈ E(q) }`, `w = d(f₁,C)`.

### 1.1 The three candidates coincide — PROVED

For an MDS code `d = n−k+1`, and `2e, n−k` are integers, so

```
2e ≤ n−k      ⟺      2e < n−k+1      ⟺      2e < d .
```

There is nothing to choose between them; the previous report's `2e ≤ n−k` and the mission's
`2e < d` are literally the same condition. What *is* a real choice is which of `d` and `n−k+1` is
the primitive: **the proofs of §2–§3 use only `2e < d`**, i.e. they hold verbatim for an arbitrary
linear code. For a non-MDS code `d ≤ n−k`, so the hypothesis `2e ≤ n−k` is *strictly weaker* than
`2e < d` and the lemma genuinely fails under it (§1.3). Hence:

> **Sharpest formulation.** Let `C ⊆ F^n` be any linear code with minimum distance `d`, let
> `f₁ ∈ F^n`, `e ∈ ℕ`, and assume `2e ≤ d − 1`. Then §2 and §3 hold. For MDS codes this hypothesis
> reads `2e ≤ n − k`.

### 1.2 Sharpness at `2e = d` — PROVED

*Minimal counterexample (both properties fail).* `C = [2,1]` repetition over `F₃`
(`n = 2, k = 1, d = 2 = n−k+1`, MDS), `e = 1`, so `2e = 2 = d`, `f₁ = (0,0)`. Then
`L = { (0,0), (1,1), (2,2) }` with supports `∅, {1,2}, {1,2}`: injectivity fails
(`E((1,1)) = E((2,2))`) and the antichain fails (`∅ ⊊ {1,2}`).

*Minimal counterexample over `F₂` (only the antichain fails).* `C = [2,1]/F₂`, `e = 1`, `f₁ = 0`:
`L = {00, 11}`, supports `∅, {1,2}` — injective, but `∅ ⊊ {1,2}`. So over `F₂` injectivity can
survive at `2e = d` while the antichain does not; the two properties are logically independent at
the boundary. (Both are recovered as soon as `2e < d`.)

*Odd `d`.* `2e` is even, so `2e = d` is impossible for odd `d`; the first violating value is then
`2e = d+1`. Example `RS[4,2]/F₅` (`d = 3`), `e = 2`, `f₁ = 0`: the 24 nonzero codewords of weight
`≤ 4` realise only 5 distinct supports — injectivity fails 24 ↦ 5 (checked exactly).

*General mechanism.* If `2e ≥ d` and `f₁ ∈ C`, pick any `v ∈ C` of weight `d`. Then `f₁, f₁+v ∈ L`
and `E(f₁) = ∅ ⊊ E(f₁+v)`: the antichain fails for **every** code with `2e ≥ d`. If moreover
`|F| ≥ 3`, `f₁+v` and `f₁+2v` have the same support, so injectivity fails too. The threshold
`2e < d` is therefore exactly sharp, not merely sufficient.

### 1.3 The hypothesis must be `d`, not `n−k` — PROVED

Take the binary `[4,2]` code `C = span{1100, 0011}`, `d = 2`, `n−k = 2`, `e = 1`, `f₁ = 0`. Then
`2e = 2 ≤ n−k` holds but `2e ≥ d`, and `L = {0000, 1100, 0011}` has supports `∅, {1,2}, {3,4}`:
the antichain fails. So writing the hypothesis as `2e ≤ n−k` is only legitimate **because** the
code is MDS; stated for general codes it is false. The previous report's use of it is correct but
the MDS assumption there is doing exactly this bookkeeping job and nothing else.

---

## 2. STEP 2 — injectivity

> ### Lemma A (unique representative per small support). **PROVED**
> Let `C` be a linear code of minimum distance `d` and let `S ⊆ ι` with `|S| ≤ d − 1`. Then there is
> at most one `q ∈ C` with `supp(f₁ − q) ⊆ S`.

*Proof.* If `q, q' ∈ C` both satisfy this, then `q − q' ∈ C` and
`supp(q − q') ⊆ supp(f₁−q) ∪ supp(f₁−q') ⊆ S`, so `wt(q−q') ≤ |S| ≤ d−1 < d`. A nonzero codeword
has weight `≥ d`; hence `q = q'`. ∎

> ### Corollary A1 (injectivity). **PROVED**
> If `2e ≤ d − 1` then `q ↦ E(q)` is injective on `L(f₁,2e)`.

*Proof.* `E(q) = E(q') =: S` has `|S| ≤ 2e ≤ d−1`; apply Lemma A. ∎

**Remarks that matter for the sequel.**

* Lemma A is strictly stronger than injectivity: it says the *support determines the error vector*,
  i.e. **each support carries multiplicity exactly one**. This settles, at the level of this lemma,
  the "support set vs error vector vs codeword vs list element" separation the parent plan asked
  for: in the regime `2e < d` the four notions are in bijection, `|L| = #{ E(q) : q ∈ L }`.
* No MDS property is used. For MDS one may phrase it as "`n − 2e ≥ k` agreements determine the
  codeword", which is the previous report's proof; that phrasing is a specialisation, not a
  strengthening.
* `f₁` is arbitrary. If `f₁ ∈ C` the regime forces `L = {f₁}` (the ball of radius `d−1` about a
  codeword meets `C` only in that codeword), so the interesting instances are exactly those with
  `0 < w = d(f₁,C) ≤ 2e`.

---

## 3. STEP 3 — antichain, and the stronger union law

> ### Lemma B (union law). **PROVED**
> Assume `2e ≤ d − 1`. For distinct `q, q' ∈ L(f₁,2e)`,
> ```
> |E(q) ∪ E(q')| ≥ d ,          equivalently     |E(q) ∩ E(q')| ≤ |E(q)| + |E(q')| − d ≤ 4e − d .
> ```

*Proof.* `q − q' ∈ C ∖ {0}` and `supp(q−q') ⊆ E(q) ∪ E(q')`, so `d ≤ wt(q−q') ≤ |E(q) ∪ E(q')|`. ∎

> ### Corollary B1 (antichain). **PROVED**
> Under `2e ≤ d−1` no `E(q)` is contained in another (proper containment *or* equality).

*Proof.* If `E(q) ⊆ E(q')` with `q ≠ q'`, then `|E(q) ∪ E(q')| = |E(q')| ≤ 2e ≤ d−1`, contradicting
Lemma B. ∎

**Does the antichain follow from injectivity?** *No.* Injectivity only excludes `E(q) = E(q')`.
The `[2,1]/F₂` example of §1.2 has injective supports and a violated antichain, so the antichain is
logically independent and needs its own argument — but that argument is the *same* one-line
computation (Lemma A with `S = E(q')`, resp. Lemma B), so the previous report's proof is sound.
The honest statement is: both are instances of Lemma A, applied to `S = E(q)` resp. `S = E(q')`.

### 3.1 Immediate structural consequences

* At most one `q ∈ L` has `|E(q)| < d/2`; if `w = d(f₁,C)` then all supports except possibly the
  unique minimal one have size `≥ d − w`. So the support sizes live in `{w} ∪ [d−w, 2e]`, a narrow
  band, not in `[0,2e]`.
* If `4e < d` then `|E(q) ∪ E(q')| ≤ 4e < d` for any two, so `|L| ≤ 1`: the unique-decoding regime
  is recovered as a degenerate case of Lemma B. The lemma has content only for
  `d ≤ 4e ≤ 2(d−1)`, i.e. `d/2 ≤ 2e ≤ d−1`.

### 3.2 Complement (agreement) form — the packing picture

Put `A(q) = ι ∖ E(q)` (the agreement locus of `q` with `f₁`). Lemma B and `|E(q)| ≤ 2e` say exactly

```
|A(q)| ≥ n − 2e            and            |A(q) ∩ A(q')| ≤ n − d      (q ≠ q') .
```

For MDS, `n − d = k − 1` and `n − 2e ≥ k`. So `{A(q)}` is a family of `≥ k`-sets meeting pairwise
in `≤ k−1` points: **a packing whose blocks pairwise fail to contain a common information set**.
This is the exact combinatorial content of the interpolation regime, and it is strictly stronger
than "antichain". Everything in §4–§5 is read off from it.

---

## 4. STEP 4 — the coordinate bound `m_x ≤ C(n−1, 2e−1)`

Throughout: `C` is `[n,k]` MDS, `t := 2e`, `1 ≤ e`, and `t ≤ n−k` (so `k ≤ n−t`).

> ### Theorem C. **PROVED**
> For every coordinate `x`,  `m_x ≤ C(n−1, t−1) = C(n−1, 2e−1)`.

Two branches, jointly exhaustive.

### 4.1 Branch L (LYM) — uses only `2e < d`, valid when `t−1 ≤ (n−1)/2`

Let `G = { E(q) ∖ {x} : q ∈ L, x ∈ E(q) }`, a family of subsets of the `(n−1)`-set `ι ∖ {x}` with
`|G| = m_x` (distinct by Corollary A1). `G` is an antichain: `E(q)∖{x} ⊆ E(q')∖{x}` with `x` in both
gives `E(q) ⊆ E(q')`, excluded by Corollary B1. All members have size `≤ t−1`. LYM gives
`Σ_{g ∈ G} 1 / C(n−1,|g|) ≤ 1`; since `|g| ≤ t−1 ≤ (n−1)/2`, `C(n−1,|g|) ≤ C(n−1,t−1)`, hence
`m_x / C(n−1,t−1) ≤ 1`. ∎

### 4.2 Branch I (information sets) — uses MDS, valid when `k ≤ t−1`

For `q` with `x ∈ E(q)`, `A(q) ⊆ ι∖{x}` and `|A(q)| ≥ n−t ≥ k`; let `φ(q)` be the lexicographically
least `k`-subset of `A(q)`. If `φ(q) = φ(q') = S` for `q ≠ q'`, then `q` and `q'` both agree with
`f₁` on `S`, hence with each other on a set of `k` coordinates, which for an MDS code is an
information set — so `q = q'`. Thus `φ` is injective and `m_x ≤ C(n−1,k)`. Since `k ≤ t−1` and
`t−1 ≤ n−1−k` (from `t ≤ n−k`), the position `t−1` lies between `k` and `n−1−k`, so
`C(n−1,k) ≤ C(n−1,t−1)`. ∎

### 4.3 The branches cover the whole regime, and the same argument bounds `|L|`

If `t−1 > (n−1)/2` then `n < 2t−1+2`, i.e. `n−t < t−1`, and `k ≤ n−t` gives `k ≤ t−2 < t−1`:
Branch I applies. Otherwise Branch L applies. Hence Theorem C holds throughout `2e ≤ n−k`. ∎

Verbatim the same two branches on the whole list (LYM on the antichain `{E(q)}` in `2^ι` when
`t ≤ n/2`; `φ : L → { k\text{-subsets of } ι }` otherwise) give

> ### Theorem D. **PROVED**
> `|L(f₁,2e)| ≤ C(n, 2e)`, and also `|L| ≤ C(n,k) / C(n−2e,k)` (each `k`-subset of `ι` lies in at
> most one `A(q)`, and every `A(q)` contains `C(n−2e,k)` of them).

This replaces the previous report's `Σ_{i≤2e} C(n,i) ≤ 2ⁿ` and `Σ_{i≤2e} C(n−1,i−1) ≤ 2^{n−1}` by
the single binomials — an exponential improvement (e.g. `n=6, 2e=4`: `15` and `10` instead of `57`
and `32`). The packing form `C(n,k)/C(n−2e,k)` is the better of the two strictly inside the regime
(e.g. `RS[5,2]`, `e=1`: `C(5,2)/C(3,2) = 3` versus `C(5,2) = 10`; the true maximum is `2`).

### 4.4 What the bound is *not*

`m_x ≤ C(n−1,2e−1)` is **not** the statement "number of supports containing `x`" — that count is
`Σ_{j<2e} C(n−1,j)`, which is larger. The gap is closed by the antichain/packing structure, i.e.
Theorem C is genuinely a coding-theoretic statement, not the trivial ambient count. Multiplicities
do not occur (Lemma A), so no correction term is needed.

---

## 5. STEP 4 (continued) — exact equality analysis

### 5.1 Equality forces the boundary `2e = n−k` — PROVED

Assume `e ≥ 1`, `t = 2e ≤ n−k−1` (strict interior) and suppose `m_x = C(n−1,t−1)`.

*Case `t−1 < (n−1)/2` (Branch L active).* Binomials are strictly increasing below the middle, so
`C(n−1,j) < C(n−1,t−1)` for `j < t−1`; LYM equality therefore forces every member of `G` to have
size exactly `t−1` and `G` to be the **complete** level. That level contains two sets `g, g'` with
`|g ∪ g'| = t` (possible since `1 ≤ t−1` and `n−1 ≥ t`, which holds as `t ≤ n−2`). The corresponding
supports satisfy `|E ∪ E'| = t+1 ≤ (n−k+1) − 1 = d−1`, contradicting Lemma B.

*Case `t−1 ≥ (n−1)/2` (Branch I active).* Then `k ≤ n−t−1 ≤ t−2 < t−1 ≤ n−1−k`, so
`m_x ≤ C(n−1,k) < C(n−1,t−1)` strictly. ∎

The identical argument (with `ι` in place of `ι∖{x}`) shows `|L| < C(n,2e)` strictly in the interior.
So **both bounds can only be tight at `2e = n−k` exactly**.

### 5.2 At the boundary: an exact formula — PROVED

Let `2e = n−k` (so `d−1 = 2e`, agreement threshold `n−2e = k`).

* For every `k`-subset `S ⊆ ι` there is a unique `q_S ∈ C` agreeing with `f₁` on `S` (MDS: `S` is an
  information set). Then `wt(f₁−q_S) ≤ n−k = 2e`, so `q_S ∈ L`. Conversely every `q ∈ L` has
  `|A(q)| ≥ k`, so `q = q_S` for some `S`. Hence `S ↦ q_S` is **onto** `L`, and
  `|L| ≤ C(n,k)`.
* `S ↦ q_S` is injective ⟺ no codeword agrees with `f₁` in `≥ k+1` places ⟺ `d(f₁,C) ≥ n−k`.
  Since `d(f₁,C) ≤ n−k` always (interpolate on any `k` coordinates), injectivity ⟺
  `d(f₁,C) = n−k`, i.e. `f₁` is a **deep hole** (a word at the maximal possible distance).

> ### Theorem E (exact boundary values). **PROVED**
> Let `C` be `[n,k]` MDS, `2e = n−k`, `f₁ ∈ F^n`. Then `|L| = #{ q_S : S ∈ \binom{ι}{k} } ≤ C(n,k)`,
> with equality **iff** `d(f₁,C) = n−k`. In the equality case every `q ∈ L` has `|E(q)| = 2e`
> exactly, the support family is the **complete level** `\binom{ι}{2e}`, and for every coordinate `x`
> ```
> |L| = C(n,k) = C(n,2e) ,        m_x = C(n−1,k) = C(n−1,2e−1) .
> ```
> Both Theorem C and Theorem D are therefore **EXACT and SHARP** at `2e = n−k`, and strict inside.

*Proof of the equality case.* Injectivity of `S ↦ q_S` means each `q_S` agrees with `f₁` on exactly
`S`, so `E(q_S) = ι ∖ S` has size `n−k = 2e` and the map `S ↦ E(q_S)` is a bijection onto the
`(n−k)`-subsets. Then `m_x = #{ S : x ∉ S } = C(n−1,k)`, uniform in `x`, and
`C(n−1,k) = C(n−1,n−1−k) = C(n−1,2e−1)`. ∎

Note this also pins the previously open direction: `max_x m_x` and `min_x m_x` coincide in the
extremal configuration, so no averaging loss occurs there.

### 5.3 Attainability (verified exactly)

`f₁ = (α^k)_{α ∈ D}` (evaluation of `X^k`, one degree above the code) is a deep hole in all four
instances checked, so equality is attained:

| code | `e` | `2e` vs `n−k` | `|L|` | `C(n,2e)` | `max_x m_x` | `C(n−1,2e−1)` |
| --- | --- | --- | --- | --- | --- | --- |
| `RS[4,2]/F₅` | 1 | `2 = 2` | 6 | 6 | 3 | 3 |
| `RS[5,3]/F₅` (full length `n=p`) | 1 | `2 = 2` | 10 | 10 | 4 | 4 |
| `RS[6,2]/F₁₁` | 2 | `4 = 4` | 15 | 15 | 10 | 10 |
| `RS[7,3]/F₁₁` | 2 | `4 = 4` | 35 | 35 | 20 | 20 |

The first two rows are maxima over **all** `p^n` received words (exhaustive); the last two use the
explicit deep hole. Interior instances are strictly below, as Theorem E predicts:
`RS[5,2]/F₅`, `e=1` (`2e = 2 < 3 = n−k`) has `max |L| = 2` against `C(5,2) = 10` and
`max_x m_x = 1` against `C(4,1) = 4`; `RS[7,2]/F₁₃`, `e=2` (measured in the previous report)
has `4` and `3` against `35` and `20`.

This reproduces and now **explains** the previously *empirically supported* saturation at
`|L| = 15`, `max_x m_x = 10` for `RS[6,2]`: it is Theorem E at a deep hole, and the values are
`p`-free because the right-hand sides contain no `p`.

**Existence of the equality case is a deep-hole question, not a field-size question.** For fixed
`[n,k]` MDS parameters, equality is attainable iff the covering radius equals `n−k`; that holds in
every instance above (and classically for full-length Reed–Solomon codes, where `X^k` is a deep
hole). We do **not** claim it for all MDS parameter sets — that is the only place where an
existence statement, and hence potentially the field, enters.

---

## 6. STEP 5 — MDS versus Reed–Solomon separation

| result | hypothesis actually used |
| --- | --- |
| Lemma A (unique word per support of size `< d`) | **arbitrary linear code**, `2e ≤ d−1` |
| Corollary A1 (injectivity) | **arbitrary linear code**, `2e ≤ d−1` |
| Lemma B (union law `|E ∪ E'| ≥ d`) | **arbitrary linear code**, `2e ≤ d−1` |
| Corollary B1 (antichain) | **arbitrary linear code**, `2e ≤ d−1` |
| Branch L of Theorem C, and `|L| ≤ C(n,2e)` when `2e ≤ n/2` | **arbitrary linear code**, `2e ≤ d−1` (only the antichain is used) |
| Branch I of Theorem C, `|L| ≤ C(n,k)/C(n−2e,k)` | **MDS** (every `k`-set is an information set); nothing about polynomials |
| translation of the threshold to `2e ≤ n−k` | **MDS** (Singleton equality) — false for non-MDS codes, §1.3 |
| Theorem E (exact boundary values, deep-hole characterisation) | **MDS** only; the interpolation is "unique codeword through `k` prescribed coordinates", available for every MDS code |
| the concrete equality witnesses of §5.3 | **RS** — used solely to exhibit deep holes, not in any proof |

**No statement above uses Reed–Solomon polynomial structure.** RS appears only as a supply of
explicit codes and explicit deep holes. Extended/doubly-extended RS behaves identically (the
arguments see only `[n,k]` MDS), so no separate case C is needed; the only RS-specific input that
could differ is which words are deep holes.

---

## 7. Immediate consequence for the projected functional (recorded, not developed)

Only as a substitution into the already-established Theorem 5 of `PROJECTED_BALL_FIRST_TEST.md`
(`M*_L(W_s) ≤ 1 + min_{x ∈ supp V_W} m_x`), and quoting Rédei–Szőnyi exactly as before: in the
regime `2e ≤ n−k`,

```
M*_L(W_s) ≤ 1 + C(n−1, 2e−1) ,        |B| ≤ 2·C(n−1,2e−1) − 1 ,
```

both `p`-free, replacing the previous `1 + 2^{n−1}` and `2^n − 1`. At `RS[6,2]`, `e=2`:
`M*_L ≤ 11` and `|B| ≤ 19`, against the previous `33` and `63`. The `RS[4,2]/F₅` sharpness instance
(`|B| = 3`, `M*_L = 3`, `|B| = 2M*_L − 3`) is consistent: `1 + C(3,1) = 4 ≥ 3` and `2·3 − 1 = 5 ≥ 3`.
Per mission instructions the two-arm theorem is **not** developed here.

---

## 8. Labels

| statement | label |
| --- | --- |
| exact threshold `2e ≤ d−1`, and `2e ≤ n−k ⟺ 2e < d` for MDS | **PROVED** |
| threshold is sharp (fails at `2e = d`, minimal witnesses `[2,1]/F₃`, `[2,1]/F₂`) | **PROVED** |
| hypothesis must be `d`, not `n−k`, for non-MDS codes | **PROVED** (counterexample §1.3) |
| injectivity of `q ↦ E(q)`, and the stronger Lemma A (multiplicity one per support) | **PROVED** |
| antichain, and the stronger union law `|E ∪ E'| ≥ d`; independence from injectivity | **PROVED** |
| packing form `|A(q) ∩ A(q')| ≤ k−1`, `|A(q)| ≥ n−2e` | **PROVED** |
| `m_x ≤ C(n−1,2e−1)` for MDS in the regime | **PROVED** |
| `|L| ≤ C(n,2e)` and `|L| ≤ C(n,k)/C(n−2e,k)` | **PROVED** |
| equality in either bound ⟹ `2e = n−k`; strictness in the interior | **PROVED** |
| at `2e = n−k`: `|L| = C(n,k)` ⟺ `f₁` is a deep hole, and then `m_x = C(n−1,k)` for all `x` | **PROVED** |
| equality attained (`RS[4,2]/F₅`, `RS[5,3]/F₅`, `RS[6,2]/F₁₁`, `RS[7,3]/F₁₁`) | **PROVED** (exact computation of explicit instances) |
| existence of deep holes for *all* MDS parameter sets | **OPEN** (not claimed; not needed) |
| "the antichain claim is false" | **REFUTED** |
| exact value of `max |L|` strictly inside the regime (`2e < n−k`) | **OPEN** — reduces to the packing problem of §3.2 |

---

## 9. Exactly ONE next mission

> **Formalise the settled lemma chain in Lean, at the level of generality the proofs actually have.**
>
> Statements to formalise, in this order, in a new file `RequestProject/Root/CodingTheory/SupportGeometry.lean`:
> 1. `Lemma A`: for a linear code `C` of minimum distance `d`, `f₁ : ι → F` and `S : Finset ι` with
>    `S.card < d`, at most one `q ∈ C` has `supp (f₁ − q) ⊆ S`.
> 2. `Corollary A1` (injectivity) and `Corollary B1` (antichain) as consequences, both under
>    `2 * e < d` for an arbitrary linear code — **not** under an MDS hypothesis.
> 3. `Lemma B` (union law `d ≤ |E q ∪ E q'|`).
> 4. `Theorem E` in its MDS form at the boundary `2e = n−k`: the map `S ↦ q_S` from `k`-subsets onto
>    `L`, its injectivity ⟺ `d(f₁,C) = n−k`, and the resulting `|L| = C(n,k)`, `m_x = C(n−1,k)`.
>
> The counting bounds of Theorem C/D (LYM branch) should be attempted only after 1–4 are closed;
> they need `Finset.card`-level LYM, which may not be available off the shelf. Nothing here needs a
> new axiom, and the whole chain is elementary — it is the first part of this project's list geometry
> that is both new and cheap to verify formally.
