# Grand MCA — the syndrome-line mechanism: gate results and its exact scaling law

**Verdict: [STRUCTURAL REDUCTION] — the syndrome-line / block-incidence mechanism is pinned
exactly, and it is proved to be `exp(Θ(1/η))` in the relative capacity gap `η`.  It is
therefore *not* a route to a Grand-MCA counterexample at constant relative gap, but the
construction side of it is strengthened here: the exponent is doubled, from `n/c` to
`≈ 2n/(c+1)`.**

Notation: `n = |D|`, `k` the dimension, `e` the radius, `C = RS_k(D)`, `κ = n − k`,
absolute capacity gap `c = n − k − e`, relative gap `η = c/n = 1 − ρ − δ`,
`#Bad = (badSet k e f₀ f₁).card` for the official predicate `Root.CodingTheory.IsBad`.

---

## 0. What was asked and what was done

The mission was to decide Grand MCA as strongly as possible, starting from the half-rate
"syndrome line" phenomenon, using the unparameterised plane `[W] ∈ Gr(2, Q)` and its
incidences with error-support subspaces `U_E`, with a first cheap gate at `RS[12,6]` over
`F_13`.  Four things were produced:

1. an **exact** syndrome-space reformulation of the official predicate, *validated against
   the literal predicate* by exhaustive computation (`analysis/gr2_validate.py`);
2. the gate experiments — which turn out to be **uninformative for the stated field sizes**,
   for a reason that is itself decisive (§2);
3. new machine-checked theory: the plane form of the predicate, the master counting
   principle, the `PGL₂` invariance of `#Bad`, and the **cap** on the block/grading
   mechanism (`RequestProject/Root/CodingTheory/SyndromeLineIncidence.lean`);
4. a strictly stronger counterexample family than the one previously in the repository
   (`RequestProject/Root/CodingTheory/HalfGapPencil.lean`).

Everything Lean-side is `sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. The exact dictionary (validated, then formalised)

With `H` the parity-check of `RS_k(D)` and `U_E = { H v : supp v ⊆ E }`:

* `f` agrees on `D ∖ E` with a polynomial of degree `< k`  ⟺  `H f ∈ U_E`;
* for `|E| = e ≤ κ`, `dim U_E = e` and its annihilator inside `F^κ` (polynomials of degree
  `≤ κ−1` under `⟨p,s⟩ = Σ p_i s_i`) is `{ X^r·Λ_E : r < c }`, `Λ_E = ∏_{x∈E}(X − x)`;
* therefore, with `s₀ = H f₀`, `s₁ = H f₁` and `W = span(s₀,s₁)`:

  > `γ` is **bad**  ⟺  there is `E`, `|E| ≤ e`, with `⟨X^r Λ_E, s₀ + γ s₁⟩ = 0` for all
  > `r < c`, and `W ⊄ U_E`.

`analysis/gr2_syndrome_incidence.py` implements this and `analysis/gr2_validate.py` checks
it against a direct Lagrange-interpolation implementation of `IsBad` on
`(q,n,k,e) = (7,6,2,3), (7,6,3,2), (11,10,6,3), (13,12,8,3), (13,12,6,4)` — **exact agreement
on every instance**.

The Lean counterpart avoids syndromes altogether and is sharper as a statement:

* `lineCloseOn_iff` : `LineCloseOn k S f₀ f₁ ↔ IsCloseOn k S f₀ ∧ IsCloseOn k S f₁`
  (the plane condition `W ⊆ U_{D∖S}`);
* `isBad_iff_exists_window` : `γ` bad iff some window of size `≥ n − e` carries the
  `γ`-point but not the plane.

### 1a. The canonical object really is `[W] ∈ Gr(2, ·)`

`isBad_reparam` : for `ad − bc ≠ 0` and `a + γc ≠ 0`,

  `IsBad k e (a f₀ + b f₁) (c f₀ + d f₁) γ  ↔  IsBad k e f₀ f₁ ((b + γd)/(a + γc))`,

and `card_badSet_reparam_le` : `#Bad` changes by at most `1` under any change of basis of the
plane (the challenge sent to infinity).  So `#Bad` is a `PGL₂`-invariant of the
unparameterised plane up to `±1`; the parametrised pair `(f₀,f₁)` carries no extra
information.  This is the formal justification for quotienting by `PGL₂`.

---

## 2. The gates: `RS[10,5]/F_11` and `RS[12,6]/F_13` — and why they cannot decide anything

Exact computation over the *stated* fields (`analysis/gr2_gate.py`, exhaustive over all
error supports of size `e`):

| instance | `c` | best `#Bad` over random syndrome lines | `|F|` |
|---|---|---|---|
| `RS[10,5]/F_11`, `e = 4` | 1 | **11** | 11 |
| `RS[10,5]/F_11`, `e = 3` | 2 | **11** | 11 |
| `RS[12,6]/F_13`, `e = 4` | 2 | **13** | 13 |
| `RS[12,6]/F_13`, `e = 4`, graded line | 2 | **13** (39 FULL incident supports) | 13 |

A *uniformly random* line already attains `#Bad = |F|`, i.e. **every** challenge is bad.  So
the reported "one common pair produces 10 distinct bad challenges" at `RS[10,5]/F_11` is not
evidence of a mechanism: at `|F| ≈ n` the bad set is generically all of `F`, and
`ε_mca = #Bad/|F| ≈ 1` for trivial reasons.  The gate as posed is therefore **not decisive**;
any test of a Grand-MCA mechanism must be run with `|F| ≫ #Bad`.

Re-run at `|F| ≈ 10^6` with the same code parameters, the picture is completely different and
sharp — see §3.

---

## 3. What the mechanism really is, exactly

Run at large `|F|`, the only lines with many bad challenges found are the **graded** ones:
`s₀, s₁` supported off a residue class mod `d`, so that the error supports `E` that are
unions of `μ_d`-cosets kill `c − 1` of the `c` syndrome conditions *simultaneously*, leaving a
single linear condition that determines one challenge per support.  Exact counts
(`analysis/gr2_graded_family.py`, `analysis/gr2_halfgap_grading.py`; `#Bad` computed over
**all** `C(n,e)` supports, not only the graded ones):

| `n` | `k` | `e` | `c` | `d` | `#Bad` (exact) | `C(n/d, e/d)` |
|---|---|---|---|---|---|---|
| 12 | 6 | 4 | 2 | 2 | 15 | 15 |
| 16 | 8 | 6 | 2 | 2 | 56 | 56 |
| 20 | 10 | 8 | 2 | 2 | 210 | 210 |
| 12 | 5 | 4 | **3** | **2** | 15 | 15 |
| 16 | 7 | 6 | **3** | **2** | 56 | 56 |
| 20 | 9 | 8 | **3** | **2** | 210 | 210 |
| 24 | 11 | 10 | **3** | **2** | 792 | 792 |
| 12 | 5 | 3 | **4** | **3** | 4 | 4 |
| 18 | 8 | 6 | **4** | **3** | 15 | 15 |

The rows in bold are the new phenomenon: **a grading of order `d` reaches absolute gap
`c = 2d − 1`, not only `c = d`.**  The reason is visible on the vanishing polynomial of the
window: with `s+1` blocks of size `d`,

  `∏_{i∈I}(X^d − b_i) = X^{ds+d} − (Σ_{i∈I} b_i)·X^{ds} + R`,  `deg R ≤ d(s−1)`,

so the pencil `f₀ = x^{ds+d}`, `f₁ = x^{ds}` may be read at any dimension `k = ds − j` with
`d(s−1) < k`, i.e. `j ≤ d − 1`, and then `c = n − k − e = d + j`.

### 3'. Is the graded point beatable?  (search evidence, not a theorem)

`analysis/gr2_maxbad_search.py`.  Unseeded hill-climbing over all syndrome lines never even
finds the graded optimum — at `|F| ≈ 10^3` the best over 20 restarts is `7` for
`(n,k,e) = (12,6,4)` and `0` for `(12,5,4)` and `(12,5,3)`: the landscape is flat almost
everywhere, so exhaustive-style search is not a viable falsification tool here.

Seeded at the graded optimum, local search at `|F| = 1009` appears to improve on it
(`17 > 15`, `65 > 56`), but this is a small-field artefact: with `C(16,6) = 8008` supports and
`|F| = 1009` the expected number of *accidental* incidences is already ≈ 8.  Repeating at
`|F| ≈ 10^6`, where the accidental rate is ≈ `10^{-2}` per line, the graded point is not
improved: `15 → 15` for `(12,6,4)` and `(12,5,4)`, `56 → 57` for `(16,8,6)`.  So within reach
of local search the block/grading configuration is optimal, up to one challenge.

### 3a. Formalised: the improved lower bound

`RequestProject/Root/CodingTheory/HalfGapPencil.lean`

* `prod_pow_sub_C_shape_sharp` — the sharp shape lemma `deg R + d ≤ ds`;
* `isBad_powerPencil_gen` — badness from a window whose vanishing polynomial is
  `X^a + γX^b + (deg < k)` with `k ≤ b < |S|` (the previous version needed `b = k`);
* `isBad_blocks_halfGap`, `card_badSet_ge_blocks_halfGap` —
  `#Bad ≥ C(m, s+1)` at dimension `k = ds − j`, radius `e = n − ds − d`, gap `c = d + j`,
  for every `j < d`;
* `card_badSet_ge_cosets_halfGap`, `exists_halfGap_counterexample` — the same over the
  explicit `μ_d`-coset domain in `ZMod p`, unconditionally.

At a prescribed gap `c`, taking `d = ⌈(c+1)/2⌉` gives

  **`#Bad ≥ C(n/d, (k+c)/d)`  with  `n/d ≈ 2n/(c+1)`,**

against `C(n/c, (k+c)/c)` for `CapacityGapCosets.card_badSet_ge_cosets` (which is the case
`j = 0`).  In the relative gap the exponent improves from `1/η` to `2/η`: the bound is
roughly *squared*.

### 3b. Formalised: the matching cap

`RequestProject/Root/CodingTheory/SyndromeLineIncidence.lean`

* `lineCloseOn_of_two`, `eq_of_isBad_window` — **a FULL-MCA window witnesses at most one
  challenge** (two challenges on one window force the whole plane into `U_E`);
* `card_badSet_le_card_windows` — hence `#Bad ≤ |𝒲|` for any family `𝒲` of windows covering
  the bad set: the master counting principle;
* `card_badSet_le_two_pow_of_saturated` — if every witness window is a union of fibres of a
  partition `π : D → ι` (the coset situation, `|ι| = n/d`), then `#Bad ≤ 2^{|ι|} = 2^{n/d}`;
* `card_badSet_le_choose_of_blockWindows` — if every witness window is a union of `s+1` of
  `m` blocks, then `#Bad ≤ C(m, s+1)`.

The last two theorems together with §3a **determine the block/grading mechanism exactly**:
with `m = n/d` blocks and windows of `s+1` blocks it produces `C(m, s+1)` bad challenges and
never more, and it reaches gap `c` only for `d ≥ (c+1)/2`, hence

  **`#Bad_graded ≤ 2^{n/d} ≤ 2^{2n/(c+1)} = exp(O(1/η))`, with equality of order attained.**

---

## 4. Consequence for Grand MCA

* At a **constant absolute gap** `c` the mechanism is exponential in `n`, so no bound of the
  form `#Bad ≤ poly(n)` can hold at `δ = 1 − ρ − c/n`.  This was already known in this
  repository (`CapacityGapPencil.not_polynomial_mca_bound_gapOne`,
  `CapacityGapCosets.card_badSet_ge_cosets`); the present work squares the exponent and
  detaches it from the divisibility condition `c ∣ e`, but does not change the qualitative
  statement.
* At a **constant relative gap** `η > 0` the same mechanism is capped by `2^{O(1/η)}`, a
  constant independent of `n`.  It therefore **cannot** produce a Grand-MCA counterexample in
  the regime that matters for FRI/STARK parameters.  This closes the syndrome-line/coset
  route at constant relative gap, and it does so quantitatively rather than heuristically:
  the cap is a theorem about *all* lines whose witness windows are block-saturated, not an
  observation about one construction.
* The remaining route is exactly the one the cap does not cover: bad challenges whose witness
  windows are **not** saturated for any coarse partition, i.e. incidences of `[W]` with
  `U_E`'s that are not orbit-closed.  §1a shows the object to search over is
  `Gr(2, F^κ)/PGL₂`, and the master counting principle says the whole question is how many of
  the `C(n,e)` subspaces `U_E` a single plane can meet non-degenerately.  At constant relative
  gap `dim(W ∩ U_E) ≥ 1` is a codimension-`(c−1)` condition on `Gr(2,κ)`, whose dimension is
  `2(κ−2)`, so a generic plane meets `O(κ/c)` of them; every known way of beating that count
  has so far gone through a grading, and the grading is now capped.

---

## 5. Files

| file | content |
|---|---|
| `RequestProject/Root/CodingTheory/SyndromeLineIncidence.lean` | plane form of the predicate, one-challenge-per-window, master counting, saturated/block caps, `PGL₂` invariance |
| `RequestProject/Root/CodingTheory/HalfGapPencil.lean` | sharp shape lemma, decoupled power pencil, `#Bad ≥ C(m,s+1)` at gap `d+j` for `j < d`, coset instance, unconditional existence |
| `analysis/gr2_syndrome_incidence.py` | exact syndrome-space bad-set computation |
| `analysis/gr2_validate.py` | validation against the literal predicate |
| `analysis/gr2_gate.py` | the `RS[10,5]/F_11` and `RS[12,6]/F_13` gates |
| `analysis/gr2_graded_family.py` | the graded family at gap 2, exact over `|F| ≈ 10^6` |
| `analysis/gr2_halfgap_grading.py` | the half-gap grading, exact |
| `analysis/gr2_maxbad_search.py` | hill-climbing over syndrome lines, unseeded and seeded at the graded optimum |
