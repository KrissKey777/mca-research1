# The κ-charging map — why every bad point but one consumes one distinct unit of excess capacity

Discovery round. **No Lean file was touched, no theorem was formalised, no axiom was added, no
`sorry` was written, no Johnson / list-size statement was used or produced, no rank / kernel /
image invariant was searched, no invariant search of any kind was run.** Exact integer arithmetic
modulo a prime throughout; **no float enters any verdict**.

Artifacts:

* `analysis/kappa_charging_map.py` — the experiment (runtime 1 min 10 s, no long-running job);
* `analysis/kappa_charging_map_output.txt` — the exact saved output;
* `analysis/kappa_charging_data/*.jsonl` — per-family persisted rows (written after every family).

---

## 0. Answer, in one line

**The mechanism exists, and it is not a matching problem.**

The slot that a bad point consumes in the capacity of a direction `q` **is the bad point itself**:
the capacity set of `q` is a set of *line parameters*, and the charged parameter is one of its
elements. The single uncharged point is the base point `γ₀`, and the reason exactly one point
escapes is that the base point lies in the capacity set of **every** realised direction — the
capacity sets form a *pencil through `(γ₀, c₀)`*. That is the entire content of the `−1` in
`κ(q) − 1`.

So the answer to "why should every bad point except one consume one distinct unit of excess
capacity" is:

> because the excess capacity of a direction `q` is, literally, the set of *other* parameters on
> the lift line of slope `q` through the base point, and a parameter cannot be two parameters.

Consequently the target inequality is not a fitted correlation: it is the counting form of an
injective map that can be written down explicitly. The theorem schema is stated in §5, with the
weakest hypotheses the argument actually needs (no Reed–Solomon structure, no minimum distance, no
relation between `e` and `n`, no list-size bound). §7 records what is *not* claimed.

---

## 1. Objects, fixed exactly as in the previous round

An MCA instance is `(C, e, f₀, f₁)`: a linear code `C ⊆ F^ι` over a finite field `F` (in the
experiment `F = F_p`, `ι = {1..n}`), a radius `e ∈ ℕ`, and the line `γ ↦ f₀ + γ f₁`.

```
Bad     = { γ ∈ F : ∃ c ∈ C, wt(f₀ + γ f₁ − c) ≤ e }        (project convention: the
                                                             degenerate γ are removed;
                                                             removal only shrinks Bad)
L       = L(f₁, 2e) = { q ∈ C : wt(f₁ − q) ≤ 2e }
Γ(u,q)  = { γ ∈ F : wt( (f₀ − u) + γ (f₁ − q) ) ≤ e }          for u ∈ C, q ∈ C
κ(q)    = max_{u ∈ C} |Γ(u,q)|
```

`κ` is exactly the canonical slope capacity of `CANONICAL_MCA_STATE_PROBE.md` (the script
recomputes it by the same closed formula, so the two rounds share one definition).

`Γ(u,q)` is the set of parameters at which the line `γ ↦ f₀ + γ f₁` is within `e` of the *lift line*
`γ ↦ u + γ q` inside the code. `κ(q)` is the largest number of parameters any single lift line of
slope `q` can capture.

---

## 2. PHASE 1 — the explicit charging trace

**The rule tested** (this is candidate rule "q determined by the error displacement of the bad
point" of the mission list; the other candidates are discussed in §4):

```
fix a base bad parameter γ₀ ∈ Bad and a witness c₀ ∈ C of it;
for every other bad γ, with a witness c_γ:

      q(γ) := (c_γ − c₀) / (γ − γ₀)   ∈ C            (the displacement direction)
      u(q) := c₀ − γ₀ · q(γ)          ∈ C            (the lift line through the base witness)

      charge γ to the slot  "γ"  inside  Γ(u(q), q(γ)) \ {γ₀}.
```

Everything that this rule must satisfy is verified **explicitly on every instance and for every
possible base point `γ₀ ∈ Bad`** (12 574 base choices in total), and, wherever the witness is not
unique, additionally for random alternative witness selections (2 052 of them, 684 instances have a
non-unique witness):

| flag | checked statement | failures |
| --- | --- | --- |
| V1 | `q(γ) ∈ L(f₁, 2e)` | 0 |
| V2 | `γ₀ ∈ Γ(u(q), q)` — the base point occupies a slot of **every** realised direction | 0 |
| V3 | `γ ∈ Γ(u(q), q)` — the charged point occupies a slot | 0 |
| V4 | `\|Γ(u(q), q)\| ≤ κ(q)` | 0 |
| V5 | `γ ↦ (q(γ), γ)` is injective | 0 |
| V6 | `\|class(q)\| ≤ κ(q) − 1` for every realised `q` | 0 |
| V7 | `#Bad − 1 ≤ Σ_realised (κ(q)−1) ≤ Σ_{q∈L} (κ(q)−1)` | 0 |
| V8 | `κ(q) ≥ 1` for every `q ∈ L` (needed for the last inequality) | 0 |

An explicit trace, reproduced verbatim from the saved output — the smallest separating example of
the previous round (RS[5,2]/F₅, `e = 2`, `f₀ = (0,0,0,1,1)`, `f₁ = (0,0,0,0,1)`, `#Bad = 4`,
`|L| = 18`):

```
Bad = [1, 2, 3, 4];  base point γ₀ = 1, witness c₀ = (3,4,0,1,2)

  γ | witness c_γ   | q = (c_γ−c₀)/(γ−γ₀) | d(f₁,q) | κ(q) | Γ(u_q, q)
  2 | (0,2,4,1,3)   | (2,3,4,0,1)         |    3    |  3   | [1, 2, 3]
  3 | (2,0,3,1,4)   | (2,3,4,0,1)         |    3    |  3   | [1, 2, 3]
  4 | (0,0,0,0,0)   | (4,2,0,3,1)         |    3    |  2   | [1, 4]

classes:  q=(2,3,4,0,1) : {2,3}   |class| = 2 ≤ κ−1 = 2
          q=(4,2,0,3,1) : {4}     |class| = 1 ≤ κ−1 = 1
#Bad−1 = 3 ≤ Σ_realised (κ−1) = 3 ≤ Σ_L (κ−1) = 18
```

Read the third column of `Γ`: every capacity set contains the base point `1`, and the charged
parameters are the *other* elements of that set. Nothing is optimised; the assignment is forced.

The companion instance of the previous round (`f₀ = (0,0,1,1,3)`, `#Bad = 5`) is traced in the same
way in the output; there `Γ(u_q,q) = [0,1,3]` and `[0,2,4]`, both containing the base point `0`,
and the two classes are `{1,3}` and `{2,4}`.

---

## 3. PHASE 3 — classification over all instances tested

Families (gap regime `(d−2e)/2 ≤ w ≤ 2e`, instances with `#Bad ≥ 2`; exhaustive over coset
representatives in the small families, deterministic pseudo-random representative samples in the
larger ones; the sample seed is recorded in the script):

| family | instances | family | instances |
| --- | --- | --- | --- |
| RS[4,2]/F₅ | 400 | RS[6,2]/F₁₃ | 9 |
| RS[5,2]/F₅ | 800 | **RS[6,2]/F₁₇** | 152 |
| RS[5,3]/F₅ | 400 | **RS[6,2]/F₁₉** | 149 |
| RS[6,2]/F₇ | 265 | **RS[7,3]/F₁₁** | 49 |
| RS[6,3]/F₇ | 484 | **RAND[6,3]/F₅** (random linear, non-RS) | 104 |
| RS[7,3]/F₇ | 145 | **RAND[7,3]/F₇** | 32 |
| RS[5,2]/F₁₁ | 9 | **RAND[6,2]/F₁₁** | 13 |
| RS[6,3]/F₁₁ | 74 | cached hardest instances of the previous round | 211 |

Two further families were scanned and produced no gap instance with `#Bad ≥ 2` under the sample used
(RS[4,3]/F₅, RS[7,2]/F₁₇); they are listed in the output with count 0.

Total **3 296** instances (`max #Bad = 11`, `max |L| = 136`). Families in bold are outside the
previous scan: two larger prime fields and, more importantly, three **random linear codes**, which
test that the mechanism does not use the Reed–Solomon structure.

```
verdict A  (inequality holds AND the canonical charging exists) : 3296
verdict B  (inequality holds, canonical charging fails)         :    0
verdict C  (inequality fails)                                   :    0
```

with, over the same set,

```
#Bad ≤ 1 + Σ_{q∈L} (κ(q)−1)              0 violations
#Bad ≤ 1 + Σ_{κ(q)≥2} (κ(q)−1)           0 violations
#Bad ≤ 1 + Σ_{q realised} (κ(q)−1)       0 violations
min_{q∈L} κ(q) = 0 anywhere              0 instances
```

No counterexample of type B or C was found, so PHASE 3's stop rule ("record the smallest
counterexample") does not trigger. Since the mechanism of §5 is a proof, a type-C instance would
have been a bug report against the experiment, and a type-B instance impossible; the run is
therefore also a consistency check of the previous round's data.

---

## 4. PHASE 2 — which rule, and why the slot cannot be reused

Two contrast rules were run alongside the canonical one, from the lex-least base point:

* **R2, "nearest admissible direction"**: charge `γ` to the `q ∈ L`, minimal in `(d(f₁,q), q)`,
  such that `γ` is chargeable to `q` at all (i.e. `γ₀, γ ∈ Γ(c₀ − γ₀q, q)`). Failures: **0/3296**.
* **R3, "some injective assignment exists"**: bipartite feasibility of `Bad \ {γ₀}` against the
  slots `{1..κ(q)−1}` over the chargeability relation. Failures: **0/3296**.

R2 and R3 succeeding is *not* the result: an arbitrary matching would leave the inequality a
coincidence. The result is that the displacement rule needs no search at all, and that its
injectivity is not a combinatorial fact but a tautology about labels:

> **The canonical geometric reason a capacity slot cannot be reused.** A slot of direction `q` is
> an element of `Γ(u_q, q) ⊆ F`, i.e. a *line parameter*. The charging map sends the bad parameter
> `γ` to the slot `γ` of its own displacement direction. Two distinct bad points therefore never
> receive the same slot, whatever else happens; a slot could only be reused by a parameter equal to
> itself. What has to be proved is not injectivity, but *membership*: that `γ` really lies in the
> capacity set of `q(γ)` (V3), that `q(γ)` really lies in the list `L` (V1), and that the base
> point already occupies one slot of that same set (V2) — which is what makes the available
> capacity `κ(q) − 1` rather than `κ(q)`.

The last point is the structural reason **exactly one** bad point escapes: all realised capacity
sets pass through the base point. The `−1` per direction and the global `+1` are the same object
counted twice; the inequality could equally be written

```
#Bad ≤ | ⋃_{q realised} Γ(u_q, q) |,
```

the union of a pencil of capacity sets through `(γ₀, c₀)` — see §6.

---

## 5. Theorem schema (for a later Lean formalisation — **not** formalised here)

Weakest hypotheses the argument uses. Let `F` be a field, `ι` a finite index set, `V = F^ι` with
Hamming weight `wt`, and `C ⊆ V` an `F`-subspace (a submodule over a field is enough; nothing below
uses a minimum distance, a bound on `e`, an RS structure, or a bound on `|L|`).

Fix `e ∈ ℕ`, `f₀, f₁ ∈ V`, and let `B ⊆ { γ ∈ F : ∃ c ∈ C, wt(f₀ + γ f₁ − c) ≤ e }` be **any**
subset (in particular the project's non-degenerate `badSet`). Define `L`, `Γ(u,q)`, `κ(q)` as in §1.

* **S1 (displacement).** If `γ ≠ γ₀` are in `B` with witnesses `c, c₀`, then
  `q := (γ − γ₀)⁻¹ (c − c₀) ∈ C` and `wt(f₁ − q) ≤ 2e`, i.e. `q ∈ L`.
  *Proof ingredients:* `(γ − γ₀)(f₁ − q) = (f₀+γf₁−c) − (f₀+γ₀f₁−c₀)`; subadditivity of `wt`;
  `wt(λ v) = wt(v)` for `λ ≠ 0`.
* **S2 (base slot).** With `u_q := c₀ − γ₀ q ∈ C`, one has `γ₀ ∈ Γ(u_q, q)`, because
  `(f₀ − u_q) + γ₀(f₁ − q) = f₀ + γ₀ f₁ − c₀`.
* **S3 (charged slot).** `γ ∈ Γ(u_q, q)`, because
  `(f₀ − u_q) + γ(f₁ − q) = f₀ + γ f₁ − (c₀ + (γ − γ₀) q) = f₀ + γ f₁ − c`.
* **S4 (capacity).** `|Γ(u_q, q)| ≤ κ(q)`, by definition of `κ` as a maximum over `u ∈ C`
  (finite because `F` is finite; over an infinite field replace `κ` by the based capacity of §6).
* **S5 (charging map).** Fix `γ₀ ∈ B` and witnesses. The map
  `Φ : B \ {γ₀} → Σ_{q ∈ L} (Γ(u_q, q) \ {γ₀})`, `Φ(γ) = (q(γ), γ)`, is well defined (S1–S3) and
  injective (the second component is `γ`).
* **T (theorem).** For every `B` as above:
  `|B| − 1 ≤ Σ_{q ∈ Q} (κ(q) − 1)` where `Q ⊆ L` is the set of realised directions; and if
  `B ≠ ∅` then `κ(q) ≥ 1` for **all** `q ∈ L` (take `u := c* − γ* q` for any `γ* ∈ B` with witness
  `c*`), so
  ```
  B ≠ ∅   ⇒   |B| ≤ 1 + Σ_{q ∈ L(f₁,2e)} (κ(q) − 1).
  ```
  Unconditionally, `|B| ≤ max(1, 1 + Σ_{q ∈ L, κ(q) ≥ 2} (κ(q) − 1))`.

Remarks for the formalisation.

1. `B` is an arbitrary subset of the `e`-close parameters, so the statement applies verbatim to the
   project's `badSet` (degeneracy filter included) and to any future variant of it.
2. Only three facts about `wt` are used: subadditivity, invariance under nonzero scaling, and
   `wt(v) ≤ e` being decidable. The alphabet may be any `F`-vector space, coordinatewise.
3. The `−1` per direction requires the *same* base point `(γ₀, c₀)` for all directions; this is the
   pencil structure and must survive into the Lean statement (it is why `u_q` is a function of `q`
   and of the fixed `c₀`, not an arbitrary codeword).
4. This is strictly a *different* mechanism from the project's already-proved packing bound
   `card_badSet_le_sum_chargeCap` (which bounds `|class(q)|` by an arithmetic function of
   `d(f₁,q)`): here `|class(q)|` is bounded by an exact count attached to `q`. See §6 for the
   measured comparison.

---

## 6. PHASE 4 — no second-order datum `κ(q,q')` is needed; two strictly sharper forms exist

The mission's Phase 4 asks whether `κ(q)` needs one extra local datum. On the evidence it does
**not**: the mechanism closes with `κ(q)` alone. What the trace does expose are two refinements
*inside* the same mechanism, both witness-free once the base point is fixed:

* **based capacity** `1 + Σ_{q realised} (|Γ(u_q, q)| − 1)` — the same sum with the exact based sets
  instead of their maxima over `u`. Violations: 0/3296. It is **attained with equality** on
  3 221/3 296 instances; in the 75 exceptions the pencil is not disjoint away from the base point,
  or a capacity set contains a parameter that the degeneracy filter removes from `Bad`.
* **pencil bound** `#Bad ≤ | ⋃_{q realised} Γ(u_q, q) |`. Violations: 0/3296; strictly smaller than
  the based capacity on 69 instances; **equal to `#Bad` on 3 290/3 296 instances** (the six
  exceptions are instances where the union contains a degenerate parameter that the project's `Bad`
  excludes).

So the direction-interaction datum the mission was prepared to introduce (`κ(q,q')`) already has a
concrete meaning here: it is the *overlap of two capacity sets of the pencil away from the base
point*, and it is the only source of slack between `#Bad` and the based capacity. This is the
smallest possible refinement, and it is a property of the pencil, not a new invariant.

Comparison with the previously proved bound of the project
(`max(1, Σ_{q∈L} chargeCap(e, d(f₁,q))`, `ChargingCapacity.lean`), over the same 3 296 instances:

```
proved bound violated                        :    0   (consistency check)
κ-charge strictly smaller than proved bound  : 3215
proved bound strictly smaller                :    0
equal                                        :   81
pencil bound strictly smaller than proved    : 3215
```

The κ-charge is never worse and is usually much better; the largest observed slack of the κ-charge
itself is still large (e.g. RS[6,3]/F₁₁, `e = 2`, `|L| = 136`, `#Bad = 5`, κ-charge 80), which is
the honest cost of summing over the whole list `L` instead of the realised directions: the
inequality is tight (`κ-charge = #Bad`) on 1 178/3 296 instances and loose on the rest, and the loss
is entirely the non-realised directions.

---

## 7. What is *not* claimed

* **Nothing here is a formalised theorem.** §5 is a proof schema written for a later Lean round; no
  Lean file was created or modified in this round, and the project's proved results are unchanged.
  Until it is formalised, the inequality remains a **conjecture with a proof sketch**, not a
  project theorem.
* The mechanism does **not** bound `|L(f₁,2e)|`, and no Johnson-type or list-size statement was
  used, assumed or produced. The index set of the sum is still `L`; what the round explains is why
  the *weights* `κ(q) − 1` are the right ones, not how many terms there are.
* `κ` remains non-monotone in `#Bad` and incomplete as a state (23/291 unseparated pairs from the
  previous round); nothing here changes that, and the charging map does not claim to.
* All statements are exact finite computations on the families listed in §3 (`e ∈ {1,2}`, `n ≤ 7`,
  `p ≤ 19`). No claim is made for larger `n`, larger fields, `e ≥ 3`, folded codes, the circle
  setting, or M31 parameters — except through §5, whose hypotheses are parameter-free and whose
  validity is a matter of proof, not of the scan.
* No performance, SOTA or Verus claim is made or implied.

---

## 8. Recommended next step

The success criterion of the mission is met: every bad point except one has a canonical,
non-reusable capacity slot — its own line parameter inside the capacity set of its displacement
direction — and the single exception is the base point of the pencil. The natural next round is
therefore a **formalisation round** for the schema of §5 (S1–S5 and T), stated over an arbitrary
finite-dimensional code as in `ChargingCapacity.lean`, followed by the comparison lemma
`κ-charge ≤ chargeCap-bound` if it can be proved in general (measured: 3 215 strict, 81 equal,
0 reversals).
