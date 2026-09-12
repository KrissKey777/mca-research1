# DIRECTION_LIST_GATE_FALSE — final status report

**Verdict: `DIRECTION_LIST_GATE_FALSE`.**
The `rsList` bound required by the direction-list route is *false* at the deployed row — and
false for **every** direction word, by an astronomically large margin. Grand MCA is **not**
thereby refuted: the direction-list inequality is one-directional, so only this *sufficient*
route is closed.

New source file: `RequestProject/Root/CodingTheory/DirectionListGateFalse.lean`
Axiom audit file: `RequestProject/DirectionListGateFalseAxiomAudit.lean`
Nothing existing was modified or deleted; all new work is additive, `sorry`-free, axiom-free
(only `propext`, `Classical.choice`, `Quot.sound`), with no `@[implemented_by]`.

---

## 1. `rsList` frozen exactly (source semantics)

Source: `RequestProject/Root/CodingTheory/IndicatorLineList.lean`, lines 50–59.

```lean
noncomputable def rsList (D : Finset F) (k e : ℕ) (f : ↥D → F) : Finset (↥D → F) :=
  Finset.univ.filter (fun g => g ∈ reedSolomonCode F D k ∧ hammingDistance f g ≤ e)

theorem mem_rsList {k e : ℕ} {f g : ↥D → F} :
    g ∈ rsList D k e f ↔ (g ∈ reedSolomonCode F D k ∧ hammingDistance f g ≤ e)
```

| item | exact source content |
|---|---|
| ambient field | `variable {F : Type u} [Field F] [DecidableEq F] [Fintype F]` — an arbitrary finite field; at the deployed instance `F = FKB = GaloisField pKB 6`, `pKB = 2³¹ − 2²⁴ + 1` |
| evaluation domain | `D : Finset F`; words are functions `↥D → F` on the subtype of `D`; deployed `D = domKB = nthRootsFinset 2²¹ 1`, `domKB.card = 2²¹` |
| RS code | `reedSolomonCode F D k` (`ReedSolomon.lean`): `{f | ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x : ↥D, f x = p.eval x}` — evaluations of polynomials of degree `< k`, a `Submodule` |
| element type | **words** `↥D → F`, *not* polynomials; membership is a `Finset` filter over `Finset.univ : Finset (↥D → F)` |
| radius convention | `hammingDistance f g ≤ e`, i.e. the **closed** ball; `hammingDistance` (`Hamming.lean`) = `#{x : ↥D | f x ≠ g x}` (disagreement count) |
| parameter `2e` | a plain radius argument; in the reduction the caller passes the literal `2 * e`, deployed `2 * 978944 = 1957888` |
| equality/quotient | function equality on `↥D`; no quotient, no projective identification |
| duplicates | none: a `Finset` of words. Distinct degree-`< k` polynomials may collapse to the same word only if `k > |D|`; at the deployed row `k = 2²⁰ < 2²¹ = |D|`, so words and polynomials correspond bijectively |
| hypotheses | none beyond `[Field F] [DecidableEq F] [Fintype F]`, `D : Finset F` |
| link to the official bad set | `ExtremalMCA.card_badSet_le_radius_mul_card_rsList : (badSet k e f₀ f₁).card ≤ 1 + e * (rsList D k (2*e) f₁).card`, extremal form `mcaMax_le_one_add_radius_mul_rsListMax`, deployed gate `deployed_mcaMax_le_of_rsListMax (hL : rsListMax D 1048576 1957888 ≤ 280895258678) : mcaMax 1048576 978944 D ≤ 274980728111395087` |

The interpretation used in the task statement matches the source object, so no
`SOURCE_SEMANTICS_CORRECTION` is raised. (Note the unlocalised variant
`DirectionListReduction.card_badSet_le_mul_card_rsList` carries the factor `|D|`, not `e`;
the sharpened `ExtremalMCA` version with factor `e` is the one used by the gate.)

## 2. Numerical closure threshold (re-verified in Lean)

`deployed_gate_arithmetic`:
`(B* − 1) / e = (274980728111395087 − 1)/978944 = 280895258678 = L_max`,
`1 + 978944 · 280895258678 = 274980728111276033 < B*`, slack `119054`.
So the gate would close the row — if its hypothesis were satisfiable. It is not.

## 3. The simultaneous RS algebra, and why the gate fails

Fix `f₁`. A member `g` of `rsList(f₁, 2e)` is a degree-`< k` evaluation word agreeing with
`f₁` on **at least `|D| − 2e`** positions. At the deployed row

```
|D| − 2e = 2097152 − 1957888 = 139264,     k = 1048576.
```

The required agreement `139264` is a factor `7.5` **below** the code dimension `k`. Agreement
on `|D| − 2e < k` positions imposes no algebraic constraint whatsoever: the equations shared by
all list elements ("`g` interpolates `f₁` somewhere") are underdetermined, so the list is not a
list but a positive-dimensional family. Concretely, split the domain into a set `T` with
`|T| = |D| − 2e` and a disjoint set `U` with `|U| = k − |T| = k + 2e − |D| = 909312`:
interpolate `f₁` on `T` and prescribe **arbitrary** values on `U`. The interpolant has degree
`< |T| + |U| = k`, agrees with `f₁` on `T`, so lies in the ball, and the values on `U` are
recovered from the word — hence the map from data to list elements is injective.

This is the exact quantitative form of the qualitative barrier already in the project
(`ForcingBarrier.lean`, `DirectionListReduction.pairwise_route_within_unique_decoding`): the
route lives strictly inside unique decoding `k + 2e ≤ |D|`, and the deployed row is far outside
it (`k + 2e = 3006464 > 2097152 = |D|`).

## 4. Load-bearing declarations

All in `RequestProject/Root/CodingTheory/DirectionListGateFalse.lean`, namespace
`Root.CodingTheory`, ambient `variable {F : Type u} [Field F] [DecidableEq F] {D : Finset F}`
and (except where `omit`ted) `[Fintype F]`. Each concerns `rsList` only, except
`deployed_gate_false*`, which concerns the interface between `rsList` and the official MCA
gate (it refutes the hypothesis of `deployed_mcaMax_le_of_rsListMax`, not its conclusion).

| declaration | signature | concerns |
|---|---|---|
| `freeExtWord` | `(T U : Finset ↥D) (f : ↥D → F) (u : ↥U → F) : ↥D → F` — Lagrange interpolant of `f` on `T` and `u` on `U` | `rsList` |
| `freeExtWord_mem_rsList` | `(hdisj : Disjoint T U) (hTU : T.card + U.card ≤ k) (hT : D.card ≤ T.card + r) (f) (u) : freeExtWord T U f u ∈ rsList D k r f` | `rsList` |
| `pow_card_le_card_rsList` | `(hdisj : Disjoint T U) (hTU : T.card + U.card ≤ k) (hT : D.card ≤ T.card + r) (f) : Fintype.card F ^ U.card ≤ (rsList D k r f).card` | `rsList` |
| `pow_le_card_rsList_beyond_frontier` | `(hk : k ≤ D.card) (hr : r ≤ D.card) (hfront : D.card ≤ k + r) (f) : Fintype.card F ^ (k + r − D.card) ≤ (rsList D k r f).card` | `rsList` |
| `card_le_rsListMax_beyond_frontier` | `(hk : k ≤ D.card) (hr : r ≤ D.card) (hfront : D.card < k + r) : Fintype.card F ≤ rsListMax D k r` | `rsList` |
| `rsListMax_small_forces_unique_decoding` | `(hk : k ≤ D.card) (he : 2*e ≤ D.card) (hL : L < Fintype.card F) (h : rsListMax D k (2*e) ≤ L) : k + 2*e ≤ D.card` | `rsList` (mechanism ceiling) |
| `deployed_radius_frontier` | `1048576 + 978944 ≤ 2097152 ∧ 2097152 < 1048576 + 1957888 ∧ 2097152 − (1048576 + 978944) = 69632` — the radius-`e` ball is inside the frontier, the radius-`2e` ball is outside | diagnostic |
| `deployed_gate_arithmetic` | the `L_max`/slack identities above | arithmetic |
| `deployed_pow_le_card_rsList` | `(hD : D.card = 2097152) (f) : Fintype.card F ^ 909312 ≤ (rsList D 1048576 1957888 f).card` | `rsList` |
| `deployed_card_rsList_gt_gate` | `(hD : D.card = 2097152) (f) : 280895258678 < (rsList D 1048576 1957888 f).card` | `rsList` |
| `deployed_gate_false` | `(hD : D.card = 2097152) : ¬ rsListMax D 1048576 1957888 ≤ 280895258678` | `rsList` + official gate |
| `KoalaRow.deployed_card_rsList_gt_gate_KB` | `(f : ↥domKB → FKB) : 280895258678 < (rsList domKB 1048576 1957888 f).card` | exact deployed instance |
| `KoalaRow.deployed_gate_false_KB` | `¬ rsListMax domKB 1048576 1957888 ≤ 280895258678` | exact deployed instance |

## 5. Measurement of the failure (task §6)

* required: `L_max = 280895258678 ≈ 2.81 · 10¹¹`;
* proved, for **every** `f₁` at the deployed row:
  `L_found ≥ |F|^909312 ≥ |D|² = 2097152² = 4398046511104 ≈ 4.40 · 10¹²`
  (the crude `|F|² ≥ |D|²` step already exceeds the threshold by a factor `> 15`; the true
  bound `(pKB⁶)^909312` is beyond astronomical);
* the failure is **not** an extremal phenomenon: there is no special violating family to bank,
  because the violation is universal in `f₁`. Its mechanism is the frontier inequality
  `|D| − 2e < k`, isolated as `rsListMax_small_forces_unique_decoding`.

## 6. Adversarial tests (task §5)

* `F₁₃` sharp example (`UniqueDecodingHoleWitness`, `|D| = 8`, `k = 3`, `e = 2`): here
  `k + 2e = 7 ≤ 8 = |D|`, i.e. *inside* the frontier, so the new lower bound does not apply
  and no conflict arises with the sharpness statements of `ExtremalMCASharpness.lean`.
* `DeployedPencilOneShort` (`deployed_extremal_pencil_one_short`) and the overlap/antichain and
  pencil-stability results are upper-bound statements about `badSet`; nothing here contradicts
  them, since no bad challenge is constructed.
* Parameter rows are respected exactly: all deployed statements are proved at `e = 978944`,
  `2e = 1957888`, `k = 2²⁰`, `|D| = 2²¹`, and additionally at the literal deployed instance
  `(FKB, domKB)`. The boundary sensitivity is *proved*, not asserted: the mechanism switches at
  `|D| = k + 2e` exactly (`pow_le_card_rsList_beyond_frontier` needs `D.card ≤ k + r`;
  `card_le_rsListMax_beyond_frontier` needs the strict `D.card < k + r`).
* Independent numeric cross-check of the lower bound in a small case (`p = 7`, `|D| = 5`,
  `k = 3`, `r = 3`, predicted `≥ 7`, brute-force list size `53`). This is exploration only; the
  Lean theorem is the verified statement.

## 7. What was *not* concluded

* No `DEPLOYED_COUNTEREXAMPLE`: no `f₀` is constructed and no official bad challenge is
  exhibited, let alone `> B*` of them.
* `M_C(1118208) ≤ B*` remains open; the extremal bridge (`deployed_security_iff`), overlap
  rigidity, the antichain theorem, pencil stability and the direction-list reduction itself all
  remain valid and untouched.
* The radius-`e` ball at the deployed row is *not* shown to explode: `k + e = 2027520 ≤ 2²¹`
  (`deployed_radius_frontier`). The failure is caused precisely by the radius doubling of the
  pairwise step.
* Consequence for route selection: any future route must avoid a radius-`2e` list step, or
  must restore the constraint lost at `|D| − 2e < k` (e.g. by using the *correlated* pair
  structure, which the ball around `f₁` alone discards).

## 8. Build and audit evidence

```
$ lake build RequestProject.Root.CodingTheory.DirectionListGateFalse
Build completed successfully.

$ lake build RequestProject.DirectionListGateFalseAxiomAudit
Build completed successfully (8047 jobs).
'Root.CodingTheory.freeExtWord'                          … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.freeExtWord_of_mem_left'              … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.freeExtWord_of_mem_right'             … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.freeExtWord_mem_rsList'               … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.pow_card_le_card_rsList'              … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.pow_le_card_rsList_beyond_frontier'   … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.card_le_rsListMax_beyond_frontier'    … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.rsListMax_small_forces_unique_decoding' … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_gate_arithmetic'             … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_frontier_gap'                … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_radius_frontier'              … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_pow_le_card_rsList'          … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_card_rsList_gt_gate'         … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.deployed_gate_false'                  … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.KoalaRow.card_domKB_eq'               … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.KoalaRow.deployed_card_rsList_gt_gate_KB' … [propext, Classical.choice, Quot.sound]
'Root.CodingTheory.KoalaRow.deployed_gate_false_KB'      … [propext, Classical.choice, Quot.sound]
```

`rg -n "sorry|admit|axiom |@\[implemented_by\]"` over the two new files returns nothing.
