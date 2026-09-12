# Canonical MCA state probe

Discovery experiment. **No Lean file was touched, no theorem was proved, no axiom was added, no
`sorry` was written.** Script: `analysis/canonical_mca_state_probe.py`; saved exact output:
`analysis/canonical_mca_state_probe_output.txt` (33 s once the Phase-1 cache in
`analysis/second_order_phase1/` exists — the script regenerates it if absent). All arithmetic is
exact: Python integers mod `p`, `fractions.Fraction` for the one normalised statistic. **No float
enters any verdict.**

Phase 1 (instance enumeration) and Phase 2 (collision pairs) are imported verbatim from
`analysis/second_order_slope_geometry.py`, so the instances and pairs are exactly those of
`SLOPE_GEOMETRY_SECOND_ORDER_REPORT.md` and `OCCUPANCY_ELIMINATION_REPORT.md`:
38 084 gap instances; **256 / 291 / 291** collision pairs in regimes I (`A` free),
II (`A` pinned), III (`A` and the list-distance multiset pinned); 221 distinct instances.

**The strongest pairs — the "hard core" — are re-selected here explicitly**: the **26** regime-III
pairs on which the *entire* slope-indexed second-order sub-vector, full support-hypergraph
isomorphism type included, is constant while `#Bad` differs. These are the pairs that
single-list invariants, slope-support geometry and support-hypergraph isomorphism all fail to
distinguish.

---

## Question

> Does the existing MCA formalism, or a natural projection of its existing objects, expose a
> witness-independent, non-support, non-occupancy state that separates those pairs?

---

## STEP 1 — inventory and classification

An MCA instance is `(p, D, k, e, f₀, f₁)`: the RS code `C`, the radius `e`, and the line
`γ ↦ f₀ + γ f₁`. `Bad = {γ : some c ∈ C has d(f₀+γf₁, c) ≤ e and the whole line does not agree
with C on that agreement set}` (the project's definition, degenerate γ excluded).

| candidate | definition | class |
| --- | --- | --- |
| `PROF` | the **line distance profile** `γ ↦ d(f₀+γf₁, C)` on all of `F_p`; statistics used: full multiset, tail multiset (values `> e`), tail value-set, exact-rational tail shape, `max`, `min` over the tail, `#{γ : δ(γ) ≤ e−1}`, `#{γ : δ(γ) = e+1}` | EXISTING-CANONICAL |
| `PUNCT` | the **punctured-distance profile** `{(s_q, ρ_q) : q ∈ L(f₁,2e)}`, `s_q = d(f₁,q)`, `ρ_q = min_{u∈C} wt((f₀−u) restricted to supp(f₁−q)^c)` — the constant the within-slope charging argument spends, computed with **no** witness | NATURAL-PROJECTION |
| `PBOUND` | `Σ_q ⌊s_q / max(1, ρ_q+s_q−e)⌋` over `q` with `ρ_q ≤ e` — the packing bound read off `PUNCT` | NATURAL-PROJECTION |
| **`KAPPA`** | the **canonical slope-capacity profile** `κ(q) = max_{u∈C} #{γ : wt((f₀−u)+γ(f₁−q)) ≤ e}`, `q ∈ L(f₁,2e)`; statistics: the multiset `{κ(q)}`, the pair profile `{(s_q, κ(q))}`, `Σκ`, `max κ`, `#{q : κ(q) ≥ 2}`, and the charge `1 + Σ_{κ(q)≥2}(κ(q)−1)` | NATURAL-PROJECTION |
| `WITSET` | the witness codeword set `C_wit = {c : c witnesses some γ}` — cardinality, affine dimension | witness-free (all witnesses used), but **BAD-adjacent** |
| `ERRSP` | error-configuration space `E = span{f₀+γf₁−c}` — `dim E`, affine hull, `dim(E∩C)`, `dim(E+C)−k`, weight multiset | witness-free |
| `SLOPE`/`LIFT` | canonical realised-slope set `Q`, intercept set `U`, lift set `Λ ⊆ C⊕C` (over **all** witness pairs) — cardinalities, affine dimensions, dependency counts, joint span `span{q−q'} + span{u−u'}` and its intersection, `dim span{f₁−q}`, `dim span{f₀−u}` | witness-free, but partly BAD-INDEXED (cardinalities) |
| `OCC` | lift spectrum `{ν(u,q)}` | OCCUPANCY-DERIVED (control) |
| `BAD` | per-parameter witness multiplicities | BAD-INDEXED (control) |

Rejected before testing (not computed): anything indexed by the bad set alone, any witness-selection
convention, any support-only statistic (those are the frozen negatives), and everything on the
forbidden list (Johnson/list-size bounds, projective geometry, nerves, spectral quantities, `A_E`).

*Canonicality remark (EXPERIMENTAL/STRUCTURAL, trivial):* the whole 2-parameter family
`(a,b) ↦ d(a f₀ + b f₁, C)` carries nothing beyond the line profile, because `d(λv, C) = d(v, C)`.
So `PROF` is the complete "plane" datum, not a chosen slice.

---

## STEP 2 — collision test (separation rates)

Separations (pairs on which the candidate's value differs), regime III and hard core:

| candidate | III (291) | hard core (26) | remark |
| --- | --- | --- | --- |
| **`KAPPA_profile` / `KAPPA_pairprofile`** | **268** | **26 / 26** | index set is `L`, whose size *and* list-distance multiset are pinned ⇒ both profiles have the same length: separation is structural, not size |
| `KAPPA_sum`, `KAPPA_ge2`, `KAPPA_charge` | 268 | 26 / 26 | 208 up / 60 down (III), 21 up / 5 down (hard core) — **not monotone** |
| `KAPPA_max` | 99 | 15 | |
| `PROF_full` | 269 | 26 / 26 | contains the `≤ e` part, i.e. `#Bad` itself — tautological |
| `PROF_le_em1` = `#{δ ≤ e−1}` | 148 | 26 / 26 | monotone **down** on all 26 hard-core pairs |
| `PROF_tail` (values `> e`) | 242 | 20 | length is `p − #{δ ≤ e}`, partly size |
| `PROF_tailset` / `PROF_tailshape` / `PROF_max` | 127 | 10 | size-free versions of the tail |
| `PUNCT_profile` / `_rho_multiset` / `_slack` | 101 | 15 | size-free (index set `L` pinned) |
| `PBOUND_total` / `_caps` | 30 | 8 | |
| `PUNCT_rho_min`, `PUNCT_admissible` | 0 | 0 | blind |
| `ERR_dim`, `ERR_affdim`, `ERR_cap_C`, `ERR_plus_C` | 4, 4, 4, 0 | **0** | blind on the hard core |
| `SLOPE_affdim`, `INT_affdim`, `LIFT_affdim`, `JOINT_dim`, `JOINT_cap`, `DIR_dim`, `OFF_dim`, `DIRQ_cap` | 4 each | **0** | every *dimensional* invariant of the canonical slope/lift/error spaces is blind on the hard core |
| `WIT_affdim` | 30 | 2 | |
| `WIT_card`, `ERR_card`, `A_can`, `U_can`, `LIFT_card`, `SLOPE_dep`, `LIFT_dep`, `DIR_dep` | 201–286 | 23–26 | cardinalities of witness-derived sets: these grow with the bad set, i.e. size accounting |
| controls `OCC_*`, `BAD_witmult` | 286–291 | 26 | known tautological separators |

**EXPERIMENTAL FACT (hard core).** The canonical slope-capacity profile `KAPPA` separates
**26 / 26** of the strongest collision pairs — pairs with identical first-order vector, identical
`A`, identical list-distance multiset and *isomorphic slope-support hypergraphs*. The separation is
not size accounting: `0 / 26` of these pairs have `KAPPA` profiles of different length
(STEP 5b of the output).

**EXPERIMENTAL FACT (smallest separating example).** RS[5,2]/F₅, `e = 2`, `w = 1`, `|L| = 18`,
`A = 2`, list-distance multiset and slope-support hypergraph identical:

```
X₁ : f₀ = (0,0,0,1,1), f₁ = (0,0,0,0,1)   #Bad = 4
X₂ : f₀ = (0,0,1,1,3), f₁ = (0,0,0,0,1)   #Bad = 5

KAPPA profile   X₁ : (1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,3,5)   Σ = 36, #{κ≥2} = 14, charge 19
                X₂ : (1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,3,3,3)   Σ = 27, #{κ≥2} =  5, charge 10
PUNCT profile   X₁ : (1,1),(3,0)×4,(4,0)×13     X₂ : (1,2),(3,0)×4,(4,0)×13
```

Note the direction: here the instance with the **smaller** `#Bad` has the **larger** capacity
profile. `KAPPA` separates, it does not order.

**EXPERIMENTAL FACT (smallest non-separating example, regime III).** RS[5,2]/F₅, `e = 2`, `w = 2`,
`|L| = 17`, `A = 2`:

```
Y₁ : f₀ = (0,0,1,1,3), f₁ = (0,0,0,1,4)   #Bad = 4
Y₂ : f₀ = (0,0,1,1,3), f₁ = (0,0,0,1,2)   #Bad = 5
common KAPPA profile : (1,1,1,1,1,2,2,2,2,2,2,2,2,3,3,3,3)   (identical, charge equal)
```

So `KAPPA` is **not** a complete invariant for `#Bad`: it fails on `23 / 291` regime-III pairs
(none of them in the hard core).

---

## STEP 3 — information-not-size test

Group the 221 instances by `(first-order signature, A, #Bad)`; 96 groups have ≥ 2 members. Does the
candidate still vary once `#Bad` is *pinned*?

```
KAPPA_pairprofile  varies in 35/96 groups        PUNCT_profile      varies in 11/96
KAPPA_profile      varies in 34/96               PROF_tail          varies in  7/96
KAPPA_ge2/charge   varies in 34/96               PBOUND_total       varies in  1/96
ERR_*, SLOPE_*, LIFT_*, JOINT_*, DIR_*, OFF_*   varies in  0/96   (all dimensional invariants)
W1-occupancy (previous report)                  varies in  0/96
```

**EXPERIMENTAL FACT.** `KAPPA` carries information in *both* directions: it separates instances with
different `#Bad`, and it is not determined by `(signature, A, #Bad)`. This is exactly the property
the occupancy matrix lacked (`W1` occupancy was an exact function of `(signature, A, #Bad)`).

---

## STEP 4 — A / #Bad information test

Over all 221 instances occurring in the pairs, exact integer arithmetic:

```
#Bad  ≤  KAPPA_charge = 1 + Σ_{κ(q)≥2}(κ(q)−1)     0 violations / 221
#Bad  ≤  KAPPA_sum                                  0 violations / 221
A     ≤  KAPPA_ge2 = #{q ∈ L : κ(q) ≥ 2}            0 violations / 221   (equality in 179/221)
#Bad  ≤  PBOUND_total                               0 violations / 221
A     ≤  PUNCT_admissible = #{q : ρ_q ≤ e}          0 violations / 221

KAPPA_charge < (e+1)A + 1   on  41 / 221 instances  (tightest: charge − #Bad = 1)
PBOUND_total < (e+1)A + 1   on   0 / 221 instances
```

**CONJECTURE (not proved, not formalised).** `#Bad ≤ 1 + Σ_{q ∈ L(f₁,2e), κ(q) ≥ 2} (κ(q) − 1)`.
Argument sketch only: fix a bad `γ₀` with witness `c₀`; every other bad `γ` with witness `c_γ`
yields `q = (c_γ−c₀)/(γ−γ₀) ∈ L(f₁,2e)` and a lift line of slope `q` through both points, so the
class of `q` is at most `κ(q)`. This is *not* a proven theorem in this project and was deliberately
not formalised.

**EXPERIMENTAL FACT.** On 41 of 221 tested instances the witness-free quantity `KAPPA_charge` is
strictly smaller than the proved bound `(e+1)A + 1`, once by exactly 1
(RS[6,2]/F₇, `e = 2`, `#Bad = 3`, charge 4, `A = 3`).

**Caveat, stated explicitly.** `KAPPA_ge2` is an upper bound for `A`, not a lower bound; the
capacity profile does *not* force `A` to be large, and its separations are non-monotone
(208 up / 60 down in regime III). Nothing here bounds `#Bad` independently of the index set `L`:
the sums run over `L(f₁,2e)`, so `|L|` has been refined, **not** eliminated.

---

## STEP 5 — `A = 2` → `A = 3` and `|L|` stratification

Hard core, split by `A` (all pairs have `A` pinned within the pair):

```
A = 2 : 16 pairs   KAPPA_profile 16/16   PUNCT_profile 12/16   PROF_tail 12/16
A = 3 :  4 pairs   KAPPA_profile  4/4    PUNCT_profile  0/4    PROF_tail  4/4
A ≥ 4 :  6 pairs   KAPPA_profile  6/6    PUNCT_profile  3/6    PROF_tail  4/6
```

Regime III: `A = 2` 38/40, `A = 3` 34/34, `A ≥ 4` 196/217 for `KAPPA_profile`.

**EXPERIMENTAL FACT.** The `KAPPA` signal survives the `A = 2 → A = 3` transition undiminished; the
`PUNCT` signal does not (0/4 at `A = 3` in the hard core). No collision pair with `|L| ∈ {2,3,4}`
exists in the data (all gap instances in these families have larger lists), so the `|L|`-small
stratification of the mission could not be run; the `A`-stratification is reported in its place.

---

## STEP 6 — explicitly rejected candidates

* **All dimensional invariants of the canonical linear objects** are blind on the hard core
  (0/26 each): `dim E`, affine hull of the error configuration, `dim(E ∩ C)`, `dim(E + C) − k`,
  affine dimension of the realised-slope set, of the intercept set, of the lift set in `C ⊕ C`,
  the joint constraint space `span{q−q'} + span{u−u'}`, its intersection with `span{u−u'}`,
  `dim span{f₁−q}`, `dim span{f₀−u}`, and the intersection of those two. Rank jumps between these
  spaces and the pinned `dim W` are therefore blind as well. **This closes the "kernel/image →
  quotient → rank jump → intersection → joint constraint space" line of the mission: there is no
  linear-algebraic degree of freedom of the realised configuration that the existing pinned data
  does not already fix.**
* `PUNCT_rho_min` and `PUNCT_admissible`: 0/291 and 0/26.
* `PBOUND_*`: weak (8/26), never better than the proved bound.
* Cardinality-valued witness-derived candidates (`WIT_card`, `ERR_card`, `A_can`, `U_can`,
  `LIFT_card`, `SLOPE_dep`, `LIFT_dep`, `DIR_dep`) separate, but they are counts of objects indexed
  by the bad set — the same size accounting that disqualified occupancy. They are reported for
  completeness and excluded from the verdict.
* `PROF_full` is excluded from the verdict (it contains `#{δ ≤ e}`, i.e. `#Bad`). Its genuinely
  size-free parts (`PROF_tailset`, `PROF_tailshape`, `PROF_max`) separate only 10/26.

---

## STEP 7 — decision

### OUTCOME A — intrinsic signal found (with explicit limits)

**The answer to the mission's question is YES.**

*Definition.* For an MCA instance `(C, e, f₀, f₁)` and each `q ∈ L(f₁, 2e)`,

```
κ(q) = max_{u ∈ C} #{ γ ∈ F_p : wt( (f₀ − u) + γ (f₁ − q) ) ≤ e },
X    = the multiset { (d(f₁,q), κ(q)) : q ∈ L(f₁,2e) }.
```

*Why it is canonical.* `κ` is a maximum over the whole code and a count over the whole field: no
witness is selected, no base point is chosen, the bad set is never consulted, and relabelling bad
parameters cannot change it — `X` is defined before the bad set exists. It is not a support object
(it uses the punctured *distance* of `f₀`, which the support hypergraph does not see) and not an
occupancy object (occupancy is indexed by the bad set and is an exact function of
`(signature, A, #Bad)`; `X` is indexed by `L` and varies in 34/96 groups at fixed `#Bad`).

*Evidence.* Separates **26/26** hard-core pairs and 268/291 regime-III pairs, with equal profile
length in every hard-core pair (so not size accounting); survives `A = 2 → A = 3`; yields
`#Bad ≤ 1 + Σ(κ(q)−1)` with 0 violations in 221 instances, strictly better than `(e+1)A+1` on 41 of
them.

*Why this is not yet a break of the barrier.* Three honest limitations:

1. `X` is indexed by `L(f₁,2e)`; the derived bounds sum over `L`. `|L|` has been **refined into a
   capacity-weighted count**, not removed. The mission's forbidden variable is therefore avoided as
   an *explanation* but not yet as a *parameter*.
2. `X` is **not monotone** in `#Bad` (208 up / 60 down), and `κ(q) ≥ 2` bounds `A` from **above**,
   so nothing here shows "`A` large ⇒ complexity(`X`) large". The desired implication remains
   untested and unproved.
3. `X` is not complete: 23/291 regime-III pairs with different `#Bad` share the same profile
   (smallest example above).

*Strongest negative result of the round (a genuine B-type finding, reported alongside).* Every
**dimensional** canonical invariant — the entire kernel/image/quotient/rank-jump/intersection/joint
constraint-space layer that the mission asked to be searched — is **blind** on the hard core
(0/26) and constant at fixed `(signature, A, #Bad)` (0/96). If a barrier-breaking bound exists, it
is not carried by the dimension of any canonical linear space attached to the realised
configuration; the only surviving intrinsic state found here is the *capacity* (a counting datum
per list element), not a rank.

---

## What is *not* claimed

* Nothing here is a theorem, and nothing was formalised. These are exact finite computations over
  RS[4,2]/F₅, RS[4,3]/F₅, RS[5,2]/F₅, RS[5,3]/F₅, RS[6,2]/F₇, RS[6,3]/F₇, RS[6,4]/F₇, RS[7,3]/F₇,
  RS[5,2]/F₁₁, RS[6,3]/F₁₁, RS[6,2]/F₁₃ with `e ∈ {1,2}`, on the collision pairs of the previous
  rounds only. No claim is made for larger `n`, larger fields, `e ≥ 3`, or M31 parameters.
* No Johnson bound, no Guruswami–Sudan list-size bound and no `A_E`-style object was used,
  searched for, or assumed.
* The frozen results (within-slope charging/packing theorem, `A − 1 ≤ #Bad ≤ (e+1)A + 1`, and the
  three previous negative rounds) were reused unchanged; no Lean definition or theorem was modified.
