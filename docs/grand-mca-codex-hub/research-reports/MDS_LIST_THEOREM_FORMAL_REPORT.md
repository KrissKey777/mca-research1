# MDS LIST-SIZE THEOREM (P1) — FORMAL REPORT

**Mission.** Formalise exactly one theorem — `|L(f₁,2e)| ≤ C(n,2e)` for an `[n,k]` MDS code in
the interpolation regime `2e ≤ n − k` — using the already verified support-geometry core, with
no `sorry`, no `admit`, no new axiom, no `native_decide`.

**Outcome: OUTCOME A — P1 IS FORMALISED.** Both branches are proved, they are shown to cover the
whole regime, the theorem holds for an arbitrary received word `f₁`, and the axiom audit reports
only `propext, Classical.choice, Quot.sound`. Per the mission's decision tree the mission stops
here; nothing about occupancy `m_x`, projected Rédei, or deep holes was formalised.

New file: `RequestProject/Root/CodingTheory/MDSListSize.lean`
(namespace `Root.CodingTheory.SupportGeometry`, continuing `SupportGeometry.lean`).

---

## 1. Exact mathematical statement

Notation: `ι` a finite index type, `n = Fintype.card ι`, `F` a field,
`C : Submodule F (ι → F)` a linear code, `d(C) = minDistance C` (`Hamming.lean`),
`f₁ : ι → F` an arbitrary received word,
`E(q) = errorSupport f₁ q`, `L = decodingList C f₁ e = { q ∈ C | d(f₁,q) ≤ 2e }`.

**Theorem (weakest form, `decodingList_ncard_le_choose`).**
Let `k : ℕ` satisfy

* `(hkn)` `k + 2e ≤ n` — the interpolation regime `2e ≤ n − k`, written without ℕ-subtraction;
* `(hd)` `n + 1 ≤ d(C) + k` — the MDS distance bound `d ≥ n − k + 1`, written without
  ℕ-subtraction.

Then `|L| ≤ C(n, 2e)`.

**Theorem (mission shape, `mds_decodingList_ncard_le`).**
If `d(C) = n − k + 1`, `dim_F C = k` and `2e ≤ n − k`, then `|L| ≤ C(n, 2e)`.

`f₁` is arbitrary: it is **not** assumed to be a codeword, **not** assumed to be outside `C`, and
no hypothesis is placed on `|F|`.

The list is a `Set (ι → F)`; its size is `Set.ncard`. `finite_decodingList` proves the list is
finite (from support injectivity), so `ncard` is the honest cardinality and not the `0`-default;
`mds_decodingList_toFinset_card_le` restates the bound as `(…).toFinset.card` when `F` is finite.

---

## 2. Branch A (`4e ≤ n`) — LYM

Hypotheses used: `2e < d(C)` and `4e ≤ n`. **No MDS hypothesis, no dimension.**

1. By `injOn_errorSupport` (support geometry, needs `2e < d`), `q ↦ E(q)` is injective on `L`, so
   `|L| = |F|` where `F = { E(q) : q ∈ L }`.
2. By `isAntichain_errorSupport` (needs `2e < d`), `F` is an antichain for `⊆`.
3. Every `E ∈ F` has `|E| = d(f₁,q) ≤ 2e =: t`, by definition of `L`.
4. `2t = 4e ≤ n`, so every occurring size lies in the increasing half of the binomial row:
   `|E| ≤ t` and `|E| + t ≤ 2t ≤ n` give `C(n,|E|) ≤ C(n,t)`
   (`choose_le_choose_of_le_of_add_le`).
5. LYM (`Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`) gives
   `Σ_{E ∈ F} C(n,|E|)⁻¹ ≤ 1`. By (4), `|F| · C(n,t)⁻¹ ≤ Σ_{E ∈ F} C(n,|E|)⁻¹ ≤ 1`, hence
   `|F| ≤ C(n,t) = C(n,2e)` (`ncard_le_choose_of_isAntichain`).
6. With (1), `|L| ≤ C(n,2e)`.

Where the hypotheses enter: **linearity** and **minimum distance** enter only through steps 1–2,
i.e. through the two support-geometry lemmas, both of which require exactly `2e < d(C)`. In the
main theorem `2e < d(C)` is obtained from `(hkn)` and `(hd)`: `2e ≤ n − k ≤ d(C) − 1`.

Note that Sperner's theorem (`IsAntichain.sperner`, bound `C(n, ⌊n/2⌋)`) is **too weak** here: it
is larger than `C(n,2e)` exactly in the interesting regime `4e < n`. That is why the lower-half
LYM lemma had to be proved (≈ 20 lines, modelled on Mathlib's own proof of Sperner).

## 3. Branch B (`4e > n`) — MDS information sets

Hypotheses used: `k + 2e ≤ n` and `d(C) ≥ n − k + 1`; the branch condition `4e > n` is used
**only** in the last step.

1. For `q ∈ L`, `|agreementSet f₁ q| = n − d(f₁,q) ≥ n − 2e ≥ k`. So a `k`-subset
   `S(q) ⊆ agreementSet f₁ q` exists; `pickSubset` selects one (`pickSubset_subset`,
   `card_pickSubset`).
2. `q ↦ S(q)` maps `L` into the `k`-subsets of `ι`, of which there are `C(n,k)`.
3. **Injectivity** (`eq_of_agree_on_card_eq`): if `S(q₁) = S(q₂) = S` with `|S| = k`, then for
   `x ∈ S`, `q₁ x = f₁ x = q₂ x`. Hence `q₁ − q₂ ∈ C` vanishes on `S`, so
   `d(q₁,q₂) ≤ n − k`. If `q₁ ≠ q₂`, linearity and the definition of the minimum distance give
   `d(C) ≤ d(q₁,q₂) ≤ n − k`, contradicting `d(C) ≥ n − k + 1`. So `q₁ = q₂`.
   *This is the exact place where MDS is used*: `d ≥ n − k + 1` is precisely the statement that
   every `k`-subset of coordinates is an information set.
4. Therefore `|L| ≤ C(n,k)` (`decodingList_ncard_le_choose_dim`). Note this holds in the whole
   regime `k + 2e ≤ n`, not only when `4e > n`.
5. **The binomial comparison, proved and not assumed.** `4e > n` together with `k + 2e ≤ n` gives
   `k ≤ n − 2e < 4e − 2e = 2e`, so `k ≤ 2e`; and `k + 2e ≤ n`. By unimodality of the binomial row
   in the form `a ≤ b ∧ a + b ≤ n ⟹ C(n,a) ≤ C(n,b)` (`choose_le_choose_of_le_of_add_le`, proved
   from `Nat.choose_le_succ_of_lt_half_left` and `Nat.choose_symm`), we get `C(n,k) ≤ C(n,2e)`.
   The direction is the required one; the target is `C(n,2e)`, and `C(n,n−k)` is not needed
   (indeed `C(n,k) = C(n,n−k)`, and `2e` lies between `k` and `n−k`).
6. Hence `|L| ≤ C(n,2e)`.

**Correction to the earlier informal report.** The implicit assumption in the previously reported
information-set injection was `k ≤ 2e`, needed for step 5. It does **not** hold throughout the
regime `2e ≤ n − k` — e.g. `n = 10, k = 6, e = 2` has `2e = 4 < 6 = k` — but it does hold whenever
`4e > n`, which is exactly the branch where it is used. The final theorem therefore carries **no**
hidden hypothesis `k ≥ 2e` or `k ≤ 2e`; that inequality is derived inside Branch B.

## 4. Branch coverage

The case split is `4e ≤ n` versus `4e > n` (trichotomy on ℕ, `le_or_gt`), so it is exhaustive by
construction. What has to be checked is that each branch's *extra* ingredient is available:

* Branch A needs `2e < d(C)`: from `(hkn)`, `(hd)`: `2e ≤ n − k` and `d(C) ≥ n − k + 1`.
* Branch B needs `k ≤ 2e`: from `4e > n` and `k + 2e ≤ n`, as in §3.5.

Both are discharged by `omega` inside the Lean proof of `decodingList_ncard_le_choose` from the
two stated hypotheses only. Consequently the two branches cover the entire regime `2e ≤ n − k`.

Equivalently, in the failure direction: if *both* branches failed we would have `2e < k` and
`4e > n`, while `2e ≤ n − k` forces `k ≤ n − 2e < 2e` — a contradiction.

---

## 5. Exact Lean declarations

All in `RequestProject/Root/CodingTheory/MDSListSize.lean`, namespace
`Root.CodingTheory.SupportGeometry`.

| declaration | statement |
| --- | --- |
| `choose_le_choose_of_le_of_add_le` | `a ≤ b → a + b ≤ n → n.choose a ≤ n.choose b` |
| `card_le_choose_of_isAntichain` | LYM lower-half form for `𝒜 : Finset (Finset α)` |
| `ncard_le_choose_of_isAntichain` | LYM lower-half form for `𝒮 : Set (Finset α)` |
| `finite_decodingList` | `2e < d(C) → (decodingList C f₁ e).Finite` |
| `ncard_decodingList_eq_ncard_image` | `|L| = |{ E(q) : q ∈ L }|` under `2e < d(C)` |
| `decodingList_ncard_le_choose_of_four_mul_le` | **Branch A**: `2e < d(C) → 4e ≤ n → |L| ≤ C(n,2e)` |
| `pickSubset`, `pickSubset_subset`, `card_pickSubset` | a chosen `k`-subset of a finset |
| `eq_of_agree_on_card_eq` | information-set property: agreement on `k` coordinates + `d ≥ n−k+1` ⟹ equality |
| `decodingList_ncard_le_choose_dim` | **Branch B**: `k + 2e ≤ n → n+1 ≤ d(C)+k → |L| ≤ C(n,k)` |
| `decodingList_ncard_le_choose` | **P1, weakest form** (§1) |
| `mds_decodingList_ncard_le` | **P1, mission shape** (§1) |
| `mds_decodingList_toFinset_card_le` | the same with `(…).toFinset.card`, for `[Fintype F]` |
| `reedSolomon_decodingList_ncard_le` | the RS instance, showing the hypotheses are satisfiable |

```lean
theorem decodingList_ncard_le_choose {C : Submodule F (ι → F)} {f1 : ι → F} {e k : ℕ}
    (hkn : k + 2 * e ≤ Fintype.card ι)
    (hd : Fintype.card ι + 1 ≤ minDistance C + k) :
    (decodingList C f1 e).ncard ≤ (Fintype.card ι).choose (2 * e)

theorem mds_decodingList_ncard_le {C : Submodule F (ι → F)} {f1 : ι → F} {e k : ℕ}
    (hd : minDistance C = Fintype.card ι - k + 1)
    (hk : Module.finrank F C = k)
    (hreg : 2 * e ≤ Fintype.card ι - k) :
    (decodingList C f1 e).ncard ≤ (Fintype.card ι).choose (2 * e)
```

The mission's suggested name was `mds_decodingList_card_le` with `(…).toFinset.card`; the
`Set.ncard` form is used as the primary statement because it needs no `Fintype F` and no
decidability instance, and `mds_decodingList_toFinset_card_le` provides the requested `Finset`
shape. `IsMDS` does not exist in the project, so the exact equivalent hypotheses
`minDistance C = n − k + 1` and `Module.finrank F C = k` are used, as instructed.

## 6. Dependency graph

```
Mathlib
 ├─ Nat.choose_le_succ_of_lt_half_left, Nat.choose_symm
 │     └── choose_le_choose_of_le_of_add_le ─────────────┐
 ├─ Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose
 │     └── card_le_choose_of_isAntichain ── ncard_le_choose_of_isAntichain
 └─ Finset.exists_subset_card_eq ── pickSubset ─ pickSubset_subset, card_pickSubset
                                                          │
SupportGeometry.lean (already verified)                   │
 ├─ injOn_errorSupport ── ncard_decodingList_eq_ncard_image, finite_decodingList
 ├─ isAntichain_errorSupport                              │
 │     └── decodingList_ncard_le_choose_of_four_mul_le  (Branch A)
 └─ card_errorSupport_le_of_mem_decodingList              │
Hamming.lean                                              │
 ├─ minDistance_le_hammingDistance ── eq_of_agree_on_card_eq
 └─ card_agreementSet_add_hammingDistance                 │
        └── decodingList_ncard_le_choose_dim  (Branch B) ──┤
                                                           ▼
                                            decodingList_ncard_le_choose  (P1)
                                                    ├── mds_decodingList_ncard_le
                                                    │        └── mds_decodingList_toFinset_card_le
                                                    └── reedSolomon_decodingList_ncard_le
                                                             (+ ReedSolomon.reedSolomon_minDistance)
```

No project file outside `Hamming.lean`, `SupportGeometry.lean` and (for the instance only)
`ReedSolomon.lean` is used. No Johnson machinery, no κ-charging, no MCA definition, no
Rédei–Szőnyi input.

## 7. Weakest hypotheses

| ingredient | needed? | where |
| --- | --- | --- |
| linearity of `C` | **yes** | both branches, through `minDistance_le_hammingDistance` on `q₁ − q₂` |
| minimum distance | **yes** | Branch A via `2e < d`; Branch B via `d ≥ n−k+1` |
| `d = n−k+1` (equality) | **no** | only `d ≥ n−k+1` is used |
| `dim C = k` | **no** | not used by `decodingList_ncard_le_choose`; in the MDS-shaped corollary it serves only to give `k ≤ n` |
| `2e ≤ n−k` | **yes** | supplies `2e < d` (Branch A) and `|agreement| ≥ k` (Branch B) |
| `4e ≤ n` | branch-local | Branch A only |
| `f₁ ∉ C` | **no** | `f₁` is arbitrary |
| field size, RS structure, `Fintype F` | **no** | not used (only the `toFinset` restatement wants `Fintype F`) |

So the honest general theorem is: *a linear code whose minimum distance satisfies
`d ≥ n − k + 1` for some parameter `k` with `k + 2e ≤ n` has `|L(f₁,2e)| ≤ C(n,2e)` for every
received word `f₁`.* This is Phase 7 of the wider plan answered in the affirmative for the two
listed weakenings: only the distance inequality (not equality) and no dimension hypothesis. Note
that by the Singleton bound `d ≥ n−k+1` together with `dim C = k` forces `d = n−k+1` exactly, so
the weaker hypothesis is genuinely weaker only when the dimension is not pinned down.

## 8. Build result

* `lake build RequestProject.Root.CodingTheory.MDSListSize` — succeeds, **zero warnings**.
* `lake build` (full default target, 8031 jobs) — `Build completed successfully`.
* `rg -n "sorry|admit|axiom|native_decide" RequestProject/Root/CodingTheory/MDSListSize.lean` —
  the only match is the sentence "No axioms are introduced and there is no `sorry`" in the
  file header.
* The new file is imported by `RequestProject/Main.lean`.

## 9. Axiom audit

`#print axioms` for all eleven new public declarations was added to `RequestProject/Main.lean`
and runs as part of the full build. Every one of

```
choose_le_choose_of_le_of_add_le          card_le_choose_of_isAntichain
ncard_le_choose_of_isAntichain            finite_decodingList
decodingList_ncard_le_choose_of_four_mul_le
eq_of_agree_on_card_eq                    decodingList_ncard_le_choose_dim
decodingList_ncard_le_choose              mds_decodingList_ncard_le
mds_decodingList_toFinset_card_le         reedSolomon_decodingList_ncard_le
```

reports exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
project-local axiom, no `@[implemented_by]`, no `native_decide`.

## 10. Occupancy theorem status

`m_x ≤ C(n−1, 2e−1)` — **not formalised, frozen** by the mission. Nothing about it entered the
Lean build. One observation recorded for the next mission and *not* used anywhere: the Branch-A
condition for occupancy is `2(2e−1) ≤ n−1`, i.e. `4e ≤ n+1`, which is *weaker* than `4e ≤ n`, so
the split for P2 can be taken at `4e ≤ n+1` rather than reusing the P1 split verbatim.

## 11. Projected-MCA theorem status

`|B| ≤ 2·C(n−1,2e−1) − 1` — **not formalised and not stated in Lean**, since it depends on P2 and
on the projected Rédei input, which is external. Unchanged from the previous report.

## 12. Equality / sharpness status

**Not formalised** (frozen). No sharpness example, no deep-hole statement, and no equality
characterisation entered the Lean build in this mission. The only sharpness-adjacent fact
recorded formally is the Reed–Solomon instantiation `reedSolomon_decodingList_ncard_le`, which
shows the hypotheses of P1 are satisfiable (so the theorem is not vacuous) but says nothing about
attainment.

## 13. Recommended next mission (exactly one)

**FORMAL MDS OCCUPANCY THEOREM** — prove
`m_x = #{ q ∈ L : x ∈ E(q) } ≤ C(n−1, 2e−1)` in the regime `2e ≤ n − k`, reusing
`ncard_le_choose_of_isAntichain` and `decodingList_ncard_le_choose_dim`. The new work is exactly
one lemma: the link family `F_x = { E \ {x} : E ∈ F, x ∈ E }` is an antichain in the Boolean
lattice on `ι \ {x}` with all members of size `≤ 2e−1`, plus the branch audit at `4e ≤ n+1`
noted in §10. Do not continue into Rédei.
