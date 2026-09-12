# MDS coordinate occupancy — formal report

**Outcome A.** The coordinate occupancy theorem

```
m_x ≤ C(n − 1, 2e − 1)
```

is formally proved in Lean, under exactly the hypotheses of the already-formalised list-size
theorem (`k + 2e ≤ n` and `n + 1 ≤ d(C) + k`), with **both branches** proved and their coverage
proved inside Lean. No `sorry`, no `admit`, no new axiom, no `native_decide`.

New module: `RequestProject/Root/CodingTheory/MDSOccupancy.lean`.
`SupportGeometry.lean` and `MDSListSize.lean` are **unchanged**.

---

## 1. Exact theorem

Setting (unchanged from `MDSListSize.lean`): `ι` a finite index type with `n = Fintype.card ι`,
`F` a field, `C : Submodule F (ι → F)` an arbitrary linear code, `f₁ : ι → F` an arbitrary
received word (not assumed to be a codeword),

```
E(q)   = errorSupport f₁ q      = { i : f₁ i ≠ q i }
L      = decodingList C f₁ e    = { q ∈ C : d(f₁, q) ≤ 2e }
```

New definitions:

```lean
def occupiedAt (C : Submodule F (ι → F)) (f1 : ι → F) (e : ℕ) (x : ι) : Set (ι → F) :=
  { q | q ∈ decodingList C f1 e ∧ x ∈ errorSupport f1 q }

noncomputable def coordinateMultiplicity (C : Submodule F (ι → F)) (f1 : ι → F) (e : ℕ)
    (x : ι) : ℕ := (occupiedAt C f1 e x).ncard
```

so `coordinateMultiplicity C f₁ e x = m_x = #{ q ∈ L : f₁ x ≠ q x }`
(`mem_occupiedAt` records the two equivalent descriptions).

**Main theorem.**

```lean
theorem coordinateMultiplicity_le_choose {C : Submodule F (ι → F)} {f1 : ι → F} {e k : ℕ}
    {x : ι} (he : 1 ≤ e) (hkn : k + 2 * e ≤ Fintype.card ι)
    (hd : Fintype.card ι + 1 ≤ minDistance C + k) :
    coordinateMultiplicity C f1 e x ≤ (Fintype.card ι - 1).choose (2 * e - 1)
```

**`e = 0` edge case, handled explicitly and not hidden in `Nat` subtraction.** For `e = 0` the
list consists of codewords at distance `0` from `f₁`, so no list element has a nonempty error
support:

```lean
theorem occupiedAt_eq_empty_of_e_zero : occupiedAt C f1 0 x = ∅
theorem coordinateMultiplicity_zero  : coordinateMultiplicity C f1 0 x = 0
```

Consequently the same inequality also holds with `he` deleted
(`coordinateMultiplicity_le_choose'`), because `m_x = 0` there; the truncated value
`2·0 − 1 = 0` plays no role in any argument.

---

## 2. Branch A — pointed antichain / LYM (`4e ≤ n + 1`)

Fix `x` and puncture: `F_x = { E(q).erase x : q ∈ L, x ∈ E(q) }`, a family of subsets of the
universe `{x}ᶜ`, which has `n − 1` elements.

1. **Injectivity.** `q ↦ E(q)` is injective on `L` (`injOn_errorSupport`, needs `2e < d`), and
   puncturing is injective on sets containing `x` (`eq_of_erase_eq_erase`). Hence
   `q ↦ E(q).erase x` is injective on `occupiedAt` (`injOn_erase_errorSupport`), so
   `m_x = |F_x|`.
2. **Antichain (Part IV audit).** The subtle step is that puncturing does *not* preserve
   incomparability in general families. Here it does, because every member of the family comes
   from a support containing `x`. Formalised as the reusable finite-set lemma

   ```lean
   theorem subset_of_erase_subset_erase (hx2 : x ∈ E2) (h : E1.erase x ⊆ E2.erase x) : E1 ⊆ E2
   ```

   Given `E(q₁).erase x ⊆ E(q₂).erase x` this yields `E(q₁) ⊆ E(q₂)`, hence
   `E(q₁) = E(q₂)` by `errorSupport_antichain`, hence equality of the punctured sets
   (`isAntichain_erase_errorSupport`).
3. **Sizes.** `x ∈ E(q)` and `|E(q)| ≤ 2e` give `|E(q).erase x| = |E(q)| − 1 ≤ 2e − 1`.
4. **LYM in the punctured universe.** `2·(2e − 1) ≤ n − 1` is exactly `4e ≤ n + 1`. The LYM
   infrastructure of `MDSListSize.lean` is reused, not duplicated: the only new ingredient is
   its *relative* form,

   ```lean
   theorem card_le_choose_of_isAntichain_subset {T : Finset α} {𝒜 : Finset (Finset α)} {t : ℕ}
       (hsub : ∀ s ∈ 𝒜, s ⊆ T) (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α)))
       (hsize : ∀ s ∈ 𝒜, s.card ≤ t) (ht : 2 * t ≤ T.card) : 𝒜.card ≤ T.card.choose t
   ```

   obtained from `card_le_choose_of_isAntichain` by transporting the family along
   `Finset.subtype (· ∈ T)` into the subtype `↥T` (whose cardinality is `|T|`), plus the
   `Set`/`ncard` adapter `ncard_le_choose_of_isAntichain_subset`.

With `T = {x}ᶜ`, `|T| = n − 1`, `t = 2e − 1` this gives
`coordinateMultiplicity_le_choose_of_four_mul_le`:

```
2e < d(C)  and  4e ≤ n + 1   ⟹   m_x ≤ C(n − 1, 2e − 1).
```

Note the threshold is genuinely *sharper* than the `4e ≤ n` split of the list-size theorem; it
was derived from the pointed LYM condition, not inherited.

---

## 3. Branch B — pointed information-set injection (`4e > n + 1`)

Hypotheses: `k + 2e ≤ n`, `n + 1 ≤ d(C) + k`.

For `q ∈ L`, `|agreementSet f₁ q| ≥ n − 2e ≥ k`, so the chosen `k`-subset
`pickSubset (agreementSet f₁ q) k` exists. **Pointedness enters here:** if `x ∈ E(q)` then
`x ∉ agreementSet f₁ q`, so the chosen `k`-subset is a `k`-subset of `{x}ᶜ`. The ambient
universe of the injection therefore drops from `n` to `n − 1`.

Injectivity is the information-set property already proved in `MDSListSize.lean`
(`eq_of_agree_on_card_eq`): two codewords agreeing on `k` coordinates coincide when
`d(C) ≥ n − k + 1`. Hence

```lean
theorem coordinateMultiplicity_le_choose_dim (hkn : k + 2 * e ≤ n) (hd : n + 1 ≤ minDistance C + k) :
    coordinateMultiplicity C f1 e x ≤ (n - 1).choose k
```

**Arithmetic audit of the binomial comparison** (the direction was checked, not assumed).
`C(n−1, k) ≤ C(n−1, 2e−1)` needs, by the unimodality lemma
`choose_le_choose_of_le_of_add_le` (`a ≤ b`, `a + b ≤ N` ⟹ `C(N,a) ≤ C(N,b)`), with
`N = n − 1`, `a = k`, `b = 2e − 1`:

* `k ≤ 2e − 1`: from `4e > n + 1`, i.e. `n ≤ 4e − 2`, and `k ≤ n − 2e`, we get
  `k ≤ 2e − 2 ≤ 2e − 1`. (There is one unit of slack; `k ≤ 2e − 1` is all that is used.)
* `k + (2e − 1) ≤ n − 1`, which is `k + 2e ≤ n`.

Both follow from the two standing hypotheses alone. **The global list bound `|L| ≤ C(n,2e)` is
not used in either branch**; the coordinate theorem does not factor through it.

---

## 4. Branch threshold and coverage

Split: `4e ≤ n + 1` (Branch A) versus `4e > n + 1` (Branch B) — exhaustive by trichotomy, and
performed inside the Lean proof of `coordinateMultiplicity_le_choose`. Each branch's extra
ingredient is derived there from `k + 2e ≤ n` and `n + 1 ≤ d(C) + k`:

* Branch A needs `2e < d(C)`: from `n + 1 ≤ d + k` and `k + 2e ≤ n`, `2e ≤ n − k < d`.
* Branch B needs `k ≤ 2e − 1`: shown above from `4e > n + 1` and `k + 2e ≤ n`.

---

## 5. Generality audit

The theorem holds at **exactly the generality of the list-size theorem P1**:

* arbitrary linear code `C` over an arbitrary field — no MDS property, no dimension hypothesis,
  no field-size hypothesis;
* arbitrary received word `f₁`, not assumed to be a codeword or a deep hole;
* only `k + 2e ≤ n` and `n + 1 ≤ d(C) + k`, with `k` a numerical parameter (never the dimension);
* `e ≥ 1` for the sharp form; `e = 0` is a separate trivial statement, and the combined
  statement `coordinateMultiplicity_le_choose'` needs no hypothesis on `e`.

The pointed argument needs **nothing stronger** than P1. Corollaries derived (not primary):
`mds_coordinateMultiplicity_le` (the `[n,k]` MDS shape `d = n−k+1`, `dim = k`, `2e ≤ n−k`) and
`reedSolomon_coordinateMultiplicity_le` (Reed–Solomon, via the project's exact minimum-distance
theorem — this also shows the hypotheses are satisfiable, i.e. the theorem is not vacuous).

---

## 6. Lean declarations (all in `Root.CodingTheory.SupportGeometry`)

| Declaration | Role |
|---|---|
| `subset_of_erase_subset_erase` | punctured antichain lemma (Part IV) |
| `eq_of_erase_eq_erase` | punctured injectivity |
| `card_le_choose_of_isAntichain_subset` | lower-half LYM relative to an ambient finset |
| `ncard_le_choose_of_isAntichain_subset` | `Set`/`ncard` form of the same |
| `occupiedAt`, `mem_occupiedAt`, `occupiedAt_subset` | definition + API |
| `coordinateMultiplicity` | `m_x` |
| `occupiedAt_eq_empty_of_e_zero`, `coordinateMultiplicity_zero` | `e = 0` edge case |
| `injOn_erase_errorSupport` | injectivity of the punctured support map |
| `isAntichain_erase_errorSupport` | punctured antichain |
| `coordinateMultiplicity_le_choose_of_four_mul_le` | **Branch A** |
| `coordinateMultiplicity_le_choose_dim` | **Branch B** |
| `coordinateMultiplicity_le_choose` | **main theorem** (`e ≥ 1`) |
| `coordinateMultiplicity_le_choose'` | main theorem, all `e` |
| `mds_coordinateMultiplicity_le` | MDS corollary |
| `reedSolomon_coordinateMultiplicity_le` | Reed–Solomon corollary |
| `occupiedAt_eq_coe_filter`, `coordinateMultiplicity_eq_card_filter` | `Finset` presentation |
| `sum_coordinateMultiplicity`, `sum_coordinateMultiplicity_le` | consistency identity (Part VIII) |
| `ncard_image_coord_le_succ_coordinateMultiplicity`, `ncard_image_coord_le` | coordinate projection (Part X) |

**Dependencies.** Only `Mathlib`, `SupportGeometry.lean` (`errorSupport`, `decodingList`,
`injOn_errorSupport`, `errorSupport_antichain`, `card_errorSupport_le_of_mem_decodingList`) and
`MDSListSize.lean` (`choose_le_choose_of_le_of_add_le`, `card_le_choose_of_isAntichain`,
`finite_decodingList`, `pickSubset`, `card_pickSubset`, `pickSubset_subset`,
`eq_of_agree_on_card_eq`), plus `Hamming.lean` / `ReedSolomon.lean` transitively. Nothing in
those files was modified.

---

## 7. Build and axiom audit

* `lake build RequestProject.Root.CodingTheory.MDSOccupancy` — succeeds, **zero warnings**.
* `lake build` (full default target, 8209 jobs) — succeeds.
* `rg -n "sorry|admit|axiom|native_decide" RequestProject/Root/CodingTheory/MDSOccupancy.lean`
  — no hits other than the prose sentence "No axioms are introduced and there is no `sorry`"
  in the module docstring.
* `#print axioms` on every new declaration (added at the end of `RequestProject/Main.lean`)
  reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` anywhere in the build
  output.

---

## 8. Equality / sharpness status

**Not formalised** (deliberately deferred, as instructed). What is recorded informally in
`MDS_SUPPORT_ANTICHAIN_AUDIT.md` — that both `|L| = C(n,2e)` and `m_x = C(n−1,2e−1)` are
attained iff `2e = n − k` and `f₁` is a deep hole, with strict inequality inside the regime —
remains an *unformalised* claim; nothing in this mission depends on it. The formal statement is
the inequality only. Deep-hole existence was not touched.

---

## 9. Coordinate-projection corollary status

**Formalised** (it was inexpensive):

```lean
theorem ncard_image_coord_le_succ_coordinateMultiplicity (hd : 2 * e < minDistance C) :
    ((fun q => q x) '' decodingList C f1 e).ncard ≤ 1 + coordinateMultiplicity C f1 e x

theorem ncard_image_coord_le (hkn : k + 2 * e ≤ n) (hd : n + 1 ≤ minDistance C + k) :
    ((fun q => q x) '' decodingList C f1 e).ncard ≤ 1 + (n - 1).choose (2 * e - 1)
```

i.e. `|λ_x(L)| ≤ 1 + m_x ≤ 1 + C(n−1, 2e−1)`: list elements agreeing with `f₁` at `x`
contribute the single value `f₁ x`, occupied ones at most one further value each. No Rédei
input is used.

The consistency identity of Part VIII is also formalised as a sanity check,
`Σ_x m_x = Σ_{q ∈ L} |E(q)|` and hence `Σ_x m_x ≤ 2e·|L|`; it is *not* used in the proof of the
occupancy theorem.

---

## 10. Exact boundary before Rédei

Formal, inside Lean, `p`-free:

```
support geometry  ⟹  |L| ≤ C(n, 2e)          (MDSListSize.lean)
                  ⟹  m_x ≤ C(n−1, 2e−1)      (MDSOccupancy.lean, this mission)
                  ⟹  |λ_x(L)| ≤ 1 + C(n−1, 2e−1)
```

Still **outside** Lean:

* the witness slope space `V_W`, the admissibility statement
  `x ∈ supp V_W ⟹ λ_x ≠ 0 on V_W`, and the projected point set `S_{λ_x}` — `V_W` is not
  formalised, so, per the mission's Part XI, no witness-geometry framework was introduced;
* the definition `M*_L = min over admissible λ of |λ(L)|` and hence the corollary
  `M*_L ≤ 1 + C(n−1, 2e−1)`;
* the Rédei–Szőnyi direction theorem, and with it
  `|B| ≤ 2·C(n−1, 2e−1) − 1` for the non-collinear arm.

Those three items are mathematical statements recorded in earlier reports; none of them is
claimed as formally verified here.

---

## 11. Recommended next mission (exactly one)

**Formal projected Rédei bridge, conditional form.** Formalise `V_W`, the coordinate functional
`λ_x` and the projected point set `S_{λ_x}`, prove the single implication
`x ∈ supp V_W ⟹ λ_x` is admissible (nonzero on `V_W`), define `M*_L` and prove
`M*_L ≤ 1 + C(n−1, 2e−1)` from the theorem of this mission; then state the *conditional* Lean
theorem `[Rédei–Szőnyi lower bound] ⟹ |B| ≤ 2·C(n−1, 2e−1) − 1`, taking the Rédei–Szőnyi
direction theorem as an explicit hypothesis of the statement (never as an axiom). Formalising
Rédei–Szőnyi itself is a separate, later mission.
