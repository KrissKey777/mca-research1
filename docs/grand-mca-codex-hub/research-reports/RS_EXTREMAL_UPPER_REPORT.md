# Universal large-Γ RS rigidity and the extremal target `M_C(t)` — research report

## PRINCIPAL STATUS

### `RS_STRUCTURE_THEOREM`

A universal, source-exact, quantitative large-Γ rigidity theorem for the **official** MCA
challenge set is proved, together with the extremal target `M_C(t)` and its exact bridge to
the official `ε_mca`, a sharpened universal reduction, and a stability (near-extremiser)
theorem whose deployed constant is sharp.

It is **not** `RS_EXTREMAL_BOUND`: the deployed inequality `M_C(1118208) ≤ B*` is *not* proved
here. It is not `RS_COUNTERCONSTRUCTION` / `DEPLOYED_COUNTEREXAMPLE`: no official construction
refuting the new statements was found (one existing official construction is used, and it
confirms sharpness rather than refuting anything). Section 7 below gives the honest
quantitative usefulness check demanded by §10 of the task.

---

## 0. Frozen deployed instance, and how it enters the statements

```
p = 2^31 − 2^24 + 1 = 2130706433      (already present in the project: KoalaBear modules)
K = F_{p^6},  H = μ_{2^21} ⊆ K^×,  n = |H| = 2097152
C = RS[K, H, k],  k = 1048576
t = 1118208,  e = n − t = 978944,  w = t − k = 69632,  B* = 274980728111395087
```

Verified arithmetic (Lean, `Root.CodingTheory.deployed_parameters`):

```
2097152 = 1048576 + 978944 + 69632         (n = k + e + w)
1118208 = 2097152 − 978944 = 1048576 + 69632   (t = n − e = k + w)
2·1118208 − 2097152 = 2·69632                  (2t − n = 2w = 139264)
2027520 = 1048576 + 978944                     (k + e)
```

All new theorems are stated for an arbitrary field `F` with `Fintype F`, an arbitrary
evaluation domain `D : Finset F`, and arbitrary `k, e`. The deployed instance is the special
case `F = K`, `D = H`, `|D| = 2097152`, `k = 1048576`, `e = 978944`; the deployed corollaries
below are stated with exactly these literals.

## 1. The official challenge set is used verbatim

Source (`RequestProject/Root/CodingTheory/MCA.lean`), unchanged:

```lean
def IsCloseOn (k : ℕ) (S : Finset ↥D) (f : ↥D → F) : Prop :=
  ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x ∈ S, f x = p.eval (x : F)

def LineCloseOn (k : ℕ) (S : Finset ↥D) (f₀ f₁ : ↥D → F) : Prop :=
  ∀ γ : F, IsCloseOn k S (lineComb f₀ f₁ γ)

def IsBad (k e : ℕ) (f₀ f₁ : ↥D → F) (γ : F) : Prop :=
  ∃ S : Finset ↥D, D.card ≤ S.card + e ∧ IsCloseOn k S (lineComb f₀ f₁ γ) ∧
    ¬ LineCloseOn k S f₀ f₁

noncomputable def badSet (k e : ℕ) (f₀ f₁ : ↥D → F) : Finset F := univ.filter (IsBad k e f₀ f₁)
```

`Γ_C(f₀,f₁;t) = badSet k e f₀ f₁` with `t = |D| − e`; the co-size convention
`|D| ≤ |S| + e` is the source's, i.e. the agreement threshold is the **closed** condition
`|S| ≥ t`.

Nothing below starts from residual children, a canonical anchor, a selected support family,
`classLoad`, `capturedChildCost` or projective classes. Where a simultaneous choice of
windows/codewords is needed, the family is an explicit universally quantified parameter
(`S : F → Finset ↥D` together with the official equations), so no witness selector can move
the statement — this is the "quantify over every valid simultaneous selection" option of §1
of the task.

## 2. The extremal target and the exact bridge

New definition (`RequestProject/Root/CodingTheory/ExtremalMCA.lean`):

```lean
noncomputable def mcaMax (k e : ℕ) (D : Finset F) : ℕ :=
  Finset.univ.sup fun q : (↥D → F) × (↥D → F) => (badSet k e q.1 q.2).card
```

i.e. `mcaMax k e D = M_C(t) = max_{f₀,f₁} |Γ_C(f₀,f₁;t)|`, `t = |D| − e`.

* `card_badSet_le_mcaMax`, `exists_line_card_badSet_eq_mcaMax` — the max is an upper bound and
  is attained.
* `mcaMax_le_iff : mcaMax k e D ≤ B ↔ ∀ f₀ f₁, (badSet k e f₀ f₁).card ≤ B`.
* **Exact bridge** `epsMCAmax_eq_mcaMax_div : epsMCAmax k e D = (mcaMax k e D : ℝ)/|F|`.
  The official `epsMCA` is `probOf (uniform F) (badSet …)`, i.e. `#Bad/|F|` — a plain rational
  quotient with **no rounding**; the official maximum `epsMCAmax` is a `sup'` over all lines.
  Hence the threshold convention transfers verbatim, and
  `epsMCAmax_le_div_iff : epsMCAmax k e D ≤ (B:ℝ)/|F| ↔ mcaMax k e D ≤ B` — closed inequality
  on both sides.
* **Deployed** `deployed_security_iff`: at `k = 1048576`, `e = 978944` the official claim
  `ε_mca^max ≤ B*/|K|` is *equivalent* to `∀ f₀ f₁, #Γ ≤ B*`, i.e. to `M_C(1118208) ≤ B*`.

This is the extremal quantity to control; `T`, residual costs and `classLoad` are not used.

## 3. The new structural results

Let `W(q₀,q₁) = polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁` be the **joint** agreement set of
the pair `(f₀,f₁)` with a pair of degree-`<k` words (the exact correlated-agreement set of the
pencil), and let a *window* of a challenge `γ` be any `S` with `|D| ≤ |S| + e` on which the
official equation `f₀ + γ f₁ = p_γ` holds for a degree-`<k` word `p_γ`.

### 3.1 Window-overlap ceiling (the rigidity theorem)

**`card_badSet_le_of_wide_overlap`** — if *two* distinct official challenges have windows with
`k + e ≤ |S₁ ∩ S₂|`, then the affine pencil `q₀ + γ q₁` spanned by their two official
equations explains **every** official challenge on its own window, hence `#Γ ≤ e + 1`.

**`card_inter_lt_of_card_badSet_gt`** (contrapositive, the universal large-Γ statement):

> `|Γ_C(f₀,f₁;t)| > e + 1` ⟹ for every two distinct official challenges and *every* valid
> choice of their windows and degree-`<k` words, `|S₁ ∩ S₂| < k + e`.

Combined with the unconditional `|S₁ ∩ S₂| ≥ 2t − n`, a large-Γ configuration is pinned into
the two-sided window `2t − n ≤ |S ∩ S'| < k + e`.

**`card_badSet_le_of_wide_windows`** — numerical form: `|D| + k + e ≤ |S₁| + |S₂|` suffices.
Specialising to the guaranteed sizes `|S| ≥ |D| − e` gives `k + 3e ≤ |D| ⟹ #Γ ≤ e + 1`, i.e.
the theorem strictly generalises the project's unique-decoding row
(`card_badSet_le_succ_radius_of_le`): the hypothesis is now on the *witnesses*, not on the
parameters, so it also applies in regimes where `k + 3e > |D|`.

*Mechanism (no forbidden ingredient):* on `S₁ ∩ S₂` the two official equations determine
`(f₀,f₁) = (q₀,q₁)` pointwise; for any third challenge the deviation `p_γ − (q₀ + γ q₁)` is a
degree-`<k` word vanishing on `(S₁ ∩ S₂) ∩ S_γ`, a set of size `≥ |S₁ ∩ S₂| − e ≥ k`, so it
vanishes identically. Then the pencil bound `card_badSet_le_of_pencil` applies. No support
counting, no disjointness assumption, no Johnson/sunflower input, no ledger.

### 3.2 Sharpness (cheap falsification test, §5 of the task)

`ExtremalMCASharpness.wide_overlap_threshold_sharp` runs the ceiling against an exact official
RS construction already in the project (`UniqueDecodingHoleWitness`: `F₁₃`, `D = {0,…,7}`,
`k = 3`, `e = 2`, four bad challenges): two of its official windows meet in exactly
`k + e − 1 = 4` positions while `#Γ = 4 > 3 = e + 1`. So the threshold `k + e` is **optimal** —
it cannot be lowered by one — and the rigidity conclusion is attained, not vacuous.

**`not_window_subset`** — a further unconditional consequence of the official badness clause:
the window of a bad challenge is never contained in the window of another challenge, i.e. the
official windows of a line form an **antichain** (otherwise the pencil spanned by the two
official equations would be a correlated-agreement pair on the whole of `S₁`). No cardinality
hypothesis is used.

### 3.3 Pencil-class stability (near-extremiser structure, §7 of the task)

**`card_jointAgreement_ge_of_pencil_family`** — if one affine pencil explains `m` distinct
challenges, each on a window of co-size `≤ e`, then

```
m · (|D| − e) ≤ (m − 1) · |W(q₀,q₁)| + |D|,      i.e.   |W| ≥ (m·t − n)/(m − 1).
```

No badness and no degree hypothesis is needed: the windows of a common pencil form a sunflower
with core `W`, and the petals are disjoint. Consequences: `m = 2` recovers `|W| ≥ 2t − n`;
`m → e + 1` (the maximum permitted by the pencil bound) drives `|W|` up to `t − 1`, i.e. to
*one position short of correlated agreement*.

**Deployed, exactly sharp** (`deployed_extremal_pencil_one_short`): a pencil class of the
extremal size `e + 1 = 978945` at `n = 2097152`, `e = 978944` forces

```
|W| ≥ 1118207 = t − 1,   and   978944 · 1118207 = 978945 · 1118208 − 2097152 (equality).
```

So the extremal pencil configuration at the target row `t = 1118208` is precisely the
"one-short" configuration, and it is *exactly* correlated agreement at the neighbouring row
`t − 1 = 1118207`. This is the structural reason the two neighbouring rows behave differently
at the level of a single pencil; it does **not** by itself compute `M_C` at either row.

### 3.4 Sharpened universal reduction (constant `|D| → e`)

**`card_shiftFibre_erase_le`** — the deviation position that pins a challenge inside the fibre
of a fixed shifted codeword pair can never lie inside the anchor's window; hence the fibre,
after removing the anchor, lives in a set of at most `e` positions (the previous bound was
`|D|`).

**`card_badSet_le_radius_mul_card_rsList`** — `#Γ ≤ 1 + e · #rsList(f₁, 2e)`, improving
`card_badSet_le_mul_card_rsList` (`1 + |D| · #rsList`) by the factor `|D|/e = 2.142…`.
Extremal form: `mcaMax_le_one_add_radius_mul_rsListMax : mcaMax k e D ≤ 1 + e · rsListMax D k (2e)`.

Deployed gate (`deployed_mcaMax_le_of_rsListMax`): a list bound
`rsListMax D 1048576 1957888 ≤ 280895258678` now suffices for `M_C(1118208) ≤ B*`; the
unlocalised reduction required `≤ 131121028953`.

## 4. Load-bearing declarations (name / file / hypotheses / axioms)

Build commands actually run (only the new modules were built):

```
lake build RequestProject.Root.CodingTheory.ExtremalMCA            → success (8041 jobs)
lake build RequestProject.ExtremalMCAAxiomAudit                    → success (8042 jobs)
lake build RequestProject.Root.CodingTheory.ExtremalMCASharpness   → success (8045 jobs)
lake build RequestProject.ExtremalMCASharpnessAxiomAudit           → success (8046 jobs)
```

No `sorry`, no `axiom`, no `@[implemented_by]`, no warnings. Every declaration listed below
was `#print axioms`-audited; each list is a subset of `{propext, Classical.choice, Quot.sound}`
(`deployed_parameters` needs only `propext`). Logs: `analysis/extremal_mca/`.

| # | declaration | file | hypotheses | scope |
|---|---|---|---|---|
| 1 | `mcaMax` | `Root/CodingTheory/ExtremalMCA.lean` | `[Field F] [DecidableEq F] [Fintype F]` | definition of `M_C(t)` |
| 2 | `card_badSet_le_mcaMax` | idem | none | `#Γ ≤ M_C` for every line |
| 3 | `exists_line_card_badSet_eq_mcaMax` | idem | none | the max is attained |
| 4 | `mcaMax_le_iff` | idem | none | extremal ↔ universal form |
| 5 | `epsMCAmax_eq_mcaMax_div` | idem | none | **exact bridge** `ε_mca^max = M_C/|F|` |
| 6 | `epsMCAmax_le_div_iff` | idem | none | closed-threshold equivalence, no rounding |
| 7 | `card_shiftFibre_erase_le` | idem | `q₀,q₁ ∈ RS`, anchor window of co-size `≤ e` | anchor-localised fibre bound `≤ e` |
| 8 | `card_badSet_le_radius_mul_card_rsList` | idem | none | `#Γ ≤ 1 + e·#rsList(f₁,2e)` |
| 9 | `rsListMax`, `card_rsList_le_rsListMax` | idem | none | list-size maximum |
| 10 | `mcaMax_le_one_add_radius_mul_rsListMax` | idem | none | extremal form of 8 |
| 11 | `card_badSet_le_of_wide_overlap` | idem | `1 ≤ k`, `k ≤ |D|`, official equations for two distinct challenges, `k + e ≤ |S₁ ∩ S₂|` | **rigidity**: `#Γ ≤ e + 1` |
| 12 | `card_inter_lt_of_card_badSet_gt` | idem | as 11 plus `e + 1 < #Γ` | **universal large-Γ conclusion** `|S₁∩S₂| < k+e` |
| 13 | `card_badSet_le_of_wide_windows` | idem | as 11 with `|D|+k+e ≤ |S₁|+|S₂|` | numerical form |
| 13b | `not_window_subset` | idem | official equations for two distinct challenges, `¬ LineCloseOn S₁` | **antichain**: `S₁ ⊈ S₂` |
| 14 | `card_jointAgreement_ge_of_pencil_family` | idem | explicit window family, official equations for one pencil | **stability** `m·(n−e) ≤ (m−1)|W| + n` |
| 15 | `deployed_parameters` | idem | none | frozen arithmetic |
| 16 | `deployed_security_iff` | idem | none | deployed claim ↔ `M_C(1118208) ≤ B*` |
| 17 | `deployed_narrow_overlap` | idem | `|D| = 2097152` | deployed dichotomy `#Γ ≤ 978945` or all overlaps `< 2027520` |
| 18 | `deployed_extremal_pencil_one_short` | idem | `|D| = 2097152`, class size `978945` | `|W| ≥ 1118207 = t − 1` (sharp) |
| 19 | `deployed_mcaMax_le_of_rsListMax` | idem | `rsListMax D 1048576 1957888 ≤ 280895258678` | conditional `M_C ≤ B*` |
| 20 | `HoleWitness.card_inter_Sh`, `HoleWitness.wide_overlap_threshold_sharp` | `Root/CodingTheory/ExtremalMCASharpness.lean` | none | ceiling `k+e` is optimal |

Exact signatures are in the source files (each carries a full docstring).

## 5. What was tested against exact official examples

* **Strict unique-decoding hole witness** (`F₁₃`, `n = 8`, `k = 3`, `e = 2`, `#Γ = 4`):
  survives, and shows the ceiling constant `k + e` is optimal (§3.2). Note the four windows of
  that witness pairwise meet in exactly `k + e − 1 = 4` positions — the rigidity conclusion is
  saturated by an existing official construction.
* **Two-challenge / overlapping-window configurations**: the ceiling reduces to
  `|W| ≥ 2t − n` (`m = 2` case of §3.3), consistent with `correlated_agreement_of_two`.
* **Extremal pencil class** (`m = e + 1`): the stability bound is an exact equality at the
  deployed numbers, so no slack was hidden.
* Residual-ledger independence models were *not* used as evidence for or against anything.

## 6. Barriers re-confirmed (not reopened)

The route "bound `M_C` through pairs of challenges" is already known in this project to be
confined to unique decoding (`DirectionListReduction.pairwise_route_within_unique_decoding`).
The new ceiling is a pair-based invariant too, and the numbers confirm the barrier: an
averaging bound gives some pair with `|S ∩ S'| ≳ t²/n = 596180`, comfortably below the ceiling
`k + e − 1 = 2027519`, so the ceiling never contradicts a large-Γ configuration at the
deployed row. Sunflower/Johnson/support-partition/ledger arguments were not used.

## 7. Quantitative usefulness check at `n = 2097152, k = 1048576, t = 1118208` (§10)

1. **Does it prove `M_C(t) ≤ B*`?** **No.** `card_badSet_le_of_wide_overlap` needs an overlap
   `≥ 2027520`, which is not forced by the parameters (guaranteed overlap is only
   `2t − n = 139264`).
2. **Does it reduce every hypothetical `M_C(t) > B*` witness to a narrow class?** **Partially,
   and unconditionally.** Any witness with `#Γ > 978945` has *all* pairwise official window
   overlaps in the exact band `139264 ≤ |S ∩ S'| ≤ 2027519`, no two windows are nested, and
   every pencil class has at most `978945` members with joint agreement
   `|W| ≥ (m·1118208 − 2097152)/(m − 1)`. This is a genuine narrowing but not a finite family.
3. **Quantitatively useful descent?** **No** descent is claimed; the stability bound is a
   one-step structural inequality, not a recursion.
4. **Does it explain the adjacent-row boundary?** **Partially.** At the level of a *single*
   pencil the answer is exact: the extremal class size `e + 1` forces `|W| ≥ t − 1`, which is
   correlated agreement exactly at `t − 1 = 1118207` and one short at `t = 1118208`. This is
   the one-short phenomenon in its sharpest form, but it constrains one pencil, not `M_C`.
5. **Numerically too weak for the deployed row?** For the *upper bound* on `M_C(1118208)`:
   yes, as stated in 1. The improvements that are numerically real at the deployed row are the
   relaxed list gate `280895258678` (was `131121028953`) and the unconditional dichotomy
   `#Γ ≤ 978945 ∨ (all overlaps < 2027520)`.

## 8. The one exact structure gate that remains

```
|Γ_C(f₀,f₁;1118208)| > 978945
   ⟹  the official windows admit ≥ ⌈(#Γ − 1)/978944⌉ distinct affine pencils through any
       fixed challenge, each with joint agreement |W| ≥ 139264 and all pairwise overlaps
       < 2027520.
```

Closing the deployed row is exactly bounding the **number of distinct pencil directions**
through one challenge by `280895258678`; equivalently the joint (correlated) `2e`-list of the
line. The cheapest exact falsification test for any proposed bound on that number is the
`F₁₃` hole witness above (4 challenges, 4 distinct pencils, overlap exactly `k + e − 1`), and
then the two-class official examples with `|W| = 2t − n`.

## 9. Files

* `RequestProject/Root/CodingTheory/ExtremalMCA.lean` (new, 19 declarations)
* `RequestProject/Root/CodingTheory/ExtremalMCASharpness.lean` (new, 2 declarations)
* `RequestProject/ExtremalMCAAxiomAudit.lean`, `RequestProject/ExtremalMCASharpnessAxiomAudit.lean`
* `analysis/extremal_mca/BUILD_AND_AXIOMS.log`, `…_SHARPNESS.log`, `AXIOMS.txt`

All additions are purely additive; no existing file was modified.
