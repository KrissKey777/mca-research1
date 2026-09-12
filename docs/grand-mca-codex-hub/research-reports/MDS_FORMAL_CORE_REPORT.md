# MDS FORMAL CORE — REPORT

**Mission.** Formalise, in Lean, the *general* support core settled in
`MDS_SUPPORT_ANTICHAIN_AUDIT.md`: for an arbitrary linear code `C` with `2e < d(C)`, support
injectivity, the union law and the antichain property on the radius-`2e` decoding list.
Everything MDS-specific and everything Rédei-specific was explicitly frozen.

**Outcome.** The general core is formalised and compiles, with no `sorry`, no `admit`, no new
axiom. The mission stop condition reached is the one for the general core (Phases 1–3 of the
hierarchy plus the packing form); Phases 4–8 were **not** entered, per the freeze. Section 7
below answers the specific question the mission raised about `|L| ≤ C(n,2e)`, and the answer is
substantive: **it does not follow from the antichain property alone.**

---

## 1. Exact theorem statements formalised

New file: `RequestProject/Root/CodingTheory/SupportGeometry.lean`
(namespace `Root.CodingTheory.SupportGeometry`).

Ambient setting throughout:
`ι` a finite index type with `DecidableEq`, `F` a field with `DecidableEq`,
`C : Submodule F (ι → F)` an arbitrary linear code, `f1 : ι → F` an arbitrary received word
(**not** assumed to be a codeword), `e : ℕ`.

### 1.1 Definitions

```lean
def errorSupport (f1 q : ι → F) : Finset ι :=
  Finset.univ.filter fun i => f1 i ≠ q i

def decodingList (C : Submodule F (ι → F)) (f1 : ι → F) (e : ℕ) : Set (ι → F) :=
  { q | q ∈ C ∧ hammingDistance f1 q ≤ 2 * e }
```

with `card_errorSupport : (errorSupport f1 q).card = hammingDistance f1 q` (definitional).

### 1.2 Phase 1 — small-support uniqueness (the engine)

```lean
theorem eq_of_errorSupport_subset_of_card_lt_minDistance
    {C : Submodule F (ι → F)} {f1 : ι → F} {S : Finset ι}
    (hS : S.card < minDistance C) {q1 q2 : ι → F} (hq1 : q1 ∈ C) (hq2 : q2 ∈ C)
    (h1 : errorSupport f1 q1 ⊆ S) (h2 : errorSupport f1 q2 ⊆ S) :
    q1 = q2
```

Proof: `q1 − q2 ∈ C`, its support lies in `E(q1) ∪ E(q2) ⊆ S`, so a nonzero difference would
have weight `≤ |S| < d(C)`.

### 1.3 Phase 2 — support injectivity

```lean
theorem injective_errorSupport
    (hd : 2 * e < minDistance C)
    (hq1 : q1 ∈ decodingList C f1 e) (hq2 : q2 ∈ decodingList C f1 e)
    (hsupp : errorSupport f1 q1 = errorSupport f1 q2) : q1 = q2

theorem injOn_errorSupport (hd : 2 * e < minDistance C) :
    Set.InjOn (fun q => errorSupport f1 q) (decodingList C f1 e)

theorem subsingleton_of_errorSupport_eq
    (hS : S.card < minDistance C) (hq1 : q1 ∈ C) (hq2 : q2 ∈ C)
    (h1 : errorSupport f1 q1 = S) (h2 : errorSupport f1 q2 = S) : q1 = q2
```

`subsingleton_of_errorSupport_eq` is the requested "at most one `q ∈ C` realises a fixed support
`S` with `|S| < d`" statement. **No surjectivity onto arbitrary supports is claimed** anywhere:
nothing in the file asserts that a given `S` *is* realised.

Consequently, on the radius-`2e` list the four notions

```
support  ↔  error vector  ↔  codeword  ↔  list element
```

are in bijection: the error vector is `f1 − q`, so codeword ↔ error vector is a bijection by
construction, and `injOn_errorSupport` gives the remaining leg support ↔ codeword.

### 1.4 Phase 3 — union law (primary) and antichain (corollary)

```lean
theorem minDistance_le_card_union_errorSupport (f1 : ι → F)
    (hq1 : q1 ∈ C) (hq2 : q2 ∈ C) (hne : q1 ≠ q2) :
    minDistance C ≤ (errorSupport f1 q1 ∪ errorSupport f1 q2).card

theorem union_errorSupport_ge_minDist
    (hd : 2 * e < minDistance C)
    (hq1 : q1 ∈ decodingList C f1 e) (hq2 : q2 ∈ decodingList C f1 e) (hne : q1 ≠ q2) :
    minDistance C ≤ (errorSupport f1 q1 ∪ errorSupport f1 q2).card

theorem card_inter_errorSupport_le (f1 : ι → F)
    (hq1 : q1 ∈ C) (hq2 : q2 ∈ C) (hne : q1 ≠ q2) :
    (errorSupport f1 q1 ∩ errorSupport f1 q2).card + minDistance C
      ≤ (errorSupport f1 q1).card + (errorSupport f1 q2).card

theorem card_inter_agreement_le (f1 : ι → F)
    (hq1 : q1 ∈ C) (hq2 : q2 ∈ C) (hne : q1 ≠ q2) :
    (agreementSet f1 q1 ∩ agreementSet f1 q2).card + minDistance C ≤ Fintype.card ι
```

The last two are the intersection and the agreement/packing forms; they are stated with `+` on
the left rather than truncated `ℕ`-subtraction, so that no information is lost.

```lean
theorem errorSupport_antichain
    (hd : 2 * e < minDistance C)
    (hq1 : q1 ∈ decodingList C f1 e) (hq2 : q2 ∈ decodingList C f1 e)
    (hsub : errorSupport f1 q1 ⊆ errorSupport f1 q2) :
    errorSupport f1 q1 = errorSupport f1 q2

theorem eq_of_errorSupport_subset (…same hypotheses…) : q1 = q2

theorem isAntichain_errorSupport (hd : 2 * e < minDistance C) :
    IsAntichain (· ⊆ ·) ((fun q => errorSupport f1 q) '' decodingList C f1 e)
```

`isAntichain_errorSupport` is the Mathlib-shaped form, deliberately produced so that the
`Mathlib.Combinatorics.SetFamily.LYM` API can be applied to it later without an adapter.

---

## 2. Theorem dependency graph

```
Hamming.lean : minDistance_le_hammingDistance
        │
        ├── filter_ne_subset_union_errorSupport
        │        └── hammingDistance_le_card_union_errorSupport
        │                 ├── hammingDistance_le_card_of_errorSupport_subset
        │                 └── minDistance_le_card_union_errorSupport   (union law, general)
        │                          ├── union_errorSupport_ge_minDist   (mission shape)
        │                          ├── card_inter_errorSupport_le
        │                          └── card_inter_agreement_le
        │
        └── eq_of_errorSupport_subset_of_card_lt_minDistance           (Lemma A, the engine)
                 ├── injective_errorSupport ── injOn_errorSupport
                 ├── subsingleton_of_errorSupport_eq
                 ├── eq_of_errorSupport_subset
                 └── errorSupport_antichain ── isAntichain_errorSupport
```

Two independent roots only: `minDistance_le_hammingDistance` (already in the project) and the
elementary set inclusion `filter_ne_subset_union_errorSupport`. Nothing else from the project is
used; in particular no Johnson machinery, no κ-charging, no Reed–Solomon file, no MCA definition
is touched or referenced.

---

## 3. Weakest hypotheses actually used

| theorem | needs | does **not** need |
| --- | --- | --- |
| `eq_of_errorSupport_subset_of_card_lt_minDistance` | `C` a submodule; `|S| < minDistance C` | `e`; MDS; RS; `f1 ∈ C`; any bound on `|F|` |
| `injective_errorSupport` | `2e < minDistance C`; both words in the list | MDS; RS; `|F|` |
| `minDistance_le_card_union_errorSupport` | `q1, q2 ∈ C`, `q1 ≠ q2` | `e` at all; list membership; MDS; RS |
| `union_errorSupport_ge_minDist` | as above | `hd` is carried in the signature because the mission asked for it, but the proof does not use it — the honest general form is the line above |
| `errorSupport_antichain` | `2e < minDistance C`; both words in the list | MDS; RS; `|F|` |

Two interface remarks, recorded because they differ from the wording of the mission text:

* The project's minimum distance is `Root.CodingTheory.minDistance` (in
  `RequestProject/Root/CodingTheory/Hamming.lean`), defined as
  `sInf { d | ∃ f ∈ C, f ≠ 0 ∧ hammingDistance f 0 = d }`. It plays the role of the mission's
  `codeMinDistance`; **no adapter lemma was needed.**
* Codes are `Submodule F (ι → F)` as requested; Mathlib's `LinearCode` is not used anywhere.
* `Field F` is only needed to state `Submodule F (ι → F)`; the purely combinatorial lemmas about
  `errorSupport` are stated with that instance `omit`ted, so they hold over any type.

---

## 4. Exact proof status

| phase | statement | status |
| --- | --- | --- |
| 1 | small-support uniqueness | **PROVED in Lean** |
| 2 | support injectivity, support/error/codeword/list bijection | **PROVED in Lean** |
| 2′ | fixed-support subsingleton | **PROVED in Lean** |
| 3 | union law (primary), intersection form, packing form | **PROVED in Lean** |
| 3′ | antichain corollary, `IsAntichain` form | **PROVED in Lean** |
| 4 | MDS interpolation equivalence `2e < d ⟺ 2e ≤ n−k` | not formalised (frozen) |
| 5 | `|L| ≤ C(n,2e)` | not formalised (frozen); see §7 — the antichain alone is **insufficient** |
| 6 | `m_x ≤ C(n−1,2e−1)` | not formalised (frozen) |
| 7 | admissible coordinate functional, `M*_L ≤ 1 + min m_x` | not formalised (frozen) |
| 8 | projected MCA corollary `|B| ≤ 2·C(n−1,2e−1) − 1` | not formalised, and **not stated** in Lean, because the projected Rédei input is not formalised (§8) |
| 9 | sharpness / deep holes | not formalised (§9) |

No statement anywhere in the Lean build is weakened, and no external result is smuggled in as a
hypothesis-free theorem.

---

## 5. Build status

* `lake build RequestProject.Root.CodingTheory.SupportGeometry` — succeeds, **zero warnings**.
* `lake build` (full default target, 8207 jobs) — `Build completed successfully`.
* `rg -n "sorry|admit" RequestProject/Root/CodingTheory/SupportGeometry.lean` — the only match is
  the sentence "there is no `sorry`" in the file's header comment.
* The new file is imported by `RequestProject/Main.lean`.

---

## 6. Axiom audit

`#print axioms` for every new public declaration was added to `RequestProject/Main.lean` and runs
as part of the full build. Every one of

```
eq_of_errorSupport_subset_of_card_lt_minDistance
injective_errorSupport
injOn_errorSupport
subsingleton_of_errorSupport_eq
minDistance_le_card_union_errorSupport
union_errorSupport_ge_minDist
card_inter_errorSupport_le
card_inter_agreement_le
errorSupport_antichain
eq_of_errorSupport_subset
isAntichain_errorSupport
```

reports exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no project-local axiom, no `@[implemented_by]`, no `native_decide`.

---

## 7. Missing combinatorial infrastructure — and one genuine correction

The mission asked specifically that `|L| ≤ C(n,2e)` **not** be accepted as an automatic
consequence of Sperner. That caution was justified.

**(a) The antichain property alone does not give `C(n,2e)`.** The implication

> antichain of subsets of an `n`-set, all of size `≤ t`  ⟹  family size `≤ C(n,t)`

is **false**. Counterexample: `n = 4`, `t = 3`, take all six 2-subsets of `{1,2,3,4}`. This is an
antichain, every member has size `≤ 3`, and `6 > C(4,3) = 4`. So any formalisation that derives
`|L| ≤ C(n,2e)` from `isAntichain_errorSupport` and `|E(q)| ≤ 2e` *and nothing else* would be
proving something false; an extra hypothesis is mandatory.

**(b) What Mathlib supplies.** `Mathlib.Combinatorics.SetFamily.LYM` contains both

* `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`
  — `∑_{s ∈ 𝒜} (C(n,|s|))⁻¹ ≤ 1` for an antichain `𝒜`, and
* `IsAntichain.sperner` — `|𝒜| ≤ C(n, n/2)`.

`IsAntichain.sperner` gives only the middle binomial `C(n, ⌊n/2⌋)`, which is **weaker** than
`C(n,2e)` whenever `2e < n/2` — i.e. exactly in the interesting regime. So Sperner is the wrong
tool; LYM is the right one.

**(c) The missing lemmas, stated exactly.** Three small items, none of them a library:

1. **(monotonicity on the lower half)** `r ≤ t ≤ n/2 → C(n,r) ≤ C(n,t)`. Mathlib exports the
   single step `Nat.choose_le_succ_of_lt_half_left` and the endpoint `Nat.choose_le_middle`, but
   the general lower-half monotonicity is a *private* lemma
   (`Nat.choose_le_middle_of_le_half_left`), so ≈ 5 lines of `decreasingInduction` are needed to
   re-derive it. Cost: trivial.
2. **(LYM-monotone)** If `𝒜` is an antichain of subsets of a finite type of card `n`, every
   member has `|s| ≤ t`, and `2t ≤ n`, then `|𝒜| ≤ C(n,t)`. From
   `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`,
   `|𝒜| · C(n,t)⁻¹ ≤ ∑_{s ∈ 𝒜} C(n,|s|)⁻¹ ≤ 1`, using (1). This is the existing Mathlib proof of
   `IsAntichain.sperner` with `n/2` replaced by `t`. Cost: ≈ 20 lines.
3. **(Set → Finset adapter)** Mathlib's LYM lemmas take a `Finset (Finset α)`, whereas
   `isAntichain_errorSupport` produces an antichain of type `Set (Finset ι)` (the image of a
   `Set` of codewords). The adapter is to work with
   `Finset.univ.filter (fun S : Finset ι => ∃ q ∈ decodingList C f1 e, errorSupport f1 q = S)`
   and to transport `|L| = |that Finset|` across `injOn_errorSupport`. This is the only genuine
   interface friction found, and it is small; it does **not** require changing any statement
   above. Cost: ≈ 30 lines, including the finiteness of `L` (which holds because
   `q ↦ errorSupport f1 q` is injective into a finite type, or simply because `ι → F` is finite
   when `F` is).

**No new combinatorics library is required.**

**(d) The hypothesis `2t ≤ n` does not hold throughout the regime**, which is why the earlier
audit needed a *second* branch. In `2e ≤ n−k` one may have `4e > n` (e.g. `n = 10, k = 1, e = 4`).
There the audit's information-set injection (`q ↦` lexicographically least `k`-subset of the
agreement set, injective because `k` agreements determine an MDS codeword) gives `|L| ≤ C(n,k)`
and `C(n,k) ≤ C(n,2e)` because `k ≤ 2e ≤ n−k`. The two branches do cover the regime: if both
failed we would have `2e < k` and `4e > n`, while `2e ≤ n−k` forces `k ≤ n−2e < 2e`, a
contradiction.

**Conclusion for Phase 5/6.** Nothing is missing from Mathlib. What is missing is
(i) the small `LYM-monotone` lemma above, and (ii) the MDS information-set injection, which needs
MDS in the project's own formulation. Both are genuinely MDS-or-branch-dependent, i.e. Phase 5 is
**not** a corollary of the general core alone — a point the general core now makes visible rather
than hiding.

---

## 8. Boundary between formalised mathematics and external input

Formalised, self-contained, machine-checked in this project:

* everything in §1, for arbitrary linear codes over arbitrary fields.

Established mathematically in earlier reports of this project but **not** formalised, and not
present in the Lean build in any form:

* the MDS specialisation `d = n−k+1` and the equivalence `2e < d ⟺ 2e ≤ n−k`;
* the list bound `|L| ≤ C(n,2e)` and the occupancy bound `m_x ≤ C(n−1,2e−1)`;
* the admissibility criterion `λ` admissible `⟺ λ|_{V_W} ≠ 0` and
  `M*_L ≤ 1 + min_{x ∈ supp V_W} m_x`.

External, cited and never re-proved, and **not** introduced as a Lean hypothesis anywhere:

* the Rédei–Megyesi/Szőnyi direction theorem over a prime field, which is what turns
  `M*_L` into `|B| ≤ 2 M*_L − 3`.

Because the projected-Rédei input is not formalised, the candidate corollary
`|B| ≤ 2·C(n−1,2e−1) − 1` is deliberately **absent from the Lean build**. It is recorded here as a
conditional statement only.

---

## 9. Sharpness status

Per the freeze, nothing about sharpness entered Lean. The status inherited from
`MDS_SUPPORT_ANTICHAIN_AUDIT.md`, restated so the open part is explicit:

* Threshold sharpness of the *general core*: at `2e = d` the antichain fails for every code
  (take `f₁ ∈ C` and a minimum-weight codeword), and injectivity fails as well once `|F| ≥ 3`.
  So `2e < d` is exactly the right hypothesis for what is formalised above. This is a short
  argument and would be cheap to formalise as explicit small counterexamples; it was not
  attempted here because the mission froze everything beyond Phase 3.
* Equality in the MDS bounds — the claimed criterion is: `|L| = C(n,2e)` (and
  `m_x = C(n−1,2e−1)`) **iff** `2e = n−k` and `d(f₁,C) = n−k`. Both directions are argued in the
  audit; neither is formalised.
* Existence of deep holes for general MDS parameter sets remains **OPEN** and is not assumed
  anywhere. Deep holes are exhibited only for specific Reed–Solomon instances.

---

## 10. Next mission (exactly one)

**FORMAL MDS INTERPOLATION REGIME AND LIST-SIZE BOUND (Phases 4–5).**

Scope, in order:

1. the arithmetic equivalence `2e < d ⟺ 2e ≤ n−k` under `d = n−k+1`, stated over `ℕ` with no
   informal prose;
2. the lemma `LYM-monotone` of §7(c), proved from
   `Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose`;
3. `|L| ≤ C(n,2e)` in the branch `4e ≤ n`, from `isAntichain_errorSupport` plus (2);
4. only then the MDS information-set injection for the complementary branch.

Stop after (3) if (4) turns out to need new MDS infrastructure in the project. Phase 6
(occupancy) and Phase 7 (coordinate functional) stay frozen until Phase 5 compiles.
