# GMCA-2026-09-12-001 — heavy-fibre invariant gate

## 1. STATUS

**CONDITIONAL.**

Items 1, 3, 4 of the gate are proved in Lean, with no `sorry` and no new axiom.
Item 2 is **not** proved, and the *inference* it was implicitly relying on is **refuted** by an
exact countermodel: `μ_n`-valuedness of the heavy-fibre invariant (the only source-level property
established for it, item 1) never implies the existence of a coprime rational presentation of
degree `≤ w`.  Moreover, in the only regime where such a presentation would be useful
(`#G_x > 146028888064`) any coprime degree-`≤ w` presentation is necessarily **constant**, so the
nonconstant branch that produces `146028888064` cannot be reached there.

Item 2 is the first failed item.  No official (deployed-row) countermodel is claimed: the failure
is a failure of derivation, formally witnessed by the general countermodel and by the self-defeat
theorem below, both stated at source level.

Frozen row (unchanged, audited against the actual source, not against the report prose):

```
n = 2097152,  k = 1048576,  e = 978944,  w = 69632,  B* = 274980728111395087
```

## 2. The invariant `I_x`, exactly as formalised

For a fixed domain point `x : ↥D` and a fixed official pair `(f₀, f₁)`:

```
G_x  :=  heavyFibre k e f₀ f₁ x
      =  (badSet k e f₀ f₁).filter (fun γ => x ∈ erasureSel k e f₀ f₁ γ)
```

— the distinct **finite official bad challenges** (the repository's `badSet`, i.e. `IsBad`) whose
**exact-size official erasure witness** `erasureSel` (co-size exactly `e`, from `erasureSel_spec`)
contains `x`; equivalently, whose official locator splits as `Q_γ = (X − x)·R_γ`.

```
R_γ  :=  twistLoc k e f₀ f₁ γ x  =  qPoly (dval D) ((erasureSel k e f₀ f₁ γ).erase x)
I_x γ :=  locInv k e f₀ f₁ x γ   =  (twistLoc k e f₀ f₁ γ x).eval 0
```

* **Field**: values lie in the deployed field `F` itself (no quotient, no residue ring).
* **Normalisation**: `I_x γ = ∏_{y ∈ E_γ \ {x}} (0 − y) = (−1)^{e−1} ∏_{y ∈ E_γ \ {x}} y`, the
  constant term of the **monic** cofactor `R_γ` (`locInv_eq_prod`).
* **Dependence on `R_γ`**: `I_x` is a function of `R_γ` alone (its constant coefficient); the
  untwisted constant term is recovered by `official_constTerm_eq : Q_γ(0) = −x · I_x γ`.
* **Value space** `Y_x = μ_n ⊆ F`, of size `≤ n = 2097152` (`locInv_pow_eq_one`).

## 3. Exact theorem statements

All in `Root.CodingTheory.HeavyFibre`, file
`RequestProject/Root/CodingTheory/HeavyFibreInvariant.lean`; ambient
`{F : Type u} [Field F] [DecidableEq F] {D : Finset F}` and, where `badSet` occurs, `[Fintype F]`.

### Item 1 — domain

```lean
theorem heavyFibre_domain {k e n : ℕ} (hk : k ≤ D.card) (he : e < D.card - k) (heD : e < D.card)
    (hn : Even n) (hn0 : 0 < n) (hroots : ∀ y : ↥D, (y : F) ^ n = 1) {f₀ f₁ : ↥D → F} {x : ↥D}
    {γ : F} (hγ : γ ∈ heavyFibre k e f₀ f₁ x) {Ψ : F[X]} (hΨ : (X - C (x : F)) * Ψ = X ^ n - 1) :
    qPoly (dval D) (erasureSel k e f₀ f₁ γ) = (X - C (x : F)) * twistLoc k e f₀ f₁ γ x ∧
      (twistLoc k e f₀ f₁ γ x).Monic ∧
      (twistLoc k e f₀ f₁ γ x).natDegree = e - 1 ∧
      twistLoc k e f₀ f₁ γ x ∣ Ψ ∧
      (locInv k e f₀ f₁ x γ) ^ n = 1 ∧ locInv k e f₀ f₁ x γ ≠ 0
```

Hypotheses: the official row inequalities `k ≤ |D|`, `e < |D| − k`, `e < |D|` (exactly those of
`erasureSel_spec`), `n` even and positive, and `D ⊆ μ_n`.  Conclusion: every `γ ∈ G_x` has the
stated split with `deg R_γ = e − 1`, `R_γ ∣ (X^n − 1)/(X − x) = Ψ`, and `I_x γ ∈ Y_x = μ_n \ {0}`.
Supporting: `locInv_eq_prod`, `official_constTerm_eq`, `locInv_pow_eq_one`,
`heavyFibre_subset_badSet`, `mem_heavyFibre_iff`.

### Item 2 — the presentation: what holds, and what fails

Provable half (denominators):

```lean
theorem presentation_denominator_ne_zero {u v : F[X]} {Γ : Finset F} {c : F → F}
    (hcop : IsCoprime u v) (hpres : ∀ γ ∈ Γ, c γ * v.eval γ = u.eval γ) :
    ∀ γ ∈ Γ, v.eval γ ≠ 0
theorem presentation_numerator_ne_zero … (hc : ∀ γ ∈ Γ, c γ ≠ 0) : ∀ γ ∈ Γ, u.eval γ ≠ 0
```

So coprimality *alone* forces the denominator (and, since `I_x ≠ 0` by item 1, the numerator) to
be nonvanishing on every official challenge of `G_x`.  This half of item 2 is unconditional.

Degree claim: **not derivable**.  Two formal statements.

```lean
theorem bounded_presentation_dichotomy {u v : F[X]} {n w : ℕ} (hn : 0 < n) (hcop : IsCoprime u v)
    (hu : u.natDegree ≤ w) (hv : v.natDegree ≤ w) (Γ : Finset F) (c : F → F)
    (hc : ∀ γ ∈ Γ, (c γ) ^ n = 1) (hpres : ∀ γ ∈ Γ, c γ * v.eval γ = u.eval γ) :
    (∀ γ ∈ Γ, ∀ δ ∈ Γ, c γ = c δ) ∨ Γ.card ≤ n * w

theorem no_bounded_presentation_countermodel :
    ¬ ∃ u v : (ZMod 3)[X], IsCoprime u v ∧ u.natDegree ≤ 1 ∧ v.natDegree ≤ 1 ∧
      ∀ γ ∈ (Finset.univ : Finset (ZMod 3)), cmInv γ * v.eval γ = u.eval γ
```

with `cmInv γ = if γ = 0 then 1 else -1`, `cmInv_sq : (cmInv γ)^2 = 1`.  This is the smallest
instance of the shape of item 2 (`|F| = 3`, `n = 2`, `w = 1`, `#Γ = 3 > n·w = 2`): a `μ_n`-valued
invariant with **no** coprime presentation of degree `≤ w`.  Hence item 2 cannot be inferred from
item 1; the presentation is an extra hypothesis, not a consequence.

Self-defeat in the needed regime:

```lean
theorem deployed_presentation_self_defeat
    (hroots : ∀ y : ↥D, (y : F) ^ 2097152 = 1) {f₀ f₁ : ↥D → F} {x : ↥D} {u v : F[X]}
    (hcop : IsCoprime u v) (hu : u.natDegree ≤ 69632) (hv : v.natDegree ≤ 69632)
    (hpres : ∀ γ ∈ heavyFibre 1048576 978944 f₀ f₁ x,
      locInv 1048576 978944 f₀ f₁ x γ * v.eval γ = u.eval γ)
    (hbig : 146028888064 < (heavyFibre 1048576 978944 f₀ f₁ x).card) :
    ∀ γ ∈ heavyFibre 1048576 978944 f₀ f₁ x, ∀ δ ∈ heavyFibre 1048576 978944 f₀ f₁ x,
      locInv 1048576 978944 f₀ f₁ x γ = locInv 1048576 978944 f₀ f₁ x δ
```

If the heavy fibre exceeds `146028888064`, every coprime degree-`≤ w` presentation of `I_x` is
constant and `I_x` is constant on `G_x`.  So a *proof* of item 2 in the large-fibre regime is a
proof of the constant branch; the nonconstant branch is unavailable exactly where it is needed.
(The `w`-row twisted linear system cannot supply the presentation either: it is `69632` equations
in `978944` unknowns, `TwistedInvariant.deployed_twisted_system_underdetermined`, audited from
source; no Cramer selection of degree `≤ w` exists there.)

### Item 3 — the bounded-root/fibre lemma, with its exact polynomial

The bound `146028888064` is obtained from the root count of the explicit polynomial

```lean
noncomputable def annihPoly (n : ℕ) (u v : F[X]) : F[X] := u ^ n - v ^ n
theorem annihPoly_natDegree_le (n) (u v) :
    (annihPoly n u v).natDegree ≤ n * max u.natDegree v.natDegree
theorem annihPoly_deployed_natDegree_le (hu : u.natDegree ≤ 69632) (hv : v.natDegree ≤ 69632) :
    (annihPoly 2097152 u v).natDegree ≤ 146028888064
theorem annihPoly_ne_zero_of_nonconstant (hn : 0 < n) (hcop : IsCoprime u v)
    (hnc : ¬ (u.natDegree = 0 ∧ v.natDegree = 0)) : annihPoly n u v ≠ 0
theorem subset_annihPoly_roots (hc : ∀ γ ∈ Γ, (c γ)^n = 1)
    (hpres : ∀ γ ∈ Γ, c γ * v.eval γ = u.eval γ) (hne : annihPoly n u v ≠ 0) :
    Γ ⊆ (annihPoly n u v).roots.toFinset
theorem card_le_of_presentation … : Γ.card ≤ (annihPoly n u v).natDegree
```

Exact polynomial: `u^2097152 − v^2097152`; exact degree bound `2097152 · 69632 = 146028888064`;
nonvanishing from coprimality plus nonconstancy (`degenerate_of_coprime`).  The count is a
root count of this polynomial — **not** an inference from rational-map degree.

### Item 4 — margin and fibre bound

```lean
theorem heavyFibre_card_le_of_presentation
    (hroots : ∀ y : ↥D, (y : F) ^ 2097152 = 1) {f₀ f₁ x u v}
    (hcop : IsCoprime u v) (hu : u.natDegree ≤ 69632) (hv : v.natDegree ≤ 69632)
    (hnc : ¬ (u.natDegree = 0 ∧ v.natDegree = 0))
    (hpres : ∀ γ ∈ heavyFibre 1048576 978944 f₀ f₁ x,
      locInv 1048576 978944 f₀ f₁ x γ * v.eval γ = u.eval γ) :
    (heavyFibre 1048576 978944 f₀ f₁ x).card ≤ 146028888064

theorem deployed_heavy_margin : (146028888064 : ℕ) < 274980728111395087
theorem heavyFibre_card_le_Bstar … : (heavyFibre 1048576 978944 f₀ f₁ x).card ≤ 274980728111395087
```

Non-globality is recorded explicitly (the gate's own warning, now a theorem):

```lean
theorem badSet_subset_biUnion_heavyFibre (hk he heD) (he0 : 0 < e) (f₀ f₁) :
    badSet k e f₀ f₁ ⊆ D.attach.biUnion fun x => heavyFibre k e f₀ f₁ x
theorem badSet_card_le_of_uniform_heavyFibre … (hM : ∀ x, (heavyFibre k e f₀ f₁ x).card ≤ M) :
    (badSet k e f₀ f₁).card ≤ D.card * M
theorem heavyFibre_bound_not_global : (274980728111395087 : ℕ) < 2097152 * 146028888064
```

i.e. even a uniform heavy-fibre bound of `146028888064` gives only
`#Bad ≤ 2097152 · 146028888064 = 306239994226147328 > B*`.

## 4. Changed Lean files and build commands

Added (purely additive; no submission root, toolchain, lakefile or manifest touched):

* `RequestProject/Root/CodingTheory/HeavyFibreInvariant.lean`
* `RequestProject/HeavyFibreInvariantAxiomAudit.lean`
* `HEAVY_FIBRE_INVARIANT_GATE_REPORT.md` (this file)

```
lake build RequestProject.Root.CodingTheory.HeavyFibreInvariant
lake build RequestProject.HeavyFibreInvariantAxiomAudit
```

Both complete successfully, with no warnings in the new files and no `sorry`/`admit`.

## 5. `#print axioms` audit

Every load-bearing declaration listed in `RequestProject/HeavyFibreInvariantAxiomAudit.lean`
(24 declarations: items 1–4, the countermodel and the self-defeat theorem) reports exactly

```
[propext, Classical.choice, Quot.sound]
```

No new axiom, no `native_decide`, no `sorry`.

## 6. What the result does and does not establish

* It does **not** prove `M_C(1118208) ≤ B*`.
* It does **not** produce an official counterexample.
* It leaves the *same* gate open, but with its failure point now exactly located: items 1, 3, 4
  are theorems; item 2 is neither available nor derivable from item 1, and in the large-fibre
  regime it collapses to the constant branch.
* Per-fibre bounds, even uniform ones, are proved insufficient for a global bound at this row
  (`heavyFibre_bound_not_global`).
* No second invariant was investigated: the gate's precondition for that step (a complete proof of
  items 1–4) is not met.

## 7. Next gate (one only)

**Prove or refute item 2 in its only surviving useful form**: from source-level hypotheses
(`badSet`/`erasureSel`/`LocatorSystem` at the frozen row, plus `D ⊆ μ_n`), decide whether the
constant branch holds for `I_x`, i.e. whether

```
∀ γ, δ ∈ G_x,  locInv 1048576 978944 f₀ f₁ x γ = locInv 1048576 978944 f₀ f₁ x δ
```

can fail while `#G_x > 146028888064`.  Equivalently: exhibit two official challenges in one heavy
fibre with distinct `I_x` values together with a degree-`≤ w` coprime presentation, or prove that
no such presentation exists.  Nothing else from the earlier programme is reopened.
