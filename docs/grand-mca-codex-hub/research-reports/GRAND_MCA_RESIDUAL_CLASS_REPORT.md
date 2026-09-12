# The canonical residual class of the Lost-filtration

**Files.**
`RequestProject/Root/CodingTheory/LostFiltrationResidual.lean`,
`LostFiltrationResidualTriple.lean`,
`LostFiltrationResidualDescent.lean`,
`LostFiltrationResidualMDS.lean`,
audit `RequestProject/LostFiltrationResidualAxiomAudit.lean`.
Everything below is proved in Lean with no `sorry` and no added axioms; every declaration in the
audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## 1. The object

For a nested pair of codes `C ≤ E` inside `ι → A` and a window `W`, the banked Lost-filtration
stage is `Lost(C,E,W) = E ⊓ (C ⊔ P_W) = C ⊔ Short(E,W)`.  Define

```
Res(C,E,W) := image of Lost(C,E,W) in the fixed ambient quotient (ι → A)/C     (`residual`)
```

a submodule of `(ι → A)/C`.  No representative — absorbed or otherwise — is chosen anywhere in
the definition, and `Lost` is recovered as `comap C.mkQ (Res)` (`comap_mkQ_residual`), so nothing
is lost in passing to `Res`.

## 2. Canonical quotient theorem (direction A)

* `residualEquivLostQuot` : `Lost(C,E,W)/C ≅ Res(C,E,W)` — unconditional.
* `residualEquivShorteningQuot` (needs only `C ≤ E`) : `Short(E,W)/Short(C,W) ≅ Res(C,E,W)`.
* `lostQuotEquivShorteningQuot` : composing the two gives the comparison isomorphism of the
  universal exact sequence `0 → Short(C,W) → Short(E,W) → Lost(C,E,W)/C → 0`.

So the two independently defined quotients are canonically the same object, and that object has
a *choice-free submodule model* inside one fixed ambient module.

**Universal property** (`residual_universal`): `Res(C,E,W)` with the canonical surjection
`resMk : Short(E,W) ↠ Res(C,E,W)` is the cokernel of `Short(C,W) → Short(E,W)`.  Every linear
invariant of window-supported words of `E` that ignores the invisible cores factors *uniquely*
through it.  This is the promised characterisation "without choosing an absorbed representative":
`Res` is determined up to unique isomorphism by the property, not by a construction.

**Restriction-kernel description** (`lostStage_eq_inf_comap_restrict`,
`residual_eq_inf_ker_punctureQuot`):

```
Res(C,E,W) = (E/C) ⊓ ker( (ι → A)/C → (Wᶜ → A)/C|_{Wᶜ} ).
```

i.e. `Res` is exactly the part of `E/C` that the restriction to the complement of the window
cannot see — the lost-direction object.  Three descriptions (sup of shortenings, quotient,
restriction kernel) are therefore one object.

**Torsor comparison** (`absorbedCores_nonempty_iff_residual_eq_top`,
`residual_extension_eq_map_lostDirections`, `lostDirections_eq_comap_residual`): for a rank-two
extension the pencil map identifies the lost directions with `Res`, and the absorbed-core family
is nonempty exactly when `Res` is all of `E/C`.  The absorbed families are thus a torsor
*presentation* of the same invariant; they are not treated as a based vector space and are not
identified with the kernel-shadow object.

## 3. Functorial residual filtration (direction B)

* In the window variable: `residualHom` is an order homomorphism `Finset ι →o Submodule F ((ι →
  A)/C)`.  All transition maps are inclusions of submodules of one fixed module, hence injective:
  a genuine increasing filtration of `E/C`, starting at `⊥` (`residual_empty`) and exhausting
  `E/C` (`residual_univ`), meet-preserving exactly modulo invisible cores (`residual_inter`).
* In the code variable: for a tower `C ≤ D ≤ E` the projection `(ι → A)/C ↠ (ι → A)/D` induces a
  short exact sequence `0 → Res(C,D,W) → Res(C,E,W) → Res(D,E,W) → 0`
  (`map_factor_residual`, `ker_factor_inf_residual`, `residualTripleEquiv`), and dimensions add
  (`finrank_residual_add_triple`).
* Dimension and spectrum: `dim Res = dim Lost − dim C = dim Short(E,W) − dim Short(C,W)`
  (`finrank_residual_add_finrank`, `finrank_residual_add_finrank_shortening`), so the defect
  spectrum is the jump sequence of `dim Res(C,E,·)`: `relDefect_eq_sInf_residual`.  The relative
  weight hierarchy is an invariant of the canonical object, not of a presentation.

## 4. Exact obstruction theory (direction C)

For a code `M` and windows `W, W'` define

```
gluingDefect M W W' := dim Short(M, W ∪ W') − dim (Short(M,W) ⊔ Short(M,W')).
```

* `finrank_shortening_modular` — the meet side is always exact (shortening turns `∩` into `⊓`,
  and the subspace lattice is modular).
* `gluingDefect_eq_zero_iff` — the defect vanishes exactly when
  `Short(M,W∪W') = Short(M,W) ⊔ Short(M,W')`: exact gluing of window data.
* `finrank_shortening_supermodular` — exact supermodularity with the defect as the only
  correction term.
* `residual_budget_identity` — **the budgets add exactly**:

```
dim Res(W) + dim Res(W') + gluingDefect E = dim Res(W∩W') + dim Res(W∪W') + gluingDefect C.
```

So the failure of the residual filtration to be modular on a pair of windows is *precisely* the
difference of the two gluing defects; nothing else contributes.  This is the exact obstruction
statement in the Lost/residual language, proved internally rather than assumed from the
complementary modular-pair development.

## 5. Canonical residualization and descent (directions D, E)

`TerminalWindow C E W` means `Lost(C,E,W) = E`, equivalently `Res(C,E,W) = E/C`
(`terminalWindow_iff_residual`), equivalently (rank two) existence of an absorbed state.

* `terminalWindow_inter` — terminal windows are closed under intersection whenever the subcode
  hides no invisible core inside their union.
* `exists_min_terminalWindow` — under `NoCore C (2m)`, if some terminal window of size `≤ m`
  exists there is a *unique smallest* one and it is contained in every terminal window of size
  `≤ m`: the canonical rank-minimal residual support.
* `absorbedCores_min_terminalWindow_unique` — at that canonical window the absorbed residual
  state exists and is unique (the `Short(C,W)²`-torsor is a point).

Existence and uniqueness of a rank-minimal residual state therefore hold with no choice, which
is the terminal case of the descent programme; the strict-descent alternative is not needed under
the no-core hypothesis, because the intersection law already produces the minimum.

## 6. MDS / Reed–Solomon classification (direction F)

For a code that is MDS (Singleton-tight distance) the Singleton law bounds the shortening
dimension from below and the distance bounds it from above, and the bounds meet:

* `finrank_shortening_of_mds` : `dim Short(E,W) = |W| + dim E − n`;
* `finrank_residual_of_mds` : `dim Res(C,E,W) + (|W| + dim C − n) = |W| + dim E − n`;
* `residual_regime_trichotomy` : exactly three regimes, determined by `|W|` alone —
  * `|W| + dim E ≤ n`: zero-loss, `Res = ⊥` (`residual_eq_bot_of_mds`);
  * `n − dim E < |W| < n − dim C`: intermediate/fixed-shadow, `dim Res = |W| + dim E − n`,
    a proper nonzero stage;
  * `n ≤ |W| + dim C`: absorbed, `Res = E/C` (`residual_eq_top_of_mds`), and for a rank-two
    extension an absorbed state exists (`absorbedCores_nonempty_of_mds`);
* `finrank_residual_reedSolomon` : the Reed–Solomon instance.

No other behaviour is possible for MDS pairs: the geometry of the window is irrelevant, only its
size matters.  This is the rigidity that the maximal MDS spectrum forces.

## 7. What was deliberately not claimed

* No identification of `Res(C,E,W)` with a *dual-side* kernel-shadow object `K_W` is claimed.
  In the dual picture the natural partner of `Res(C,E,W)` is a quotient of shortenings of the
  dual codes whose dimension involves the complementary window `Wᶜ` (a Wei-type duality), so a
  literal equality with `K_W` is not available at this generality and was not asserted.
* No connection is made to any external exceptional-variety classification; only an exact
  theorem would justify it, and none was obtained here.
