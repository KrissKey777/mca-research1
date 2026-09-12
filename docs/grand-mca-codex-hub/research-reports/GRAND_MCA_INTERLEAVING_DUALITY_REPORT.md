# GRAND MCA — interleaving, extension-field challenge transport, complementary-window duality

Session report.  Everything below is formalised in Lean 4 / Mathlib, builds without `sorry`, and
was axiom-audited: every theorem named here depends only on `propext`, `Classical.choice`,
`Quot.sound`.

## Source handling

The attached ArkLib bundle (`arklib-grand-mca-bundle-2026-09-08.zip`, six files) was unpacked and
read as ground truth.  ArkLib is **not** importable in this project (it is a separate Lean package
with its own dependency tree, and only six of its files were supplied), so the declarations that
are needed are *mirrored* here, with the ArkLib source quoted in each file header and the mirror
justified line by line:

| ArkLib declaration (bundle) | mirrored as |
|---|---|
| `Code.ModuleCode.moduleInterleavedCode`, `mem_moduleInterleavedCode_iff` | `Root.CodingTheory.Absorption.interleavedCode`, `mem_interleavedCode` |
| `projectedCodeSubmod_moduleInterleavedCode_iff` | `projectedCode_interleavedCode_iff` (a corollary of the stronger submodule identity `projectedCode_interleavedCode`) |
| `gridPt`, `grandMcaChallenge`, `GrandMcaResolution`, `GrandMcaAnswer`, `GrandMcaAnswer.to_challenge`, `prizeThreshold` | `ArkLibWrapper.grandMcaChallengeMirror`, `McaBoundary`, `McaAnswer`, `McaAnswer.to_challenge`, `prizeThreshold` |
| `mcaError G MC δ = ⨆ U, Pr_{x ←$ᵖ S}[IsMCA …]` | abstract grid error `err : ℕ → ℝ≥0∞` with the uniform-probability semantics passed as an explicit hypothesis |

Files that the bundle does **not** contain (`Basic/LinearCode.lean` with `projectedWord` /
`projectedCodeSubmod`, and `Data/Probability/Instances.lean` with `Pr_{x ←$ᵖ S}`) are never
assumed: the one place where their content is needed (Mission E) takes it as a hypothesis.

## A — `[INTERLEAVING-RES FUNCTORIALITY]`

`RequestProject/Root/CodingTheory/InterleavedResidual.lean`

Interleaving is an injective lattice map on codes (`interleavedCode_inf`, `interleavedCode_sup`,
`interleavedCode_injective`) that **fixes the window subspace**
(`interleavedCode_positionSpace`).  Everything follows from that one fact:

```
Short(C^⋈κ, W)          = Short(C,W)^⋈κ                     interleavedCode_shortening
Lost(C^⋈κ, E^⋈κ, W)     = Lost(C,E,W)^⋈κ                    interleavedCode_lostStage
(ι → κ→A)/C^⋈κ          ≃ₗ κ → ((ι → A)/C)                  interleavedQuotEquiv
Res(C^⋈κ, E^⋈κ, W)      ≃  Res(C,E,W)^⋈κ                    map_interleavedQuotEquiv_residual
```

The last line is the highest-value target of Mission A, and it is proved as a **commuting
diagram**, not as separate lemmas: `interleavedQuotEquiv ∘ mkQ = interleavedQuotMap`
(`interleavedQuotEquiv_mkQ`), and the residual class is the image of the Lost stage under it.
`residualInterleaveEquiv` packages the conclusion as a linear isomorphism
`Res(C^⋈κ,E^⋈κ,W) ≃ₗ (κ → Res(C,E,W))`.

Consequences, all proved:

* restriction-kernel description is interleaved too (`interleavedCode_restrictionKernel`);
* `dim Res` scales by `|κ|` (`finrank_residual_interleavedCode`), hence the defect spectrum is
  multiplied by `|κ|` with unchanged jump positions;
* the gluing-defect budget scales by `|κ|` (`gluingDefect_interleavedCode`);
* terminal windows are **unchanged** (`terminalWindow_interleavedCode_iff`), so the canonical
  minimal terminal window of the interleaved pair is the base one;
* on the projection side, the projected interleaved code is the interleaving of the projected
  code (`projectedCode_interleavedCode`), which specialises to ArkLib's
  `projectedCodeSubmod_moduleInterleavedCode_iff` (`projectedCode_interleavedCode_iff`).

## B — `[EXACT K/F_p CHALLENGE TRANSPORT]`

`RequestProject/Root/CodingTheory/ExtensionChallengeTransport.lean`

For `K/F` of degree `d` with basis `b` (deployed: `K = F_(p^6)`, `d = 6`), interleaving a
`K`-word into its `d` coordinate rows is exactly ArkLib's interleaving at `κ = Fin d`.  A single
challenge `r ∈ K` transports **exactly**, as one matrix acting on every interleaved symbol:

```
Interleave(f₀ + r • f₁) = Interleave(f₀) + M_r · Interleave(f₁)      wordCoords_add_smul
```

with `M_r = Algebra.leftMulMatrix b r`.  The map `r ↦ M_r` is an injective `F`-algebra map
(`mulMatrixAlgHom`, `mulMatrix_injective`): the challenges form a *field* of matrices, so the one
`K`-parameter is never replaced by `d` independent base-field scalars.  Quantitatively, for
`f₁ ≠ 0` the interleaved image of the challenge line is an `F`-subspace of dimension exactly `d`
(`finrank_range_challengeLine`), hence not an `F`-line for `d ≥ 2`
(`not_finrank_range_challengeLine_one`); the deployed instances are `sextic_challenge_transport`
and `sextic_challenge_dimension`.

The interleaving MCA API preserves this family exactly: the extension code
(`extensionCode`, the coordinatewise base change, identified with ArkLib's interleaved code by
`map_wordCoords_extensionCode`) is stable under `r • ·` (`extensionCode_smul_mem`) — and the
proof of that stability *is* the `M_r`-transport.  Combining A and B,

```
Res(C ⊗_F K, E ⊗_F K, W) ≃ Res(C,E,W)^d                     map_extQuotEquiv_residual
```

so passing to the sextic challenge field multiplies every dimension in the defect spectrum by 6
and moves no jump position.

## C — `[COMPLEMENTARY-WINDOW DUALITY]`

`RequestProject/Root/CodingTheory/ComplementaryWindowDuality.lean`

The dual-code theory over `ι → F` is built from scratch (`dualCode`, `finrank_dualCode`,
`dualCode_dualCode`, `dualCode_sup`, `dualCode_inf`), the key input being
`dualCode_positionSpace`: `(P_W)^⊥ = P_{Wᶜ}`.  From it:

```
Short(M,W)^⊥       = M^⊥ ⊔ P_{Wᶜ}                            dualCode_shortening
Lost(C,E,W)^⊥      = Lost(E^⊥, C^⊥, Wᶜ)                      dualCode_lostStage
```

The second line is the strongest form of the requested Wei-type relation: an **equality of
subspaces**, no dimension count, no literal `Res = K_W` on the dual side.  In residual form,

```
{y ∈ C^⊥ : ⟨x,y⟩ = 0 ∀ x ∈ Short(E,W)} = Lost(E^⊥,C^⊥,Wᶜ)    residual_dual_annihilator
comap mkQ (Res(E^⊥,C^⊥,Wᶜ)) = Lost(C,E,W)^⊥                  comap_mkQ_residual_dual
```

together with elementwise mutual annihilation (`dot_eq_zero_of_shortening_compl`): the pairing
between `Res(C,E,W)` and `Res(E^⊥,C^⊥,Wᶜ)` is perfect.  Its numerical shadow is the exact
complementary defect identity

```
dim Res(C,E,W) + dim Res(E^⊥,C^⊥,Wᶜ) = dim E − dim C
                                     finrank_residual_add_finrank_residual_dual
```

(proved through the Wei shortening/puncturing relation `finrank_shortening_add_card_compl`), and
a clean structural corollary:

```
TerminalWindow C E W  ↔  Res(E^⊥, C^⊥, Wᶜ) = ⊥
                                     terminalWindow_iff_residual_dual_eq_bot
```

— the terminal windows of the primal pair are exactly the complements of the windows carrying no
dual residual.

## D — `ResidualClass` / `ModularDefect`: what could and could not be done

`ResidualClass`, `ModularDefect` and the primal/dual `ModularDefect` pairing referred to in the
brief are **not present in this repository and were not among the supplied sources**, so no
faithful bridge to them could be formalised; inventing a definition and calling it
`ResidualClass` would prove nothing about the intended object.  What *was* proved is the part of
the requested diagram that lives entirely on this side, namely the identification of the gluing
defect of the `Res`-filtration with the dual complementary-window obstruction:

```
dim (M^⊥ ⊔ P_{Wᶜ ∩ W'ᶜ}) + gluingDefect(M,W,W')
    = dim ((M^⊥ ⊔ P_{Wᶜ}) ⊓ (M^⊥ ⊔ P_{W'ᶜ}))        gluingDefect_eq_dual_obstruction

gluingDefect(M,W,W') = 0 ↔ the dual complementary windows distribute over M^⊥
                                                   gluingDefect_eq_zero_iff_dual_distrib
```

i.e. "zero class ↔ gluing" in the only form that is currently grounded: the primal gluing
obstruction and the dual complementary-window obstruction are the same number, and vanish
together.  Connecting this to a `ResidualClass`/`ModularDefect` object requires that object's
definition as an input.

## E — ArkLib final wrapper

`RequestProject/Root/CodingTheory/ArkLibGrandMcaWrapper.lean`

The minimal exact chain, in three links:

1. `err_le_of_card_bad_le` — `#Bad ≤ B*` per family gives `mcaError ≤ B*/|F|` (uniform-challenge
   semantics as an explicit hypothesis);
2. `div_le_prizeThreshold` — `B*/|F| ≤ 2⁻¹²⁸` as soon as `B*·2¹²⁸ ≤ |F|`, with the deployed
   sextic instance `deployed_sextic_safe` (`B* ≤ 2²⁰`, `|F| ≥ 2¹⁴⁸`);
3. `exists_mcaAnswer` + `McaAnswer.to_challenge` — the boundary dichotomy `allGood | boundary`
   and its passage to the ArkLib challenge disjunction; `McaBoundary.kStar_unique` reproves the
   uniqueness of the crossing index for monotone error.

Composite: `safe_of_card_bad_le` and `grandMcaChallengeMirror_of_card_bad_le` — from `#Bad ≤ B*`
to official SAFE.

## Stop rules

Nothing in this session uses Ackermann/primitive recursion, generic Sudan or Johnson list-size
bounds, raw Rank2 adapter theory, or six independent base-field challenges, and the canonical
quotient theory of `Res` was reused, not rebuilt.
