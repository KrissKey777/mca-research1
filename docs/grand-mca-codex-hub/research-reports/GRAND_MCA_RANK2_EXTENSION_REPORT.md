# Grand MCA — the rank-2 extension `E = C + ⟨f₀,f₁⟩` beyond capacity

This report accompanies four new Lean modules:

* `RequestProject/Root/CodingTheory/RankTwoExtension.lean` — the extension and the geometry of
  the quotient `E/C`;
* `RequestProject/Root/CodingTheory/RankTwoClusterStructure.lean` — the structure theorem;
* `RequestProject/Root/CodingTheory/RankTwoCostBound.lean` — the explicit finite cost;
* `RequestProject/Root/CodingTheory/RankTwoDeployedBoundary.lean` — the boundary test.

Axiom audit: `RequestProject/RankTwoExtensionAxiomAudit.lean` (only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`).

Notation as in the repository: `C = RS_k(D)` on the domain `D ⊆ F`, `|D| = n`, received pair
`(f₀,f₁)`, radius `e`, `IsBad k e f₀ f₁ γ` the official badness predicate (a window `S` with
`|S| ≥ n − e` explaining `f₀ + γ f₁` but not the whole line), `Q_S = rsDualOn k S`,
`Λ = synMap f₀ f₁`, `K_S = kernelShadow k S f₀ f₁ = Q_S ⊓ ker Λ`.

The sub-capacity theorem (`ShadowDescentSharpBound`, `#Bad = e + 1` exactly) is **banked and
untouched**.  Everything below concerns the structure of the problem itself and the regime
`n < k + 3e`.

---

## 1. `K = ker Λ` versus `E^⊥`, and `K_S` as the shortened dual of `E`

**Theorem (`kernelShadow_eq_extDualOn`).**
`K_S = { μ : supp μ ⊆ S } ⊓ E^⊥`, where `E^⊥ = {μ : ⟨μ,g⟩ = 0 for all g ∈ E}` and
`E = C + ⟨f₀,f₁⟩` (`extCode`, `extDualOn`).

So the kernel shadow is not a two-step construction (dual of `C`, then kernel of the syndrome):
it is *one* object, the **shortening of the dual of the extended code to the window `S`**.  Its
Hamming-dual reading is immediate from the definition: a vector supported in `S` annihilates `E`
iff its restriction annihilates the punctured code `E|_S`, i.e. `K_S ≅ (E|_S)^⊥`.  The whole
shadow family is therefore the shortened/punctured dual data of the single rank-≤2 object `E`,
which is exactly why it is invariant under moving `(f₀,f₁)` inside its coset modulo `C`
(`kernelShadow_sub_polyWord`, banked).

## 2. Bad supports through the rank of `E/C` restricted to the support — an exact equivalence

Write `restrKer k S f₀ f₁ ⊆ F²` for the kernel of the restriction map
`E/C → E|_S / C|_S` in the coordinates `(α,β) ↦ α f₀ + β f₁` (`restrKer`).  Then:

* **rank loss two = line-closeness**: `restrKer = ⊤ ↔ LineCloseOn k S f₀ f₁`
  (`restrKer_eq_top_iff_lineCloseOn`).  The official noncontainment condition is *precisely* the
  statement that the restriction does not lose two ranks;
* **exact equivalence** (`isBad_iff_restrKer_eq_span`):

  `IsBad k e f₀ f₁ γ  ↔  ∃ S, |D| ≤ |S| + e  and  restrKer k S f₀ f₁ = F·(1,γ)`.

  A bad challenge is exactly a **projective point of `ℙ(E/C)` whose restriction to a large
  support loses exactly one rank**, and the lost line is the challenge itself.  No hypotheses.
* dimension form: `finrank restrKer = 1` on a bad window
  (`finrank_restrKer_of_isBad_window`);
* weight form (`isBad_iff_exists_light_rep`): `γ` is bad iff the coset `f₀ + γ f₁ + C` has a
  representative `v` of Hamming weight `≤ e` such that the complementary window `D ∖ supp v`
  does not explain the whole line.  This is the coset-leader reading of the same fact and it is
  the form used in the structure theorem.
* duality (`mem_restrKer_iff_forall_synMap`): `restrKer` is the annihilator of `im Λ_S ⊆ F²`, so
  the projective kernel in `E/C` and the projective syndrome direction of
  `ProjectiveSyndromeDirection` are orthogonal complements of one another; the two pictures are
  the same picture.

**Corollary — the theory is exactly rank two** (`card_badSet_le_one_of_dependent`): if `f₀,f₁`
are linearly dependent modulo `C` (`dim E/C ≤ 1`) then `#Bad ≤ 1`.  Unconditional, valid beyond
capacity.  So `E` really is the fundamental object: everything nontrivial is a statement about
rank-exactly-two extensions.

## 3. The invariant of many different shadows

The rank profile `S ↦ dim (E/C)|_S = 2 − dim restrKer(S)`, equivalently the corank of `K_S`
inside `Q_S`, is the invariant that the shadow family measures: `#Bad` counts the rank-one
windows and records their kernel lines.  Beyond capacity, however, the *decisive* invariant is
not the profile itself but the following pair of representable data attached to `E`:

* the **relative weight of the 2-dimensional quotient**: the least size of `supp a ∪ supp b`
  over pairs `a ≡ f₀`, `b ≡ f₁ (mod C)` — the relative generalized weight `M₂(E,C)`.  Two bad
  challenges force `M₂(E,C) ≤ 2e` (the witness-preserving descent);
* the **absolute low-weight spectrum of `C`** at radius `3e`.

The structure theorem says the bad set is controlled by exactly these two numbers, and nothing
else.

## 4. What must decrease beyond capacity

Shortening is capacity-neutral (it preserves `n − k`), and the descent to defect support `≤ 2e`
is unconditional but *also* capacity-neutral: it does not by itself bound `#Bad`.  The quantity
that has to move is the comparison

  `M₂(E,C) ≤ 2e`   (always available after two bad challenges)
  versus
  `d(C) > 3e`      (available only below capacity).

If `d(C) > 3e`, the light representatives of *all* bad challenges lie in one fixed 2-dimensional
`C`-complement inside `E` — **global rigidity** — and the pencil count closes the problem.  If
`d(C) ≤ 3e` the light representatives may leave that plane, and each departure is *literally* a
nonzero codeword of weight `≤ 3e`.  That is the additional invariant: the number of distinct
deviation codewords, which is at most the low-weight spectrum count of `C`.

## 5. The obstruction to fibre-disjointness, and what overlapping fibres force

Sub-capacity, the official windows cut the defect support into disjoint nonempty fibres.  The
obstruction is now identified exactly.  Fix two bad challenges `γ₀ ≠ γ₁`, let `v_γ` be light
representatives and let `(a,b)` be the reference pair they produce (`a ≡ f₀`, `b ≡ f₁ mod C`,
`|supp a ∪ supp b| ≤ 2e`).  Define the **deviation**

  `Φ(γ) = a + γ·b − v_γ ∈ C`,   `wt Φ(γ) ≤ 3e`,   `Φ(γ₀) = Φ(γ₁) = 0`.

*Fibres of different challenges overlap only through a nonzero deviation.*  On a fixed level set
`Φ⁻¹(c)` (a **cluster**) the light representatives are again a genuine pencil
`(a − c) + γ·b`, and there the classical argument applies verbatim:

**Pencil counting lemma** (`card_le_succ_of_pencil_light`, no code-theoretic hypothesis): if
every member of a pencil `γ ↦ a + γ·b`, `γ ∈ T`, has weight `≤ e` and vanishes somewhere on
`supp a ∪ supp b`, then `#T ≤ e + 1`.

The vanishing hypothesis is exactly the official noncontainment condition, and the size bound
`|supp a ∪ supp b| ≤ 2e` is automatic from two members of the pencil.  Hence **every cluster has
at most `e + 1` challenges**, and:

**Theorem (`card_badSet_le_succ_mul_succ_card_lowWeight`), no hypotheses at all:**

  `#Bad ≤ (e + 1) · (1 + #{c ∈ C : c ≠ 0, wt c ≤ 3e})`.

Equivalently (`lt_card_lowWeightCodewords_of_card_badSet`): a bad set larger than
`(e+1)(1+t)` forces more than `t` distinct nonzero codewords of weight `≤ 3e`.  Many
overlapping fibres are paid for, one by one, in low-weight codewords — this is the algebraic
content of the overlap.

**Localised form (the sharpest statement proved here), `exists_localised_cluster_bound`:** there
is one set `A` of at most `2e` coordinates — the descent support `supp a ∪ supp b` — such that

  `#Bad ≤ (e+1)·(1 + #{c ∈ C : c ≠ 0, wt c ≤ 3e, |supp c ∖ A| ≤ e})`.

So the cost is not merely finite: every deviation codeword is supported in the fixed `2e`-set of
the witness-preserving descent apart from at most `e` coordinates.  The global form above is
this statement with the localisation forgotten (`localLowWeightCodewords_subset`).

Disjunctive form (`card_badSet_le_succ_or_exists_lowWeight`): **global rigidity**
(`#Bad ≤ e + 1`) **or explicit finite cost** (a nonzero codeword of weight `≤ 3e` exists), the
witness-preserving descent being built into both branches.

### Explicit finite cost

`card_lowWeightCodewords_le`: for Reed–Solomon, with `m = n − w`,

  `#{c ∈ C : c ≠ 0, wt c ≤ w} ≤ C(n, m) · q^(k − m)`,

because such a codeword is a nonzero polynomial of degree `< k` vanishing on `m` domain points,
hence divisible by the nodal polynomial of an `m`-subset, and the pair (subset, cofactor) is a
complete invariant.  Combining (`card_badSet_le_explicit_cost`):

  `#Bad ≤ (e + 1) · (1 + C(n, n − 3e) · q^(k − (n − 3e)))`, unconditionally.

Below capacity `m = n − 3e ≥ k`, no nonzero codeword qualifies
(`lowWeightCodewords_eq_empty`) and the bound collapses to `#Bad ≤ e + 1`
(`card_badSet_le_succ_of_capacity`) — the banked sub-capacity constant, re-derived without the
hypothesis `1 ≤ k` and without any interpolation step.  Together with the banked sharpness
construction this is again *exact* below capacity.

## 6. Scope, hypotheses, and what is **not** claimed

* The pencil lemma and the cluster decomposition use **only linearity** of the code: the
  deviation `Φ(γ)` is a codeword by construction and the counting is code-free.  The
  Reed–Solomon/MDS structure enters at exactly one place, the cost factor — through the minimum
  distance (emptiness below capacity) and through the nodal factorisation (the closed formula).
  So the statement is a theorem about rank-2 extensions of a linear code, with the MDS/RS
  parameters substituted at the end.
* The theorem is an upper bound; it does **not** claim that the bound is attained beyond
  capacity, and it is consistent with the superpolynomial lower bounds already in this
  repository (those instances come with correspondingly many low-weight codewords).
* No performance, benchmark or implementation claim is made anywhere.

## 7. Boundary-consistency test at `e = 978945`

`RankTwoDeployedBoundary.lean`, arithmetic only, no tuning:

* `testRadius_capacity_iff` — at rate `1/2` the rigid branch for `e = 978945` requires block
  length `n ≥ 5 873 670`;
* `testRadius_blocklength_le` — at the relative radius recorded in `DeployedTargetGap`
  (`δ = 0.46782684`) a row with `e = 978945` has `n ≤ 2 092 539`;
* `testRow_beyond_rigid_branch` — hence the rigid branch is unavailable for that row, by a
  factor of about `2.8`; the cost branch is the operative one;
* `three_deployedRadius_gt_capacity` — block-length-free form: `3δ > 1 − ρ`;
* `testRow_lowWeight_nonvacuous` — and at those parameters `3e` exceeds the minimum distance, so
  the cost term is genuinely nonzero.

The test is a consistency check on the location of the row relative to the two branches.  It is
not a bound on `#Bad` for that row, and no attempt is made to optimise it.

## 8. Where this leaves the programme

The remaining gap is now a single, sharply posed question about the code alone rather than about
shadows or windows:

> Beyond capacity, how many *distinct deviation codewords* can actually occur for one received
> pair — i.e. how large can the image of `Φ` be, given that all its values have weight `≤ 3e`
> and vanish outside a fixed `2e`-set union an `e`-set?

Any bound better than the full low-weight count feeds directly into
`card_badSet_le_succ_mul_succ_card_lowWeight` and improves the beyond-capacity theorem, without
touching the geometry established here.
