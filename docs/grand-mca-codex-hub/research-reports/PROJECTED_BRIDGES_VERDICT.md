# PROJECTED-RÉDEI BRIDGES — VERDICT

**Mission: decide the two bridges. Nothing else.**
Constraints respected: no Rédei–Szőnyi, no full projected-Rédei theorem, no new axiom, no
`sorry`/`admit`/`native_decide`, no numerical experiment, no refactoring; exactly one new Lean
file was created (`RequestProject/Root/CodingTheory/ProjectedSecantBridges.lean`), no existing
file was touched.

---

## OUTCOME **A** — both bridges are valid.

Both are now *machine-checked*, not merely argued on paper. Axiom audit of every certifying
lemma: `[propext, Classical.choice, Quot.sound]` only.

---

## TEST 1 — secant → projected list: **PASS**

The containment reduces to **one** algebraic identity, and the existing secant lemmas are
strong enough; no new geometry was needed.

**The identity** (`projDirection_eq_apply_secantSlope`):

```
projDirection λ c γ γ'  =  (γ − γ')⁻¹ · (λ(c γ) − λ(c γ'))  =  λ( (γ − γ')⁻¹ • (c γ − c γ') )
                        =  λ( q_{γγ'} ) .
```

Exactly two properties of `λ` are consumed: **additivity** (`map_sub`) and **`F`-homogeneity**
(`map_smul`) for the scalar `(γ − γ')⁻¹`. Nothing else.

**The two existing lemmas that close it** (both from
`RequestProject/Root/CodingTheory/ListGeometrySlopeBound.lean`, unchanged):

| step | lemma | gives |
| --- | --- | --- |
| slope is a codeword | `Alphabet.slope_mem` | `q_{γγ'} ∈ C` |
| slope is near `f₁` | `Alphabet.hammingDistance_slope_le` | `d(f₁, q_{γγ'}) ≤ 2e` |

Hence `q_{γγ'} ∈ L(f₁,2e)` and `λ(q_{γγ'}) ∈ λ(L(f₁,2e))`.

**Certified statement** (`projDirections_subset_image_nearbyList`):

> for every `F`-linear `λ : (ι → F) →ₗ[F] F`, every witness selection `(S γ, c γ)_{γ ∈ B}` with
> `|ι| ≤ |S γ| + e`, `c γ ∈ C`, `f₀ + γ f₁ = c γ` on `S γ`:
> `D_λ(B) ⊆ λ( L(f₁,2e) )`.

No genericity, no injectivity of `λ`, no primality, no bound on `|B|`, no minimum-distance
hypothesis, no non-collinearity. Both the pointwise form and the set form are proved.

*Recorded scope limit (not an obstruction to the bridge as stated):* `F`-homogeneity is
indispensable — a merely `F_p`-linear `λ` over `F = F_{p^m}` breaks step 2 (the `F₄`/Frobenius
three-point computation of `PROJECTED_REDEI_CLAIMS.md` §2.4). The Lean statement carries
`F`-linearity, so it is unaffected; extension fields stay OPEN and separate.

---

## TEST 2 — coordinate admissibility of `λ_x`: **PASS**

The three properties are proved **separately**, as required.

| property | lemma | hypotheses used |
| --- | --- | --- |
| **A. first-coordinate injectivity** | `projPoint_injective` | *none* — `γ ↦ (γ, λ(c γ))` is injective for every `λ`, so `\|S_λ\| = \|B\|` |
| **B. no vertical collapse** | `projPoint_fst_ne` | *none* — distinct parameters give distinct abscissae, so every determined direction is an affine slope, never `∞` |
| **C. non-collinearity** | `not_collinear_projPoint_of_mem_supp` | exactly `hx : x ∈ supp(V_W)` (plus `γ₀ ∈ B`, `B' ⊆ B ∖ {γ₀}` fixing the base point) |

### Does `hx` really imply non-collinearity? **Yes.** Exact lemma chain:

1. `exists_secantSlope_ne_of_mem_supp` — `x ∈ supp(V_W)` is inherited by a **generator**: if
   every generator `q_γ − q_{γ'}` vanished at `x`, then `V_W = span{…} ≤ ker(ev_x)` and no member
   of `V_W` could be nonzero at `x`. So `hx` yields `γ, γ' ∈ B'` with `q_γ(x) ≠ q_{γ'}(x)`, i.e.
   `ev_x ∉ Ann(V_W)`.
2. `apply_secantSlope_const_of_collinear` — the collinearity criterion, proved from Mathlib's
   `collinear_iff_of_mem`: if `S_λ = {(γ, λ(c γ)) : γ ∈ B}` is collinear with base point
   `γ₀ ∈ B`, then the direction vector `v` has `v₁ ≠ 0` (because `r·v₁ = γ − γ₀ ≠ 0`) and every
   projected slope equals `v₂/v₁`; in particular `λ(q_γ)` is **constant**.
3. Combining: `hx` contradicts constancy, so `S_{ev_x}` is **not** collinear.

`coordFunctional_admissible` bundles the three certificates only as a final record; each is
proved on its own and none of the three needs strengthening.

**Nothing beyond `hx` is required**: no primality of `|F|`, no `|B| ≤ p`, no MCA structure
(`f₀, f₁, e`, admissibility, code being RS), no genericity, no finiteness of `F`. In particular
no definition had to be strengthened to make Lean accept it.

Companion fact, also certified: `exists_mem_suppSpace_of_ne_bot` — `V_W ≠ 0` implies
`supp(V_W) ≠ ∅`, so a coordinate `x` satisfying `hx` exists exactly when the witness
configuration is non-collinear (`V_W ≠ 0`). The hypothesis `hx` is therefore not vacuous and is
the sharp one: if `V_W = 0` every projection is collinear, for every functional, so no `λ`
whatsoever is admissible.

---

## Exact hypotheses needed for the full projected-Rédei theorem

Collecting only what the two bridges consume (the external Rédei–Megyesi/Szőnyi direction
bound is *not* part of this mission and is not proved anywhere here):

1. `F` a field; the projecting functional `λ` **`F`-linear and `F`-valued** on `C`
   (`F_p`-linearity over `F_{p^m}` is not enough);
2. a witness selection: for each `γ ∈ B` a codeword `c γ ∈ C` and an agreement set `S γ` with
   `|ι| ≤ |S γ| + e` and `f₀ + γ f₁ = c γ` on `S γ` — this is what feeds
   `hammingDistance_slope_le`;
3. non-collinearity of the witness configuration, in the usable form
   `∃ x ∈ supp(V_W)` with `V_W = span{ q_γ − q_{γ'} }` based at some `γ₀ ∈ B`; then `λ = ev_x`
   is admissible, giving `|S_λ| = |B|`, no vertical direction, and `S_λ` non-collinear;
4. for the quoted direction theorem only: `F = F_p` prime and `|B| ≤ p` (automatic for
   `B ⊆ F_p`).

Under 1–4, `D_λ ⊆ λ(L(f₁,2e))` and the admissibility side conditions hold, which is precisely
the input the Szőnyi step needs. Nothing else in the chain is missing on the MCA side.

---

## Reduction signal (per the mission's standing rule)

The whole of Bridge 2 collapses to a single general mechanism rather than a pile of local
lemmas: **admissibility is the linear condition `λ ∉ Ann(V_W)`**, and the coordinate functionals
`{ev_x}_{x ∈ ι}` already cover it (`supp(V_W) ≠ ∅` whenever `V_W ≠ 0`). Bridge 1 similarly
collapses to the single identity `direction = λ(secant slope)`, i.e. to the statement that
projection is a morphism of *slope* data, not merely of points. The only genuinely external
ingredient left in the projected-Rédei chain is the Rédei–Megyesi/Szőnyi direction theorem in
`AG(2,p)`.

---

## Lean artefacts

`RequestProject/Root/CodingTheory/ProjectedSecantBridges.lean` (new; builds clean):

* `projDirection_eq_apply_secantSlope` — the reduction identity;
* `projDirection_mem_image_nearbyList`, `projDirections_subset_image_nearbyList` — Test 1;
* `projPoint_injective`, `projPoint_fst_ne` — Test 2 A and B;
* `exists_secantSlope_ne_of_mem_supp`, `exists_mem_suppSpace_of_ne_bot`,
  `apply_secantSlope_const_of_collinear`, `not_collinear_projPoint_of_mem_supp` — Test 2 C;
* `coordFunctional_admissible` — the assembled record.
