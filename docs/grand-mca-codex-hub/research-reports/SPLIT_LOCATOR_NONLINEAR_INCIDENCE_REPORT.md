# Nonlinear split-locator incidence — pencil rank-drop layer

**Primary status: `HIGHER_ORDER_INCIDENCE_LEMMA`.**

No bound `#Γ ≤ B*` is claimed, and no counterexample is claimed. What is new is a set of exact,
machine-checked incidence lemmas for the split-locator pencil, one of them *unconditional and
quantitative* (a proved constant below `B*` on an exactly delimited subset of the challenge
space), plus an exact characterisation that localises the whole remaining difficulty in a single
rank identity.

Frozen parameters (unchanged):

```
p = 2130706433,  F = F_{p^6},  D = μ_{2^21},  n = 2097152,  k = 1048576,
r = 1048576,     e = 978944,   t = 1118208,   w = r − e = 69632,
B* = 274980728111395087
```

New Lean modules (purely additive; nothing existing was modified):

* `RequestProject/Root/CodingTheory/PencilRankDrop.lean` — general pencil theory over any field.
* `RequestProject/Root/CodingTheory/SplitLocatorPencilIncidence.lean` — the deployed application.
* `RequestProject/SplitLocatorPencilAxiomAudit.lean` — `#print axioms` for all 40 load-bearing
  declarations; every one prints `[propext, Classical.choice, Quot.sound]`. No `sorry`, no
  `native_decide`, no new axiom.

---

## PHASE 0 — orientation and adapter safety

**Result: no `OFFICIAL_ADAPTER_GAP`.** The adapter is replayable from the exact source
definitions inside the new modules.

* Orientation is kept explicit. The pencil acts on the **monic** locator
  `Q_E(X) = ∏_{x∈E}(X − x)`, never on the reciprocal `Λ_E(X) = ∏(1 − xX)`; the reciprocal is
  used nowhere in the new modules. The repository's `LocatorOrientation.lean` records
  `Λ_E = reverse(Q_E)` and `Λ_E(y) = y^e Q_E(1/y)`, and the new modules do not silently identify
  the two.
* Every matrix/map in the new modules states its argument type: `synLin w f : F[X] →ₗ (Fin w → F)`,
  `synRestrict w e f : F[X]_{<e+1} →ₗ (Fin w → F)`, and the pencil is
  `A + γ·B = synRestrict w e f₀ + γ • synRestrict w e f₁`, all acting on the **monic** locator
  space. `locLinRestrict_eq_pencil` proves that this pencil *is* the repository's official
  `locLin` restricted map, so all statements below are statements about the official object.
* Both directions of the adapter are exercised in the new file:
  forward (`kernel_witness_of_locatorChallenge`: official badness ⇒ monic degree-`e` split kernel
  vector, with the nondegeneracy witness), and the equality
  `card_badSet_eq_ncard_locatorChallengeSet` is used inside every deployed theorem
  (`deployed_badSet_bound_of_monic_rank_lt`, `deployed_badSet_decomposition`, …), so the deployed
  conclusions are about `#badSet` itself, not about a relaxation.
* `pencil_ker_of_locatorSystem` / `locatorSystem_of_pencil_ker` prove that "kernel of the pencil"
  and "the `w` global syndrome equations in the correct locator orientation" are the same
  condition, in both directions.

---

## PHASE 1 — the new mathematics

### 1. The pencil is a Hankel (moment) pencil — exact identity

`synLin_eq_hankel`:

```
synLin w f Q j = ∑_{i ≤ deg Q} Q_i · m_{i+j},      m_s := gsynd f (X^s).
```

So `A` and `B` are the `w × (e+1)` **Hankel matrices of the moment sequences of `f₀` and `f₁`**,
and the deployed object is the Hankel pencil `H(m⁰ + γ·m¹)` with `w = 69632` rows and
`e + 1 = 978945` columns. (The repository's Hankel collapse bounds are *not* inherited: they live
in the unique-decoding regime `k + 2e + 1 ≤ n`, which the deployed row violates by a wide margin.
Only the identification is claimed.)

### 2. The rank-drop theorem (general, unconditional)

`PencilRank.ncard_rank_lt_le`: for arbitrary linear `A, B : V →ₗ[F] W` with `W`
finite-dimensional and **any** reference scalar `γ₀`,

```
#{ γ : rk (A + γB) < rk (A + γ₀B) }  ≤  rk (A + γ₀B).
```

Proof: a square window `pr ∘ (A + γ₀B) ∘ ι` of size `ρ = rk (A + γ₀B)` is constructed which is
*literally the identity* (`exists_pencil_witness`, built from a basis of the range, a complement
projection and chosen preimages); its determinant along the pencil is a polynomial of degree
`≤ ρ` (`pencilDet`, `natDegree_pencilDet_le`) that is nonzero at `γ₀`, and any `γ` of smaller rank
is a root.

Deployed instance (`ncard_rank_drop_le_width`, `deployed_rank_drop_le`):
**the rank-drop locus of the deployed syndrome pencil has at most `w = 69632 ≤ B*` elements.**
This is unconditional, and it is the first exactly delimited subset of the challenge space with a
*proved* bound below `B*`.

### 3. The monic-locator condition is exactly a rank identity

`range_comp_ker_subtype_eq` / `rk_comp_ker_subtype_eq` / `exists_ker_vec_of_rk_eq`, and their
deployed packaging `monicChallengeSet_eq_rank_locus`:

```
γ has a monic degree-e kernel vector   ⇔   rk( (A+γB)|_{coeff_e = 0} ) = rk(A+γB).
```

Both directions are proved; the forward direction uses that `x = h + c·v` with `h` in the
hyperplane whenever `v` is a kernel vector off it (so the ranges are *equal*, not merely
comparable), the converse uses equality of ranges of equal finite rank and rescales the witness to
be monic. Since `Q_E` is monic of degree exactly `e` (`topCoeffLin_locVec`) and, because
`0 ∉ D = μ_{2^21}`, has nonzero constant term (`constCoeffLin_locVec_ne_zero`), the official bad
set is contained in this rank locus for *both* functionals.

### 4. The unconditional decomposition

`PencilRank.ncard_le_drop_add_residual`, deployed as `deployed_badSet_decomposition`:

```
#Bad(f₀,f₁)  ≤  69632  +  #{ γ bad : rk((A+γB)|_{coeff_e=0}) = max_δ rk(A+δB) }.
```

i.e. every bad challenge is either a rank-drop challenge (at most `w = 69632 ≤ B*` of them) or a
**residual** challenge, one at which the monic hyperplane costs no rank. No hypothesis beyond the
deployed parameters is used.

Conditional corollaries (`deployed_badSet_bound_of_monic_rank_lt`,
`deployed_badSet_bound_of_const_rank_lt`): if the hyperplane-restricted pencil never attains the
maximal rank — for the leading-coefficient hyperplane, or for the constant-coefficient hyperplane —
then

```
#Bad ≤ 69632 ≤ B*.
```

### 5. Route A — higher-order incidence of the joint syndrome vectors

With `v_γ = B Q_γ ≠ 0` (nondegeneracy) and `A Q_γ = −γ · v_γ`:

* `joint_pair_independent`: two **distinct** challenges never admit a dependency of their joint
  vectors `(A Q, B Q) ∈ F^{2w}`. This is the pairwise fact in exact algebraic form: no window, no
  interpolation, no parameter inequality — so it is *not* the interpolation-vacuous pairwise
  comparison of the previous round.
* `joint_divided_difference` (the new higher-order identity): if
  `∑_i c_i (A Q_i, B Q_i) = 0`, then for every base point `j`

  ```
  ∑_i c_i (γ_i − γ_j) · v_i = 0,
  ```

  a dependency of the `f₁`-syndrome vectors that is one term shorter. For three challenges this
  forces the three syndrome directions to be collinear.
* `card_le_two_mul_width_of_regular`: if the only coefficient family annihilating both `{v_i}` and
  `{γ_i v_i}` is zero — the exact "no challenge-compatible dependency" condition — then there are
  at most `2w = 139264 ≤ B*` challenges.

---

## PHASE 2 — discriminating tests

* **Sharpness of the dichotomy** (`PencilRank.residual_branch_nonvacuous`, exact, over an
  arbitrary field, exhaustive by construction). There is a pencil and a functional `φ` for which
  every scalar has a kernel vector off `ker φ`, the restricted pencil always has full rank, and the
  rank-drop locus is *empty*. Consequently the rank-drop bound alone can never bound the monic
  challenge set, and the hypothesis of `ncard_le_of_restricted_rank_lt` is a genuine dichotomy
  branch, not a formality. This test falsifies the conjecture "monicity always costs rank".
  It says nothing about which branch the deployed pair is in.
* No toy model over a small field is used to assert anything about `F_{p^6}`; no deployed claim
  rests on a toy computation.

---

## PHASE 3 — required reporting

**1. Strongest exact new identity.**

```
{ γ : ker(A + γB) contains a monic polynomial of degree exactly e }
      =  { γ : rk( (A + γB)|_{coeff_e = 0} ) = rk(A + γB) },
```

together with the unconditional root count
`#{γ : rk(A+γB) < rk(A+γ₀B)} ≤ rk(A+γ₀B) ≤ w = 69632`, and the identification of `A`, `B` as the
Hankel matrices of the two moment sequences.

**2. The first implication that fails.**

From splitness we extract only *single linear* facts about the kernel vector (leading coefficient
`= 1`; constant coefficient `≠ 0`). Each such fact is one linear condition, while
`dim ker(A + γB) ≥ e + 1 − w = 909313`. The implication that fails is therefore

> "a fixed nonzero linear functional is nonvanishing somewhere on the kernel" ⇒ "γ is constrained",

because by the rank identity of item 1 this is *equivalent* to the restricted pencil not losing
rank, and losing rank is exactly the codimension-one event that the sharpness example shows may
never happen. Concretely: the deployed bound would follow if the truncated Hankel pencil
`H(m⁰+γm¹)` with its last column deleted had, for all but few `γ`, strictly smaller rank than the
full one — and nothing proves that it does.

**3. Why this is stronger, and where it is weaker, than the pairwise obstruction.**

*Stronger.* The pairwise-overlap route was quantitatively vacuous: its conclusion (line-closeness
on a window of `2w = 139264 ≤ k` points) holds for *every* pair by Lagrange interpolation, so it
excludes nothing and yields no numerical bound whatsoever. The present layer yields, for the first
time, an unconditional numerical statement below `B*` about the deployed challenge space
(`#rank-drop locus ≤ 69632`), an unconditional decomposition `#Bad ≤ 69632 + #residual`, and two
conditional deployed bounds `#Bad ≤ 69632` with explicitly stated, checkable hypotheses. The
Route-A identity is genuinely higher-order: the three-point relation is a divided-difference
identity, not the two-window intersection, and it does not degenerate into the `2w ≤ k`
interpolation fact.

*Weaker.* Everything proved here uses only the codimension-one shadow of splitness. It does not
touch `Q | X^n − 1` beyond monicity and non-vanishing at `0`, so it cannot by itself decide the
residual case, and the sharpness example shows the residual case is logically possible. No claim
is made that the deployed residual set is small.

**4. The smallest next equation to attack.**

The truncated-Hankel rank gap of the deployed moment pencil:

```
ρ'(γ) := rk of  H(m⁰ + γ m¹)  with the column of index e removed,
ρ(γ)  := rk of  H(m⁰ + γ m¹),                      (w = 69632 rows, e+1 = 978945 columns)

question:  for how many γ is ρ'(γ) = ρ(γ) = max_δ ρ(δ) ?
```

Equivalently, in moment coordinates: for how many `γ` is the last Hankel column
`(m_{e}, m_{e+1}, …, m_{e+w−1})(γ)` in the span of the previous `e` Hankel columns *and* the
resulting kernel vector split over `μ_{2^21}`? By the rank identity of item 1 this is exactly the
residual set of the decomposition, and by the sharpness example it cannot be settled by rank
counting alone: the next real input must be a **second, independent** consequence of
`Q | X^n − 1` — the natural candidate being the multiplicative restriction
`Q(0)^n = 1` for `Q` split over `μ_n`, combined with the Hankel-Cramer form of the kernel, which is
the smallest equation that mixes the additive (rank) and multiplicative (root-of-unity) data.

---

## Do-not-reopen compliance

Not used, not reopened: unconstrained kernel annihilators as a bound source (the rank-drop
theorem is a statement about *where the kernel jumps*, not about the kernel being nonzero);
the pairwise `2w = 139264` overlap; generic interpolation on windows `≤ k`; Johnson/list-size
bounds; residual ledgers, support partitioning, classLoad, pricing; the `m = 8` construction
branch (untouched and kept separate); the `Q_E`-versus-`Λ_E` confusion; and no toy model is used
to support a deployed claim.
