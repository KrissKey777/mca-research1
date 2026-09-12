# Support-covering triples for a large official bad-support family

*Module: `RequestProject/Root/CodingTheory/BadSupportCoveringTriple.lean`.
Axiom audit: `RequestProject/BadSupportCoveringTripleAxiomAudit.lean` (36 declarations, only
`propext`, `Classical.choice`, `Quot.sound`).  No `sorry`.*

## The question

> From a large official bad-support family, derive either a support-covering triple / nonzero
> obstruction, or a direct finite challenge-cost bound `≤ B*`.

The answer is a **single unconditional dichotomy** with `B* = e + 1`, proved from the `Res`/dual
side, for an **arbitrary linear code over an arbitrary alphabet** — no window condition of the
form `e·|B| + k ≤ n`, no rate condition, no distance condition, no non-degeneracy assumption,
and no bound on the size of the family.

## The object

`BadSupportFamily C e f₀ f₁` is a finite set `chal` of challenges together with a chosen
official bad support `supp γ` for each of them:

* `|(supp γ)ᶜ| ≤ e`;
* `AgreeOn C (supp γ) (f₀ + γ·f₁)` — the window explains its own point of the line;
* `¬ LineAgreeOn C (supp γ) f₀ f₁` — it does not explain the whole line.

This is exactly official badness with the existential support chosen once and for all, and
`exists_badSupportFamily` produces such a family from any finite set of officially bad
challenges (in particular from the whole `badSet`).

`Covering C S` ("`S` is support-covering") is `Short(C, Sᶜ) = ⊥`: no nonzero codeword is
invisible outside `S`; equivalently (`covering_iff_forall_eq`) two codewords agreeing on `S` are
equal, i.e. `S` contains an information set.

## 1. The engine: the unconditional line-class bound

`card_lineClass_le_card_compl` / `card_lineClass_le`.  For **any** pair of codewords `p₀, p₁`,
the challenges of the family whose own support is explained by the single codeword line
`γ ↦ p₀ + γ·p₁` number at most `|(supp γ₀)ᶜ| + 1 ≤ e + 1`, where `γ₀` is *any* member of that
class (so the sharp constant is governed by the smallest official bad support in the class).

Mechanism, in one line: if a challenge of the class agreed with the line everywhere on its
support, its support would explain the whole line, contradicting badness; so it must disagree
at some position of its support, that position determines the challenge (`γ = −u/v` on the
deviation pair `u = f₀ − p₀`, `v = f₁ − p₁`), and hence it lies outside every *other* support of
the class.  The disagreement positions are therefore pairwise distinct and all sit in one fixed
set of size `≤ e`.

## 2. The dichotomy

`card_le_or_exists_obstruction`.  For every bad-support family, **either**

* `#chal ≤ e + 1` (finite challenge cost `≤ B*`), **or**
* there are three pairwise distinct challenges `γ₁, γ₂, γ₃` of the family and an explicitly
  exhibited codeword `z ∈ Short(C, (S₁ ∩ S₂ ∩ S₃)ᶜ)` with `z ≠ 0` and `wt(z) ≤ 3e`.  In
  particular the triple is **not** support-covering.

Both branches are effective.  The obstruction is produced as
`z = c₃ − (p₀ + γ₃·p₁)`, where `(p₀, p₁)` is the codeword line obtained by solving the two
local explanations at `γ₁ ≠ γ₂` (`p₁ = (γ₂−γ₁)⁻¹(c₂−c₁)`, `p₀ = c₁ − γ₁ p₁`), and `γ₃` is any
challenge outside the line class of that pair.

Contrapositive (`card_chal_le_of_covering`): **no support-covering failure ⇒ challenge cost
`≤ e + 1`**.

## 3. The finite-cost branch

* `card_chal_le_of_noCore`, `card_badSet_le_succ_radius`: `NoCore C (3e)` — no nonzero codeword
  of weight `≤ 3e` — gives `#Bad ≤ e + 1` for the official `badSet` of an arbitrary linear code
  over an arbitrary alphabet.  This strengthens the banked `Alphabet.card_badSet_le`
  (`3e < d ⇒ #Bad ≤ n`) to `#Bad ≤ e + 1` at the same hypothesis, and it needs no window
  hypothesis at all (contrast with the banked `card_le_or_support_le`, whose branch structure is
  valid only inside `e·|B| + k ≤ n`).
* `card_badSet_le_succ_radius_of_minDist`: the same under `3e < d`.
* `epsMCA_le_of_noCore`: soundness error `≤ (e+1)/|F|`; `epsMCA_le_prize_threshold`:
  `≤ 2⁻¹²⁸` as soon as `(e+1)·2¹²⁸ ≤ |F|`.
* `card_badSet_interleaved_le_succ_radius`: the same bound for the **interleaved** code `C^⋈κ`
  (the shape of the deployed extension-field instance, `κ = Fin d`) under the hypothesis on the
  **base** code alone, since covering and `NoCore` are interleaving invariants
  (`covering_interleavedCode_iff`, `noCore_interleavedCode`).

## 4. Reading the covering condition on the other sides

* **Dual / kernel shadow** (`covering_iff_dual_finrank`): via the complementary-window (Wei)
  identity, `S` is support-covering for `M` exactly when
  `dim Short(M^⊥, S) = |S| − dim M`, i.e. the dual code shortened at `S` attains its maximal
  possible dimension.  Failure of covering is precisely a deficiency of the dual shadow on the
  triple window.
* **Matroid / dual support** (`exists_two_codewords_of_not_covering`): a non-covering window
  contains no information set — two distinct codewords already agree on it.
* **`Res` filtration** (`covering_iff_lostStage_bot`): `Covering C S` says the Lost-filtration of
  the pair `⊥ ≤ C` has not yet jumped at the complementary window.
* **MDS/RS residual regime** (`covering_of_mds`, `card_badSet_le_of_mds`): for an MDS code of
  dimension `k`, covering holds for every window with `|Sᶜ| + k ≤ n`; hence `k + 3e ≤ n` puts
  every Reed–Solomon instance in the `B* = e + 1` branch.

## 5. What a failed triple forces (the structural branch)

* **Jump form** (`relDefect_one_le_of_not_covering`, `card_le_or_relDefect_one_le`): the
  dichotomy in its strongest parametric shape —
  **either `#chal ≤ e + 1`, or the first jump `δ₁` of the `Res`-filtration of `⊥ ≤ C` (the
  minimum weight of the code) is `≤ 3e`.**  Nothing else can happen; no hypothesis is used.
  In particular the minimal window realising the first jump — the terminal window of the
  obstruction — has size at most `3e`.
* **Gluing-defect charging** (`finrank_shortening_union_three`,
  `one_le_gluingDefect_sum_of_not_covering`): if no *single* bad support hides a core
  (`NoCore C e`) then the three complementary windows have exactly additive budgets,
  `dim Short(C, W₁∪W₂∪W₃) = gluingDefect C W₁ W₂ + gluingDefect C (W₁∪W₂) W₃`, and a failed
  covering triple forces that sum to be `≥ 1`: the obstruction is paid for, exactly, by
  non-modularity of the shortening on the three windows.  A code whose shortening glues exactly on
  windows of size `≤ e` cannot produce a failed triple.

## 6. Scope and honest limits

* The bound `B* = e + 1` is on the challenges of *one* bad-support family, hence on `#Bad`; it
  says nothing about lists of codewords and uses no list-decoding argument.
* The structural branch converts "no support-covering triple" into `δ₁ ≤ 3e`, i.e. into a
  genuine small-weight codeword.  It does **not** bound the number of challenges in that branch:
  the family may then be large, and the banked witnesses (`UniqueDecodingGapWitness`) show that
  no bound of this shape can hold when `d ≤ 3e`.  So `3e < d` (equivalently `NoCore C (3e)`) is
  the exact frontier of the `B* = e+1` branch for this argument, and the obstruction returned in
  the other branch is the minimal one: a nonzero codeword of weight `≤ 3e` supported in the
  complement of a triple intersection of official bad supports.
* Everything is stated for an arbitrary `F`-linear code inside `ι → A` with `A` an arbitrary
  `F`-module; the MDS section additionally assumes a one-dimensional alphabet, and the dual
  section is stated for `A = F`.
