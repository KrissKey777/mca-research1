# GRAND MCA — the residual programme: refined instruction and plan

This document does two things, in the order requested.

1. **§1 restates the research instruction** in the language of *this* repository (official MCA
   over Reed–Solomon codes), keeping the discovery methodology and the tool rules of the
   original brief but replacing its imported vocabulary (`ResidualRSState`, `HigherDD`,
   `Short(C^⊥,S^c)`, `WitnessBad`, `Rank2 adapter`) by objects that either already exist here
   or are constructed here.
2. **§2 fixes the plan** that was then executed, with success and abort criteria.

Everything called *banked* below is machine-checked and `sorry`-free in this repository.

---

## §1 Refined instruction

### 1.1 What the object of study actually is here

Notation used throughout: `F` a field, `D ⊆ F` a finite evaluation domain, `n = |D|`,
`C = RS_k(D) ⊆ F^D` the Reed–Solomon code of degree `< k`, `e` the proximity radius,
`q = |F|`, and `(f₀,f₁)` the received pair spanning the line `γ ↦ f₀ + γ f₁`.

*Official badness* (`Root.CodingTheory.IsBad`, banked equivalent to the literature definition
via `GG25Literal.strongMCA_iff_GG25MCA`): `γ` is bad if some window `S ⊆ D` with `|S| ≥ n − e`
explains `f₀ + γ f₁` by a codeword but does **not** explain the whole line.
`#Bad = |badSet k e f₀ f₁|`, `ε_mca = #Bad/q`.

The original brief's spine

> `WitnessBad → Q_S = Short(C^⊥, S^c) → (K_S, ℓ_S) → ResidualRSState(X_D, r) → terminal structure
> or strict descent`

is, in the vocabulary of this repository, already realised up to its fourth arrow:

| brief | here | status |
|---|---|---|
| `WitnessBad` | `IsBad`, `badSet` (`MCA.lean`) | banked |
| `Q_S = Short(C^⊥, S^c)` | `rsDualOn k S` = shortened dual, and `kernelShadow_eq_extDualOn`: `K_S` is the shortened dual of the *extension* `E = C + ⟨f₀,f₁⟩` | banked (`FixedShadowLift.lean`, `RankTwoExtension.lean`) |
| `(K_S, ℓ_S)` | `kernelShadow`, `localSyndrome`, the label `ℓ(S) = [−γ_S : 1] ∈ PG(1,F)` | banked (`ProjectiveSyndromeDirection.lean`) |
| `ResidualRSState(X_D, r)` | **missing — this run supplies it** | new |
| terminal structure ∨ strict descent | `badSet_descent_dichotomy` (descent), `card_badSet_le_succ_mul_succ_card_lowWeight` (finite cost) | banked |

So the instruction is *not* "invent a new bridge to an external skeleton". It is:

> **Make the residual state a first-class object of this theory, find the invariant of the
> residual state that controls rigidity, and prove the rigidity theorem in that invariant.**

### 1.2 The precise open question, restated

The brief asks:

> What additional structure of RS shortenings prevents arbitrarily many invisible projective
> directions, or forces a smaller residual state?

Made precise here. After a witness-preserving descent, the instance is replaced by a *residual
state*: a pair `(a,b)` congruent to `(f₀,f₁)` modulo `C` and supported on a window `A`. A bad
challenge is *explained* by a polynomial `q_γ` of degree `< k`; if `q_γ = 0` the challenge is
*visible* (it is caused by the residual defect itself) and the classical fibre argument applies;
if `q_γ ≠ 0` the challenge is *invisible* — it is caused by a codeword that the window cannot
see. So:

* invisible directions live in the **shortenings** `Short(C, A ∪ Z)`, `Z ⊆ D \ A`, `|Z| ≤ e`;
* the structure that kills them is a *dimension count on the residual domain*, not the
  capacity condition on the ambient one.

### 1.3 Discovery methods (kept from the brief, with the local reading)

* **Hypothesis minimisation.** After each lemma, delete/generalise hypotheses and record the
  exact level at which it lives: linear code → MDS → evaluation code → RS. Concretely: the
  fibre/pencil step uses only linearity; the vanishing step uses only "degree `< k` and `k`
  roots ⟹ `0`", i.e. the evaluation-code level; nothing here needs `RS` beyond that.
* **Converse mining.** Prefer exact characterisations. Every one-sided bound must be asked for
  its converse; a shortening being trivial should be an *iff*, not an implication.
* **Representation switching.** The same object as: primal shortening `Short(C,B)`, dual
  constraints `rsDualOn`, kernel shadow `K_S`, restriction kernel `restrKer ⊆ F²`, projective
  label `ℓ(S) ∈ PG(1,F)`, polynomial residual `q_γ`.
* **Counterexample-guided refinement.** Test candidate universal statements on tiny models
  before formal investment; use failure to locate the missing hypothesis.
* **Boundary metamathematics.** Every theorem strong enough to be interesting must be audited
  against the known extremal families of this repository (gap-one pencil, capacity-gap pencil,
  subspace pencil, Frobenius/linear-set families). A theorem that also "closes" those families
  is wrong.
* **Invariant mutation.** If an invariant only yields smooth cardinal bounds, enrich it until it
  separates the families the abstract matroid cannot.
* **Reuse before rebuild.** Search the repository first (`rg`, `exact?`, local search) — this
  project already contains ~83 000 lines of coding theory; a "new" lemma is usually a rename.
* **Build discipline.** Build *only* the modules actually added, minimally, keeping the modular
  file architecture; never rebuild the world to check one lemma.

### 1.4 The shape of the wanted result

Preferred form: `Structure ⟺ rigidity / finite cost / canonical residual state`, with Grand MCA
a **corollary**, never the statement. Forbidden: brute force, Johnson-radius tuning, raw overlap
counting, or a predetermined rank-2 adapter.

---

## §2 The plan (as executed)

**Step 1 — name the residual state.** Define `ResidualRSState k D f₀ f₁`: a codeword pair
`(p₀,p₁)` together with a window `A` outside which the defects `a = f₀ − p₀`, `b = f₁ − p₁`
vanish. Its **rank** is `|A|`. Prove the state is *faithful*: it has literally the same bad set
as the original instance (reuse `badSet_sub_polyWord`).
*Success:* the structure and `badSet_eq` compile. *Abort:* impossible, definitions.

**Step 2 — the canonical invariant.** Define the **joint defect**
`jointDefect k f₀ f₁ = min |{x : f₀ x ≠ p₀(x) ∨ f₁ x ≠ p₁(x)}|` over codeword pairs: the rank of
the *smallest* residual state. Prove it is attained, monotone under exhibited pairs, and
`≤ 2e` whenever at least two challenges are bad (reuse `badSet_descent_dichotomy`).

**Step 3 — the rigidity theorem in the residual invariant.** Prove, with no capacity
hypothesis:

> if `k + rank + e ≤ n` for some residual state of that rank, then `#Bad ≤ e + 1`,
> and moreover `#Bad ≤ rank`.

Mechanism: on `S \ A` the residual defect vanishes on `≥ k` points, so the explaining polynomial
is forced to be `0` — there are **no invisible directions** — and then the zero sets
`M_γ = {x ∈ supp a ∪ supp b : a(x) + γ b(x) = 0}` are nonempty (officiality) and pairwise
disjoint (a point cannot kill two challenges), each missing at most `e` points of the support.
*Success:* sorry-free proof. *Abort:* a counterexample in a tiny model.

**Step 4 — Grand-MCA-style corollaries.** Derive: the sub-capacity bound `#Bad ≤ e+1` for
`k + 3e ≤ n` with *no* auxiliary hypothesis; the dichotomy `#Bad ≤ e+1 ∨ n < k + jointDefect + e`;
and the contrapositive obstruction `e+1 < #Bad ⟹ n < k + 3e`.

**Step 5 — the shortening geometry, with an exact converse.** Define `shortCode k B` =
`Short(C,B)` (codewords vanishing outside `B`) and prove the **exact** criterion
`shortCode k B = ⊥ ↔ (B = ∅ ∨ k + |B| ≤ n)`. Identify the invisible directions of a residual
state with the nonzero elements of `Short(C, A ∪ Z)`, `|Z| ≤ e`, so that the rigidity hypothesis
of Step 3 is *exactly* the vanishing of all of them.

**Step 6 — localised cost.** Refine the banked global cost
`#{c ∈ C : c ≠ 0, wt c ≤ 3e} ≤ C(n,3e)·q^{k+3e−n}` to the residual one: the deviation codewords
are stratified by `Z = supp c \ A` and each stratum sits in `Short(C, A ∪ Z)`, giving
`≤ Σ_{|Z| ≤ e} (q^{k−(n−|A|−|Z|)} − 1)`, i.e. the combinatorial factor drops from
`C(n,3e) ≈ n^{3e}` to `C(n−|A|,≤e) ≈ n^{e}`.

**Step 7 — boundary audit.** Check the rigidity hypothesis against the known extremal families:
they must all violate it. For the gap-one pencil `f₀ = x^{k+1}`, `f₁ = x^k` prove
`jointDefect ≥ n − k`, hence `k + jointDefect + e ≥ n + e > n`: the hypothesis fails, as it must.

**Step 8 — report the smallest remaining obstruction.** State exactly what is missing for Grand
MCA in the residual language.
