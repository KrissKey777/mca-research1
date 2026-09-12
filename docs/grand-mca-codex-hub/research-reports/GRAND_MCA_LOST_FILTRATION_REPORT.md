# The universal Lost-filtration: one exact sequence behind Rank2, fixed-shadow pencils and residual absorption

*Companion to `RESULTS.md` §132.  All statements below are machine-checked and `sorry`-free;
axiom audit `RequestProject/LostFiltrationAxiomAudit.lean` (77 declarations, only `propext`,
`Classical.choice`, `Quot.sound`).  Nothing existing was modified or deleted.*

New modules:

* `RequestProject/Root/CodingTheory/LostFiltration.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationSpectrum.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationInformationSet.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationMDS.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationRankTwo.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationTorsor.lean`

---

## 1. The question, and the object that answers it

The absorption theory of §§128–131 has four objects that kept reappearing: the rank-two
extension `E = C + ⟨f₀,f₁⟩` and its quotient `E/C`; the subspace `Lost(W) ≤ F²` of pencil
directions that degenerate at a window; the fixed-shadow phenomenon (a window explains one
challenge, or the state collapses); and the absorbed-core torsor over `Short(C,W)²`.  They were
tied together by a *dimension identity*, proved separately in each rank-two incarnation.

The object that explains all four at once has **nothing to do with rank two**.  For an arbitrary
nested pair of `F`-linear codes `C ≤ E` inside `ι → A` and a window `W ⊆ ι` put

> **`lostStage C E W  =  E ⊓ (C ⊔ P_W)`**

— the part of `E` that becomes invisible modulo `C` once the window is deleted.  It is a
submodule of the interval `[C,E]`, monotone in `W`, equal to `C` at `W = ∅` and to `E` at
`W = univ`: an exhaustive filtration of the pair indexed by the lattice of windows, packaged as
an order homomorphism `lostStageHom` (a functor on the poset of windows).

## 2. The universal exact sequence

`lostStage_eq_sup_shortening`: for `C ≤ E`,

    Lost(C,E,W)  =  C ⊔ Short(E,W),

i.e. the sequence

    0 ⟶ Short(C,W) ⟶ Short(E,W) ⟶ Lost(C,E,W)/C ⟶ 0

is exact; with `finrank_kernelShadow` this is the dimension identity previously proved by hand
in the rank-two setting.  **The invisible cores are literally the kernel of the filtration.**
That single sentence is the source of everything below.

## 3. The lattice law, and the invisible core as its exact obstruction

The filtration is monotone always, and `lostStage_inter_le` gives one half of meet-preservation
unconditionally.  The other half holds *modulo the cores*:

> `lostStage_inter`: if `Short(C, W ∪ W') = ⊥` then `Lost(W ∩ W') = Lost(W) ⊓ Lost(W')`
> (equivalently `lostStage_inter_of_noCore` under `NoCore C w`).

and this is sharp: for the repetition code `C = ⟨(1,1)⟩` inside the full space on two positions
(`repCode`), each singleton window already gives `Lost = ⊤` while their intersection gives
`Lost = C` (`repCode_lostStage_inter_ne`), and the invisible core is present
(`repCode_shortening_ne_bot`).  So **the invisible core is exactly the obstruction to the
Lost-filtration being a lattice homomorphism** — a structural reformulation of the `NoCore`
hypothesis that the whole absorption theory turns on.

## 4. The defect spectrum, and why it climbs in unit steps

The jumps of the filtration are the invariants:

    δ_j(C,E) = min { |W| : dim Lost(C,E,W) ≥ dim C + j }      (`relDefect`)

— the relative weight hierarchy of the pair.  Two structural facts:

* **Deletion bound** (`finrank_lostStage_erase_le`): removing one position from a window costs
  at most `dim A` dimensions of the filtration.  Over a field alphabet (`dim A = 1`) this is one
  dimension, hence **`δ_j < δ_{j+1}`** (`relDefect_lt_succ`) and `j ≤ δ_j` (`le_relDefect`).
  A filtration of the interval `[C,E]` cannot gain two dimensions by adding one coordinate.
* **Singleton laws**: `dim E ≤ dim Lost(C,E,W) + (n − |W|)·dim A`
  (`finrank_le_finrank_lostStage_add`), whence `δ_j ≤ n − r + j` with `r = dim E − dim C`
  (`relDefect_le`); refined by the minimum distances of the two codes in
  `relDefect_le_of_minDistGe` and `le_relDefect_of_minDistGe`.

The two ends have their expected meaning: `δ_1` is the least weight of a word of `E` outside `C`
(`relDefect_one_le_card_support`, `exists_word_of_relDefect_one`), and `δ_r` is the least size of
a window into which `E` collapses modulo `C` (`lostStage_eq_top_iff`,
`exists_window_lostStage_eq_top`) — the joint defect.

## 4b. Information sets and the sharp Singleton law

The bound `δ_j ≤ n − r + j` of §4 is weak when the subcode is large.  The sharp *relative*
Singleton law needs one new ingredient, built here from scratch:

> `exists_information_set`: **every linear code has an information set** — a set `I` of `dim E`
> positions on which the code is rigid, `Short(E, Iᶜ) = ⊥`, equivalently the restriction
> `E → (I → A)` is an isomorphism (`exists_mem_agree_on_information_set`).

The proof is a greedy induction on the dimension using the deletion bound: as long as the code
is nonzero, some position separates a nonzero word, and passing to the kernel of that coordinate
drops the dimension by exactly one.

With it, at the complement of an information set **of the subcode** the filtration is already at
its top (`lostStage_compl_information_set`), because every word of the ambient space agrees with
a codeword of `C` on `I`.  Hence `δ_r ≤ n − dim C` (`relDefect_top_le_sub_finrank`), and since
the jumps are separated by at least their index gap (`relDefect_add_le`, from strict
monotonicity),

> **`relDefect_le_sharp`:  δ_j ≤ n − dim E + j   for every `j ≤ r`.**

## 5. Evaluation codes: the spectrum is computed exactly

When the *big* code is **MDS** the sharp Singleton law is matched by the distance lower bound
`le_relDefect_of_minDistGe`, and the spectrum is determined (`relDefect_eq_of_mds`):

> if `C ≤ E` have dimensions `k ≤ k'` and `E` has distance `n − k' + 1` — with **no hypothesis
> on the subcode `C`** — then for every `1 ≤ j ≤ k' − k`
>
>     δ_j(C,E) = n − k' + j.

The hierarchy is *maximal*: it jumps as late as the Singleton laws allow, in unit steps, from
`n − k' + 1` to `n − k`.  Specialised to Reed–Solomon (`relDefect_reedSolomon`):

    δ_j(RS_k, RS_{k'}) = |D| − k' + j.

## 6. Rank2, fixed shadows and absorption as corollaries

Let `E = C + ⟨f₀,f₁⟩` with `f₀, f₁` independent modulo `C` (`Dep = Lost(∅) = ⊥`).  Then
`dim E = dim C + 2` (`finrank_extension_of_dep`), the pair has relative dimension `2`, and

* `pencilDefect = δ_1` (`pencilDefect_eq_relDefect_one`), `jointDefect = δ_2`
  (`jointDefect_eq_relDefect_two`) — the two banked invariants *are* the two jumps;
* hence, over a field alphabet, **`pencilDefect < jointDefect`**
  (`pencilDefect_lt_jointDefect`), strictly.  This sharpens the banked
  `pencilDefect_le_jointDefect` and says that the **fixed-shadow band is never empty**: every
  genuine rank-two state has a window at which it degenerates in exactly one projective
  direction;
* `rank_two_regime_classification` collects the trichotomy quantitatively — below `pencilDefect`
  every window loses nothing; below `jointDefect` no window is terminal; a window of size
  `pencilDefect` carries a fixed shadow, a single point of `PG(1,F)`; a window of size
  `jointDefect` carries an absorbed residual state and none smaller does;
* for a code of dimension `k` the whole picture is confined to
  `pencilDefect ≤ n − k − 1 < jointDefect ≤ n − k`, with **no hypothesis on the code at all**
  (`jointDefect_le_sub_finrank`, `pencilDefect_le_sub_finrank`): a residual state can always be
  absorbed into the complement of an information set.  The earlier MDS-hypothesis versions
  `pencilDefect_le_of_mds`, `jointDefect_le_of_mds` are the special case.

The torsor side is the kernel of the same exact sequence: `absorbedCores C f₀ f₁ W` is nonempty
exactly when the filtration has reached its top (`absorbedCores_nonempty_iff_lostStage_eq`), its
translation module `corePairs C W = Short(C,W)²` vanishes exactly when the window hides no core
(`corePairs_eq_bot_iff`), and it is a torsor in the strict sense (`exists_unique_corePair`,
`absorbedCores_vadd_bijective`).  So the filtration is the obstruction theory of the torsor: the
top stage says *whether* a residual state exists, the kernel says *how many*.

## 7. Scope and what is not claimed

* Two Singleton laws are proved: the elementary `δ_j ≤ n − (dim E − dim C) + j` and the sharp
  relative one `δ_j ≤ n − dim E + j`; the latter is an equality when the big code is MDS.  The
  sharp law uses `dim A = 1`.
* Strict monotonicity of the spectrum, and therefore the strict inequality
  `pencilDefect < jointDefect`, is proved for a one-dimensional alphabet (`dim A = 1`), which
  covers all evaluation codes; for larger alphabets the deletion bound gives steps of at most
  `dim A`.
* No performance, implementation or optimality claim is made anywhere.
