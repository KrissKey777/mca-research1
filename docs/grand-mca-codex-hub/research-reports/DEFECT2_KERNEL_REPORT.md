# DEFECT-2 FRONTIER BREAK — report

All Lean statements below live in the new module
`RequestProject/Root/CodingTheory/HankelLocatorKernel.lean` (sorry-free; axioms
`propext`, `Classical.choice`, `Quot.sound` only, audited in `RequestProject/Main.lean`).
The exact GF(p) probe is `analysis/hankel_kernel_defect_probe.py`.

Throughout: `E` is the error support, `a_x ≠ 0` the amplitudes, `S r = ∑_{x∈E} a_x x^r` the
moment/syndrome sequence, `H i j = S(i+j)` the `rows × cols` Hankel matrix, and a kernel
vector is read as a polynomial `L` of degree `< cols`.  `Λ_E = ∏_{x∈E}(X − x)`.
In the MCA pencil of `JOHNSON_STRUCTURAL_DICHOTOMY_REPORT.md`: `rows = n − k − e`,
`cols = e + 1`, `d = 2e − (n−k)`.

---

## REQUIRED REPORT BLOCK

**VANDERMONDE LOCATOR LEMMA: PROVED.**
`eval_eq_zero_of_hankelRel` / `supportLocator_dvd_of_hankelRel`: if the kernel vector
satisfies `rows ≥ |E|` consecutive recurrence equations then `Λ(x) = 0` for every `x ∈ E`,
hence `Λ_E ∣ Λ`.  Proved exactly as proposed (moment expansion
`∑_j λ_j S_{i+j} = ∑_{x∈E} a_x x^i Λ(x)` plus Vandermonde non-degeneracy, the latter proved
directly from the Lagrange basis rather than from a determinant).  The general Vandermonde
annihilation step is `eq_zero_of_moments_vanish`.

**NUMBER OF AVAILABLE RECURRENCE EQUATIONS: `m = rows = n − k − e = e − d`.**
Confirmed from the pencil's own dimensions, not assumed: the Hankel block is
`(n−k−e) × (e+1)`, its entries run over `S_0 … S_{n−k−1}`, i.e. over the *entire* syndrome
window of an `RS_{<k}` code of length `n`.  At the schedule `n = 2²⁰`, `k = 2¹⁹`,
`e = 262145`: `rows = 262143 = e − 2` (`defect_two_schedule`).

**AUTOMATIC SUPPORT RANGE: `|E| ≤ n − k − e = e − 2 = 262143`.**
Exactly the range predicted in the mission text.

**BOUNDARY SUPPORTS: `|E| ∈ {e−1, e} = {262144, 262145}`.**

**DEFECT-2 KERNEL DIMENSION: 3, and now explained.**
For `|E| ≥ rows` (and `|E| ≤ cols`) the kernel splits as
`(cols − |E|)` locator directions `⊕ (|E| − rows)` non-locator directions, total
`cols − rows = d + 1 = 3` — independent of which boundary layer one is on:
`|E| = e−1` gives `2 + 1`, `|E| = e` gives `1 + 2`.
`hankelRel_first_boundary` states the `|E| = rows+1` case explicitly.

**TESTED KERNEL FACTORIZATION `ker H = Λ_E · P_{≤ d}`: TRUE exactly on the automatic range,
FALSE on the boundary layers — and this is now a theorem, not a test.**

* Positive: `hankelRel_iff_locator_mul` — for `rows ≥ |E|`,
  `L ∈ ker H ⟺ L = Λ_E·G` with `deg G < cols − |E|`; i.e. `ker H = Λ_E · F[X]_{≤ d}` with
  `d = cols − 1 − |E|`.
* Sharp iff: `hankelKernel_locator_law_iff` — for `E ≠ ∅`, `|E| ≤ cols`, nonzero amplitudes,
  *every* kernel vector is divisible by `Λ_E` **iff** `rows ≥ |E|`.
* Complete description in all cases: `hankelRel_iff_values` — `L ∈ ker H` iff the value
  vector `x ↦ a_x L(x)` on `E` equals `R(x)·v_x` for some `deg R < |E| − rows` (`v_x` the GRS
  multiplier `(∏_{y≠x}(x−y))⁻¹`); polynomial form `hankelRel_iff_seed_decomposition`:
  `ker H = { (R·L₀ mod Λ_E) + Λ_E·G : deg R < |E| − rows }`, where `L₀` is the interpolant of
  `x ↦ v_x / a_x` (`kernelSeed`).

**STATUS BOUNDARY `|E| = e−1`: KILLED for the kernel-only route.**
`exists_hankelRel_nonvanishing` gives a kernel vector vanishing at *no* point of `E`.
Worse for route 3B: that vector has degree `< |E|`, whereas every nonzero multiple of `Λ_E`
has degree `≥ |E|`, so the *minimal-degree / primitive* kernel vector is precisely a
non-locator (`exists_minimal_hankelRel_not_locator`).  A minimality argument cannot repair
the layer; it points the wrong way.

**STATUS BOUNDARY `|E| = e`: KILLED for the kernel-only route,** by the same theorems
(`rows < |E| ≤ cols` is all they need); here the non-locator part is 2-dimensional.

**ANNIHILATOR FAMILY SIZE:** unchanged, `B ≈ n·e ≈ 2³⁸·⁰⁰⁰⁰⁰⁶`, comfortably inside the
KoalaBear sextic budget `2⁵⁷·⁹³²¹` (slack ≈ 19.93 bits).  **Not cashed out** — the family's
validity still needs kernel-vector-⇒-locator at the two boundary layers, which the results
above show cannot come from the Hankel kernel alone.

**UNCONDITIONAL δ > 1/4: NO.**  No new radius is certified.  The certified unconditional
radius at `ρ = 1/2` remains `δ = 0.177124…`; the `δ > 1/4` schedule theorem remains
conditional exactly as before.

**LEAN STATUS:** new sorry-free module with 17 declarations; whole project builds; axiom
audit clean.

**GENERAL DEFECT-d CONJECTURE:** *settled, in the sharp form.*
`ker H = Λ_E · F[X]_{≤ d}` holds **iff** `|E| ≤ rows = e − d`.  Equivalently the conjectured
law is exactly the statement "there are at least as many recurrence rows as errors"; the top
`d` layers `|E| ∈ {e−d+1, …, e}` are *not* covered, and on each of them the kernel acquires
`|E| − rows` genuinely non-locator directions.  So the observed multiplicity `d+1 = 3` is
**not** "true locator times an arbitrary low-degree factor" on the boundary layers: at
`|E| = e−1` only a 2-dimensional subspace of the 3-dimensional kernel consists of locator
multiples, and at `|E| = e` only a 1-dimensional subspace does.

**NEXT SINGLE BOTTLENECK:** a *source of extra equations* for the top `d` layers.  Route 3A
(extra endpoint syndrome relations) is dead inside the syndrome data itself: the
`(n−k−e) × (e+1)` block already consumes all `n − k` available syndromes, and the maximum
number of consecutive recurrence rows available for a locator of degree `≤ e` is exactly
`(n−k) − (e+1) + 1 = n−k−e`.  Any additional relation must therefore come from *outside* the
single-syndrome-vector picture — e.g. from the badness data that the current chain discards
(the `¬ LineCloseOn` conjunct), from a second parity check on a different `(k+1)`-subset, or
from a genuinely multi-syndrome (block) Hankel system.

**DECISION: REDUCE (with a KILL of the kernel-only sub-route).**
The frontier problem is no longer "control the kernel multiplicity": the multiplicity is now
completely understood.  It is: *supply `d` more independent moment equations, or an
independent certificate, for the top `d` support layers.*

---

## CHEAP FALSIFICATION (as requested, done first)

`analysis/hankel_kernel_defect_probe.py` — exact GF(p) linear algebra (full row reduction,
full kernel basis; no sampling, no floats) over `p ∈ {11, 13, 17, 31, 101, 1009}`, supports
`|E| = 1…5`, several RS domains and amplitude vectors, `d = 0…4`, `rows` ranging around
`|E|`.  **7920 instances.**

* `ker H = Λ_E · P_{≤d}` ⟺ `rows ≥ |E|` in **7920/7920** instances (no exceptions).
* Among the 2520 instances with `rows < |E| ≤ cols`: in **0** of them was every kernel vector
  a locator, and in **0** of them was the minimal-degree kernel vector a locator.
* Among the 5400 instances with `rows ≥ |E|`: **0** kernel vectors failed to be locators.

The Lean theorems then prove exactly this dichotomy at arbitrary parameters.

## WHAT THIS DOES AND DOES NOT CHANGE

It does *not* produce a frontier crossing; `ε_MCA ≤ 2⁻¹²⁸` at
`(n, k, e) = (2²⁰, 2¹⁹, 262145)` is **not** proved, and the earlier conditional statement is
untouched.  It does replace the previously vague obligation "control the kernel multiplicity
3" by a complete structure theorem plus an explicit counterexample family, so the remaining
obligation is now a statement about *extra information*, not about kernel geometry.

No novelty is claimed for the moment/Vandermonde argument (it is the classical
Berlekamp–Massey / key-equation ingredient, cf. the generalized key equation and block
Hankel literature); the contribution here is the exact iff, the complete kernel description
including the deficient case, and their machine-checked proofs.
