# SUBRESULTANT ↔ CORRELATED-AGREEMENT BRIDGE — REPORT

New module: `RequestProject/Root/CodingTheory/SubresultantCorrelatedBridge.lean`
(namespace `Root.CodingTheory.Subresultant`).  No existing certified declaration was modified.
Only the module import and `#print axioms` lines were added to `RequestProject/Main.lean`.

## 1. EXACT TYPES / DEFINITIONS

Ambient: `{F : Type u} [Field F] [DecidableEq F] {D : Finset F}`, words `f₀ f₁ : ↥D → F`,
`BiPoly F := Polynomial (Polynomial F)` (outer variable `Z` = line parameter, inner `X` = code
variable), `specX x : BiPoly F →+* F[Z]`, `genWord f₀ f₁ x = C (f₀ x) + X · C (f₁ x)`.

* `IsWBKernel k e f₀ f₁ Lam Q : Prop` := `(∀ i, (Lam.coeff i).natDegree ≤ e) ∧
  (∀ i, (Q.coeff i).natDegree < k + e) ∧ ∀ x : ↥D, specX x Lam * genWord f₀ f₁ x = specX x Q`.
* `KernelNonzero k e f₀ f₁` := `∃ Lam Q, IsWBKernel k e f₀ f₁ Lam Q ∧ Lam ≠ 0`;
  `nu` = minimal `Z`-degree of such a `Lam`; `MinimalKernelVector` = a kernel element attaining it.
* `colPoly k Lam Q j` (columns `Λ·X^j`, `j < k`, and `Q`), `subresMatrix`, `subresDet`
  (the `(k+1)`-minors), `canGens` (all minors of kernel elements with `Lam.natDegree ≤ nu`),
  `canIdeal := Ideal.span (canGens …)`, `W_can := normalize (generator canIdeal) : F[Z]`.
* RS correlated agreement (frozen, exactly the predicate of `CORRELATED_COMMON_SUPPORT_GATE.md`
  and of `card_badSet_le_of_correlatedAgreement`):
  `∃ q₀ q₁ : F[X], q₀.degree < k ∧ q₁.degree < k ∧
   D.card ≤ (polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁).card + e`.
  Common-error-support normal form: `commonErrorSupport`, `correlatedAgreement_of_commonErrorSupport`.
* Existing endpoints used, unchanged: `card_badSet_le_of_correlatedAgreement (hk : 1 ≤ k)
  (hkD : k + 2e ≤ D.card) … : #badSet ≤ e`; `badSet_card_le_poly (hk) (hkD)
  (hK : KernelNonzero …) (hW : W_can ≠ 0) : #badSet ≤ (k+1)e + 1`;
  `card_badSet_le_of_wbDet_ne_zero (hk : 1 ≤ k) (h : wbDet k e f₀ f₁ ρ ≠ 0) : #badSet ≤ e + 1`.

## 2. ZERO-KERNEL / W_CAN SEMANTICS (Gate 0)

* **Q0.1** `W_can` is total: it is defined for every input, including a zero kernel.
* **Q0.2** If the kernel is zero then `canGens = ∅` (`canGens_eq_empty_of_kernel_zero`), hence
  `canIdeal = ⊥` and `W_can = 0` (`W_can_eq_zero_of_kernel_zero`).
* **Q0.3** **Yes — `W_can = 0` can hold vacuously.**  It is proved (not conjectured) that the
  vacuous case really occurs and really breaks the naive dichotomy: `kernelNonzero_not_automatic`
  exhibits `F = 𝔽₂`, `D = F`, `k = 1`, `e = 0`, `f₀ = id`, `f₁ = 0`, where `1 ≤ k`, `k + 2e ≤ |D|`,
  the kernel is zero, `W_can = 0`, and RS correlated agreement at radius `e` **fails**.
* **Q0.4** The existing nonzero branch `badSet_card_le_poly` **does** carry `KernelNonzero`.

Consequence: the bridge `W_can = 0 ⇒ RSCorrelatedAgreement` is *false unconditionally*; the
nonzero-kernel hypothesis is genuinely load-bearing and is kept explicit.

## 3. STRONGEST CONSEQUENCE OF `W_can = 0`

Under `hK : KernelNonzero`, take `MinimalKernelVector (Lam, Q)` (`exists_minimalKernelVector`).
Machine-checked consequences of `hW : W_can = 0`, in order of increasing strength:

1. *ideal/minor vanishing* — `canGen_eq_zero_of_W_can_eq_zero` : every `subresDet k e Lam Q ρ = 0`
   **identically in `Z`** (from `W_can_dvd` + `zero_dvd_iff`), for every `ρ : Fin (k+1) → Fin (k+e)`.
2. *kernel existence over `F(Z)`* — `exists_kernel_dependence` : the `k+1` columns of
   `[T_Λ(Z) | Q(Z)]` are `F[Z]`-linearly dependent (determinantal rank over the fraction field
   `FractionRing F[Z]`, then denominators cleared by `IsLocalization.exist_integer_multiples_of_finset`).
3. *algebraic identity* — `exists_bivariate_relation` : `∃ d ≠ 0, a : Fin k → F[Z]` with
   `iZ d · Q = − (Lam · ∑_{j<k} iZ (a j) · C (X^j))`.

Route taken: **B (kernel extraction)**.  Route A was unavailable (no existing predicate is
equivalent to the frozen RS predicate); no constant locator, minimal kernel vector of special
shape, common denominator or particular minor was assumed in advance.

## 4. BRIDGE PROOF (Gate 5) — SUCCESS

`rsCorrelatedAgreement_of_W_can_eq_zero (hK : KernelNonzero k e f₀ f₁) (hW : W_can k e f₀ f₁ = 0)
: ∃ q₀ q₁, q₀.degree < k ∧ q₁.degree < k ∧ D.card ≤ (polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁).card + e`.

Mechanism: specialise the identity of §3.3 at `X := x` for `x ∈ D`, use the kernel equation
`specX x Lam · (f₀ x + Z f₁ x) = specX x Q`, and read the `Z`-coefficients at `t` and `t+1`,
where `t = d.natTrailingDegree`.  This yields **one fixed pair** `q₀, q₁` of degree `< k`
(explicitly `q₀ = −(d_t)⁻¹ ∑_j (a_j)_t X^j`, and `q₁` the corresponding second-order term) such
that `f₀ x = q₀(x)` and `f₁ x = q₁(x)` at every `x` with `specX x Lam ≠ 0`.  The exceptional set
`E = {x ∈ D | specX x Lam = 0}` satisfies `|E| ≤ e` (locator degree bound), and the common
support statement is converted by the existing `correlatedAgreement_of_commonErrorSupport`.
Hypotheses used: exactly `hK` and `hW`; no hypothesis on `|F|`, on `k`, or on the window.

Gate 3 compliance: the argument is symbolic (polynomial identity ⇒ evaluations); it never
infers a polynomial identity from vanishing at all points of a finite field, and never replaces
the RS predicate by a statement over `F̄`.

## 5. EXACT RADIUS

Radius **exactly `e`**.  The only inequality used is `|E| ≤ deg_Z-free locator bound ≤ e`, coming
from `(Lam.coeff i).natDegree ≤ e` in `IsWBKernel`.  No `e + θ`, `e + 1` or `2e` loss anywhere.

## 6. KERNEL EXISTENCE AUDIT (Gate 7)

* **Negative part.**  `kernelNonzero_not_automatic` (see §2) proves that
  `k ≥ 1 ∧ k + 2e ≤ n ⇒ K ≠ 0` — the mission's proposed T3 — is **false**.
* **Positive part (replacement).**  `kernelNonzero_of_forall_wbDet_eq_zero (hk : 1 ≤ k)
  (hkD : k + e ≤ D.card) (h : ∀ ρ, wbDet k e f₀ f₁ ρ = 0) : KernelNonzero k e f₀ f₁`.
  Proof: determinantal rank of the Welch–Berlekamp pencil over `F[Z]` (rows `↥D`, columns
  `WBIdx k e = Fin (e+1) ⊕ Fin (k+e)`), via `FractionRing F[Z]` and denominator clearing
  (`exists_nonzero_polyVec_of_forall_det_eq_zero`); the resulting vector assembles into
  `(Λ, Q)` with the required degree bounds, and `Λ ≠ 0` because otherwise every `Q`-coefficient
  is a polynomial of degree `< k + e ≤ |D|` vanishing on `D`.

## 7. FINAL DICHOTOMY

* **T1** `rsCorrelatedAgreement_of_W_can_eq_zero` — §4 (needs `KernelNonzero`).
* **T2** `card_badSet_le_of_W_can_eq_zero (hk : 1 ≤ k) (hkD : k + 2e ≤ D.card) (hK) (hW)`
  `: #badSet ≤ e` — pure composition with `card_badSet_le_of_correlatedAgreement`.
* **T4a** `card_badSet_le_dichotomy (hk) (hkD) (hK) : #badSet ≤ (k+1)e + 1` (no hypothesis on `W_can`).
* **T4b** `card_badSet_le_unconditional (hk : 1 ≤ k) (hkD : k + 2e ≤ D.card) : #badSet ≤ (k+1)e + 1`
  — **no structural hypothesis at all**.  Split on the pencil: if some `wbDet ≠ 0`, the certified
  `card_badSet_le_of_wbDet_ne_zero` gives `#Bad ≤ e + 1 ≤ (k+1)e + 1`; otherwise §6 supplies
  `KernelNonzero` and T4a applies.  (`[Fintype F]` is required, as in all `badSet` statements.)

## 8. AXIOM / SORRY AUDIT

`rg -n "sorry|admit"` on the new module: no occurrence (only the word “sorry” inside the header
docstring).  Full `lake build` succeeds (8213 jobs).  `#print axioms` in `RequestProject/Main.lean`
for `W_can_eq_zero_of_kernel_zero`, `exists_kernel_dependence`, `exists_bivariate_relation`,
`rsCorrelatedAgreement_of_W_can_eq_zero`, `card_badSet_le_of_W_can_eq_zero`,
`card_badSet_le_dichotomy`, `kernelNonzero_not_automatic`,
`kernelNonzero_of_forall_wbDet_eq_zero`, `card_badSet_le_unconditional`:
each reports exactly `[propext, Classical.choice, Quot.sound]`.

## 9. DECISION

**A — FULL MACHINE-CHECKED CLOSURE.**

`k ≥ 1 ∧ k + 2e ≤ n ⇒ #Bad ≤ (k+1)e + 1` is machine-checked with no additional structural
assumption (`card_badSet_le_unconditional`).

Two exact caveats, both machine-checked rather than assumed:

* the *zero bridge itself* `W_can = 0 ⇒ RSCorrelatedAgreement` holds at radius exactly `e`
  **only under a nonzero Welch–Berlekamp kernel**, and this hypothesis is provably not removable
  (`kernelNonzero_not_automatic`): with a zero kernel `W_can = 0` is vacuous;
* the unconditional bad-set bound therefore does **not** proceed by the naive `W_can` case split
  alone: the kernel hypothesis is discharged by the separate pencil-rank gate of §6.
