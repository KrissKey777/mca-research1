# SUBRESULTANT_DEPENDENCY_AUDIT

Audit of the proof dependency structure of `WB_SUBRESULTANT_GATES.md` (+ `BAD_GAMMA_ALGEBRAIC_LOCUS_REPORT.md`).
No Lean file touched, no axiom, no `sorry`, no new theory, no strengthening of the theorem.

**Notation (frozen).** `D ⊆ F`, `|D| = n`, `f₀,f₁ : D → F`, radius `e`, rate `k ≥ 1`.
`𝒦` = WB kernel over `F[Z]`: pairs `(Λ,Q)`, `deg_X Λ ≤ e`, `deg_X Q < k+e`, `Λ(Z,x)(f₀(x)+Zf₁(x)) = Q(Z,x)` on `D`.
`ν` = minimal `deg_Z Λ` over `0 ≠ (Λ,Q) ∈ 𝒦`; `v = (Λ,Q)` a minimiser; `W = W_v` = gcd of the `(k+1)`-minors of `[T_Λ(Z)|Q(Z)]`;
`I_can` = ideal of all such minors over all `0 ≠ u ∈ 𝒦`; `W_can` = its monic generator.
`Close ⊆ F̄`, `Bad = badSet k e f₀ f₁ ⊆ F`.
Labels: **LEAN** = kernel-checked in this repository, **PAPER** = complete paper proof, **CHECKED** = exact small-instance arithmetic, **OPEN** = no proof.

---

## 1. NU RANGES

Common minimal hypotheses for all three: `𝒦 ≠ 0` and `k + e ≤ n` (this is what makes `Q` the unique interpolant, hence `(Λ,Q) ↦ Λ` injective and the kernel condition a *matrix pencil* `S(Z)λ = 0`, `S(Z) = S₀ + Z S₁`, `m = n−k−e` rows, `e+1` columns). `k+2e ≤ n` is **not** needed for any ν-bound.

| # | claim | status | minimal hypotheses |
|---|---|---|---|
| 1 | `k+2e ≤ n ⇒ ν ≤ e+1` | **PAPER**, true but **not minimal and not sharp** | implied by #2′ |
| 2 | `k+2e = n ⇒ ν ≤ e` | **PAPER**, but the wall hypothesis is **spurious** | implied by #2′ |
| 2′ | `𝒦 ≠ 0, k+e ≤ n ⇒ ν ≤ e` (uniform, interior *and* wall) | **PAPER** (micro-lemma M below) | `𝒦 ≠ 0`, `k+e ≤ n` |
| 3 | `k+3e ≤ n ⇒ ν = 0` | **CHECKED**; **PAPER only for `e ≤ 1`**; **OPEN for `e ≥ 2`** | `𝒦 ≠ 0`, `k+3e ≤ n` |

**Micro-lemma M (the only lemma added by this audit; classical, 6 lines).** *If a pencil `S₀+ZS₁` with `N` columns has a nonzero kernel vector over `F[Z]`, a minimal-degree kernel vector `v(Z)=Σ_{j≤ν}Z^j v_j` has `F`-linearly independent coefficients `v_0,…,v_ν`; hence `ν ≤ N−1`.* Proof: `v_0 ≠ 0` (else `v/Z` is smaller). Let `m` be least with `v_m = Σ_{j<m}c_j v_j`. Put `u_{m-1-t} := v_{m-1-t} − Σ_{i≤m-2-t} c_{i+1+t} v_i` for `t = 0,…,m−1`. Using `S₀v_0=0`, `S₀v_j = −S₁v_{j-1}`, `S₁v_ν=0` one checks `S₁u_{m-1}=0`, `S₀u_i + S₁u_{i-1} = 0`, `S₀u_0 = S₀v_0 = 0`, so `u(Z)=Σ_{i<m}u_iZ^i` is a kernel vector of degree `≤ m−1 < ν`, nonzero since `u_0=v_0`. Contradiction. With `N = e+1` this gives `ν ≤ e` uniformly — it replaces both the Cramer bound (`e+1`) and the separate wall count, and **removes the interior/wall distinction from the DAG**.

**Sharpness.** `ν ≤ e−1` is **false**: smallest witness `GapWitness` (`F₅, n=4, k=2, e=1`, in `UniqueDecodingGapWitness.lean`) has `ν = 1 = e`, and it attains `deg W = #Close = 4 = (k+1)ν+1`.

**Range 3, exact status.** The recorded proof (`BAD_GAMMA` §5) forms `G := Λ₀²Q₂ + Λ₁²Q₀ − Λ₀Λ₁Q₁`, uses `Q₂ = Λ₁f₁`, `deg G ≤ k+3e−1 < n`, hence `G ≡ 0`, then the gcd split `Λ₀=da, Λ₁=db` produces a `Z`-degree-0 kernel vector. `Q₂ = Λ₁f₁` holds **only if `ν = 1`** (in general `Q₂ = Λ₂f₀ + Λ₁f₁`, leaving the residual `Λ₀²Λ₂f₀`; adding the correction term `−Λ₀Λ₂Q₀` restores `G ≡ 0` but the subsequent division by `d²` no longer stays in `F[X]`, so only `a ∣ dQ₀`, not `a ∣ Q₀`, is obtained). So what is proved is: **`k+3e ≤ n ⇒ ν ≠ 1`**, hence with M: `ν = 0` when `e ≤ 1`. For `e ≥ 2` the case `2 ≤ ν ≤ e` is **OPEN**. Pencil theory alone cannot close it: the pencil `[Zb | −b]` (any `m`) has `ν = 1` with no common kernel of `S₀,S₁`, so the arithmetic of `f₀,f₁` must be used. A stronger version, `k+3e ≤ n+1 ⇒ ν = 0`, is **false**: `GapWitness` sits at `k+3e = n+1` with `ν = 1`.
Range 3 is **not used by any other arrow** (see §2); it only feeds the deep-interior corollary `#Close ≤ 1`, which duplicates the already-LEAN `card_badSet_le_succ_radius`.

## 2. PROOF DAG

Standing hypotheses of the whole graph: `k ≥ 1`, `D ⊆ F` with `|D| = n`, `k+2e ≤ n`, `𝒦 ≠ 0`, and `Close` taken in the **infinite** field `F̄`.

**Common part** (all arrows PAPER unless marked):

| arrow | name (proposed) | hypotheses | uses | assumes `W≠0`? CA-exclusion? ν-bound? |
|---|---|---|---|---|
| `𝒦 ≠ 0` ⇒ ∃ minimiser `v`, `ν` | `wbKernel_exists_minimal` | `𝒦 ≠ 0` | — | no / no / no |
| minimal ⇒ primitive `Λ(γ,·) ≠ 0 ∀γ∈F̄` | `wbMinimal_primitive` (1a) | minimality, `k+e ≤ n` | previous | no / **no** / no |
| `γ ∈ Close ⇒ rank[T_Λ(γ)|Q(γ)] ≤ k` | `wbClose_imp_minors_vanish` (1b) | `k+2e ≤ n`, `k ≥ 1`; LEAN core `wbPair_cross`, `wbPair_eq_mul_of_isCloseOn` | — | no / no / no |
| `rank ≤ k ⇒ γ ∈ Close` | `wbMinors_vanish_imp_close` (1c) | primitivity, `deg_X Λ ≤ e`; LEAN core `isCloseOn_of_wbPair_mul` | primitivity | no / no / no |
| `rank[·](γ) ≤ k ⇔ W_v(γ)=0` | `gcd_root_iff_minors_vanish` | none (gcd over `F̄[Z]`, `(Z−γ)` prime) | — | **no** (also correct when `W_v ≡ 0`: both sides = `F̄`) |
| ⇒ `Close = V(W_v)` | `wbClose_eq_zeroLocus` | union of the four above | — | no / no / no |
| `Close ⊆ V(W_u)` for **every** `0 ≠ u ∈ 𝒦` | `wbClose_subset_zeroLocus_any` (3a) | `k+2e ≤ n` | 1b (plus the trivial case `Λ'(γ,·)=0 ⇒ Q'(γ,·)=0`) | no / no / no |
| `W_can` defined, `W_can ∣ W_v` | `wbWcan_dvd` | `F[Z]` PID | definition of `I_can` only | no / no / no |
| `V(W_can) = Close` | `wbWcan_zeroLocus_eq_close` | above | 3a (`⊇`), `W_can ∣ W_v` + `Close = V(W_v)` (`⊆`) | no / no / no |

**Non-correlated branch** (hypothesis of the branch: `W_can ≠ 0`):

| arrow | name | hypotheses | uses |
|---|---|---|---|
| `W_can ≠ 0 ⇒ W_v ≠ 0` | `wbWv_ne_zero_of_wcan` | `W_can ∣ W_v` | — |
| `deg_Z` of every `(k+1)`-minor `≤ (k+1)ν+1` | `wbMinor_degree_le` (Gate 4) | `deg_Z Λ ≤ ν`, `deg_Z Q ≤ ν+1` (interpolation linearity), `k+e ≤ n` | — (**no** root count, **no** classification) |
| `deg W_can ≤ deg W_v ≤ (k+1)ν+1` | `wbWcan_degree_le` | `W_v ≠ 0` | two above |
| `#Close = #V(W_can) ≤ deg W_can` | `card_close_le_degree` | `W_can ≠ 0` | `V(W_can)=Close` |
| `#Bad ≤ #Close` | LEAN (`wbDet_eval_eq_zero_of_isBad` / `mem_badSet`) | `k ≥ 1` | — |
| `#Bad ≤ (k+1)ν+1 ≤ (k+1)e+1` | `card_bad_le_budget` | branch hypothesis | above + ν-range 2′ |

**Correlated branch** (`W_can = 0`):

`W_can = 0` ⇔ all minors of all `u ∈ 𝒦` vanish identically ⇒ (for `v`) `Q = Λ·P` over `F(Z)[X]`, `deg_X P < k` (`T_Λ` has rank `k` over `F(Z)` since `Λ ≢ 0`) ⇒ `P ∈ F[Z][X]` (2a, uses primitivity) ⇒ every `γ ∈ Close` by 1c ⇒ `Close = F̄` ⇒ `P = p₀+Zp₁` with `f₀|_S = p₀|_S`, `f₁|_S = p₁|_S`, `|S| ≥ n−e ≥ k` (2c, uses `k+e ≤ n`) = correlated agreement at radius `e`. Converse: CA ⇒ every `γ ∈ Close` ⇒ `V(W_u) = F̄` for all `u` ⇒ every `W_u ≡ 0` (**uses `|F̄| = ∞` only**) ⇒ `I_can = 0` ⇒ `W_can = 0`. LEAN anchor for one direction: `wbDet_eq_zero_of_correlatedAgreement`.

## 3. CANONICITY / CYCLES

**No cycle.** The suspected cycle `W≠0 ⇒ root count ⇒ classification ⇒ W≠0` does not exist: the classification `W_can = 0 ⇔ Close = F̄ ⇔ CA` never uses a root count or a degree bound; its only finiteness input is "a nonzero polynomial has finitely many roots over the infinite field `F̄`", which is a fact about `F̄`, not about `W_can`'s degree. The degree bound `deg ≤ (k+1)ν+1` is a statement about minors of a matrix with prescribed column degrees and is independent of `Close`.

Point-by-point:
* primitivity (1a) uses minimality + `deg_X Q < k+e ≤ n` — **does not use `Close ≠ F̄`**; ✔
* `Close ⇔ V(W)` (1b+1c) uses the cross-product and injectivity of multiplication by `Λ(γ,·)` — **does not use the degree bound**; ✔
* canonicity: `I_can`/`W_can` are defined from the kernel module and its minors only, with no reference to `Close`; `V(W_can) = Close` is derived afterwards — **not circular**; ✔
* `W = 0 ⇔ CA` — **does not assume `Close` finite** (it concludes `Close = F̄`); ✔
* wall argument — after micro-lemma M there is no separate wall argument, so it cannot depend on the interior inequality; the previously separate wall count and the interior defect theorem are independent anyway. ✔

**One genuine hidden hypothesis, recorded:** `Close` and `V(·)` must be read over `F̄` (infinite). Over the finite prime field the step "vanishes on all of `Close` ⇒ `W_u ≡ 0`" fails, and with it the direction `CA ⇒ W_can = 0`. Second, smaller: `k ≥ 1` is needed by 1b and by `Bad ⊆ Close`.

**Step 4 order, verified as mandated.** `W_u` (any nonzero `u`, arrow 3a) → `I_can := ⟨all (k+1)-minors of [T_{Λ'}|Q'] : 0 ≠ u=(Λ',Q') ∈ 𝒦⟩` → `W_can` = monic generator (`F[Z]` PID) → `V(W_can) = Close`. The definition of `W_can` is **independent of the `Close` theorem**. Divisibility: every minor of `v` lies in `I_can`, so `W_can` divides each of them, hence `W_can ∣ gcd = W_v`. Zero sets: (⊇) `Close ⊆ V(W_u)` for every `u` by 3a, and `V(W_can) = ⋂_u V(W_u)`, so `Close ⊆ V(W_can)`; (⊆) `W_can ∣ W_v` gives `V(W_can) ⊆ V(W_v)`, and `V(W_v) = Close` by 1a+1b+1c. Hence `V(W_can) = Close`. Degenerate consistency: `W_v ≡ 0 ⇔ W_can ≡ 0 ⇔ Close = F̄`.

## 4. W=0 STATUS

Exact theorem: **`W_can = 0 ⇔ Close = F̄ ⇔ f₀,f₁ have correlated agreement at radius `e``**, under `k+2e ≤ n`, `k ≥ 1`, `𝒦 ≠ 0`, `Close` over `F̄`.

| implication | status | note |
|---|---|---|
| `W_can = 0 ⇒ Close = F̄` | **PAPER** | via `Q = ΛP`, `P` polynomial (2a), then 1c |
| `Close = F̄ ⇒ W_can = 0` | **PAPER** | uses `|F̄| = ∞` |
| `W_can = 0 ⇒ CA at radius e` | **PAPER** | `P = p₀ + Zp₁`, `|S| ≥ n−e ≥ k` |
| `CA at radius e ⇒ W_can = 0` | **PAPER** (LEAN for the single-minor form: `wbDet_eq_zero_of_correlatedAgreement`) | via `Close = F̄` |
| all four | **CHECKED** | 4 random singular + all 625 multi-minimal instances of the `F₅,n=4,k=2,e=1` family |

**Bad in this branch: nothing is proved.** `Bad ⊆ Close = F̄` is vacuous, and the classification of `Close` is **not** a bound on `Bad`. The pencil mechanism yields no bound here; the earlier note that a global kernel vector "gives a bound of order `k+2e`" is itself recorded as an open gap (it needs pseudo-remainder control) and is assumed nowhere. Only the project's branch-independent bounds survive (`card_badSet_le_choose_radius`, the charging/list-geometry family), none of them better than the generic ones. **Status: OPEN.**

## 5. LEAN ORDER

Minimal order (each item depends only on earlier ones):

1. definitions: `𝒦`, `ν`, `T_Λ`, minors, `W_v`, `I_can`, `W_can`, `Close` over `F̄` (reuse `IsWBPair`, `wbVec`, `wbMatrix` from `WelchBerlekampPencil.lean`);
2. minimal element + primitivity: `wbKernel_exists_minimal`, `wbMinimal_primitive`;
3. specialisation/divisibility: `wbClose_imp_minors_vanish` (from LEAN `wbPair_cross`, `wbPair_eq_mul_of_isCloseOn`), `wbMinors_vanish_imp_close` (from LEAN `isCloseOn_of_wbPair_mul`, `not_isCloseOn_of_not_dvd`);
4. minor/subresultant characterisation: `gcd_root_iff_minors_vanish`, `wbClose_eq_zeroLocus`;
5. canonical generator: `wbClose_subset_zeroLocus_any`, `wbWcan_dvd`, `wbWcan_zeroLocus_eq_close`;
6. degree bound: `wbMinor_degree_le`, `wbWcan_degree_le`, plus micro-lemma **M** (`ν ≤ e`) as an independent leaf;
7. nonzero root count: `card_close_le_degree`, then `card_bad_le_budget` on top of the LEAN `Bad ⊆ Close`;
8. correlated-agreement equivalence: the four implications of §4;
9. final dichotomy: `W_can = 0` (⇔ CA) or `#Bad ≤ #Close ≤ deg W_can ≤ (k+1)ν+1 ≤ (k+1)e+1`.

Items 1–9 are independent of ν-range 3; the deep-interior corollary (`k+3e ≤ n ⇒ ν = 0 ⇒ #Close ≤ 1`) must be **omitted** from the formalisation, or formalised only in the proved form `k+3e ≤ n ⇒ ν ≠ 1` (which gives `ν = 0` for `e ≤ 1`).

## 6. DECISION

> **D. PAPER THEOREM OVERSTATED** — exactly one item: **ν-range 3**. `k+3e ≤ n ⇒ ν = 0` is claimed **PROVED** in
> `BAD_GAMMA_ALGEBRAIC_LOCUS_REPORT.md` §5 and quoted in `WB_SUBRESULTANT_GATES.md` §4 and §6, but the recorded
> argument proves only `k+3e ≤ n ⇒ ν ≠ 1`; for `e ≥ 2` the range `2 ≤ ν ≤ e` is unproved (CHECKED only), and no
> pencil-theoretic argument can close it. The deep-interior corollary `#Close ≤ 1` inherits that status.

Scope of the failure, stated precisely so the gate is not misread: the overstated item is a **leaf** of the DAG. The common part, both branches, the canonicity chain of §3 and the budget `#Bad ≤ #Close ≤ deg W_can ≤ (k+1)ν+1 ≤ (k+1)e+1` are acyclic, hypothesis-explicit and paper-proved, with `ν ≤ e` now uniform (micro-lemma M) instead of the previous split `e+1` / wall `e`. Formalisation of items 1–9 of §5 may therefore proceed; the deep-interior sharpening may not be stated as a theorem until the `ν ≥ 2` case is closed or refuted.
