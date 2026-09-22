# S16.78 — Bellman primary, support-exact secondary: wynik

```text
PRIMARY: REDUCED_TO_ONE_LEMMA (shallow-HARD exclusion) + KILLED shapes (computational receipts)
SECONDARY: COMPUTATIONAL (planted hcov triples present, overlap never big, WEAK/DEAD at deployed row)
```

`GRAND_MCA_SAFE` nie zgłoszone. Zero `sorry`, zero buildu (cache Mathlib nadal
absent), zero merge'u paczek, zero modyfikacji banked files.

## 1. Łańcuch zależności + sygnatury (Phase 0, literalne, REPO3_ASSEMBLED)

Consumer (banked, `PostJohnsonSafePotential.lean`):
`cost_le_potential_of_four_regimes` (cost/localCost/rad/children/base/low/core/hard,
`Φ`, pB/pL/pC; hstep/hdesc/hsplit/hdBL/hdBLC/hdBLCH/hbase/hlow/hcore/hpot →
`cost X ≤ Φ (rad X)`), `dyadic_units_criterion` (Kraft: uLocal+uCheap+Σ2^L ≤ 2^L),
`deployed_badSet_le_of_dyadic_potential` (root 978944, `Φ₀=153126785377107968`,
`#Bad ≤ Bstar`). Certyfikat: L(978944)=42, Φ₀<C*=274980728110416142,
margines 121853942733308174, m=22480 optymalne.

Rekurencja (banked): `officialClass k e A f₀ f₁ γ := windowZeros A (officialWitness …).1`,
`officialWitness` (kanoniczny wybór, `officialWitness_spec`), `classCost := (resBadSet).card`,
`parentMult` (włókno), `occupiedClasses` (obraz), `totalChildCost`,
`officialClass_complexity_lt` (instComplexity + resRad spadają),
`officialClass_capacity_gap` (n_R = k_R + e_R + w, w=69632),
`fibre_subset_resBadSet` (μR ≤ C(R)), `mem_resBadSet_of_positiveMass` (transport),
`resRad e A Z := e - (A.card - Z.card)`, `resBadSet` (child badSet),
`resDim k Z := k - Z.card`.

Ceny (banked, `PostJohnsonLowBand.lean` + `CapacityRegimeLoadGate.lean`):
BASE `|R|≤69632 → ≤1` (=`deployed_classCost_le_one`), LOW `≤104448 → ≤34817`
(`deployed_classCost_le_34817`, via `classCost_le_succ_resRad` + triple MDS:
`3e_R < d_R`), CORE (P-klasa, core `|T|≥n_R−w`) `→ ≤69632`
(`deployed_classCost_le_of_core`, hipoteza `hcore` jawna). Partycja:
`deployedBase/Low/Core/HardClasses` + `deployed_occupied_partition`
(rozłączna, wyczerpująca) + `deployed_card_badSet_le_four_regimes`
(978945 + Σ) + `deployed_endpoint_of_four_regimes` (NB+NL·34817+NC·69632+M≤C*).

## 2. Pricing receipt + one-short (Phase 0/2, exact integers)

s1676 rerun: frontier {1:22448, 2:44928, 3:44928, 4:67408} match=True,
root Φ₀=153126785377107968, one-child-one-block maxcheap=2199023255523.
B2 planted (TARGET e=978944 / ONE-SHORT e=978945, wszystkie neutral):
`two_shallow_1down` FAIL/FAIL (LHS 3.06e17>1.53e17 — unary-HARD + shallow
zabite z zapasem 2x), `two_shallow_block` FAIL/FAIL (o 978945 — sam localCost),
`one_deep_plus_cheap` FAIL/FAIL, `unary_deep` FAIL/FAIL;
`three/four_identical_mid` (R=900000, drop 148576, level 35) PASS z zapasem ~20x;
`core_flagged_big`, `hard_plus_core` PASS; `empty` PASS (978945).
B3 RS: resRad ujemne w małych modelach (pas terminalny), proxyCost 0/11,
dual Gauss+minor agree wszędzie. B5: Z3 sat h=2 (discovery) + exact reprice
FAIL; SymPy: level monotoniczny, frontier recheck identyczny.

## 3. Najmniejszy kontrmodel / artefakt dowodowy (Phase 1+2)

Zabite kształty (computational, z receiptami):
(a) **unary-HARD przy drop <22448** — `unary_deep` (drop 0) i `two_shallow_1down`;
banked `dyadic_two_hard_children_not_payable` to pokrywa dla 2 dzieci.
(b) **dwoje HARD-dzieci o jeden blok w dół** — `two_shallow_block` FAIL o
dokładnie 978945 = localCost; to jest twarda granica: dwoje dzieci na level 41
wyczerpuje cały potencjał rodzica.
Najmniejszy ocalały producer (REDUCED_TO_ONE_LEMMA):

```text
official shallow-HARD exclusion:
  ∀ X, ∀ Y ∈ hard X, rad Y ≤ rad X − 22448 ∨ (singleton-HARD-drop-0-impossible…)
```

a ściślej, najmniejszy falsyfikowalny kształt: **co najwyżej jedno HARD-dziecko
z drop <22448 jest dopuszczalne tylko jeśli nie ma drugiego HARD-dziecka
z drop <44928** (frontier 1→22448, 2→44928). Dowód wymaga literalnej
semantyki `officialClass` (parentMult, transport, capacity-gap) — radius
descent sam nie wystarcza (banked `binary_branching_exceeds_deployed_target`).
CORE price: `hcore` jest jawną hipotezą `deployed_card_badSet_le_four_regimes`
— brak producenta P-klasy dla konkretnych R to `SOURCE_GAP` wewnątrz
REDUCED_TO_ONE_LEMMA, nie osobny sorry.

## 4. Targeted build + #print axioms: NIE URUCHOMIONE (uczciwie)

`Mathlib.olean` nie istnieje nigdzie na dysku (ustalone S16.69/S16.73);
targeted `lake env lean` bez cache = pełny build Mathlib (godziny, zabroniony).
Nowe moduły Lean: brak (harness-only tura). `#print axioms`: RNR z paczek.

## 5. Secondary Phase 3: COMPUTATIONAL / WEAK-DEAD

Planted hcov-triple (S₁⊆S₂∪S₃) istnieją: GF(5):3, GF(7):12, GF(11):16, GF(13):6 —
ale **overlap_big=False wszędzie** (inter ≤1 vs Kz=q−k), resid_rank_proxy=2.
Przesłanka pakietu (`>Kz`) nigdy nie zachodzi w wiernych małych modelach →
kill-test nierozstrzygający dla implikacji, a gałąź `wt≤3e` to
`3e=2936832 > N=2097152` → WEAK/DEAD na wierszu deployed bez
`jointDefect≤69632`. Status S16.72 podtrzymany. S16.73-proxy-survival NIE
użyte jako dowód (zgodnie z zakazem misji).

## 6. Next single gate

```text
G-S16.79: official shallow-HARD exclusion
  (≤1 HARD child with drop<22448 unless compensated; exact multiset pricing;
   literal officialClass semantics; falsifier first, one sorry max after green downstream)
```

Pliki: `analysis/s1678_bellman_adversarial.py` (+JSON/TXT),
`analysis/s1678_fiveflat_planted.py` (+JSON/TXT), ten raport.
