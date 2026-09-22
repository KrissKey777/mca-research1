# S16.79 — shallow-HARD with exact Bellman target: wynik

```text
BELLMAN_PRODUCER_REDUCED_TO_ONE_EXACT_LEMMA (mixed-profile compensation, exact statement below)
 shapes (0,0),(0),(22480,22480),(drop-0+cheap): KILLED computationally (4 receipts)
 shapes mid/core/mixture: PASS as acceptance tests (not proofs)
```

`GRAND_MCA_SAFE` nie zgłoszone. Zero `sorry`, zero buildu (cache Mathlib absent),
zero modyfikacji banked files, zero cloud-only deklaracji.

## 1. Łańcuch + sygnatury (wszystko LOCAL_BANKED, REPO3_ASSEMBLED)

`IsOfficialWitness k e f₀ f₁ γ (p,S)`: p≠0 ∧ deg<k ∧ |D|≤|S|+e ∧ lineComb=p.eval
na S. `officialWitness` (wybór kanoniczny) + spec. `officialClass := windowZeros
A (witness).1`, `windowZeros A p = filter (eval=0)`, `card_windowZeros_lt`
(stopień<k → |Z|<k), `card_windowZeros_add_windowMass` (|Z|+mass=|A|).
`childClasses = powerset.filter (|Z|<k ∧ |A|≤|Z|+e)`, `officialClass_mem_childClasses`
(wymaga `NormalisedWindow` + posBadSet; dowód przez `windowMass_le_of_witness`).
`NormalisedWindow`: zero na A + maximal agreement ≤|A|.
`resRad = e−(|A|−|R|)`, `resDim = k−|R|`, `posBadSet = badSet \ zeroWitnessBadSet`.
Consumer: `cost_le_potential_of_four_regimes` + `dyadic_units_criterion` +
`deployed_badSet_le_of_dyadic_potential` (S16.78, bez zmian).
Ceny: BASE ≤1, LOW ≤34817, CORE ≤69632 (jawna hipoteza `hcore`).
Partycja `deployedBase/Low/Core/HardClasses` + `deployed_occupied_partition` +
`deployed_card_badSet_le_four_regimes` + `deployed_endpoint_of_four_regimes`.

## 2. Mixed-profile pricing (niezależna implementacja, exact integers)

`analysis/s1679_mixed_bellman.py` (+JSON/TXT): level przez odejmowanie
(iteracja, nie divmod), phi przez mnożenie w pętli — drugi tor rachunkowy.
M1 grid (drops 0..944128): h=1: 14 pass/5 fail; h=2: 171/190; h=3: 1884/4975;
h=4 (coarse): 148/477. `first_fail` wszędzie multizbiór zerowych dropów —
najsłabszy kształt to dzieci bez spadku promienia.
M2 mieszanki: hard1+10k-cheap PASS (slack 7.66e16), hard1+max-cheap PASS,
hard2+core PASS, hard1deep+low-heavy PASS (slack 1.5e17), hard3mixed+base PASS.
M3 one-short: **DIVERGES na granicy** — `drops=(22448,)`: T=True/O=False;
`(44928,44928)`: T=True/O=False; `(0,)`, `(22480,22480)`: neutral FAIL/FAIL.
Weryfikacja niezależna: level(E)=level(E1)=42, phi równe; drop 22448 daje
level 41 (T: 41+local → mieści się) a przy E1 ten sam kardynał R daje promień
o 1 większy → level 42 → nie mieści się. To jest knife-edge o szerokości 1
poziomu: granica jest wrażliwa na +1 promienia, ale separacja wierszy SAFE/UNSAFE
musi pochodzić z guardów semantycznych (istnienie/nieistnienie takich dzieci),
nie z samej arytmetyki — wynik boundary-DIVERGENT, nie dowód.

## 3. Kontrmodele / proof artefakt (S16.78 rerun w tej turze)

Planted B2 (identyczne płytkie promienie, HARD+CORE, one-short):
`two_shallow_1down` FAIL/FAIL (3.06e17, 2x ponad budżet),
`two_shallow_block` FAIL/FAIL (o dokładnie 978945),
`one_deep_plus_cheap` FAIL/FAIL, `unary_deep` FAIL/FAIL;
`three/four_identical_mid`, `core_flagged_big`, `hard_plus_core` PASS (testy
akceptacyjne). Reguły odrzuceń misji zastosowane: radius-alone ✗, unary-HARD
z BranchingCertificate ✗, unweighted counts ✗, parentMult≤classCost bez wag ✗,
wt≤3e ✗, S16.73-proxy ✗, cloud-only ✗.

## 4. Najmniejszy ocalały producer (opcja B, exact statement)

```text
mixed_profile_compensation:
  ∀ official HARD children (literal officialClass, NormalisedWindow,
    windowMass≤e, deg<k, Z∈childClasses, capacity-gap w=69632),
  localCost + Σ_cheap + Σ Φ(resRadᵢ) ≤ Φ(rad)
  follows from the witness guards alone (no extra geometry).
```

Status: sformułowany jako kształt (`mca_work/S1679_LegalPlant.lean`,
PROPOSED_SOURCE_ONLY), nie udowodniony. Legal-plant pytanie: czy guardy
(`|Z|<k`, `|A|≤|Z|+e`, `windowMass≤e`) wymuszają kompensację, czy istnieje
legalny kontrmodel z multizbiorem (0,0)? Bez falsyfikatora na pełnej
semantyce (RS + świadkowie + klasy, nie same promienie) odpowiedź to
`SOURCE_GAP — exact missing official semantic edge`, nie twierdzenie.
Opcja A (full Bellman) wymaga tego samego + instancję partycji w σ-modelu;
opcja C (weighted aggregate) to wniosek z B przez `dyadic_units_criterion`.

## 5. Build + axiomy: NIE URUCHOMIONE (uczciwie)

Cache Mathlib absent (S16.69/S16.73, bez zmian). Nowych modułów Lean do buildu:
brak (spec-only). `#print axioms`: RNR.

## 6. Next single gate

```text
G-S16.80: legal-plant falsifier on full official semantics
  (NormalisedWindow + witnesses + classes + resRad; multiset (0,0) first;
   kill → LANE_KILLED with witness; survival → compensation proof attempt)
```

Pliki: `analysis/s1679_mixed_bellman.py` (+JSON/TXT), ten raport.
