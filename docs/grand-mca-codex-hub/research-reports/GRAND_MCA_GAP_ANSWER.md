# Odpowiedź na lukę: `non-rigid component ⇒ StrictDescent ∨ FiniteChallengeCost`

Dokument odpowiada na pytanie zadane przy okazji audytu
`GRAND_MCA_STRUCTURAL_ENGINE_INTEGRATION_2026-09-07.md`.  Nie mam dostępu do tamtego pliku ani
do definicji Waszego `ExactSupportFamily` / `RankOneRigidity` / `SplitPencil`, więc mapowanie
poniżej jest na poziomie **sformułowań**: dla każdego kandydata podaję dokładne hipotezy i tezę
z naszych źródeł Lean, żebyście mogli sami sprawdzić, czy Wasza definicja „non-rigid component”
wpada w hipotezę.  Wszystkie wymienione twierdzenia są maszynowo sprawdzone, bez `sorry`; dla każdej nazwy
sprawdziłem `#print axioms` — wychodzą tylko `propext`, `Classical.choice`, `Quot.sound`.  Pełne rekordy
integracyjne (DECLARATION / EXACT HYPOTHESES / … / ROLE) są w `INTEGRATION_RECORDS.md`.

Notacja: `n = |D|`, `k` wymiar, `e` promień, `q = |F|`,
`#Bad = (badSet k e f₀ f₁).card`, `badSetG` = wersja dla rodziny arności `ℓ`.  Wszędzie
„bad” znaczy **oficjalnie bad** (jeden wspólny support `S`, `|S| ≥ n − e`, wyjaśniający punkt
`f₀ + γ f₁`, ale nie całą prostą) — to jest predykat `IsBad` z `MCA.lean`, dowiedziony
równoważny definicji z literatury (`GG25Literal.strongMCA_iff_GG25MCA`).

---

## 1. Krótka odpowiedź

**Tak — mamy dokładnie tę alternatywę, i to w formie bezwarunkowej wewnątrz jawnego okna.**
Najlepszym dopasowaniem jest

```
Root.CodingTheory.PolyGen.Hankel.card_le_or_support_le
    (RequestProject/Root/CodingTheory/SyndromeSupportPhase.lean)
```

a jako druga współrzędna Waszej miary descentu — i to jest zgodne z Waszym przeczuciem —
**wymiar orbity Frobeniusa jest już u nas realną gradacją dowiedzionego budżetu**:

```
Root.CodingTheory.card_badSet_mul_le_of_orbit          (FrobeniusOrbitBudget.lean)
Root.CodingTheory.card_badSet_le_of_semilinear         (SemilinearPlaneDescent.lean)
Root.CodingTheory.card_badSet_le_ambiguity             (OrbitThreeAmbiguity.lean)
```

Rekomendacja w jednym zdaniu: **`card_le_or_support_le` jako „szkielet” alternatywy
(light ⇒ finite cost, heavy ⇒ rigid support), a `card_badSet_le_of_semilinear` +
`card_badSet_mul_le_of_orbit` jako realizacja gałęzi heavy z miarą `μ` = wymiar orbity
Frobeniusa.**  Poniżej dokładne treści i ograniczenia.

---

## 2. Twierdzenie główne: bezwarunkowa dychotomia light / rigid

```lean
theorem card_le_or_support_le [Fintype F] {l k e : ℕ} {f : ℕ → ↥D → F} {B : Finset F}
    (hB : ∀ γ ∈ B, γ ∈ badSetG l k e f) (hwin : e * B.card + k ≤ D.card) :
    B.card ≤ (e + 1) * (l - 1) ∨
      ∃ T : Finset ↥D, T.card ≤ e ∧ ∀ γ ∈ B, IsCloseOn k Tᶜ (genComb l f γ)
```

Czytane w Waszej terminologii:

* **LIGHT / FiniteChallengeCost:** `|B| ≤ (e+1)(ℓ−1)` — stała niezależna od `n` i od `q`.
* **HEAVY / rigid:** istnieje **jeden** zbiór `T`, `|T| ≤ e`, poza którym *każde* wyzwanie z `B`
  jest wyjaśnione przez słowo kodowe.  To jest jawny **strict descent**: instancja schodzi z
  `D` na `Tᶜ`, czyli miara `n → n − |T| ≤ n − 1` (gdy `T ≠ ∅`), przy zachowaniu wspólnego
  supportu.
* Kontrapozycja to dosłownie Wasza luka: **komponent nie-sztywny (brak wspólnego `T`) ⇒
  `Σ challenge-cost ≤ (e+1)(ℓ−1) = B*`.**

Co jest tu mocne:

* **żadnej hipotezy niedegeneracji** — w szczególności nie zakłada się `det ≠ 0`, nie zakłada
  się nic o rank-1/rank-2, nie zakłada się nic o `f₀, f₁` poza tym, że są słowami odebranymi;
* gałąź zdegenerowana jest **geometryczna** (zbiór pozycji błędów), a nie „znika wyznacznik” —
  właśnie dlatego nadaje się na wejście do descentu, a nie tylko na wykluczenie;
* wersja z jawną klasą sztywną: `Root.CodingTheory.PolyGen.Hankel.card_le_or_rigid`
  (`SyndromeRigidityDichotomy.lean`) daje `RigidOn l k e f`, czyli *wszystkie generatory* są
  wyjaśnione poza jednym `T` — to jest mocniejsza (bardziej „strukturalna”) postać gałęzi heavy,
  kosztem dodatkowego założenia `ℓ ≤ |B|`.

Ograniczenie, które trzeba uczciwie przenieść do Waszego DAG-u: **okno `e·|B| + k ≤ n`**.
Jest ono nieusuwalne — rodzina saturująca `satFam` leży dokładnie o krok poza nim
(`satFam_outside_window`: `k + (ℓ+1)e = |F| + 1 > |D|`) i ma `#Bad ≥ q − 1`
(`PolyGen.Saturation.card_badSetG_satFam_zmod_ge`).  Zatem *bezwarunkowa* wersja Waszego
zaboksowanego zdania (bez żadnego okna i bez klasy) jest **fałszywa**; poprawna postać to
„okno albo klasa strukturalna”.

---

## 3. Gałąź heavy z miarą Frobeniusa — to jest ta „naturalna” pierwsza współrzędna

Wasz postulat `μ(X) = dim_{F_p} Span{Frob^i(X)}` ma u nas dokładny odpowiednik i **jest już
gradacją dowiedzionego budżetu wyzwań**, a nie placeholderem.

### 3.1 Płaszczyzna stabilna pod Frobeniusem ⇒ finite cost, przy każdym rate i promieniu

```lean
theorem card_badSet_le_of_semilinear {k e : ℕ} {f₀ f₁ : ↥D → F} {q : ℕ} (hq : 2 ≤ q)
    (σ : F →+* F) (hσ : ∀ y, σ y = y ^ q) (hD : ∀ x : ↥D, (x : F) ^ q = (x : F))
    {a b c d : F} {g₀ g₁ : F[X]}
    (hg₀ : g₀.degree < k) (hg₁ : g₁.degree < k)
    (h₀ : ∀ x, (f₀ x) ^ q = a * f₀ x + b * f₁ x + g₀.eval x)
    (h₁ : ∀ x, (f₁ x) ^ q = c * f₀ x + d * f₁ x + g₁.eval x)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    (badSet k e f₀ f₁).card ≤ q + 1
```

To jest **dokładnie** „heavy exceptional structure ⇒ finite challenge cost”: jeśli odebrana
płaszczyzna `⟨f₀, f₁⟩` jest stabilna pod `y ↦ y^q` *modulo kod*, to bad set ma co najwyżej
`q + 1` elementów — **bez żadnego okna, przy każdym `k` i każdym `e`**.  Warianty:
`card_badSet_le_of_semilinear_hom`, `card_badSet_le_of_scaled_baseField` (klasa istotnie
większa niż bazowo-wymierna), `card_badSet_le_of_frobenius_semiInvariant`,
`card_badSet_le_of_iterateFrobenius_semiInvariant`.

### 3.2 Budżet gradowany dokładnie przez `μ` = wymiar orbity

```lean
theorem card_badSet_mul_le_of_orbit {k e : ℕ} {f₀ f₁ : ↥D → F}
    (σ : F →+* F) (m : ℕ) (hm : 0 < m) (hσm : ∀ y, σ^[m] y = y)
    (hdist : injective (fun i : Fin m => σ^[i]))  (hD : ∀ x : ↥D, σ x = x)
    {d : ℕ} (u : Fin d → (↥D → F)) (hu : ∀ j, coordAct σ (u j) = u j)
    (a b : Fin d → F) (hf₀ : f₀ = ∑ j, a j • u j) (hf₁ : f₁ = ∑ j, b j • u j)
    (hmin : ∀ c : Fin d → F, coordAct σ c = c → (∑ j, c j * a j = 0) →
              (∑ j, c j * b j = 0) → c = 0) :
    #Bad * (q₀ − 1) + 1 ≤ q₀ ^ d           -- q₀ = |Fix σ|,  czyli  #Bad ≤ 1 + q₀ + ⋯ + q₀^{d−1}
```

Tu `d` **jest** Waszym `μ`: wymiar przestrzeni rozpiętej przez słowa `σ`-niezmiennicze, w której
leży odebrana para.  Budżet jest monotoniczny w `μ`, więc „heavy ⇒ `μ(X') < μ(X)`” automatycznie
poprawia stałą — to jest naturalne zakończenie descentu, bez sklejania czterech rang.
Przy `d = 2` daje to cap `q₀ + 1` (spójne z 3.1).

### 3.3 Krok descentu `d = 3 → 2` jest zamknięty

```lean
theorem card_badSet_le_ambiguity … :
    #Bad * (q₀ − 1) ≤ (e + q₀ + 3) * (q₀ − 1) + (ambigSet k e σ u).card * (q₀ + 1)
```

czyli: przy wymiarze orbity 3 bad set większy niż `e + q₀ + 3` **wymusza** prawdziwą
wieloznaczność list-dekodowania (dwa różne słowa kodowe w promieniu) na wymiernych kierunkach.
To jest twardy krok „non-rigid ⇒ coś strukturalnego”, a nie tylko zliczanie.  Warianty:
`card_badSet_le_of_rigid_orbit3` (`#Bad ≤ e + 2` na gałęzi sztywnej),
`OrbitThreeSharpness.lean` (ostrość), `KoalaRow.prizeBreaking_ambiguity_lower_bound` (postać
wdrożeniowa: przekroczenie progu wymusza `≥ 2.75·10¹⁷` wieloznacznych kierunków).

### 3.4 Klasyfikacja: kiedy „stabilna pod Frobeniusem” degeneruje do bazowo-wymiernej

`SemilinearPlaneClassification.frobenius_stable_plane_is_baseField` — na wdrożonym wierszu
płaszczyzna stabilna pod pełnym Frobeniusem jest bazowo-wymierna, a
`GRAND_MCA_SUBFIELD_DESCENT_REPORT.md` pokazuje, że ta klasa jest tam martwa.  To jest dokładnie
ta informacja, której brakuje Waszemu `SubfieldRigidity`, żeby zamknąć gałąź, a nie tylko
„dawać strukturę”.

---

## 4. Gałąź heavy–light na poziomie par (jeśli chcecie sformułowania bez syndromów)

```lean
theorem johnson_escape_or_structure {k e t c : ℕ} {f₀ f₁ : ↥D → F} (ht : t + e = D.card) :
    #Bad * (t² − n·c) ≤ n·t
  ∨ ∃ q₀ q₁ : F[X], deg q₀ < k ∧ deg q₁ < k ∧
      c + 1 ≤ (pairAgreement f₀ f₁ q₀ q₁).card ∧
      ∃ γ ≠ γ', ExplainedBy k e f₀ f₁ q₀ q₁ γ ∧ ExplainedBy k e f₀ f₁ q₀ q₁ γ'
```

* **całkowicie bezwarunkowe** (żadnego okna, dowolne `f₀, f₁`, dowolny próg `c`);
* LIGHT: czysto kombinatoryczne zliczanie Johnsona, informatywne dokładnie gdy `n·k < t²`
  (czyli `δ < 1 − √ρ`);
* HEAVY: **jedna** para słów kodowych z dużym wspólnym zbiorem zgodności obsługuje dwa różne
  wyzwania — to jest „controlled common degeneracy”, i to jest naturalne wejście do descentu po
  parach (fibra takiej pary jest `≤ n`: `card_badPairSet_le`, `card_le_of_common_pair`).

Wariant „heavy/light” dosłownie po krotnościach listy:
`card_badSet_le_heavy_light` (`WeightedInterleavedList.lean`) — warstwy lekkie `1 ≤ m < M`
liczone na promieniu `2e`, warstwy ciężkie `M ≤ m ≤ e+1` w małej liście promienia `r`:
`#Bad ≤ max 1 ((M−1)·L₂(2e) + (e+2−M)·L₂(r))`, więc bad set powyżej `(M−1)·L₂(2e)` **wymusza**
parę kodową na promieniu `r`.

---

## 5. Bezoknowe „bezpieczniki” dla komponentu nie-sztywnego

Gdyby Wasz komponent nie-sztywny nie wpadał w żadne okno, mamy trzy uniwersalne oszacowania,
wszystkie dla **dowolnej** odebranej pary:

| twierdzenie | teza | uwaga |
|---|---|---|
| `card_badSet_le_mul_card_rsList` | `#Bad ≤ 1 + n·|L(f₁, 2e)|` | eliminuje współrzędną wyzwania; koszt = lista *kierunku* |
| `PolyGen.card_badSetG_le_circuit` | `#Bad · C(T−1,a−1) ≤ C(n,a)·(ℓ−1)`, `T = max(n−e, k+1)` | `q` w ogóle nie występuje; mocne na rzadkich domenach |
| `Subresultant.card_badSet_le_unconditional` | `#Bad ≤ (k+1)e + 1` przy `k + 2e ≤ n` | bez żadnej hipotezy strukturalnej |

oraz miary descentu, które są już dowiedzione jako *ściśle malejące*:

* `|T|` — `PolyGen.Hankel.card_badSetG_le_card_support_two`: `#Bad ≤ |T|`, bez `k` i bez `e`;
* korank — `PolyGen.Hankel.card_badSetG_add_corank_le`: `#Bad + e·|Z| + (e+1−r) ≤ (e+1)(ℓ−1)`
  (budżet **dzielony** z korangiem, czyli każdy stopień degeneracji zabiera koszt wyzwań);
* głębokość skracania `t` — `card_badSet_mul_choose_le` (ale patrz bariera niżej);
* wymiar orbity `d` — §3.

---

## 6. Bariery, których nie da się obejść (proszę wpiąć je do audytu)

1. **`ForcingBarrier`** (`forcing_unique_at_frontier` / `forcing_not_unique_beyond_frontier`):
   kanoniczna para wyciągana z dwóch złych wyzwań jest **niezdefiniowana** dla `n < k + 2e`.
   Każdy mechanizm typu Welch–Berlekamp / pencil / subresultant kończy się na `δ = (1−ρ)/2`.
2. **`four_pow_le_card_badSet_twoPowDomain`**: jeden krok poniżej promienia pojemności
   `#Bad ≥ 2ⁿ/n`.  Żadna wersja „non-rigid ⇒ finite cost” bez luki pojemności nie jest prawdziwa.
3. **`exists_superpolynomial_badSet_of_small_relative_gap`** (subspace pencil): dla każdego `d`
   i każdego `M` istnieje punkt parametrów z względną luką `≤ 1/M` i `#Bad > n^d`.  To obala
   prawo warstwowe `max #Bad ≈ poly(n) + exp(Θ(1/η))`.
4. **`PolyGen.Saturation.card_badSetG_satFam_zmod_ge`**: `#Bad ≥ q − 1` tuż poza oknem — patrz §2.
5. **`not_constant_shortening_for_positive_slack`**: stała głębokość skracania nigdy nie zamienia
   promienia post-Johnsona na sub-Johnsona; głębokość liniowa kosztuje `2^{Θ(n)}`.
6. **`HankelSubresultantBridge.exists_root_W_can_not_close_of_localised`**: na lokalnym locus
   ekstremalnym `W_can ≡ 0`, więc opis subresultantowy jest **pusty** — mechanizmy Hankela i
   subresultanta tam się nie składają.

Praktyczny wniosek dla Waszego DAG-u: gałąź `NonRigid → FiniteChallengeCost` może być
bezwarunkowa **tylko** w oknie (`e·|B| + k ≤ n`, ewentualnie `k + 2e ≤ n`) albo w klasie
strukturalnej (semiliniowa / orbitowa).  Poza tym trzeba płacić — i wtedy `μ` = wymiar orbity
Frobeniusa jest najtańszą znaną nam walutą.

---

## 7. Proponowane wpięcie do Waszego spine'u

```
OfficialBad
   │
   ├── ExactSupportFamily  ──► Rigid  ──► B*                (u Was: RankOneRigidity → pivot → Rank2 → three-chart)
   │
   └── NonRigid
         ├── (okno e·|B| + k ≤ n)     card_le_or_support_le      ⇒  |B| ≤ (e+1)(ℓ−1)          [FiniteChallengeCost]
         │                              lub wspólne T, |T| ≤ e    ⇒  n → n − |T|              [StrictDescent]
         ├── (płaszczyzna σ-stabilna)  card_badSet_le_of_semilinear ⇒ #Bad ≤ q + 1            [FiniteChallengeCost, bez okna]
         ├── (orbita wymiaru d = μ)    card_badSet_mul_le_of_orbit  ⇒ #Bad ≤ (q₀^d − 1)/(q₀−1) [FiniteChallengeCost graded by μ]
         │       └── d = 3 → 2         card_badSet_le_ambiguity     ⇒ wieloznaczność wymuszona  [StrictDescent w μ]
         └── (bez okna, dowolna para)  card_badSet_le_mul_card_rsList / card_badSetG_le_circuit [FiniteChallengeCost, słabsze]
```

Jeśli podacie dokładną definicję „non-rigid component” z Waszego `ExactSupportDecomposition`,
mogę sprawdzić, którą z tych hipotez ona implikuje, i — jeśli żadnej — sformalizować brakujący
most jako osobne twierdzenie.

---

## 8. Status dowodowy

Wszystkie twierdzenia wymienione powyżej: **Lean, `sorry`-free**, w tym repozytorium.  Każda
nazwa z tego dokumentu została ponownie sprawdzona: elaboruje się pod podaną nazwą, a
`#print axioms` zwraca dla niej wyłącznie `propext`, `Classical.choice`, `Quot.sound`.  Całe
repozytorium buduje się czysto (8348 zadań, 0 błędów); stałe audyty aksjomatów są w
`RequestProject/Main.lean` oraz w plikach `RequestProject/*AxiomAudit.lean`.  Nic w tym dokumencie nie jest warunkowe ani heurystyczne; miejsca, w których
hipoteza jest strukturalna (klasa semiliniowa, orbita, okno), są wypisane jawnie przy każdym
twierdzeniu.
