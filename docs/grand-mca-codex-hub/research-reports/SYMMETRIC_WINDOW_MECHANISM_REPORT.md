# Krok 4 planu Grand MCA: **wyzwanie jest funkcją symetryczną okna** — i co z tego wynika

**Status.** Wszystko poniżej jest maszynowo sprawdzone w Lean, `sorry`-free, zbudowane
modułowo (bez pełnego `lake build`), a każde twierdzenie ma wpis `#print axioms`
(`RequestProject/SymmetricWindowAxiomAudit.lean`) — wyłącznie `propext`, `Classical.choice`,
`Quot.sound`. Nic z istniejącego repozytorium nie zostało zmienione ani usunięte.

Nowe moduły:

* `RequestProject/Root/CodingTheory/SymmetricWindowMechanism.lean` — mechanizm (krok 4),
* `RequestProject/Root/CodingTheory/ProjectiveCubeRank.lean` — właściwy (rzutowy) inwariant,
* `RequestProject/Root/CodingTheory/GapOneUniversality.lean` — uniwersalność przy luce 1,
* `RequestProject/SymmetricWindowAxiomAudit.lean` — audyt aksjomatów.

---

## 0. Punkt wyjścia

`CircuitPencilMap.lean` sprowadził zbiór zły do obrazu **mapy obwodowej pęku**

```
Ψ : T ↦ [divDiff k T f₀ : divDiff k T f₁] ∈ P¹(F),   T ⊆ D, |T| = k+1,
```

i policzył `Ψ` dla pęku jednomianowego (`Ψ = mapa sumy`). Otwarte pozostawało pytanie
**czym jest `Ψ` dla dowolnego pęku** — to jest dokładnie krok 4 planu.

## 1. Mechanizm: momenty okna i tożsamość Newtona

Dla okna `T` (obwodu) definiuję

* `winPoly T = ∏_{x∈T} (X − x)` — wielomian zerujący okna, z Vietą
  `winPoly_coeff : (winPoly T).coeff i = (−1)^{k+1−i} · e_{k+1−i}(T)`;
* `winSym i T = e_i(T)` — funkcje symetryczne elementarne okna;
* `winMoment k T m = divDiff k T (x ↦ xᵐ)` — **momenty okna**.

Udowodnione:

| twierdzenie | treść |
|---|---|
| `winMoment_of_lt`, `winMoment_self`, `winMoment_one` | `H_m = 0` dla `m<k`, `H_k = 1`, `H_{k+1} = e₁` |
| `winMoment_succ` | redukcja `X^{k+1+j}` modulo `winPoly T` |
| `winMoment_newton` | **tożsamość Newtona**: `H_{j+1} = e₁H_j − e₂H_{j−1} + ⋯` |
| `winMoment_two` | `H_2 = e₁² − e₂` |
| `divDiff_polyWord_eq_sum_moments` | `divDiff k T P = ∑_m P.coeff m · H_m` |

Tożsamość Newtona pokazuje, że `H_j` jest *pełną jednorodną funkcją symetryczną* okna, a więc
zależy wyłącznie od `e₁, …, e_j`.

## 2. Twierdzenie o faktoryzacji (cel kroku 4)

> `divDiff_polyWord_congr_of_winSym` — pęk stopnia `≤ k + c` **nie odróżnia** dwóch okien
> o tych samych `e₁, …, e_c`.

Konsekwencje:

* `circuitChallenge_congr_of_winSym` — wyzwanie obwodowe też ich nie odróżnia;
* `newtonChallenge` / `badSet_subset_image_newtonChallenge` — istnieje **jedna** funkcja
  `Φ : F^c → F` taka, że każde złe wyzwanie ma postać `Φ(e₁(T), …, e_c(T))`.

To jest dokładnie postać docelowa kroku 4: *mapa `Bad → {okna}` faktoryzuje się przez mapę
Newtona*. Przy `c = 1` układ redukuje się do jednej wartości `e₁ = ∑_{x∈T} x`, przy `c = 2`
dochodzi `e₁² − e₂` (`divDiff_polyWord_gapTwo`, `isBad_gapTwo_newton`).

## 3. Luka 1: postać dokładna, nie oszacowanie

* `divDiff_polyWord_gapOne` — `divDiff k T P = P.coeff(k+1)·σ + P.coeff k`, `σ = ∑_{x∈T} x`;
* `isBad_gapOne_mobius_sum` — każde złe wyzwanie dowolnego pęku stopnia `≤ k+1` jest
  **obrazem Möbiusa** sumy okna, z macierzą złożoną z czterech górnych współczynników;
* `mem_badSet_iff_circuit_gapOne`, `mem_badSet_iff_gapOne_mobius` — przy `|D| = k+1+e` to jest
  **równoważność**, dla dowolnej pary słów (odpowiednio dowolnego pęku wielomianowego);
* `card_badSet_le_one_of_top_proportional` — gałąź zdegenerowana (macierz osobliwa):
  `#Bad ≤ 1` przy każdym promieniu.

Twierdzenie `badSet_powerPencil_eq_image_sum` z poprzedniej sesji jest przypadkiem macierzy
jednostkowej.

## 4. Właściwy inwariant: **rzutowa ranga kostki**

Zbiór zły jest kowariantny względem pełnej grupy Möbiusa, a nie tylko afinicznej — punkt 3
pokazuje, że to nie jest artefakt. Dlatego inwariant kroku 1 (`CubeRankLe`) zostaje podniesiony:

```
MobiusCubeRankLe B m  :=  ∃ macierz (a b; c d) odwracalna, ∃ kostka rangi m,
                          ∀ γ ∈ B, ∃ punkt kostki t:  γ·(c t + d) = a t + b
```

* `card_le_two_pow_of_mobiusCubeRankLe` — `#B ≤ 2^m` (rachunek przeżywa rzutowanie);
* `MobiusCubeRankLe.mobius_image` — **kowariancja `PGL₂(F)`**, dokładnie ta symetria, której
  wersji afinicznej brakowało; macierze składają się jak w grupie;
* `mobiusCubeRankLe_of_cubeRankLe` — inwariant afiniczny jest szczególnym przypadkiem;
* `mobiusCubeRankLe_badSet_gapOne` — każdy niezdegenerowany pęk luki 1 ma
  `rank_Möbius(Bad) ≤ |D|`;
* **`gapOne_structure_dichotomy`** — bezwarunkowo dla całej klasy luki 1:
  `#Bad ≤ 1` **albo** `Bad` jest addytywnie ustrukturyzowany rangi `≤ |D|`.
  To jest hipoteza **H1** planu, udowodniona w klasie, w której żyją wszystkie znane
  superwielomianowe dolne granice.

## 5. Uniwersalność: przy luce 1 rozmiar `#Bad` jest inwariantem *domeny*

Niech `Σ = { ∑_{x∈T} x : T ⊆ D, |T| = k+1 }`.

* `card_badSet_gapOne_eq_card_winSums` — **dokładna równość**: `#Bad` = liczba dopuszczalnych
  sum okien (tych, dla których mianownik nie znika);
* `card_badSet_gapOne_le_card_winSums`, `card_winSums_le_card_badSet_succ` —
  `#Σ − 1 ≤ #Bad ≤ #Σ`;
* `card_badSet_gapOne_pencil_invariant` — **dowolne dwa** niezdegenerowane pęki luki 1 nad tą
  samą domeną mają zbiory złe równej mocy z dokładnością do 1;
* `choose_le_card_badSet_gapOne_succ` — nad domeną o różnych sumach podzbiorów każdy taki pęk
  ma `#Bad ≥ C(|D|, k+1) − 1`.

Interpretacja programowa: **przy luce 1 pytanie MCA o zliczanie degeneruje się do pytania
addytywnego o domenę** — „ile różnych sum `(k+1)`-podzbiorów ma `D`” — i pęk nie ma już nic do
powiedzenia. Znana rodzina ekstremalna (`C(n,k+1)`) to przypadek, w którym wszystkie te sumy są
różne; jedynym sposobem na mały zbiór zły jest domena o małej liczbie różnych sum podzbiorów,
czyli o prawdziwej strukturze addytywnej. To jest kierunek „duży `Bad` ⇔ struktura addytywna”
(H2) — udowodniony **dokładnie**, ale na razie tylko dla `c = 1`.

## 6. Uczciwy zakres

Grand MCA nie jest rozwiązane. Udowodnione tu jest: mechanizm kroku 4 dla **dowolnej** luki
(faktoryzacja przez mapę Newtona), pełne rozstrzygnięcie klasy `c = 1` (postać dokładna,
dokładne zliczanie, dychotomia strukturalna, uniwersalność) oraz właściwy, `PGL₂`-kowariantny
inwariant. Otwarte pozostają: gałąź `c ≥ 2` (odwrotność faktoryzacji, tzn. czy obraz mapy
Newtona jest mały dla domen multiplikatywnych), kroki 5–8 planu, i wszystkie stwierdzenia
o wydajności — żadnych benchmarków ani porównań z bibliotekami tu nie ma.

---

## 7. Dopisek: układ okna w postaci nieredundantnej i **ostry próg stopnia**

Moduł `RequestProject/Root/CodingTheory/HigherDividedDifferences.lean`.

Opis obwodowy używa `C(|S|, k+1)` równań na okno, z czego prawie wszystkie są zbędne. Postać
nieredundantna to wektor **wyższych różnic dzielonych** `higherDivDiff j S u` (współczynniki
interpolantu), znikających dla `j ≥ |S|`:

* `isCloseOn_iff_forall_higherDivDiff` — `IsCloseOn k S u` **wtedy i tylko wtedy**, gdy znikają
  wszystkie `higherDivDiff j S u` dla `j ≥ k`; przy luce `c` to jest dokładnie `c` równań;
* `isBad_iff_higherDivDiff` — złość `γ` to dokładnie: macierz `2 × (|S| − k)` wyższych różnic
  dzielonych obu słów anihiluje wektor `(1, γ)`, a jej drugi wiersz nie znika tożsamościowo;
* `higherDivDiff_minor_eq_zero` — stąd **macierz okna złego wyzwania ma rangę 1**: wszystkie jej
  minory `2 × 2` znikają. To są warunki na *samo okno*, bez `γ` — dokładnie warunki
  determinantalne (Schuberta), które plan przewidywał jako resztę mechanizmu Newtona;
* `card_badSet_le_one_of_degree_lt` — **ostry próg stopnia**: jeśli oba słowa są wielomianami
  stopnia mniejszego niż najmniejsze dopuszczalne okno `w` (`w + e ≤ |D|`), okno wypada z układu
  (`higherDivDiff_polyWord_of_degree_lt`), równania dotyczą wyłącznie współczynników i
  `#Bad ≤ 1` przy każdym rate. Próg jest ostry: ekstremalny pęk luki 1 (`X^{k+1}, X^k`) ma
  stopień dokładnie `k+1 = |D| − e`, o jeden powyżej granicy, i osiąga `C(|D|, k+1)`.

Wniosek: cała złożoność zbioru złego włącza się przy jednym stopniu — słowa muszą sięgnąć
rozmiaru okna, zanim więcej niż jedno wyzwanie może być złe.
