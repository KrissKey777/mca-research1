# Plan badawczy — Fala 3

Dokument opisuje (a) co zostało **formalnie udowodnione** w tej turze, (b) które dźwignie
z bibliotek okazały się najmocniejsze, (c) ranking dalszych ścieżek według stosunku
wartość/koszt i prawdopodobieństwa sukcesu, (d) listę NO-GO.

Wszystkie wymienione twierdzenia kompilują się bez `sorry`; audyt aksjomatów
(`RequestProject/Main.lean`) pokazuje wyłącznie `propext`, `Classical.choice`, `Quot.sound`.

---

## 1. Co zostało zamknięte w tej turze (Fala 0 + Fala 1)

### 1.1 Infrastruktura (Fala 0) — `RequestProject/AlgebraSplit.lean`

| Narzędzie | Nazwa w Lean | Po co |
|---|---|---|
| algorytm indeksowany dowolnym zbiorem skończonym | `GenAlg.ofFintype` | koniec z ręcznym żonglowaniem `Fin k` |
| suma prosta algorytmów, `R(A₁ × ⋯ × A_t) ≤ Σ R(Aᵢ)` | `GenAlg.pi`, `GenAlg.pi_computes_mul` | składanie algorytmów blokowych |
| transport wzdłuż równoważności liniowych / algebr | `GenAlg.congr`, `GenAlg.congr_computes_mul` | zmiana bazy jest darmowa w modelu biliniowym |
| most `ConvAlg → GenAlg` (brakujący kierunek) | `GenAlg.toConvAlg` (`ConvExact.lean`) | swobodne przenoszenie wyników splot ↔ algebra |
| monotoniczność ilorazowa i podalgebrowa `R(B) ≤ R(A)` | `exists_genAlg_of_surjective`, `exists_genAlg_of_injective` | przenoszenie granic w obie strony |
| `F[C_n] ≅ (ℤ/n → F)` przenoszące mnożenie na splot | `groupAlgEquivFun`, `groupAlgEquivFun_mul` | splot cykliczny *to* mnożenie w `F[x]/(xⁿ−1)` |

### 1.2 Strukturalne domknięcie górnych granic (Fala 1)

* **`split_algebra_exact`** — jeżeli `A ≃ₐ[F] ∏ᵢ Kᵢ` (t ciał, każde z bazą potęgową), a ciało
  bazowe jest dość duże, to mnożenie w `A` wymaga **dokładnie** `2·dim A − t` mnożeń ogólnych.
  Górna granica: algorytm chińskiego twierdzenia o resztach (rzut na czynniki — darmowy,
  mnożenie w czynniku przez ewaluację/interpolację `2dᵢ−1`, rekombinacja — darmowa).
  Dolna granica: rzuty są łącznie injektywnymi charakterami w dziedziny (Alder–Strassen z Fali 2a).
* **`reduced_algebra_exact`** — to samo **bez podawania rozkładu**: nad ciałem skończonym każda
  skończenie wymiarowa zredukowana algebra przemienna rozpada się sama (Mathlib:
  `IsArtinianRing.equivPi`), a `t = #MaxSpec A`.
* **`convComplexity_eq` / `convComplexity_M31_eq`** — **twierdzenie Winograda w postaci dokładnej**:
  dla każdego `n` odwracalnego w ciele (nad `M31`: każde `n ≤ 2³⁰` niepodzielne przez `p`)
  złożoność biliniowa splotu cyklicznego długości `n` wynosi **dokładnie `2n − t(n)`**,
  gdzie `t(n)` to liczba czynników nierozkładalnych `xⁿ − 1`.
  To jest cała rodzina Winograda naraz, a nie pojedyncze długości.
* **`factorCount_M31_five/six/ten/fifteen/thirty`** — `t(n) = 2, 6, 4, 6, 12`.
  Uzyskane przez połączenie twierdzenia ogólnego z wcześniej udowodnionymi wartościami
  dokładnymi; to niezależny **cross-check** dwóch dróg (kombinatoryka warstw cyklotomicznych
  vs. struktura ideałów maksymalnych).

### 1.3 Konsekwencje dla wcześniej otwartych punktów

* `c(30) = 48` (było `30 ≤ c ≤ 48`) — luka zamknięta; `c(5) = 8`, `c(6) = 6`, `c(10) = 16`,
  `c(15) = 24` również dokładne.
* Pełne Alder–Strassen dla algebr **przemiennych półprostych** (t dowolne) — zamknięte.
  Zostaje wyłącznie przypadek z nilpotentami (patrz §3.1).

---

## 2. Dźwignie: co z bibliotek okazało się najmocniejsze

Poszukiwanie „niedocenianych filarów” dało jednoznaczny wynik — najsilniejsze dźwignie
leżą w **algebrze przemiennej i teorii pierścieni artinowskich**, nie w topologii:

| Dźwignia | Co daje |
|---|---|
| `IsArtinianRing.equivPi` (`R ≃ₐ[R] ∏_{I ∈ MaxSpec} R/I` dla `R` zredukowanego artinowskiego) | **cały rozkład CRT za darmo** — nie trzeba formalizować faktoryzacji `xⁿ − 1` |
| `isArtinian_of_tower` | skończony wymiar nad ciałem ⇒ artinowskość |
| `Field.powerBasisOfFiniteOfSeparable` + doskonałość ciał skończonych | baza potęgowa w każdym ciele reszt ⇒ algorytm ewaluacja/interpolacja |
| instancja Maschkego `IsSemisimpleRing k[G]` + `IsSemisimpleRing → IsReduced` (przemienne) | zredukowanie `F[C_n]` bez ani jednego rachunku |
| `Module.finrank_pi_fintype`, `Submodule.finrank_quotient_le`, `PowerBasis.finrank` | księgowość wymiarów `Σ(2dᵢ−1) = 2n − t` |
| `MonoidAlgebra.mul_apply_left`, `Finsupp.linearEquivFunOnFinite` | most współrzędne ↔ algebra grupowa |

Wniosek metodologiczny: **jeden lemat strukturalny z Mathlib (`equivPi`) zastąpił całą
planowaną Falę 1 „świadków nierozkładalności Φ_n”**. Katalog świadków nie jest już potrzebny
do uzyskania dokładnych wartości — jest potrzebny dopiero do *nazwania* `t(n)` liczbą warstw
cyklotomicznych (§3.2).

---

## 3. Ranking dalszych ścieżek (malejący iloraz wartość/koszt)

### 3.1 [NAJWYŻSZY PRIORYTET BADAWCZY] Pełne Alder–Strassen z nilpotentami

**Cel:** `R(A) ≥ 2 dim A − t(A)` dla **dowolnej** skończenie wymiarowej algebry przemiennej,
nie tylko zredukowanej. Obecny dowód (charaktery w dziedziny) wymaga zredukowania.

**Dlaczego to jest ważne dla FFT:** mnożenie wielomianów **modulo `xᵏ`** (obcięte szeregi,
mnożenie „mod x^k” w NTT-based big-int, algorytmy Newtona na odwrotności) to algebra lokalna
`F[x]/(xᵏ)`, `t = 1`. Górną granicę `2k−1` już mamy (`adjoinRoot_bilinear_upper`),
dolna `2k−1` jest niedostępna obecną metodą.

**Ścieżka:** metoda podstawień na ideale maksymalnym `m`: wybrać `dim m` produktów tak,
by wyzerować lewe formy na `m`, i indukcyjnie schodzić po `m ⊃ m² ⊃ …`.
W obecnej infrastrukturze (`Substitution.lean`: `Restricts`, `cutLeft/cutRight`,
`exists_genAlg_of_restricts`) brakuje wariantu, w którym rolę „dziedziny” gra moduł
`m^i/m^{i+1}`. Szacowany koszt: średni; ryzyko: średnie.
**Kryterium sukcesu:** `R(F[x]/(xᵏ)) = 2k − 1` w Lean.

### 3.2 [TANIE, WYSOKA CZYTELNOŚĆ] `t(n)` = liczba warstw `p`-cyklotomicznych

Obecnie `t(n) := #MaxSpec F[x]/(xⁿ−1)` (definicja wewnętrzna) i konkretne wartości
wyprowadzamy z wartości dokładnych. Warto udowodnić tożsamość ogólną
`#MaxSpec = #{warstwy p-cyklotomiczne mod n}`, bo wtedy `t(n)` staje się **obliczalne
przez `decide`** dla dowolnego `n`, a wzór `c(n) = 2n − t(n)` — w pełni efektywny.

Kierunek „≤” jest już udowodniony (`factorCount_le_cover`: dla każdego pokrycia `S`
warstwami Frobeniusa mamy `t(n) ≤ |S|`, a warunek pokrycia jest rozstrzygalny przez
`decide`). Brakuje kierunku „≥”, czyli różnowartościowości przyporządkowania
„warstwa ↦ ideał maksymalny”. Brakujący lemat techniczny: dla `α` w ciele skończonym rozszerzającym `𝔽_p`,
`dim_{𝔽_p} 𝔽_p(α) = min{ j > 0 : α^{p^j} = α }`
(dowód: `𝔽_p[α]` zawiera się w zbiorze pierwiastków `X^{p^j} − X`, więc `p^{dim} ≤ p^j`;
odwrotnie `|𝔽_p(α)| = p^{dim}` daje `α^{p^{dim}} = α`). Koszt: mały; ryzyko: małe.

### 3.3 Normalizacja: model biliniowy → prostoliniowy

Twierdzenia dolne mówią o *algorytmach biliniowych*. Standardowe twierdzenie
(Strassen / Bini) mówi, że liczba mnożeń ogólnych w programie prostoliniowym obliczającym
formę kwadratową jest równa randze tensora z dokładnością do stałej 1/2 (a dla algorytmów
„quadratic” — dokładnie). Formalizacja tego mostu podnosi wszystkie wyniki dolne z modelu
biliniowego do modelu realnych programów (`SLPLowerBound.lean`).
Koszt: średni/duży; wartość: bardzo duża („optymalne dla realnych programów”).

### 3.4 Most do Verusa dla jąder o dokładnej złożoności

Mamy teraz *dowiedzione optymalne* jądra: długości 5 (8 mnożeń), 6, 10, 15, 30 (48).
Kolejny krok inżynierski: iteracyjny FFT in-place + niezmienniki pętli + kontrakty Verus,
z liczbą mnożeń jako częścią kontraktu. Koszt: średni; ryzyko: małe; wartość praktyczna: duża.

### 3.5 Rozszerzenia rodziny (tanie żniwa)

* `c(n)` dla wszystkich `n | p−1` (transformata daje `n`, `t(n) = n` — wynik natychmiastowy);
* splot wielowymiarowy i Agarwal–Cooley w wersji „dokładnej” (`c(mn) = c(m)c(n)`? — **nie**,
  równość na ogół nie zachodzi; ciekawe pytanie: dla których par `m,n` tensor jest optymalny —
  teraz mamy narzędzie, by to rozstrzygać *dokładnie*, bo znamy obie strony);
* `R(F[x]/f)` dla dowolnego bezkwadratowego `f` — **zrobione** w tej turze
  (`polyQuotient_exact`, `PolyQuotientExact.lean`).

---

## 4. NO-GO (potwierdzone ponownie)

* **Snopy / étale / homotopia / K-teoria** poza opisem wyznacznika: brak niezmiennika
  monotonicznego względem długości programu; `Spec(𝔽_p)` jest punktem; nic w literaturze
  2023–2026 nie łączy tych narzędzi z dolnymi granicami złożoności biliniowej. Koszt ogromny,
  ROI ≈ 0. Ta tura potwierdza to *pozytywnie*: dokładne wartości uzyskano wyłącznie
  narzędziami algebry przemiennej.
* **`Ω(n log n)`** w modelu liniowym — otwarte od dekad, zero poszlak.
* **„Ukryte symetrie Mersenne'a”** skalujące się poza dzielniki 31 (`|⟨2⟩| = 31`).
* **Pełna teoria faktoryzacji `xⁿ − 1`** — niepotrzebna: `IsArtinianRing.equivPi` załatwia
  rozkład, a `t(n)` liczymy strukturalnie (§3.2 tylko dla wygody obliczeniowej).

---

## 5. Kolejność wdrożenia

1. §3.2 (tanie, uzupełnia obraz `t(n)`).
2. §3.5 (żniwa: rodzina długości bez dodatkowej teorii).
3. §3.1 (najwyższa wartość merytoryczna — pełne Alder–Strassen z nilpotentami).
4. §3.3 (normalizacja do modelu prostoliniowego).
5. §3.4 (Verus, gdy jądra są już „dokładne”).
