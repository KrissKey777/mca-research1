# Grand MCA — plan 10 kroków i teoria, z której rozwiązanie ma wynikać naturalnie

**Status dokumentu.** To jest plan badawczy, a nie raport z wyników. Każdy krok podaje: cel,
*dlaczego akurat to* (z odwołaniem do już udowodnionych twierdzeń tego repozytorium),
postać docelową w Lean, kryterium sukcesu i kryterium przerwania. Wszystko, co poniżej jest
nazwane „twierdzeniem tego repozytorium”, jest maszynowo sprawdzone i `sorry`-free; wszystko,
co jest nazwane „hipotezą H1–H4”, jest do udowodnienia albo obalenia i **nie wolno na tym
budować wyników**.

---

## 0. Co dokładnie jest jeszcze do rozstrzygnięcia

Notacja: `n = |D|`, `k` wymiar, `e` promień, `κ = n − k`, gap `c = κ − e`, `η = c/n`,
`q = |F|`, `#Bad = (badSet k e f₀ f₁).card`, `ε_mca = #Bad/q`.

Stan wiedzy w repozytorium (skrót `MCA_RESEARCH_KERNEL.md` + `CAPACITY_GAP_REPORT.md`):

| reżim | najlepsza górna granica | najlepsza dolna granica |
|---|---|---|
| `3e < κ+1` | `e+1` (`card_badSet_le_succ_radius`) | `e+1` |
| `k+2e ≤ n` (UD) | `(k+1)e+1` (`card_badSet_le_unconditional`) | `≈ n/e` |
| `δ < 1−√ρ` (Johnson) | `n·Λ` (`card_badSet_le_listSizeMax`) | — |
| dowolny promień | `C(n,e)` (`card_badSet_le_circuit`) | — |
| `c = 1` | `C(n,k+1)` | `C(n,k+1)` — **równość** |
| `c` dowolne | — | `C(n/c, k/c+1) = exp(Θ(1/η))` |
| `η = o(1)` dowolnie wolno | — | `n^{Θ(log 1/η)}` (`exists_superpolynomial_badSet_of_small_relative_gap`) |

Wnioski, które przesądzają kształt planu:

1. **Postać „`#Bad ≤ poly(n)` aż do pojemności” jest fałszywa** — i to nie tylko o krok od
   pojemności: jest fałszywa przy **każdym** stałym progu `η ≤ 1/M`
   (`exists_superpolynomial_badSet_of_small_relative_gap`). Prawo warstwowe
   `poly(n) + exp(Θ(1/η))` też jest obalone.
2. Zatem „rozwiązać Grand MCA” **nie może** znaczyć „udowodnić `#Bad ≤ poly(n)`”. Musi
   znaczyć: **opisać dokładnie klasę, w której leżą wszystkie duże zbiory złych wyzwań**, i
   pokazać, że wiersze wdrożeniowe do tej klasy nie należą (albo należą — wtedy jest atak).
3. Wszystkie znane duże zbiory złych wyzwań są **addytywnie ustrukturyzowane**, a struktura
   jest dziedziczona z domeny:
   * `CapacityGapPencil` — wyzwania to `−∑_{i∈I} b_i`, czyli plaster kostki `{0,1}^m`,
     `m = n/c`; domena to suma `m` kosetów `μ_c`;
   * `card_badSet_ge_gapOne` — wyzwania to sumy `(k+1)`-podzbiorów domeny;
   * `SubspacePencil` — wyzwania to `−L_V(w)`, wartości wielomianów podprzestrzeniowych
     `ℓ`-wymiarowych `F_p`-podprzestrzeni `V ⊆ U`; domena to `U ∪ {w}`, `U` — `F_p`-podprzestrzeń;
   * `SemilinearPlaneDescent` / `FrobeniusOrbitBudget` — w klasie Frobeniusowej zbiór zły jest
     **zbiorem liniowym** (linear set) rangi `d` w `PG(1,q)`, mocy `≤ 1+q₀+…+q₀^{d−1}`.

To jest obserwacja, wokół której zbudowany jest cały plan.

---

## 1. Teoria: **struktura addytywna zbioru złych wyzwań** (ASB)

**Teza teorii (H1, hipoteza główna).** Zbiór złych wyzwań jest albo mały, albo
ustrukturyzowany, a jego struktura pochodzi ze struktury *domeny*:

> **H1 (dychotomia strukturalna).** Istnieją funkcje `P` (wielomianowa) i `R` takie, że dla
> każdej prostej MCA
> ```
> #Bad ≤ P(n)      ∨      rank(Bad) ≤ R(n, k, e, str(D)),
> ```
> gdzie `rank` to *ranga struktury* zbioru wyzwań (ranga kostki / GAP-u albo ranga zbioru
> liniowego), a `str(D)` to *addytywna złożoność domeny* (największy wymiar `F_p`-podprzestrzeni
> prawie zawartej w `D`, względnie ranga dysocjacyjna `D`).

**Dlaczego to jest właściwa teoria, a nie kolejny wariant zliczania:**

* jest **zgodna ze wszystkimi znanymi kontrprzykładami** — one nie są anomaliami, tylko
  *elementami ekstremalnymi klasy strukturalnej*: `rank ≈ n/c` (kostka), `rank ≈ ℓ(m−ℓ)`
  (podprzestrzenie), `rank ≤ d` (Frobenius);
* daje **inwariant malejący**: `rank` jest miarą descentu, której brakowało w `card_le_or_support_le`
  (tam descent był geometryczny: `n → n − |T|`); `rank` jest niezmiennikiem *wyzwań*, nie nośnika,
  więc obie miary są niezależne i można je składać;
* jest **kowariantna względem symetrii problemu**: `#Bad` jest z dokładnością do `±1`
  niezmiennikiem nieparametryzowanej płaszczyzny (`isBad_reparam`, `card_badSet_reparam_le`),
  a ranga kostki jest niezmiennicza względem afinicznych reparametryzacji `γ ↦ uγ+v`
  (udowodnione: `CubeRankLe.affine`); część rzutowa symetrii Möbiusa odpowiada drugiej
  połowie inwariantu — randze zbioru liniowego;
* **naturalnie implikuje Grand MCA dla wierszy wdrożeniowych**: `rank ≤ R` daje
  `#Bad ≤ 2^R` (albo `≤ (q₀^R−1)/(q₀−1)`), a wiersze protokołów mają `R` małe, bo ich domeny są
  **multiplikatywne** (`μ_{2^m}`), a nie addytywne;
* **jest pojemniejsza niż samo Grand MCA**: mówi o dowolnej rodzinie parametrycznej i o dowolnym
  kodzie ewaluacyjnym, a nie o prostych nad RS (patrz krok 10).

**Dwa naturalne obiekty teorii** (oba już zdefiniowane albo obecne w repozytorium):

* **ranga kostki / GAP-u** `CubeRankLe B m` — `B` mieści się w `{a + ∑_{i∈I} b_i}`;
  `#B ≤ 2^m` (nowy moduł `Root/CodingTheory/BadSetAdditiveStructure.lean`);
* **ranga zbioru liniowego** — `B` to zbiór kierunków `F₀`-podprzestrzeni `W ⊆ K×K`;
  `(|F₀|−1)·#B + 1 ≤ |F₀|^{dim W}` (`SpreadMCA.card_badWithPair_le_of_finrank`).

---

## 2. Plan 10 kroków

Kolejność jest zależnościowa: 1→2→3→4 to trzon (mechanizm), 5–7 to trzy gałęzie dowodu H1,
8–9 to złożenie i wiersze wdrożeniowe, 10 to uogólnienie.

### Krok 1 — inwariant i jego rachunek *(rozpoczęty)*

**Cel.** Zdefiniować `CubeRankLe` / rangę zbioru liniowego jako pierwszoklasowe obiekty i
udowodnić rachunek: `#B ≤ 2^m`, monotoniczność, dziedziczenie na podzbiory, kowariancja
afiniczna, zachowanie przy sumach i iloczynach kartezjańskich, oraz relacja obu rang
(zbiór liniowy rangi `r` nad `F_p` ma rangę kostki `≤ (p−1)r`).

**Lean.** `RequestProject/Root/CodingTheory/BadSetAdditiveStructure.lean` (istnieje;
`icube`, `CubeRankLe`, `card_le_two_pow_of_cubeRankLe`, `CubeRankLe.mono/subset/affine`).

**Sukces.** Rachunek zamknięty, bez hipotez. **Przerwanie:** niemożliwe — to definicje.

### Krok 2 — katalog ekstremalny: każda znana dolna granica jest ustrukturyzowana

**Cel.** Dla każdej rodziny z tabeli §0 udowodnić *jawną* granicę rangi, obok znanej granicy
mocy. Docelowa tabela: rodzina ↦ `#Bad` ↦ `rank` ↦ `log_2 #Bad / rank`.

**Konkretne zadania.**
1. `CapacityGapPencil`: rodzina świadków `{−∑_{i∈I} b_i : |I| = s+1}` ma `rank ≤ m = n/c`,
   przy `#Bad ≥ C(m, s+1)`;
2. `card_badSet_ge_gapOne`: `rank ≤ n`, przy `#Bad = C(n, k+1)`;
3. `SubspacePencil`: `{−L_V(w)}` — pokazać, że leży w `F_p`-podprzestrzeni `⟨L_{V_0}(w)⟩`
   generowanej przez `O(m)` elementów, czyli `rank ≤ m` (a `#Bad ≥ p^{ℓ(m−ℓ)}`);
4. `PolyGen.Saturation.satFam`: ranga rodziny saturującej;
5. `CommonWindowPencil` i `FoldPencil`: rodziny *wielomianowo* duże — sprawdzić, czy mają
   **dużą** rangę (jeśli tak, to rangowa gałąź dychotomii nie może być jedyna i `P(n)` w H1
   jest istotne; to jest test poprawności sformułowania H1).

**Sukces.** Cała tabela udowodniona. **Przerwanie:** gdyby któraś rodzina o superwielomianowej
mocy miała rangę `Θ(log #Bad)` bez struktury addytywnej — wtedy H1 w postaci kostkowej pada i
trzeba przejść na inwariant rzutowy (ranga zbioru liniowego) jako jedyny.

### Krok 3 — pierwsze pełne twierdzenie teorii: gap 1 jest *dokładnie* addytywny *(w toku)*

**Cel.** Nie tylko „istnieje duża ustrukturyzowana rodzina zła”, ale **równość**:

> Dla pęku potęgowego `f₀ = x^{k+1}`, `f₁ = x^k` i dowolnego promienia z `k+1+e ≤ n`:
> `badSet k e f₀ f₁ = { −∑_{x∈S} x : S ⊆ D, |S| = k+1 }`.

Zawieranie `⊇` to `isBad_gapOne` (istnieje). Zawieranie `⊆` jest nowe i jest sercem kroku:
okno wymusza *dokładną* interpolację `X^{k+1} + γX^k − p = ∏_{x∈S}(X−x)`, a współczynnik przy
`X^k` odczytuje `γ = −∑_{x∈S} x`. To jest pierwszy przypadek, w którym zbiór zły jest
**policzony strukturalnie, a nie oszacowany**.

**Lean.** `powerPencil_eq_vanishing`, `badSet_powerPencil_subset_image_sum`,
`badSet_powerPencil_eq_image_sum`, `cubeRank_badSet_powerPencil`
(w `BadSetAdditiveStructure.lean`).

**Sukces.** Równość udowodniona. **Konsekwencja natychmiastowa:** ekstremalny obiekt całej
teorii (ten, który realizuje `C(n,k+1)` i obala wszelkie granice wielomianowe) jest
*dosłownie* zbiorem sum podzbiorów domeny — czyli H1 jest w tym punkcie prawdziwa i ostra.

### Krok 4 — mechanizm ogólny: **wyzwanie jest funkcją symetryczną okna**

**Cel.** Uogólnić krok 3 na dowolny gap i dowolną prostą. Kształt docelowy:

> Niech `γ` będzie złe ze świadkiem `S`, `|S| = k+c`. Wtedy `γ` spełnia układ `c` równań
> algebraicznych o współczynnikach będących funkcjami symetrycznymi `e_1(S), …, e_c(S)`
> elementów okna; przy `c = 1` układ redukuje się do `γ = −e_1(S)`.

To jest *jedyny* znany mechanizm, który tłumaczy jednocześnie: dlaczego gap 1 jest addytywny,
dlaczego przy gapie `c` konstrukcje muszą używać bloków binomialnych (`X^c − b` zeruje
`e_2,…,e_c`), i dlaczego wykładnik `n/c` jest wewnętrzny dla metody (`CAPACITY_GAP_REPORT` §5).
Formalnie: mapa `Bad → {okna}/∼` faktoryzuje się przez mapę Newtona
`S ↦ (e_1(S), …, e_c(S))`, a rezydualne warunki `c−1` to dokładnie warunki Schuberta z §5.1
tamtego raportu.

**Sukces.** Twierdzenie „`Bad ⊆ obraz mapy Newtona ograniczonej do okien dopuszczalnych`”
w Lean, dla dowolnego `c`. **Przerwanie:** jeśli dla `c ≥ 2` nie da się wyeliminować
zależności od `p` (interpolant), zostawiamy wersję dla pęku potęgowego i przechodzimy do
kroku 5 — ona wystarcza do katalogu.

### Krok 5 — twierdzenie odwrotne (gałąź „lekka”): mała ranga ⇒ skończony koszt

**Cel.** Udowodnić drugą połowę użyteczności inwariantu: `rank(Bad) ≤ r` **implikuje descent**,
a nie tylko `#Bad ≤ 2^r`. Kształt:

> Jeżeli `Bad` leży w kostce rangi `r` (odpowiednio: w zbiorze liniowym rangi `r`), to pęk
> `(f₀, f₁)` jest — modulo kod — niezmienniczy względem grupy translacji generowanej przez
> generatory kostki, co redukuje instancję do instancji z `r−1` generatorami.

Punkt zaczepienia: `SemilinearPlaneDescent.card_badSet_le_of_semilinear` jest dokładnie
przypadkiem `r = 1` wersji rzutowej (`#Bad ≤ q+1`), a `card_badSet_mul_le_of_orbit`
przypadkiem ogólnym z `μ = dim` orbity Frobeniusa. Trzeba to przenieść z klasy semiliniowej na
klasę „ranga kostki mała”.

**Sukces.** Rekurencja `r → r−1` z jawnym kosztem. **Przerwanie:** jeśli translacja generatora
nie zachowuje wspólnego nośnika (a to jest realne ryzyko: przesunięcie wyzwania rusza okno),
wynik zostaje w postaci warunkowej i przechodzimy do kroku 6, gdzie mechanizm jest
nośnikowy, a nie wyzwaniowy.

### Krok 6 — gałąź „ciężka”: struktura addytywna wyzwań ⇒ struktura addytywna domeny

**Cel.** To jest centralny krok całego programu i tu leży ryzyko:

> **H2.** Jeżeli `#Bad > P(n)`, to domena `D` zawiera dużą strukturę addytywną: `Ω(n)`
> elementów `D` leży w sumie `O(1)` kosetów `F_p`-podprzestrzeni wymiaru `o(n)` — albo `D`
> zawiera `m = Ω(log #Bad)`-elementowy podzbiór dysocjacyjny sprzężony z oknami.

Dowód ma iść przez krok 4: duży zbiór wyzwań ⇒ dużo okien o *różnych* pierwszych funkcjach
symetrycznych i *tych samych* wyższych ⇒ addytywna struktura na `D`. Dokładnie ten schemat
działa w obie znane konstrukcje i dokładnie on nie jest jeszcze udowodniony w żadną stronę.

**Sukces.** H2 udowodnione choćby dla `c ≤ 2`. **Przerwanie:** kontrprzykład (duży `Bad` nad
domeną bez struktury addytywnej) — to również jest wynik pierwszej klasy, bo obala H1 i
przenosi teorię na inwariant czysto rzutowy.

### Krok 7 — wejście multiplikatywne: domeny `μ_N` nie mają struktury z kroku 6

**Cel.** Uzupełnić dychotomię o twierdzenie odcinające dla domen protokołowych.

> **H3.** Podgrupa multiplikatywna `μ_N ⊆ F_q^*` (a także jej koset) nie zawiera struktury
> addytywnej wymaganej przez H2 powyżej progu `N ≤ q^{1−ε}`.

To jest klasyczny teren *sum-produktu* i metody Stepanowa; częściowe, w pełni elementarne
wersje są osiągalne (np. „`μ_N` nie rozkłada się na `m` kosetów `μ_c` dla `c ∤ N`”, co już
wyklucza konstrukcję blokową na wierszu wdrożeniowym, bo tam `c = 67472 ∤ 2^{21}`).

**Sukces.** Choćby jedno bezwarunkowe twierdzenie odcinające dla `μ_{2^m}`.
**Kryterium przerwania:** jeśli potrzebne są ograniczenia typu Weila niedostępne w Mathlib,
formalizujemy wariant elementarny (dzielnikowy), a resztę zostawiamy jako jawną hipotezę.

### Krok 8 — złożenie: twierdzenie Grand MCA w postaci strukturalnej

**Cel.** Złożyć 5+6+7 w jedno:

> **Twierdzenie (docelowe).** Dla domeny bez struktury addytywnej progu H2 i dla dowolnej
> prostej MCA: `#Bad ≤ P(n)`. W szczególności dla `D = μ_N` z `N ≤ q^{1−ε}` proximity gap
> zachodzi aż do pojemności z `ε_mca ≤ P(n)/q`.

To jest dokładnie „rozwiązanie Grand MCA” w jedynej postaci, która po §0 może być prawdziwa:
z jawną klasą wyjątkową, a nie bezwarunkowo.

**Lean.** `StructureDichotomy` (predykat już zdefiniowany) + `card_badSet_le_of_structureDichotomy`
jako brama liczbowa; potem podstawienie udowodnionych `P`, `R`.

### Krok 9 — wiersze wdrożeniowe i Prize

**Cel.** Podstawić parametry (`p = 2^{31}−2^{24}+1`, `K = F_{p^6}`, `H = μ_{2^{21}}`, `k = 2^{20}`,
`B* = 274980728111395087`) i uzyskać dwustronny nawias na `δ*`. Wszystkie liczby jako
arytmetyka całkowita sprawdzona jądrem, żadnych benchmarków, żadnych obietnic wydajnościowych.
Uwaga metodologiczna: **wiersz nie wchodzi do matematyki rdzenia** — wchodzi wyłącznie tutaj.

### Krok 10 — pojemność teorii: to samo twierdzenie poza RS i poza prostymi

**Cel.** Pokazać, że inwariant i dychotomia nie zależą od tego, że kod to RS, a rodzina to prosta:

* dowolny kod ewaluacyjny / generator wielomianowy arności `ℓ` (`badSetG`) — mechanizm kroku 4
  to nadal funkcje symetryczne okna;
* folded RS i kody przeplatane — `FoldedRSMCA*`, `WeightedInterleavedList`;
* rodziny parametryczne wyższego wymiaru (krzywe, podprzestrzenie) — wtedy „prosta w `PG(1,q)`”
  zastępuje się `PG(d,q)`, a ranga zbioru liniowego jest tym samym inwariantem;
* kody AG: rolę krzywej wymiernej normalnej (obraz `x ↦ (1,x,…,x^{κ−1})` w przestrzeni syndromów)
  przejmuje krzywa kodu, a rolę katalektikanta — jej równania secantowe.

**Sukces.** Twierdzenie z kroku 8 sformułowane dla klasy kodów, z Grand MCA jako korolarzem.

---

## 3. Mapa zależności (DAG planu)

```
   [1] inwariant  ──────────────┐
        │                       │
        ▼                       ▼
   [2] katalog ekstremalny   [3] gap 1: równość (pierwsze twierdzenie)
        │                       │
        └──────────┬────────────┘
                   ▼
        [4] wyzwanie = funkcja symetryczna okna      ← mechanizm
                   │
        ┌──────────┴───────────┐
        ▼                      ▼
  [5] mała ranga ⇒ descent   [6] duży Bad ⇒ struktura domeny   (H2, ryzyko)
        │                      │
        │                      ▼
        │              [7] μ_N nie ma tej struktury (H3, sum-product)
        └──────────┬───────────┘
                   ▼
        [8] Grand MCA w postaci strukturalnej
                   │
        ┌──────────┴───────────┐
        ▼                      ▼
  [9] wiersze / Prize    [10] uogólnienie (badSetG, folded, AG, PG(d,q))
```

Ścieżka krytyczna: **4 → 6 → 7**. Kroki 1–3 są tanie i już się dzieją; 5 jest niezależny i
może iść równolegle; 9–10 są mechaniczne po 8.

---

## 4. Co ten plan **obala**, jeśli się powiedzie, i co **potwierdza**

* potwierdza: proximity gap aż do pojemności dla domen multiplikatywnych — czyli dla wszystkich
  wierszy FRI/STIR/WHIR, których używa praktyka;
* obala: przekonanie, że „Grand MCA” może mieć postać bezwarunkową (już obalone,
  `exists_superpolynomial_badSet_of_small_relative_gap`), i przekonanie, że przeszkodą jest
  rozmiar listy — przeszkodą jest **struktura addytywna domeny**;
* daje protokołom kryterium projektowe: *nie wybieraj domeny addytywnej* (`F_p`-podprzestrzeni,
  sumy kosetów `μ_c` z `c | n`), bo dokładnie tam żyją wszystkie znane kontrprzykłady.

---

## 5. Kryteria uczciwości (obowiązują w każdym kroku)

1. Żadnych `axiom`. Hipotezy H1–H3 są `def … : Prop` albo jawnymi założeniami twierdzeń.
2. Każde twierdzenie liczbowe o wierszu wdrożeniowym — z `#print axioms`.
3. Żadnych twierdzeń o wydajności bez benchmarku (zasada z `DISCREPANCIES.md`).
4. Kontrprzykład jest wynikiem równorzędnym z twierdzeniem: obalenie H1/H2/H3 zamyka krok
   tak samo dobrze jak dowód, o ile podaje klasę, w której leży awaria.
