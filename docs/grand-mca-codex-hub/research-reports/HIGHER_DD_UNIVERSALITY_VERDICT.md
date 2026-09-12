# Higher divided differences: uniwersalny most czy engine dla pencils?

Analiza **wyłącznie już udowodnionych** twierdzeń z
`RequestProject/Root/CodingTheory/SymmetricWindowMechanism.lean`,
`RequestProject/Root/CodingTheory/HigherDividedDifferences.lean`,
`RequestProject/Root/CodingTheory/GapOneUniversality.lean`
(oraz ich bazy `MCA.lean`, `CircuitPencilMap.lean`).
Żadnych nowych eksperymentów, żadnych przeniesień plików, żadnych nowych dowodów.
Wszystko, co poniżej opisane jest jako „udowodnione”, jest machine-checked, bez `sorry`
i bez axiomów; wszystko, co jest propozycją, jest wyraźnie oznaczone jako **nieudowodnione**.

---

## 0. Wspólny słownik (definicje, na których stoją te twierdzenia)

Kontekst globalny wszystkich trzech plików:

```lean
variable {F : Type u} [Field F] [DecidableEq F] {D : Finset F}
```

`D` — domena ewaluacji (Finset ciała `F`), słowa to funkcje `↥D → F`.

```lean
-- MCA.lean
def IsCloseOn (k : ℕ) (S : Finset ↥D) (f : ↥D → F) : Prop :=
  ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x ∈ S, f x = p.eval (x : F)

def LineCloseOn (k : ℕ) (S : Finset ↥D) (f₀ f₁ : ↥D → F) : Prop :=
  ∀ γ : F, IsCloseOn k S (lineComb f₀ f₁ γ)

def IsBad (k e : ℕ) (f₀ f₁ : ↥D → F) (γ : F) : Prop :=
  ∃ S : Finset ↥D, D.card ≤ S.card + e ∧ IsCloseOn k S (lineComb f₀ f₁ γ) ∧
    ¬ LineCloseOn k S f₀ f₁

noncomputable def badSet [Fintype F] (k e : ℕ) (f₀ f₁ : ↥D → F) : Finset F  -- filter IsBad

-- ProximityGapLines.lean
def lineComb (f₀ f₁ : ↥D → F) (z : F) : ↥D → F := fun x => f₀ x + z * f₁ x

-- CircuitPencilMap.lean
noncomputable def divDiff (k : ℕ) (T : Finset ↥D) (u : ↥D → F) : F :=
  (Lagrange.interpolate T (fun x : ↥D => (x : F)) u).coeff k

-- SymmetricWindowMechanism.lean
noncomputable def polyWord (D : Finset F) (P : F[X]) : ↥D → F := fun x => P.eval (x : F)
noncomputable def winSym (i : ℕ) (T : Finset ↥D) : F := ∑ S ∈ T.powersetCard i, ∏ x ∈ S, (x : F)

-- HigherDividedDifferences.lean
noncomputable def higherDivDiff (j : ℕ) (S : Finset ↥D) (u : ↥D → F) : F :=
  (Lagrange.interpolate S (fun x : ↥D => (x : F)) u).coeff j
```

Uwaga terminologiczna, kluczowa dla całej dalszej dyskusji:
**`S` w `IsBad` to zbiór zgodności (agreement window), a nie support błędu.**
„Official bad support” w semantyce MCA to `E = D \ S`, `|E| ≤ e`.
Wszystkie twierdzenia poniżej mówią o `S`; przejście `S ↔ E` jest bijektywne
(`D.card ≤ S.card + e` ⟺ `|E| ≤ e`), więc „obiekt lokalny supportu” to u nas
„macierz okna komplementarnego”.

---

## 1. Dokładne sygnatury i scope

### 1.1 `Root.CodingTheory.isCloseOn_iff_forall_higherDivDiff`

Plik: `HigherDividedDifferences.lean`.

```lean
theorem isCloseOn_iff_forall_higherDivDiff {k : ℕ} {S : Finset ↥D} {u : ↥D → F} :
    IsCloseOn k S u ↔ ∀ j, k ≤ j → higherDivDiff j S u = 0
```

* Typy: `F` dowolne ciało z `DecidableEq` (bez `Fintype`!), `D : Finset F`,
  `k : ℕ` dowolne, `S : Finset ↥D` **dowolne** (bez założeń o rozmiarze),
  `u : ↥D → F` **dowolna funkcja**.
* Hipotezy: **żadnych**. To czysty `iff` bez side conditions.
* `u` arbitrary word — **nie** musi pochodzić z wielomianu.
* Gap: bez znaczenia; nie ma tu pojęcia gapu. Liczba nietrywialnych równań to
  `|S| − k` (dla `j ≥ |S|` znikanie jest automatyczne — `higherDivDiff_eq_zero_of_card_le`).
* Klasyfikacja: **A. arbitrary official MCA received words.**

### 1.2 `Root.CodingTheory.isBad_iff_higherDivDiff`

```lean
theorem isBad_iff_higherDivDiff {k e : ℕ} {f₀ f₁ : ↥D → F} {γ : F} :
    IsBad k e f₀ f₁ γ ↔
      ∃ S : Finset ↥D, D.card ≤ S.card + e ∧
        (∀ j, k ≤ j → higherDivDiff j S f₀ + γ * higherDivDiff j S f₁ = 0) ∧
        (∃ j, k ≤ j ∧ higherDivDiff j S f₁ ≠ 0)
```

* Typy: jak wyżej; `f₀ f₁ : ↥D → F` **dowolne received words**, `γ : F` dowolne,
  `e : ℕ` dowolne. Bez `Fintype F`.
* Hipotezy: **żadnych** — ani o `|D|`, ani o `k`, `e`, ani o stopniu.
* Nie ma żadnego założenia wielomianowego.
* Gap: **dowolny `c`**. Okno `S` ma rozmiar `≥ |D| − e`; liczba kolumn układu to `|S| − k`
  (przy `|D| = k + e + c` i maksymalnym `S` daje to `c` kolumn niezerowych ponad wymuszone zera).
* Klasyfikacja: **A. arbitrary official MCA received words.**

### 1.3 `Root.CodingTheory.higherDivDiff_minor_eq_zero`

```lean
theorem higherDivDiff_minor_eq_zero {k e : ℕ} {f₀ f₁ : ↥D → F} {γ : F}
    (h : IsBad k e f₀ f₁ γ) :
    ∃ S : Finset ↥D, D.card ≤ S.card + e ∧
      (∀ j j', k ≤ j → k ≤ j' →
        higherDivDiff j S f₀ * higherDivDiff j' S f₁
          - higherDivDiff j' S f₀ * higherDivDiff j S f₁ = 0) ∧
      (∃ j, k ≤ j ∧ higherDivDiff j S f₁ ≠ 0)
```

* Typy: `f₀ f₁ : ↥D → F` **dowolne**, `γ : F`, `k e : ℕ` dowolne. Bez `Fintype F`.
* Jedyna hipoteza: `IsBad k e f₀ f₁ γ`.
* Bez założeń wielomianowych, bez bound na stopień.
* Gap: **dowolny `c`**.
* Klasyfikacja: **A. arbitrary official MCA received words.**
* Zastrzeżenie o zakresie kwantyfikacji (istotne dla pytania 2): `S` jest **egzystencjalne**,
  tzn. twierdzenie mówi „istnieje official window, którego macierz ma rank ≤ 1”, a nie
  „dla każdego official window”. Wersja punktowa (dla zadanego świadka `S`) nie jest w pliku
  wyeksponowana jako osobne twierdzenie — patrz §2.3.

### 1.4 `Root.CodingTheory.badSet_subset_image_newtonChallenge`

Plik: `SymmetricWindowMechanism.lean` (sekcja `Newton`), z

```lean
noncomputable def newtonChallenge (k c : ℕ) (D : Finset F) (P₀ P₁ : F[X]) (v : Fin c → F) : F :=
  if h : ∃ T : Finset ↥D, T.card = k + 1 ∧ ∀ i : Fin c, winSym ((i : ℕ) + 1) T = v i then
    - divDiff k h.choose (polyWord D P₀) / divDiff k h.choose (polyWord D P₁)
  else 0
```

```lean
theorem badSet_subset_image_newtonChallenge {k e c : ℕ} (hD : k + 1 + e ≤ D.card)
    {P₀ P₁ : F[X]} (h₀ : P₀.natDegree ≤ k + c) (h₁ : P₁.natDegree ≤ k + c) :
    badSet k e (polyWord D P₀) (polyWord D P₁) ⊆
      ((Finset.univ : Finset ↥D).powersetCard (k + 1)).image
        (fun T => newtonChallenge k c D P₀ P₁ (fun i : Fin c => winSym ((i : ℕ) + 1) T))
```

(w tej sekcji obowiązuje `[Fintype F]`, bo występuje `badSet`).

* Typy: `P₀ P₁ : F[X]`; received words są **wyłącznie** postaci `polyWord D P`.
* Hipotezy: `k + 1 + e ≤ |D|`, oraz **dokładny bound na stopień**:
  `P₀.natDegree ≤ k + c` i `P₁.natDegree ≤ k + c`, gdzie `c` to gap parametryzujący
  liczbę użytych funkcji symetrycznych.
* Gap: dowolne `c`, ale `c` jest sprzężone ze stopniem — to jest sedno: to twierdzenie
  ma treść tylko wtedy, gdy `c` jest małe (`c ≥ k+1` daje trywialny obraz).
* Klasyfikacja: **C. bounded-degree polynomial pencil.**

### 1.5 Dwa dodatkowe punkty odniesienia (dla kompletności skali)

* `card_badSet_le_one_of_degree_lt` (`HigherDividedDifferences.lean`): hipotezy
  `P₀.degree < w`, `P₁.degree < w`, `w + e ≤ |D|`, teza `#badSet ≤ 1`. Klasa **C**.
* Cały `GapOneUniversality.lean` (`card_badSet_gapOne_le_card_winSums`,
  `card_winSums_le_card_badSet_succ`, `choose_le_card_badSet_gapOne_succ`,
  `card_badSet_gapOne_pencil_invariant`) ma hipotezy
  `D.card = k + 1 + e`, `P₀.natDegree ≤ k+1`, `P₁.natDegree ≤ k+1`,
  `hdet : P₀.coeff (k+1) * P₁.coeff k − P₀.coeff k * P₁.coeff (k+1) ≠ 0`.
  Klasa: **C ∧ D** — bounded-degree polynomial pencil **i** wyłącznie `c = 1`.
  (`winSums D k` to czysto addytywny niezmiennik domeny.)

**Podsumowanie klasyfikacji**

| twierdzenie | klasa |
|---|---|
| `isCloseOn_iff_forall_higherDivDiff` | **A** |
| `isBad_iff_higherDivDiff` | **A** |
| `higherDivDiff_minor_eq_zero` | **A** |
| `badSet_subset_image_newtonChallenge` | **C** |
| `card_badSet_le_one_of_degree_lt` | **C** |
| cały `GapOneUniversality` | **C + D** |

Czyli: **mechanizm higher-DD jest klasy A, a mechanizm Newton/symetryczny jest klasy C/D.**
To dwie różne warstwy, mimo że leżą w sąsiednich plikach.

---

## 2. Najważniejsze pytanie: czy dla dowolnego official supportu istnieje `M_S` rangi ≤ 1?

**TAK — jako obiekt lokalny.** Bez żadnej hipotezy polynomial/degree.

### 2.1 Definicja `M_S`

Dla official świadka `S ⊆ D` (`|D| ≤ |S| + e`, `E = D \ S` to official bad support) i pary
received words `(f₀, f₁)` kładziemy `c_S := |S| − k` i

```
M_S ∈ F^{2 × c_S},   (M_S)_{r, j} = higherDivDiff (k + j) S f_r,   r ∈ {0,1}, 0 ≤ j < c_S,
```

czyli wiersze to wektory `(hdd_k S f_r, hdd_{k+1} S f_r, …, hdd_{|S|−1} S f_r)`.
Kolumny o indeksie `j ≥ |S|` można dopisywać dowolnie — są zerowe automatycznie
(`higherDivDiff_eq_zero_of_card_le`), więc `c_S = |S| − k` jest kanonicznym obcięciem.

Wtedy udowodnione są:

* `higherDivDiff_lineComb`: `M_S · (1, γ)ᵀ = (hdd_j S (f₀ + γ f₁))_j` — wiersze są *liniowe* w słowie;
* `isCloseOn_iff_forall_higherDivDiff`: `M_S (1,γ)ᵀ = 0` ⟺ `IsCloseOn k S (lineComb f₀ f₁ γ)`;
* `isBad_iff_higherDivDiff`: badness ⟺ ∃ official `S` z `M_S (1,γ)ᵀ = 0` i drugim wierszem ≠ 0;
* `higherDivDiff_minor_eq_zero`: wszystkie minory `2×2` macierzy `M_S` znikają, tzn. `rank M_S ≤ 1`;
* `challenge_eq_of_higherDivDiff`: `γ = − (M_S)_{0,j} / (M_S)_{1,j}` z dowolnej kolumny o
  niezerowym drugim wpisie.

### 2.2 Jakie dane official witnessu koduje `M_S`

`M_S` koduje **dokładnie syndrom pary `(f₀,f₁)` względem kodu RS(k) obciętego do `S`**:
wiersz `r` to obraz `f_r|_S` w przestrzeni ilorazowej `F^S / RS_k|_S`, wyrażony w bazie
Newtona (współczynniki `X^k, …, X^{|S|−1}` interpolanta Lagrange'a).
Ponieważ `hdd_j S u = 0` dla wszystkich `j ≥ k` ⟺ `u|_S ∈ RS_k|_S`, macierz `M_S`
jest kompletnym niezmiennikiem pary `(f₀|_S, f₁|_S)` modulo kod.

Zatem:

* `rank M_S = 0` ⟺ oba słowa są close na `S` ⟺ `LineCloseOn k S f₀ f₁` (świadek zdegenerowany);
* `rank M_S = 1` ⟺ istnieje **dokładnie jeden** `γ` z `IsCloseOn k S (f₀ + γ f₁)` — to jest
  official bad witness;
* `rank M_S = 2` ⟺ `S` nie jest świadkiem żadnego challenge'u.

To jest pełna trychotomia i jest to treść (a nie tylko konsekwencja) twierdzeń §1.2–§1.3.

### 2.3 Od czego `M_S` zależy

* **Zależy** od supportu `S` (równoważnie od `E = D \ S`) i od pary received words `(f₀,f₁)`.
* **Nie zależy** od challenge'u `γ` ani od żadnego interpolanta: `γ` jest *odzyskiwany*
  z `M_S` (jądro rzutowe `[1 : γ]`), a nie wchodzi do jego definicji. To jest właśnie
  „determinantal residue” — warunki `rank ≤ 1` są warunkami na oknie samym w sobie.
* **Sam support nie wystarcza** do rekonstrukcji `M_S`: potrzeba `S` *oraz* wartości
  `f₀|_S, f₁|_S`. Sam support wystarcza natomiast do rekonstrukcji **przestrzeni funkcjonałów**
  (parity-check space `dual(RS_k|_S)`), w której `M_S` jest zapisane — i to jest ten kawałek,
  który jest czysto kombinatoryczny (zależy tylko od `S`, przez Vieta / `winSym`).

### 2.4 Ograniczenie, którego trzeba być świadomym

To, co jest machine-checked, ma kwantyfikator `∃ S`, nie `∀ S`.
Wersja „pointwise”, tzn.

> dla **zadanego** official świadka `S` badness na `S` jest równoważna
> (`rank M_S ≤ 1` ∧ drugi wiersz `M_S ≠ 0`),

nie jest osobnym twierdzeniem w pliku. Jest to jednak konsekwencja już udowodnionych
składników (`isCloseOn_iff_forall_higherDivDiff` + `higherDivDiff_lineComb`
+ `not_isCloseOn_direction_of_isBad`) — dokładnie tak przebiega dowód `isBad_iff_higherDivDiff`
dla świadka wziętego z `IsBad`. To jest luka w **ekspozycji**, nie w matematyce.
Propozycja dokładnego statementu — §6, punkt 5.

---

## 3. Relacja z teorią Aristotle(new)

Nazwy `BadSupport`, `exists_aligns_pair`, „pairwise rank-one alignment”, „triple non-flat rank
law” **nie występują w tym projekcie** — nie mogę więc podać identyfikacji przez unifikację
symboli, tylko przez treść matematyczną opisaną w pytaniu. Z tym zastrzeżeniem:

Odpowiedź: **(2) obiekt równoważny po zmianie bazy**, z jednym dopiskiem, że
w wymiarze kolumn jest to obiekt *większy* (kanonicznie zawiera opisane obiekty jako obcięcia).

Uzasadnienie algebraiczne:

1. Dla ustalonego `S` funkcjonały `hdd_k, …, hdd_{|S|−1}` tworzą **bazę** przestrzeni
   `dual(RS_k|_S) ≅ (F^S / RS_k|_S)^*`, wymiaru `|S| − k`.
   („Baza” — bo znikanie wszystkich jest równoważne przynależności do kodu, a wymiar się zgadza.)
2. Każdy „carrier / divided difference” w sensie support-level theory jest funkcjonałem
   dualnym o nośniku w `S`. W szczególności circuit functional `divDiff k T` dla `(k+1)`-podzbioru
   `T ⊆ S` jest elementem tej samej przestrzeni; w projekcie zapis `divDiff_eq_higherDivDiff`
   mówi wprost `divDiff k T = higherDivDiff k T` (`rfl`).
3. Wobec tego „pairwise rank-one alignment” w bazie circuitów i „`rank M_S ≤ 1`” w bazie Newtona
   to **ta sama macierz w dwóch bazach przestrzeni dualnej**, tzn. `M_S^{circ} = M_S · A`
   dla pewnej macierzy `A` o `c_S` wierszach (kolumny = wybrane circuity). Ranga jest
   niezmiennikiem, więc implikacja `rank M_S ≤ 1 ⟹ rank M_S^{circ} ≤ 1` jest darmowa;
   implikacja odwrotna wymaga, by wybrane circuity **rozpinały** `dual(RS_k|_S)`
   (co dla `|S| ≥ k+1` jest prawdą, bo circuity rozpinają dual kodu MDS).
4. „Support → canonical challenge/interpolant” to u nas dokładnie
   `challenge_eq_of_higherDivDiff` (`γ = −hdd_j S f₀ / hdd_j S f₁`), plus
   `challenge_eq_of_isBad` w wersji circuitowej (`CircuitPencilMap.lean`).
   Kanoniczny interpolant to `Lagrange.interpolate S _ (lineComb f₀ f₁ γ)`, tzn. dosłownie
   obiekt, którego współczynniki definiują `higherDivDiff`.
5. „Triple non-flat rank law” nie ma odpowiednika: w naszej warstwie wszystko jest
   `2 × c` (dwa received words). Trójkowe prawa rangi żyją w wariancie
   `QuadraticGeneratorMCA` / `PolynomialGeneratorMCA`, gdzie generator ma arity `> 2`,
   i tam analogon `M_S` nie jest udowodniony.

**Identyfikacja w jednym zdaniu.** `M_S` to macierz odwzorowania
`Λ_S : dual(RS_k|_S) → F²`, `λ ↦ (λ(f₀), λ(f₁))`, w bazie Newtona przestrzeni źródłowej;
support-level „rank-one alignment object” to ta sama `Λ_S` w bazie circuitowej.
Różnica: `Λ_S` jest bazowo-niezależna i **irredundantna** (`|S| − k` kolumn), podczas gdy opis
circuitowy używa `C(|S|, k+1)` kolumn, z których prawie wszystkie są kombinacjami pozostałych.

---

## 4. Relacja z syndrome-space

**TAK.** `M_S` jest dosłownie macierzą syndromów, a nie tylko jej analogiem.

Zapis przez parity-check submatrix. Niech `H_S ∈ F^{c_S × S}` będzie macierzą, której wiersz `j`
(`k ≤ j < |S|`) ma wpisy

```
(H_S)_{j,x} = (−1)^{|S|−1−j} · e_{|S|−1−j}(S \ {x}) / ∏_{y ∈ S, y ≠ x} (x − y),   x ∈ S,
```

gdzie `e_i` to elementarna funkcja symetryczna (w projekcie: `winSym i`, a Vieta dla okna
to `winPoly_coeff`). Wiersze `H_S` to współczynniki `X^j` w bazie Lagrange'a, czyli
`H_S` jest parity-check matrix kodu `RS_k|_S` (rank `|S| − k`, MDS). Wtedy

```
M_S = [ f₀|_S ; f₁|_S ] · H_Sᵀ ,        tzn.  (M_S)_{r,j} = ∑_{x∈S} (H_S)_{j,x} · f_r(x).
```

To jest **minor syndrome matrix / restricted evaluation matrix** w czystej postaci:
„restricted” do `S`, tzn. z shortenowanego kodu (support błędu `E = D \ S` wycięty).

Zastrzeżenie o statusie: powyższy jawny wzór na `(H_S)_{j,x}` jest standardowym faktem
o bazie Lagrange'a i **nie jest w tej ogólności machine-checked w projekcie**; machine-checked
jest przypadek `j = k`, `|T| = k+1` (`divDiff_eq_sum`:
`divDiff k T u = ∑_{x∈T} u x / ∏_{y ∈ T.erase x} (x − y)`) oraz cała Vieta okna
(`winPoly_coeff`, `winSym`). Machine-checked jest natomiast to, co się naprawdę liczy:
liniowość `hdd` w słowie (`higherDivDiff_add`, `higherDivDiff_smul`) i charakteryzacja jądra
(`isCloseOn_iff_forall_higherDivDiff`) — czyli że wiersze `hdd_j S ·` **są** bazą syndromów.

Pozostałe pozycje z listy pytania:

* **syndrome matrix** — tak, po ustawieniu `S = D` i `k` ustalonym; wtedy
  `M_D ∈ F^{2 × (|D|−k)}` to pełny syndrom pary względem RS(k) na całej domenie.
* **error-locator annihilator** — częściowo: locator pojawia się w projekcie osobno
  (`MinimalSupportHankelBridge.mem_badSetG_iff_det_syndromeMatrix_eq_zero`,
  `det_syndromeMatrix_eq` — determinant Hankela = iloczyn error-value polynomials × Vandermonde²),
  ale ten most jest udowodniony **przy hipotezie `(jointSupport).card = e + 1`**
  (minimal-support phase) i dla generatora wielomianowego, więc nie jest częścią warstwy A.
  Formalnego twierdzenia „`M_S` = obcięcie syndromu przez locator supportu `E`” **brak**.
* **row/column-equivalent matrix** — tak, i to jest najuczciwsze sformułowanie: klasa
  równoważności `M_S` względem `GL₂` (lewostronnie: reparametryzacja pencila,
  por. `divDiff_reparam`) i `GL_{c_S}` (prawostronnie: zmiana bazy dualu) jest jedynym
  niezmiennikiem, a `rank ≤ 1` to jedyny nietrywialny warunek na tej klasie.

Czego brakuje, by domknąć most syndromowy formalnie: (i) lematu `M_S = [f|_S] H_Sᵀ`
z jawnym `H_S`, (ii) lematu, że `hdd` na `S` jest obcięciem `hdd` na `D` przez locator `E`.
Oba są w zasięgu, żadnego z nich nie ma.

---

## 5. Czy z rank-one local windows wynika naturalny gluing?

Odpowiedź krótka: **nie ma ani jednego twierdzenia local-to-global** dla dwóch okien
w tych trzech plikach. Poniżej dokładnie, co jest, a czego nie ma, oraz co blokuje.

### 5.1 Relacja między `M_S` i `M_T`

Kanoniczna, ale **nieudowodniona** w projekcie: rozszerzanie przez zero.
Funkcjonał dualny o nośniku w `S` jest funkcjonałem dualnym o nośniku w `S ∪ T`, więc

```
dual(RS_k|_S) + dual(RS_k|_T)  ⊆  dual(RS_k|_{S∪T}),
```

a `M_S`, `M_T` są obcięciami jednego odwzorowania `Λ_{S∪T} : dual(RS_k|_{S∪T}) → F²`
do dwóch podprzestrzeni. Wspólny czynnik: **nie wspólne wiersze/kolumny, lecz wspólna
współrzędna rzutowa** — jądro. Jeśli oba okna świadczą o **tym samym** `γ`, to obie
podprzestrzenie leżą w `ker` tego samego funkcjonału `[1 : γ] ∈ P¹`, i wtedy
`rank Λ|_{dual(S)+dual(T)} ≤ 1`.

### 5.2 Wymiar: dlaczego `|S ∩ T| ≥ k` jest progiem

Dla kodu MDS (RS) wymiary są dokładne:

```
dim dual(RS_k|_S) = |S| − k,      dim (dual(S) ∩ dual(T)) = max(|S ∩ T| − k, 0),
dim (dual(S) + dual(T)) = |S| + |T| − 2k − max(|S ∩ T| − k, 0).
```

* Jeśli `|S ∩ T| ≥ k`: suma ma wymiar `|S ∪ T| − k`, czyli **rozpina cały dual na `S ∪ T`**.
  Wówczas rank-one na `S` i rank-one na `T` z tym samym `γ` daje rank-one na `S ∪ T`,
  tzn. `IsCloseOn k (S∪T) (lineComb f₀ f₁ γ)` — pełny gluing.
* Jeśli `|S ∩ T| < k`: przecięcie jest zerowe i suma ma wymiar `|S| + |T| − 2k < |S∪T| − k`.
  Ograniczenia **akumulują się** (kodimensja rośnie o `|T| − k` przy dołożeniu `T`),
  ale nigdy nie rozpinają dualu jednym krokiem. Wielorodzinowa akumulacja
  (`S₁, …, S_m` pokrywające `D` tak, że `∑(|S_i| − k) ≥ |D| − k` i sumy są w general position)
  jest jedyną drogą do globalnego wniosku i **żadne takie twierdzenie nie istnieje** w projekcie.

Co istnieje w projekcie jako namiastka: `ProximityGapLines.correlated_agreement_of_two`
— z dwóch *różnych* challenge'ów `z₁ ≠ z₂`, każdy `e`-close, dostaje się wspólne okno
rozmiaru `≥ |D| − 2e` dla obu słów. To jest gluing po **challenge'ach**, nie po supportach,
i traci połowę promienia (`e → 2e`). Nie jest oparty na `M_S`.

### 5.3 Werdykt dla ścieżki

```
local rank-one windows  →  accumulated rank  →  global rank-one / bounded list
        [udowodnione]         [BRAK]                    [BRAK]
```

Pierwsza strzałka wymaga lematu wymiarowego z §5.2 (nieformalizowany),
druga wymaga argumentu pokryciowego/Johnsonowskiego (nieformalizowany w tej warstwie).

---

## 6. Werdykt

### **B — UNIVERSAL LOCAL OBJECT, GLUING MISSING**

Obiekt rank-one (`M_S` = macierz wyższych ilorazów różnicowych okna) jest **uniwersalny**:
`isCloseOn_iff_forall_higherDivDiff`, `isBad_iff_higherDivDiff` i
`higherDivDiff_minor_eq_zero` obowiązują dla **arbitrary official MCA received words**,
przy **dowolnym gapie `c`**, bez jakiejkolwiek hipotezy o stopniu.
Warstwa Newton/symetryczna (`badSet_subset_image_newtonChallenge`, cały `GapOneUniversality`)
jest natomiast klasy C/D i **nie** jest kandydatem na backbone.
Brakuje wyłącznie twierdzenia local-to-global: nie ma ani lematu o rozpinaniu
`dual(S) + dual(T) = dual(S ∪ T)` przy `|S ∩ T| ≥ k`, ani akumulacji dla `|S ∩ T| < k`.

---

### 1. Strongest universal theorem

`Root.CodingTheory.isBad_iff_higherDivDiff` (z bezpośrednim wnioskiem
`higherDivDiff_minor_eq_zero`): dla **dowolnych** `f₀ f₁ : ↥D → F`, dowolnych `k, e`,
dowolnego gapu, badness `γ` jest równoważna istnieniu official okna `S` (`|D| ≤ |S| + e`),
którego macierz `2 × (|S|−k)` wyższych ilorazów różnicowych anihiluje `(1, γ)` przy
niezerowym drugim wierszu; w konsekwencji wszystkie minory `2×2` tej macierzy znikają.

### 2. Strongest degree-restricted theorem

`Root.CodingTheory.card_badSet_le_one_of_degree_lt`: jeśli oba received words są
wielomianowe stopnia `< w` przy `w + e ≤ |D|`, to `#badSet ≤ 1` — przy każdym rate,
z ostrym progiem (pencil `X^{k+1}, X^k` o stopniu `k+1` osiąga `C(|D|, k+1)`).
Tuż obok, jako najsilniejszy wynik ilościowy: `card_badSet_gapOne_eq_card_winSums`
(równość `#Bad` z liczbą dopuszczalnych sum `(k+1)`-podzbiorów domeny) wraz z
`card_badSet_gapOne_pencil_invariant`.

### 3. Exact obstruction to universality

Nie jest nią hipoteza polynomial/degree — obiekt lokalny jest już uniwersalny.
Przeszkodą jest **kwantyfikacja i sklejanie**:
(a) `higherDivDiff_minor_eq_zero` daje `∃ S`, a nie `∀ official S` (luka w ekspozycji,
matematycznie już zamknięta przez `isCloseOn_iff_forall_higherDivDiff`);
(b) brak lematu wymiarowego `dim(dual(S) + dual(T)) = |S ∪ T| − k` przy `|S ∩ T| ≥ k`,
bez którego rank-one na wielu oknach nie przenosi się na `S ∪ T`;
(c) hipotezy stopnia blokują wyłącznie warstwę Newtona (`natDegree ≤ k + c`
w `badSet_subset_image_newtonChallenge`) i całą teorię `c = 1`, tzn. to, co służy do
**liczenia** bad setu, a nie do jego **opisu**.

### 4. Exact missing bridge to Grand MCA

Brakuje łańcucha: *(official support `S`) ⟹ (`rank M_S ≤ 1` pointwise)* →
*(dwa supporty z `|S ∩ T| ≥ k` i wspólnym `γ` ⟹ rank-one na `S ∪ T`)* →
*(rodzina supportów o łącznej kodimensji `≥ |D| − k` ⟹ globalny correlated agreement lub
bounded list)*. Pierwsze ogniwo jest o dwa wiersze od gotowego; drugie i trzecie nie istnieją.
Dodatkowo brakuje mostu syndromowego w jawnej postaci `M_S = [f|_S] · H_Sᵀ`, który spiąłby
tę warstwę z już udowodnionym Hankel/locator bridge'em z minimal-support phase.

### 5. Shortest plausible theorem statement connecting this work to support-level theory

Dwa statementy, oba **nieudowodnione**, w istniejącej notacji projektu
(kolejność: najpierw uniwersalizacja pointwise, potem właściwy gluing):

```lean
/-- Pointwise rank-one law: dla zadanego official okna `S`. -/
theorem rankOne_window_iff_witness {k e : ℕ} {f₀ f₁ : ↥D → F} {S : Finset ↥D}
    (hS : D.card ≤ S.card + e) :
    ((∀ j j', k ≤ j → k ≤ j' →
        higherDivDiff j S f₀ * higherDivDiff j' S f₁
          - higherDivDiff j' S f₀ * higherDivDiff j S f₁ = 0)
      ∧ (∃ j, k ≤ j ∧ higherDivDiff j S f₁ ≠ 0))
    ↔ ∃ γ : F, IsCloseOn k S (lineComb f₀ f₁ γ) ∧ ¬ LineCloseOn k S f₀ f₁
```

```lean
/-- Gluing dwóch okien: próg `k ≤ |S ∩ T|`. -/
theorem isCloseOn_union_of_inter_card {k : ℕ} {f₀ f₁ : ↥D → F} {γ : F} {S T : Finset ↥D}
    (hk : k ≤ (S ∩ T).card)
    (hS : IsCloseOn k S (lineComb f₀ f₁ γ))
    (hT : IsCloseOn k T (lineComb f₀ f₁ γ)) :
    IsCloseOn k (S ∪ T) (lineComb f₀ f₁ γ)
```

Ten drugi jest minimalnym zdaniem, które zamienia „local rank-one windows” w
„accumulated rank”: iterowany po rodzinie official supportów daje globalne okno,
a razem z `isCloseOn_iff_forall_higherDivDiff` — globalny obiekt rangi jeden.
