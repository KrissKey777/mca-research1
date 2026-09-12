# Badania przed-dowodowe: trzy ścieżki i wybór jednej

Dokument z sesji poświęconej *taniej* fazie badawczej: przegląd literatury (arXiv,
Semantic Scholar), eksperymenty numeryczne i symboliczne w Pythonie oraz weryfikacje
meta-dowodowe — wszystko **zanim** wydano choć jedną minutę na dowód w Lean.

Skrypty odtwarzające liczby:

```bash
python3 analysis/tensor_rank.py   # dokładne rangi tensorowe małych algebr nad F_2, F_3, F_5
python3 analysis/fz_meta.py       # dokładne tożsamości tensorowe + symulacja dowodu + próby falsyfikacji
```

---

## 0. Metoda

Kolejność działań w tej sesji była z góry ustalona i jest zgodna z zaleceniem
„najpierw tanio, potem Lean”:

1. **Sprawdzenie stanu wiedzy** — czy problem jest już rozwiązany (matematycznie) i czy
   jest już sformalizowany (maszynowo). Bazy: arXiv API, Semantic Scholar API, wyszukiwanie
   w źródłach Mathlib.
2. **Eksperyment rozstrzygający** — dla każdej kandydującej ścieżki policzyć coś, co albo
   ją obali, albo pokaże, że cel jest osiągalny (dokładne rangi tensorowe, dokładne
   tożsamości algorytmów).
3. **Symulacja dowodu** („meta-dowód”) — wykonać *numerycznie* wszystkie kroki dowodu,
   który zamierzamy pisać w Lean, na losowych instancjach. Jeśli w rozumowaniu jest luka,
   ujawnia się w sekundach, a nie po godzinach formalizacji.
4. **Próba falsyfikacji** — aktywne szukanie kontrprzykładu do tezy (algorytmu krótszego
   niż przewidywane optimum).
5. Dopiero potem Lean.

---

## 1. Stan wiedzy (weryfikacja w bazach)

| pytanie | status w literaturze | źródło sprawdzenia |
| --- | --- | --- |
| dolne ograniczenie `R(A) ≥ 2·dim A − t(A)` dla algebr | **rozwiązane**: Winograd (1977) dla przemiennych, Alder–Strassen (1981) ogólnie | klasyka; potwierdzone przez prace pochodne (Bläser 2000, 2005) indeksowane w S2 |
| dokładna złożoność biliniowa `F[x]/f` dla dużego `F` | **rozwiązane** (`2n − t`) | jw. |
| rangi tensorowe nad **małymi** ciałami (np. `F_2`) | częściowo otwarte; aktywny nurt automatycznych dolnych ograniczeń (arXiv 2603.07280, 2026) | arXiv |
| `Ω(n log n)` dla FFT w modelu obwodów liniowych | **otwarte od ~40 lat**; są tylko wyniki w modelach ograniczonych (Morgenstern, Ailon 2013/2014) | arXiv 1305.4745, 1403.1307 |
| hipoteza addytywności rangi (Strassen) | obalona dla ogólnych tensorów (Shitov), wciąż badana dla algebr (arXiv 2025) | arXiv |
| **formalizacja** (Lean/Coq/Isabelle) jakiegokolwiek nietrywialnego dolnego ograniczenia złożoności biliniowej | **brak** — brak trafień w arXiv, brak `tensor rank`/`bilinear complexity`/`Alder` w Mathlib | arXiv + `rg` po źródłach Mathlib |

Wniosek metodologiczny: w tej dziedzinie *matematyka* jest w dużej mierze zrobiona, a
**puste miejsce jest w weryfikacji maszynowej**. To jest realny, sprawdzalny wkład: nie
„nowe twierdzenie, którego nikt nie zna”, lecz „pierwszy maszynowo zweryfikowany dowód
klasy twierdzeń, na których opiera się cała inżynieria FFT/NTT”.

---

## 2. Eksperymenty rozstrzygające

### 2.1 Dokładne rangi tensorowe małych algebr (`analysis/tensor_rank.py`)

Ranga liczona **wyczerpująco** (przestrzeń plastrów zawarta w powłoce `r` macierzy rangi 1):

| algebra | dim `n` | `q` | `t` | `2n − t` | ranga dokładna `R` |
| --- | --- | --- | --- | --- | --- |
| `F_4 = F_2[x]/(x²+x+1)` | 2 | 2 | 1 | 3 | **3** |
| `F_8 = F_2[x]/(x³+x+1)` | 3 | 2 | 1 | 5 | **6** |
| `F_9 = F_3[x]/(x²+1)` | 2 | 3 | 1 | 3 | **3** |
| `F_2[x]/(x²−1)` (lokalna) | 2 | 2 | 1 | 3 | **3** |
| `F_2[x]/(x³−1)` | 3 | 2 | 2 | 4 | **4** |
| `F_3[x]/(x²−1)` | 2 | 3 | 2 | 2 | **2** |
| `F_5[x]/(x²−1)` | 2 | 5 | 2 | 2 | **2** |

Dwa wnioski, oba istotne dla sformułowania twierdzenia:

* ograniczenie `2n − t` jest respektowane **we wszystkich** przypadkach (żadnego kontrprzykładu),
* `F_8/F_2` daje `R = 6 > 5`: przy **małym** ciele bazowym ograniczenie nie jest osiągalne.
  Dlatego twierdzenie o *dokładnej* wartości musi zawierać założenie o liczbie elementów
  ciała (`|F| ≥ 2d − 1` punktów interpolacji) — i tak zostało sformułowane w Lean.

### 2.2 Dokładne tożsamości tensorowe algorytmów górnych (`analysis/fz_meta.py`)

Nie losowe próbki, lecz porównanie **pełnych tensorów** (co jest kompletnym dowodem
poprawności konkretnego algorytmu, bo arytmetyka `F_p` jest dokładna):

| algorytm | liczba iloczynów | tożsamość dokładna |
| --- | --- | --- |
| Toom w `F_p[x]/Φ₅` (stopień 4) | 7 = `2·4−1` | ✔ |
| Toom w `F_p[x]/(x²+1)` | 3 = `2·2−1` | ✔ |
| splot cykliczny długości 5 (CRT + Toom) | 8 | ✔ |
| splot cykliczny długości 6 (DFT) | 6 | ✔ |
| splot cykliczny długości 30 (Agarwal–Cooley 6⊗5) | **48** | ✔ |

To podnosi wynik `c(30) ≤ 48` z poprzedniej sesji ze statusu „sprawdzone na 20 losowych
wektorach” do statusu „sprawdzone jako tożsamość wielomianowa”.

### 2.3 Symulacja dowodu Fiducciego–Zalcsteina

Zamierzony dowód (patrz §4) wykonano numerycznie na 200 losowych algorytmach biliniowych:
wybór `m−1` iloczynów, rozwiązanie `l_i(u) = 0`, sprawdzenie, że obraz `v ↦ T(u,v)` leży
w powłoce pozostałych kolumn, oraz że dla algebry bez dzielników zera ten obraz ma pełny
wymiar. **Zero naruszeń.** Dowód jest więc „przetestowany” zanim powstał.

### 2.4 Próby falsyfikacji

Poszukiwanie (ALS + losowe restarty nad `M31`) algorytmów o 2 iloczynach dla `F_{p²}`
i 6 iloczynach dla `F_p[x]/Φ₅`: **nic nie znaleziono**. (Uczciwie: ALS nad ciałem
skończonym jest słaby — nie znalazł też optimum, więc jest to słaba przesłanka; mocne
przesłanki to §2.1 i dowód z §4.)

---

## 3. Trzy ścieżki i decyzja

### Ścieżka A (WYBRANA) — maszynowo zweryfikowana teoria dolnych ograniczeń złożoności biliniowej

**Teza.** Sformalizować w Lean twierdzenie Fiducciego–Zalcsteina (`R ≥ dim U + dim V − 1`
dla odwzorowań biliniowych bez dzielników zera), a na jego bazie *dokładną* złożoność
biliniową skończonych rozszerzeń ciał: `R(K/F) = 2d − 1`, w tym instancje istotne dla
M31: `R(F_{p²}) = 3` i `R(F_{p⁴}) = 7`.

* **Nowość:** matematyka klasyczna, ale **weryfikacja maszynowa — pierwsza** (§1).
* **Ryzyko:** niskie; dowód jest krótki, elementarny i przetestowany numerycznie (§2.3).
* **Wartość dla projektu:** `F_{p²}` i `F_{p⁴}` to dokładnie te rozszerzenia, w których
  liczy się arytmetyka rozszerzona w implementacjach nad M31; twierdzenie mówi, że
  3 mnożenia (odpowiednio 7) **nie da się poprawić** — to formalny dowód optymalności
  używanego dziś jądra, a nie heurystyka.
* **Rozszerzenie (stretch):** wersja Alder–Strassen `2n − t` dla algebr przemiennych →
  `c(5) = 8` i `c(30) = 48` (górne granice już zweryfikowane dokładnie w §2.2).

### Ścieżka B — automatyczne dolne ograniczenia nad małymi ciałami z certyfikatem sprawdzanym w Lean

Wyczerpujące/SAT-owe wyznaczanie dokładnych rang tensorowych nad `F_2`, `F_3` i eksport
certyfikatu, który jądro Lean przelicza (`decide`). Daje *nowe* liczby (nad małymi ciałami
wiele wartości jest nieznanych), ale: (i) w marcu 2026 pojawiła się praca automatyzująca
dokładnie ten schemat (arXiv 2603.07280), (ii) rozmiary osiągalne wyczerpująco są małe
(`n ≤ 3–4`), (iii) wartość dla podstaw matematycznych — mała. **Odłożone.**

### Ścieżka C — `Ω(n log n)` dla FFT w modelu obwodów liniowych

Największa nagroda, ale problem jest **otwarty od ok. 40 lat** i wszystkie znane wyniki
wymagają dodatkowych ograniczeń modelu (ograniczone współczynniki — Morgenstern;
dobre uwarunkowanie — Ailon). Brak jakiejkolwiek poszlaki numerycznej w danych tego
projektu. **NO-GO** (podtrzymanie decyzji z `TRIAGE.md`).

---

## 4. Dowód, który idzie do Lean (spisany zanim zaczęto formalizację)

**Twierdzenie (Fiduccia–Zalcstein).** Niech `φ : U × V → W` będzie odwzorowaniem
biliniowym nad ciałem `F`, `dim U = m`, `dim V = n ≥ 1`, takim że dla każdego `u ≠ 0`
odwzorowanie `v ↦ φ(u,v)` jest injektywne. Wtedy każdy algorytm biliniowy dla `φ`
wykonuje co najmniej `m + n − 1` mnożeń.

*Dowód.* Niech algorytm ma `k` iloczynów o lewych formach `l_1,…,l_k`, prawych `r_i`
i wektorach wyjściowych `w_i ∈ W`. Wybierzmy zbiór `S` indeksów o mocy `min(k, m−1)`.
Odwzorowanie `u ↦ (l_i(u))_{i∈S}` idzie z przestrzeni wymiaru `m` w przestrzeń wymiaru
`< m`, więc ma nietrywialne jądro: istnieje `u ≠ 0` z `l_i(u) = 0` dla `i ∈ S`. Wtedy
dla każdego `v`: `φ(u,v) = Σ_{i∉S} l_i(u) r_i(v) · w_i`, czyli obraz injektywnego
odwzorowania `v ↦ φ(u,v)` (wymiaru `n`) leży w powłoce `k − |S|` wektorów. Stąd
`n ≤ k − |S|`. Jeśli `k ≤ m−1`, to `|S| = k` i `n ≤ 0` — sprzeczność. W przeciwnym razie
`|S| = m−1`, czyli `k ≥ m + n − 1`. ∎

**Wniosek.** Dla skończonego rozszerzenia ciał `K/F` stopnia `d`: `R ≥ 2d − 1`.
Górna granica `2d − 1` to interpolacja Lagrange'a w `2d − 1` punktach (wymaga
`|F| ≥ 2d − 1`, co pokazuje przykład `F_8/F_2` z §2.1). Razem: `R(K/F) = 2d − 1`.

Ten dowód został przed formalizacją: (a) spisany, (b) zasymulowany numerycznie (§2.3),
(c) skonfrontowany z dokładnymi rangami z §2.1 (`F_4`, `F_9`: `R = 3 = 2·2−1`).

Realizacja w Lean: `RequestProject/AlgebraRank.lean`.

---

## 5. Co z tego wyszło w Lean (ta sama sesja)

Po fazie taniej weryfikacji ścieżka A została zrealizowana. Nowe moduły, oba budujące się
czysto, bez `sorry` i bez dodanych aksjomatów (audyt `#print axioms` w
`RequestProject/Main.lean`):

**`RequestProject/AlgebraRank.lean`**

* `FFT.Bilinear.GenAlg` — bezwspółrzędny model algorytmu biliniowego;
* `FFT.Bilinear.GenAlg.fiducciaZalcstein` — dolne ograniczenie `dim U + dim V − 1`;
* `FFT.Bilinear.domain_bilinear_lower_bound` — `≥ 2d − 1` dla algebry bez dzielników zera;
* `FFT.Bilinear.powerBasisAlg` + `..._computes` — algorytm ewaluacyjno-interpolacyjny
  osiągający `2d − 1`;
* `FFT.Bilinear.ext_bilinear_complexity` — **dokładna wartość `2d − 1`**;
* `FFT.Bilinear.M31sq_bilinear_complexity` — **`𝔽_{p²}` nad `M31`: dokładnie 3**
  (jądro „zespolone”/Karatsuby jest optymalne — dwóch mnożeń nie da się osiągnąć);
* `FFT.Bilinear.M31quartic_bilinear_complexity` — **`𝔽_{p⁴}` nad `M31`: dokładnie 7**.

**`RequestProject/Conv5.lean`**

* `FFT.Bilinear.ConvAlg.computes_of_tensor` — poprawność algorytmu splotowego sprowadzona
  do skończonej tożsamości tensorowej (a więc do rachunku jądra);
* `FFT.Bilinear.exists_conv5_M31_eight` — **długość 5 w 8 iloczynach** (cel Winograda);
* `FFT.Bilinear.cyclicConv30_M31_48` — **długość 30 w 48 iloczynach** (poprzednio 54),
  przy dolnym ograniczeniu 30.

Kolejność „tanio → drogo” sprawdziła się liczbowo: eksperyment z §2.1 wymusił dodanie
założenia o liczności ciała w twierdzeniu o dokładnej wartości (bez niego twierdzenie
byłoby fałszywe — `𝔽_8/𝔽_2`), a algorytm długości 5 trafił do Lean dopiero po
potwierdzeniu go jako dokładnej tożsamości tensorowej.

**Co pozostaje otwarte po tej sesji.** Dolne ograniczenie Aldera–Strassena
`R(A) ≥ 2 dim A − t(A)` dla algebr przemiennych z `t` ideałami maksymalnymi — jedyny
brakujący element, by `c(30) = 48` i `c(5) = 8` stały się wartościami dokładnymi, a nie
tylko górnymi granicami. Sformalizowany jest przypadek `t = 1` (rozszerzenia ciał).
Analiza w §4 pokazuje, że argument FZ w naiwnym uogólnieniu daje dla `t = 2` tylko
`2n − 3`, więc potrzebna jest pełna metoda podstawień Aldera–Strassena — to zadanie na
osobną sesję, o wyraźnie większym koszcie.
