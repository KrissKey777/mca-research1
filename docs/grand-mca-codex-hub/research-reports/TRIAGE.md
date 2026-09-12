# Triage badawczy: co zyskujemy, co jest osiągalne, w co iść i czego nie ruszać

Dokument powstał jako **szybka analiza numeryczna** (Python + tanie sprawdzenia jądrem Lean),
zanim zainwestujemy czas w powolne dowody. Skrypty odtwarzające wszystkie liczby:

```bash
python3 analysis/triage_numerics.py     # struktura F_p*, t(n), jawne algorytmy bilinearne
python3 analysis/triage_costs.py        # modele kosztów przy n = 2^20, "darmowe twiddle"
```

**Status dowodowy.** Wszystko w sekcjach „numerycznie” to *obliczenia*, nie dowody: algorytmy
sprawdzono na losowych wektorach nad M31 (20 prób, arytmetyka dokładna), a nie udowodniono.
Jedyny **nowy wynik zweryfikowany maszynowo** w tej sesji to moduł
`RequestProject/CyclotomicCosets.lean` (liczby cyklotomicznych warstw, `decide +kernel`).
Nadal obowiązuje zasada z `DISCREPANCIES.md`: żadnych twierdzeń o wydajności bez benchmarku.

---

## 1. Co już mamy (bilans zysków)

Realny, sprawdzalny dorobek projektu to nie „szybszy FFT”, lecz **zweryfikowany łańcuch od
algebry do słowa maszynowego**:

| Warstwa | Stan |
| --- | --- |
| ciało M31, pierwszość, struktura `F_p^*`, brak pierwiastków `2^k` i `30` | udowodnione |
| DFT: odwracalność, wyznacznik, twierdzenie o splocie, `F[C_n] ≃ₐ Fⁿ`, `Rep F C_n ≌ Mod(Fⁿ)` | udowodnione |
| Cooley–Tukey, split-radix, PFA/Good–Thomas, Rader, bit-reversal | udowodnione z dokładnymi kosztami w jawnych modelach |
| circle FFT nad M31 (rozmiary `2^m`, `m ≤ 29`) — poprawność i koszt | udowodnione |
| jądra `UInt32`/`UInt64`, niezmiennik quasi-kanoniczny, leniwa redukcja, brak przepełnienia | udowodnione |
| model bilinearny: dolne ograniczenia, dokładne złożoności (`n`, `m+n+1`, Karatsuba) | udowodnione |
| kontrakty Verus | **niesprawdzone** (brak toolchainu Rust/Verus w tym środowisku) |
| benchmarki | **nie wykonano żadnych** |

Zysk, który da się dziś uczciwie sprzedać: *poprawnościowy*. Jądro arytmetyki M31 i circle FFT
mają dowody aż do poziomu operacji na `u32`/`u64` z kontrolą przepełnienia — to jest rzecz,
której implementacje SOTA nie mają.

---

## 2. Twarde liczby z tej analizy

### 2.1 Struktura (przesądza, co w ogóle jest możliwe)

`p − 1 = 2 · 3² · 7 · 11 · 31 · 151 · 331`.

* jedyne potęgi dwójki dzielące `p − 1` to `1, 2` → **żadnego radix-2 NTT w ciele bazowym**;
* największa gładka długość transformaty w ciele bazowym: `42966 = 2·3²·7·11·31`;
* dla `n = 2^20` pozostają dokładnie dwie drogi: **grupa okręgu** (rząd `2^31`, w ciele bazowym)
  albo **`F_{p²}`**. Obie już są w projekcie opisane; circle FFT jest udowodniony.

### 2.2 Liczba nierozkładalnych czynników `xⁿ − 1` nad M31 i granica Winograda `2n − t(n)`

| n | t(n) | 2n − t(n) | stopnie czynników |
| --- | --- | --- | --- |
| 2 | 2 | 2 | 1,1 |
| 3 | 3 | 3 | 1×3 |
| 5 | 2 | **8** | 1, 4 |
| 6 | 6 | 6 | 1×6 |
| 30 | 12 | **48** | 1×6, 4×6 |
| 31 | 31 | 31 | 1×31 |

`t(5) = 2`, `t(6) = 6`, `t(30) = 12`, `t(31) = 31` są teraz **sprawdzone jądrem Lean**
(`FFT.Cosets.cosetCount_five/six/thirty/thirtyone`), podobnie jak konsekwencja
`2·30 − t(30) = 48` (`FFT.Cosets.winograd_target_thirty`).

### 2.3 Jawny algorytm długości 30 na **48** mnożeń (numerycznie zweryfikowany)

Zbudowany i sprawdzony na losowych danych nad M31:

* długość 6: 6 iloczynów (DFT — M31 ma pierwotny pierwiastek 6. stopnia),
* długość 5: **8 iloczynów** (CRT `x⁵−1 = (x−1)Φ₅`, `Φ₅` nierozkładalny + Toom w 7 punktach),
* tensor Agarwala–Cooleya `6 ⊗ 5`: **48 iloczynów**, poprawność potwierdzona numerycznie.

To domyka lukę O5/P25f: dotąd w Lean było `30 ≤ c ≤ 54`. Numerycznie mamy `c ≤ 48`,
a granica Winograda daje `c ≥ 48`. **Spodziewana wartość dokładna: `c = 48`.**

### 2.4 Ile realnie leży na stole przy `n = 2^20` (model kosztów z `SplitRadix.lean`)

| wariant | mnożenia bazowe | pamięć |
| --- | --- | --- |
| radix-2, ciało bazowe/okrąg | 8 912 898 | 1× |
| split-radix, ciało bazowe/okrąg | 6 058 440 (−32 %) | 1× |
| radix-2 nad `F_{p²}` (Karatsuba 3×) | 26 738 694 | 2× |
| split-radix nad `F_{p²}` | 18 175 320 | 2× |

Wniosek: **wybór „ciało bazowe (okrąg) vs rozszerzenie” to czynnik ~3× w mnożeniach i 2× w ruchu
pamięci; split-radix to dodatkowe ~32 %**. Kolejność priorytetów inżynierskich wynika z tych liczb.

### 2.5 „Darmowe rotacje” Mersenne'a przy rozmiarach `2^m` — praktycznie nie istnieją

`⟨2⟩ ⊂ F_p^*` ma **31** elementów. Zliczenie twiddle'i circle FFT leżących w `⟨2⟩`:

| m | twiddle'e | z nich w `⟨2⟩` |
| --- | --- | --- |
| 8 | 256 | 3 |
| 12 | 4096 | 3 |
| 16 | 65536 | 3 |
| 18 | 262144 | 3 |

Górna granica to i tak 31 z ~10⁶. **Kluczowa hipoteza z pierwotnego zlecenia („ukryte symetrie
Mersenne'a zastąpią mnożenia”) jest przy rozmiarach `2^k` obalona ilościowo**: mechanizm działa
wyłącznie dla długości dzielących `ord(2) = 31` (stąd bezmnożeniowe jądro długości 31, P18),
i nie skaluje się.

### 2.6 Rader długości 31: matematycznie ciekawy, inżyniersko martwy

| wariant | mnożenia ogólne | dodawania | mnożenia przez stałe |
| --- | --- | --- | --- |
| jądro bezpośrednie (P9) | **0** | ~930 | 0 (930 rotacji) |
| Rader + tensor 6⊗5 | 48 | ~990 (szacunek strukturalny) | ~770 |

Nad M31 wersja bezpośrednia jest tańsza w każdej kolumnie poza „mnożeniami ogólnymi”, których
i tak nie ma. Zatem: **wynik `c(30) = 48` warto udowodnić jako matematykę (dokładna złożoność
multiplikatywna), ale nie jako ścieżkę do szybszego kodu.**

---

## 3. Scenariusze

### 3.1 Scenariusz realistyczny (wysokie prawdopodobieństwo, znany koszt)

1. **`c(30) = 48` w modelu bilinearnym** — górna granica: sformalizować algorytm długości 5 na
   8 iloczynów (CRT + Toom, cała maszyneria jest już w `PolyMul.lean` i `AgarwalCooley.lean`)
   i wpiąć w istniejące `tensor_computes`. Dolna: twierdzenie Fiduccii–Zalcsteina/Winograda
   „złożoność bilinearna `F[x]/f` wynosi `2n − t`”, którego nie ma w Mathlib.
2. **Split-radix na grupie okręgu** — przeniesienie P20b z NTT na circle FFT; ~32 % mnożeń
   w modelu, przy zerowym ryzyku matematycznym.
3. **Iteracyjny FFT in-place z niezmiennikami pętli (O8)** — jedyny brakujący element między
   udowodnioną matematyką a kodem, który realnie się uruchamia. Największa wartość dla Verusa.
4. **Domknięcie kontraktów Verus** — u użytkownika, bo tu nie ma toolchainu.

Wynik realistyczny: **zweryfikowana biblioteka circle-FFT nad M31 z dowodami aż do `u32`,
z kosztem w modelu równym split-radix, i z dwoma dokładnymi wynikami o złożoności
multiplikatywnej** (`c(n) = n` przy istniejącym pierwiastku, `c(30) = 48`). Bez obietnic
o pobiciu SOTA — z jasno opisanym protokołem benchmarku do wykonania.

### 3.2 Scenariusz optymistyczny (możliwy, ale z ryzykiem)

1. **Formalizacja pełnego twierdzenia Winograda `2n − t(n)`** dla dowolnej algebry `F[x]/f`
   — realny wkład do Mathlib i natychmiast domyka całą rodzinę pytań O2/O5/O6b.
2. **Dolne ograniczenie w modelu prostoliniowym (nie tylko bilinearnym)** dla długości 3–6,
   czyli „prawdziwa” optymalność, a nie optymalność w modelu bilinearnym.
3. **Optymalność Karatsuby (O6b, `3 ≤ mulCount`)** — brakuje normalizacji „co najwyżej dwa
   mnożenia ogólne”; wykonalne, ale to kilka dni dowodów.
4. **Charakteryzacja darmowych twiddle'i circle FFT (O12)** — teraz wiemy (numerycznie), że
   odpowiedź brzmi „3”, więc formalizacja to *wynik negatywny*: tani i uczciwy.

### 3.3 Czego nie osiągniemy

* **Złożoności poniżej `O(n log n)`** dla DFT/splotu nad M31 — nic w tych danych na to nie
  wskazuje; hipoteza z pierwotnego zlecenia pozostaje bez poszlak.
* **Dolnego ograniczenia `Ω(n log n)`** (O1) — problem otwarty w literaturze.
* **Realnego przyspieszenia z K-teorii/topologii** — patrz niżej.

---

## 4. Tabela decyzyjna: GO / NO-GO

| kierunek | wartość | koszt w Lean | werdykt |
| --- | --- | --- | --- |
| `c(30) = 48`: algorytm 8-mnożeniowy dla `n=5` + tensor | wysoka (domyka O5) | średni | **GO — pierwszy** |
| Twierdzenie Winograda `2n − t(n)` (dolna granica) | bardzo wysoka | wysoki | **GO — drugi**, z kryterium przerwania |
| Split-radix na grupie okręgu | wysoka (inżyniersko) | niski/średni | **GO** |
| Iteracyjny in-place + niezmienniki (O8) | najwyższa dla Verusa | średni | **GO** |
| O12: darmowe twiddle'e circle FFT | średnia (wynik negatywny) | niski | **GO (tanie)** |
| Radix-4/8 (O3) | niska: te same mnożenia, zysk w pamięci | średni | ODŁÓŻ |
| Bluestein / truncated FFT (O4) | niska przy `n = 2^k` | średni | ODŁÓŻ |
| NTT nad `F_{p²}` i porównanie (O6) | niska: liczby 2.4 przesądzają na korzyść okręgu | średni | ODŁÓŻ |
| Rader-31 jako ścieżka implementacyjna | **ujemna** (2.6) | — | **NO-GO** |
| „Ukryte symetrie Mersenne'a” przy `2^k` | **obalona ilościowo** (2.5) | — | **NO-GO** |
| K-teoria poza opisem wyznacznikowym, BZ/n, wiązki, operady, snopy (O11) | brak treści obliczeniowej: żadna z tych struktur nie wchodzi do licznika operacji | wysoki | **NO-GO** |
| `Ω(n log n)` (O1) | otwarte w literaturze | nieograniczony | **NO-GO** |
| Hipoteza sub-`log` dla specjalnych rozkładów | brak jakichkolwiek poszlak numerycznych | nieograniczony | **NO-GO** |

**Kryteria przerwania.** (a) Dla twierdzenia Winograda: jeśli w ciągu jednej sesji nie uda się
zredukować dowodu do „algebra przemienna wymiaru `n` z `t` ideałami maksymalnymi wymaga `2n − t`
iloczynów”, zostawiamy `c(30) ≤ 48` (górna granica) i zamykamy pytanie jako częściowe.
(b) Dla każdego kierunku „inżynierskiego”: jeśli zysk w modelu jest `< 5 %`, nie formalizujemy.

---

## 5. Dlaczego wątek topologiczny/K-teoretyczny odrzucamy

Nie dlatego, że jest fałszywy, tylko dlatego, że **nie dotyka wielkości, którą optymalizujemy**.
Konkretnie: `K₀(F_p) ≅ ℤ`, `K₁(F_p) ≅ F_p^*`, a klasa wyznacznika DFT w `K₁` jest już w projekcie
(P6). Przejście od tej klasy do liczby mnożeń wymagałoby niezmiennika, który ogranicza długość
programu — a wszystkie znane takie niezmienniki (rząd tensora, wymiar algebry, liczba ideałów
maksymalnych) są *algebraiczne* i już je w projekcie mamy w modelu bilinearnym. `BZ/n`, wiązki
i snopy nie dostarczają w tym miejscu nowego ograniczenia; dopóki ktoś nie wskaże konkretnego
funktora `algorytm ↦ niezmiennik topologiczny` monotonicznego względem długości programu,
inwestycja ma zerową oczekiwaną stopę zwrotu. To jest formalne uzasadnienie „NO-GO”, a nie
opinia o wartości teorii.

---

## 6. Rekomendowana kolejność prac (następna sesja)

1. `n = 5` w 8 iloczynach (Lean, model bilinearny) → `c(30) ≤ 48`, zastępuje 54.
2. Winograd `2n − t(n)` dla `F[x]/f` → `c(30) = 48`; przy niepowodzeniu punkt 1 i tak stoi.
3. Split-radix na okręgu + koszt.
4. Iteracyjny in-place z niezmiennikami; potem transliteracja do Verusa i **uruchomienie
   `verus` po stronie użytkownika** (tu nie ma toolchainu).
5. Benchmark według protokołu z `DISCREPANCIES.md` §7 — dopiero on pozwoli cokolwiek powiedzieć
   o SOTA.
