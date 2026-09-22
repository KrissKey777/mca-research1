# Leanstral S16.69 — official circuit producer + D7 fallback

## Cel

Znajdź najmniejszy prawdziwy producer, który zasila istniejący konsument SAFE.
Masz dwa źródła pomocnicze z pełnymi plikami, ale nie integruj ich ślepo z
lokalnym drzewem. Każdy wynik oznacz `LOCAL_BANKED`, `PACKAGE_PRESENT_UNREPLAYED`,
`COMPUTATIONAL`, `KILLED` lub `SOURCE_GAP`.

## P0 — most IsMCA/OfficialWitnesses ↔ IsBad/badSet (najwyższy priorytet)

Zbuduj dokładny most między stroną Aristotle(new) a lokalną:

```text
Aristotle(new): IsMCA (import z ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges,
  rev Arklib e65197892 — NIE definicja lokalna POBIERZ1) / OfficialWitnesses
        ↔
lokalne: IsBad k e f₀ f₁ γ (MCA.lean: ∃ S, D.card ≤ S.card + e ∧ IsCloseOn k S (lineComb f₀ f₁ γ)
  ∧ ¬ LineCloseOn k S f₀ f₁) / badSet k e f₀ f₁
```

Most musi zachować: wspólny support `S`/`agree`, `¬LineCloseOn` ↔ `no_common`
(`∃ j, row j ∉ projectedCodeSubmod`), wybranego świadka (lokalny `p : F[X]`
z `IsCloseOn` ↔ `w ∈ C` z `Explained`), oraz wszystkie progi
(`D.card ≤ S.card + e`, `|S| ≥ n(1−δ)`, `a ∈ {1116048, 1118208}`, `Kz = 1048575`).

Kroki (po kolei, każdy z receiptem):

```text
P0.1 wyciągnij literalną definicję IsMCA z ArkLib rev e65197892
  (GrandChallenges) — nie zgaduj jej z użycia; status: EXTERNAL_SOURCE.
P0.2 wykaż albo sfalsyfikuj implikację w obie strony na wiernych małych
  modelach RS (GF(5/7/11/13), dual Gauss + minor):
  IsBad(k,e) ↔ IsMCA-przy-odpowiednim-δ.
P0.3 jeśli P0.2 przeżyje: sformułuj most jako jeden twierdzenie-adapter
  (tylko statements, zero sorry) i wskaż dokładnie brakujące przesłanki
  typów (wielomian F[X] vs LinearCode C, ↥D vs ι, ℕ vs ℝ).
P0.4 jeśli P0.2 padnie: zapisz najmniejszy kontrmodel z pełnymi guardami
  i natychmiast przejdź do P1-D (producent bezpośrednio dla lokalnego IsBad).
```

Bez zielonego P0 nie wolno przenosić `ResidualSystemOn`-konsumentów na lokalny
`badSet` ani przez rename, ani przez "oczywistą odpowiedniość".

## P1 — package-assisted official route

Przeczytaj literalne definicje w:

```text
Aristotle(new)1-22wrz/POBIERZ1/repo/ProximityPrize/Audit/
  OfficialResidualCircuit.lean
  PrizeRowResidualDescent.lean
  ResidualRankDescentMca.lean
  UltraStarDichotomy.lean
```

Nie kopiuj nazw z raportu. Wydobądź dokładne typy `OfficialWitnesses`,
`officialResidual`, `ResidualSystemOn`, coveru i `badSet`. Następnie rozstrzygnij:

```text
matching-like official family
  -> residual rank ≤ 9
  OR -> cover by at most 5 rank-9 residual systems
  OR -> circuit-cluster cover ≤ 280000000000
```

Preferowana kolejność: rank-9, potem pięć flatów, na końcu ogromny circuit-cluster
cap. Każda alternatywa musi mieć literalne `badSet ⊆ ⋃ G` i downstream theorem.

## P1-D — producent bezpośrednio dla lokalnego IsBad (fallback mostu)

Jeśli P0.4 (most fałszywy): sformułuj ten sam cover-producent dla lokalnego
`IsBad k e f₀ f₁ γ` / `badSet k e f₀ f₁`, bez odwołań do `IsMCA`/`LinearCode`:

```text
local_isbad_five_cover:
  badSet k e f₀ f₁ ⊆ ⋃ j : Fin 5, G j →
  (∀ j, ∃ S V_local, …) →
  (badSet k e f₀ f₁).card ≤ Bstar
```

gdzie `V_local` to lokalny odpowiednik residual space (wielomiany `F[X]`
z `IsCloseOn`, nie `Submodule F (ι → F)` z ArkLib). Najpierw falsyfikuj na
modelach GF(5/7/11/13) z dual Gauss + minor; jedno `sorry` wyłącznie na
najmniejszym producencie po zielonym downstream.

## Nisko wiszące owoce (zbieraj po drodze, tylko jeśli zasilają endpoint)

```text
L1. deployed threshold certs: 13017 / 55801 / 124778 / 14385 / 161136 / 226703
  jako czyste `norm_num [Nat.descFactorial]` certyfikaty — zero ryzyka, kotwiczą pricing.
L2. sharpness dolna: 13016 / 55800 / 124777 fail — ten sam koszt, domyka boundary table.
L3. McaBadCertificate.bad_subset jako wzorzec mostu certyfikat→badSet
  (POBIERZ1, PACKAGE_PRESENT_UNREPLAYED) — kształt dowodu do naśladowania w P0.3.
L4. rank9_cap replay: 51873822725733337 (non-sharp) vs 5178081604 (proza S16.69)
  — rozstrzygnij, który lemat daje mniejszą liczbę, zanim użyjesz jej w cenie.
L5. FarRow POBIERZ1 (`∀ c∈C, ∀ S, agree→card<k`) vs FarRow V47R
  (jointIdPos + m ≤ s) — jawna tabela różnic, nie rename; ta sama nazwa, inny typ.
L6. UltraBall mismatch 4627 vs 74384 jako twardy filtr: każdy pomysł używający
  UltraBall musi najpierw pokazać, skąd bierze brakujące ~70k pozycji.
```

## Statusy (obowiązkowe, rozszerzone o most)

```text
BRIDGE_PROVED      — most P0 udowodniony, obie implikacje z receiptami
BRIDGE_KILLED      — most fałszywy, kontrmodel z guardami, przejście do P1-D
BRIDGE_INCONCLUSIVE — modele nie rozstrzygają, nie promować
LOCAL_DIRECT_PRODUCER — P1-D sformułowany dla IsBad bez IsMCA
```

## P2 — lokalny D7

Tylko dla pełnej rangi 3 i `K ∈ [11207,124777]` sprawdź:

```text
active dependent bucket
 -> K−3 common zeros of bucketKer
 OR -> lower-rank CompressionSpectrum branch
 OR -> exact cross-bucket incidence priced by deployed_bucket_num_band
```

Nie zakładaj, że core należy do bucket kernel. Wskaż pierwszy literalny edge,
na którym zerowanie lub transport się kończy.

## Harness obowiązkowy

Przed Leanem uruchom `python analysis/s1669_dual_repo_pricer.py` i rozszerz go
bez losowości o:

1. exact pricing target/one-short dla rank 9, pięciu flatów, circuit clusters;
2. enumerację GF(5), GF(7), GF(11), GF(13) official supports;
3. dwa niezależne rank checks: modular Gaussian elimination i nonzero minors;
4. graph/clique-cover search z Z3 jako narzędziem odkrywczym;
5. SymPy tylko do exact determinant/resultant checks;
6. persistent killed-conjectures registry; każdy counterexample zapisuj z pełnymi
   guardami i niezależnym replayem;
7. one-short regression: wynik boundary-neutral nie jest dowodem;
8. source-presence/signature census i `#print axioms` receipts.

Nie promuj wyników bounded computation do theorem. Nie wracaj do zabitych dróg
pod zmienioną nazwą. Nie uruchamiaj szerokiego buildu.

## Kryterium sukcesu

```text
OFFICIAL_RANK9_PRODUCER_BANKED
OFFICIAL_FIVE_FLAT_PRODUCER_BANKED
OFFICIAL_CIRCUIT_COVER_BANKED
D7_PRODUCER_BANKED
FAITHFUL_COUNTEREXAMPLE
SOURCE_GAP
```

Raport ma zawierać: exact signature, source status, pricing, falsifier receipts,
first missing edge, targeted build, axiom audit, downstream endpoint composition
i jedną rekomendację dalszego kroku. Nie zgłaszaj SAFE bez producenta official.
