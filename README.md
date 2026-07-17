# Couret-Unification

**Formalisation Lean 4 d'un noyau spectral fini modulo 30 — théorie des caractères, lemme du défaut ponctuel et classification
spectrale complète des triplets de `G₃₀ = (ℤ/30ℤ)×` — avec encodage structurel des couches analytiques supérieures (programme
Hilbert-Pólya autour de l'Hypothèse de Riemann).**

*Dédié à la mémoire de Bernard Couret (1928–1999).*

---

## ⚠️ RHClaimed = false

Ce projet **ne prétend pas prouver** l'Hypothèse de Riemann. Il formalise en Lean 4 un
**noyau fini exact** autour de la structure modulo 30, l'**arithmétique fondamentale**
(Möbius, Mertens, second moment), et encode les couches analytiques supérieures comme un
**éventail de composition** structurellement disjoint. Le dépôt prouve exactement ce qu'il
dit, et ne dit rien de plus.

---

## État du dépôt (v38.5.14)

| Métrique | Valeur |
|----------|--------|
| Toolchain | Lean 4.29.1 · Mathlib 4.29.1 |
| Branche | `main` |
| Compilation `Frozen` | `lake build` ✓ — **3569 jobs, 0 sorry, 0 warn** |
| Compilation `All` | `lake build` ✓ — **3754 jobs**, 11 sorry documentés |
| Sorries doctrinaux | **11** (documentés, dans les couches Active) |
| Fichiers `.lean` (source) | `find lean -name '*.lean' \| wc -l` |
| RHClaimed | `false` |

> Le compte de fichiers est laissé sous forme de commande : il se relit à l'instant `t`
> plutôt que de figer un nombre qui périme. Le sol, c'est le build, pas une métrique
> recopiée.

### Sorries doctrinaux — les 11, honnêtement

`make audit-scripts` déclare 11 `sorry`, sur 6 fichiers, tous explicitement posés dans les
couches **Active** (routes en travaux), **hors de la couche `Frozen`** :

| Fichier:ligne | Couche |
|---|---|
| `Logic/H3/Lemma7Residual.lean:13` | **verrou central F3** — annulation du résidu sur la ligne critique |
| `Logic/H3/RouteC.lean:780` | chaîne de raffinement `Σ\|E_d\|` |
| `Logic/L10NoGoTheorem.lean:69, :239, :245` | no-go L10 (×3) |
| `Logic/L6RatioEstimateDerived.lean:90` | estimation de ratio L6 |
| `Analytic/GammaFactor.lean:62, :83, :95, :112` | facteur Γ (×4) |
| `AnalyticHorizon/Det2Transport.lean:71` | transport det₂ |

**`Lemma7Residual.lean:13` est le verrou *(genuine)* mathématique central du passage global** du programme — celui
qui relie le socle fini à l'horizon analytique (équivalence `det₂ ↔ ξ`, branche β.2 de `PhaseBComposition`).
Les 9 autres sorry sont des obligations locales ou analytiques documentées dans les couches actives sur des routes en
cours, dans les couches `Logic` / `Analytic` / `AnalyticHorizon`. **Aucun `sorry` n'existe
dans `Frozen`.**

---

## Couche v38.5.3 — Core : défaut ponctuel & classification de `G₃₀`

Quatre fichiers intégrés et vérifiés fix par fix lors du sprint v38.5.3 (tags `v38.5.3-1`
à `v38.5.3-4`), **0 sorry** :

| Fichier | Contenu | Certification | Portée |
|---|---|---|---|
| `Core/CharacterSubgroupSums.lean` | sommes de caractères sur le noyau d'un caractère d'ordre 2 | **noyau pur** (sans axiome ajouté) | groupe abélien fini |
| `Core/PointDefectLemma.lean` | lemme du défaut ponctuel : dominante `(\|ker χ\|−1)²`, secondaires `=1` | **noyau pur** | groupe abélien fini |
| `Core/G30Classification.lean` | dichotomie Q/C des 56 triplets, caractérisations positives | `native_decide` (`Lean.ofReduceBool`) | `G₃₀` |
| `Core/G30ClassificationFromPointDefect.lean` | pont énumératif ↔ abstrait sur `G₃₀` | `native_decide` | `G₃₀` |

**Résultat fini complet.** Les 56 triplets de `G₃₀` se répartissent en **24 de type Q**
(spectre `(9,1⁶)`, contenus dans une fibre quadratique) et **32 de type C** (spectre
`(5,5,1⁵)`, quasi-alignés sur un caractère d'ordre 4, `5 = |2+i|²`), sans autre profil.
Énergie non triviale totale constante `= 15` (Parseval) ; exactement 2 triplets fixes sous
`Aut(G₃₀)`. La dichotomie est symétrique : ordre 2 → 9 par alignement, ordre 4 → 5 par
divergence orthogonale.

Deux régimes de certification, **distingués explicitement** : *noyau pur* (preuve dans le
noyau Lean, aucun axiome ajouté) pour les deux fichiers abstraits ; *computationnel*
(`native_decide`, donc `Lean.ofReduceBool` dans la base d'axiomes) pour les deux fichiers
sur `G₃₀`. Les deux sont `[D]` ; ils ne sont pas du même grain, et le code le dit.

---

## Architecture

```
lean/CouretUnification/
├── Core/                  ← noyau fini exact + arithmétique fondamentale
│                            (groupe, spectre, classification, certificats Couret,
│                             Möbius, Mertens, κ(q)) + couche v38.5.3 :
│                            CharacterSubgroupSums, PointDefectLemma,
│                            G30Classification, G30ClassificationFromPointDefect
├── Finite/                ← projecteurs et défauts dérivés du noyau
├── FiniteDefect/          ← théorèmes T1–T7 (pythagoréité, kurtosis)
├── Spectral/              ← analyse fine du gap spectral
├── Logic/                 ← C3Weak, L10NoGoTheorem, EulerBridgeInfinite, …
│   └── H3/                ← pont H3 conditionnel
│       ├── PhaseBComposition.lean   ← éventail à 5 branches (α, β, γ, δ, η)
│       ├── Lemma7Residual.lean      ← verrou central F3
│       ├── RouteC.lean              ← borne raffinée Σ|E_d|
│       └── (autres)
├── Analytic/              ← Abel pondéré, GammaFactor, intervalles vérifiés
├── AnalyticHorizon/       ← Det2Transport (horizon global)
├── FunctionalFoundation/  ← chemins discrets, connexion
└── Meta/                  ← SnapshotSentinel (sentinelle de signatures)
```

Points d'entrée : `CouretUnification.lean` (façade canonique stratifiée),
`Active.lean`, `Frozen.lean`, `ResGold.lean`, `SophieGermainUmbrella.lean`, `All.lean`
(agrégation exhaustive).

L'architecture monte du local arithmétique (`Core`, démontré) vers le global analytique
(`AnalyticHorizon`, ouvert), et **nomme le mur** entre les deux : `Lemma7Residual` (F3).

---

## Éventail de composition Phase B — statut honnête

Le pont H3 n'est pas une pyramide linéaire mais un **éventail à cinq branches
structurellement disjointes**, agrégé dans `Logic/H3/PhaseBComposition.lean`.

| Branche | Statut réel | Contenu | Sorry consommé |
| --- | --- | --- | --- |
| **α** Smooth Bump | conditionnel à axiomes analytiques | `C3_weak_from_C1C2` | aucun |
| **β** Pont arithmétique | branche ouverte / conditionnelle | β.1 axiome direct ; β.2 consomme `Lemma7Residual` | β.2 |
| **γ** Bridge L² | **inconditionnel** | Cauchy-Schwarz, sans axiome ajouté | aucun |
| **δ** Annulation spectrale | **inconditionnel** | combinatoire finie, bloc `R₃₀×S₃₀ = 0` | aucun |
| **η** Statut Schur | marqueur structurel | `closable`, sans revendication de fermeture globale | aucun |

La branche **β.2** est l'unique chemin par lequel le verrou doctrinal
`Lemma7Residual` entre dans la fermeture de `PhaseBComposition`. Les branches
γ et δ sont inconditionnelles ; α reste conditionnée à des hypothèses analytiques
déclarées ; η est un marqueur de statut, non une preuve de fermeture.

Ainsi, l'éventail est **architecturalement en place**, mais le passage global
`det₂ ↔ ξ` demeure ouvert.

---

## Résultats certifiés machine (sélection)

Tous vérifiés par le compilateur Lean 4. *(Corpus préexistant — la couche v38.5.3
ci-dessus s'y ajoute.)*

La liste ci-dessous est une sélection de résultats Lean vérifiés ; elle ne remplace pas
le registre canonique des claims `[D]`.

### Spectre et algèbre linéaire
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 1 | `Spec(A) = {3², 1⁴, (−1)²}` | `Core/CayleySpectrum` | `native_decide` |
| 2 | `(A−3I)(A−I)(A+I) = 0` | `Core/CayleySpectrum` | `native_decide` |
| 3 | 8 vecteurs propres orthogonaux non nuls | `Core/CayleySpectrum` | `native_decide` |
| 4 | Polynôme caractéristique `(X−3)²(X−1)⁴(X+1)²` | `Core/CharPoly` | `native_decide` |
| 5 | Unicité des multiplicités `(2,4,2)` | `Core/MultiplicityUniqueness` | `omega` |
| 6 | Unicité altVec centré pour `λ=3` | `Core/CenteredEigenspace` | `omega` |
| 7 | Gap coercif `κ = 2` sur `H° ∩ altVec⊥` | `Spectral/FiniteCore` | algébrique |
| 8 | `λ² = 1/7` | `Core/Lambda` | `nlinarith` |

### Graphe de Cayley et composantes
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 9 | Cayley **déconnecté** (2 composantes) | `Core/CayleyConnected` | `native_decide` |
| 10 | Spec composantes `= {3,1,1,−1}` | `Core/ComponentSpectrum` | `native_decide` |
| 11 | `Aeven = Aodd` | `Core/ComponentSpectrum` | `native_decide` |

### Classification et combinatoire
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 12 | 63/255 sous-ensembles à spectre entier | `Core/Classification63` | `native_decide` |
| 13 | Ventilation palindromique `4,8,12,14,12,8,4,1` | `Core/Classification63Detail` | `native_decide` |
| 14 | 8 coefficients de Fourier de `TC` | `Core/TripletToFiniteSpectrum` | `simp + norm_num` |
| 15 | Profil quadratique `[9,1,1,1,9,1,1,1]` | `Core/TripletPowerSpectrum` | `rw + norm_num` |
| 16 | Défaut `δ₁₉−δ₂₉` sur 4 canaux | `Core/DefectProjection` | `native_decide` |

### Tour primorielle, Parseval, transport CRT
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 17 | Parseval `= 24`, `E = 3` (L3, L4) | `Core/Parseval`, `Core/InvariantE` | `native_decide` |
| 18 | Parseval `= 960`, `E = 2` (L5) | `Core/ParsevalL5` | `native_decide` |
| 19 | `gcd(11, 2310) = 11` (correction v17→v18) | `Core/ParsevalL5` | `native_decide` |
| 20 | `E/\|TC_cop\| = 1` aux 3 niveaux | `Core/ParsevalL5` | `norm_num` |

### Moments spectraux et récurrence
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 21 | `L_k = 2 + (4+2(−1)ᵏ)/3ᵏ`, k=1..10 | `Core/FormuleLk` | `norm_num` |
| 22 | Paires `L_{2j−1} = L_{2j}`, monotonie `L_k ↘ 2` | `Core/FormuleLk` | `norm_num` |
| 23 | Moments `Tr(M^k) = 8, 24, 56, 168, 488` | `Core/SpectralMoments` | `native_decide` |
| 24 | Récurrence `s_k = 3s_{k−1}+s_{k−2}−3s_{k−3}` | `Core/TraceRecurrence` | `ring + pow_add` |
| 25 | Kurtosis brute `7/3`, ratio non trivial `5/3` | `Core/Kurtosis` | `norm_num` |

### Propriétés algébriques et obstructions
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 26 | `TC` auto-inverse (`1²=11²=29²≡1 mod 30`) | `Core/TCAutoInverse` | `native_decide` |
| 27 | `TC` non sous-groupe (`11·29≡19∉TC`) | `Core/TCAutoInverse` | `native_decide` |
| 28 | `J²=−I` impossible en dim impaire | `Core/OddDimComplexObstruction` | `nlinarith + omega` |
| 29 | Mersenne mod 30 `∈ {1,7}` (p=3..31) | `Core/MersenneMod30` | `native_decide` |
| 30 | Vandermonde `det = 16 ≠ 0` (unicité de μ) | `Core/CarlemanUniqueness` | `native_decide` |
| 31 | Sophie Germain mod 30 (restrictions `{S.11,S.23,S.29}`) | `Core/SophieGermainMod30` | `native_decide` |

> La restriction Sophie Germain mod 30 est intégrée **avec antériorité explicite** comme
> corollaire du Théorème 2.1 d'Agoh (*Integers* 25, 2025, #A83, preuve par A. Granville).
> Le programme cite sa source ; il ne se l'attribue pas.

### Composition Phase B (théorèmes inconditionnels) & arithmétique fondamentale
| # | Résultat | Fichier | Méthode |
|---|---|---|---|
| 32 | Smooth Bump : `0 < EvaluateExplicit` sous biais | `Logic/H3/C3Weak` | `linarith` |
| 33 | Bridge L² : `((1−λ)²β²)/B² ≤ ‖main‖²` | `Logic/H3/L10Bridge` | Cauchy-Schwarz |
| 34 | Bloc spectral `R₃₀×S₃₀ = 0` | `Logic/H3/SpectralSpatial` | `fin_cases` |
| 35 | `μ(n) ≠ 0 ↔ Squarefree(n)`, `n ≥ 1` | `Core/Arithmetic` | induction forte |
| 36 | `M(n+1) = M(n) + μ(n+1)` | `Core/Arithmetic` | `Finset.sum_range_succ` |
| 37 | `K(q) ≥ 0`, second moment | `Core/Arithmetic` | somme de carrés |

---

## Ce qui n'est PAS dans le dépôt Lean

Distinction nette entre ce qui est **machine-vérifié en Lean** (ci-dessus) et ce qui est
établi **sur papier** (analytique) ou **numériquement** (PARI/GP, Python) :

| Résultat | Nature | Pourquoi hors Lean |
|---|---|---|
| `‖M‖_HS ≤ P(3/2) < 1` (borne H1) | **analytique** | analyse fonctionnelle, pas d'API Lean |
| `M ∈ S₂` (Hilbert-Schmidt) | **analytique** | idem |
| Auto-adjonction KLMN / Friedrichs | **analytique** | idem |
| `det₂(I−zS) = ξ(1/2+iz)/ξ(1/2)` | **ouvert = RH** | branche β.2, `Lemma7Residual` |
| `V_eff ≈ 0,055` | **numérique** (PARI/GP) | non formalisable en Lean |
| Falsification `λ = 1/√7` universelle | **numérique** | `scripts/` |
| Convergence NBC (Nyman-Beurling-Couret) | **ouvert = RH** | reformulé, non démontré |

> Note : la borne H1 et l'auto-adjonction sont des résultats **analytiques sur papier**,
> non des théorèmes Lean. Le dépôt ne les compte pas parmi ses résultats certifiés machine.

---

## Horizon

Ce socle fini appartient à un programme dont l'horizon est la structure spectrale de type
**Hilbert-Pólya** associée à la fonction `ξ` de Riemann. L'orientation est sincère et
nommée ; elle n'est **pas** une revendication. Le mur unique qui sépare le socle fini de
l'horizon analytique est désigné — l'équivalence `det₂ ↔ ξ` (`Lemma7Residual`, F3) — et il
relève de l'analyse continue : il n'est ni résolu ni approché par accumulation de résultats
finis.

### Non-transport spectral → comptage premier

La dominance `3/5` obtenue sur `G₃₀` est une **dominance d'énergie de Fourier** :
pour les triplets quadratiques, le canal dominant porte `9` unités d'énergie sur une énergie
non triviale totale `15`, soit `9/15 = 3/5`.

Cette valeur ne doit pas être lue comme une densité de nombres premiers. Un triplet de
classes modulo 30 contient `3` classes inversibles sur les `8` classes de `G₃₀`; par
équidistribution asymptotique des nombres premiers dans les classes réduites modulo 30, la
densité de comptage attendue est donc `3/8`, non `3/5`.

Ainsi, le résultat fini dit :

> le triplet possède une structure harmonique fortement dominante dans le groupe fini ;

mais il ne dit pas :

> les nombres premiers réels se distribuent selon cette proportion spectrale.

C'est un cas explicite de **non-transport** : une structure algébrique exacte du socle fini
ne devient pas automatiquement une loi statistique globale sur les nombres premiers.

Invariants maintenus dans tout le dépôt :

```
RHClaimed = false   ·   HilbertPolyaClaimed = false   ·   Det2IdentityClaimed = false
GoldbachProofClaimed = false   ·   EngineeringVerdictClaimed = false   ·   ScopeExpansionClaimed = false
```

---

## Grammaire des statuts

Chaque énoncé du programme porte un statut explicite ; aucun ne circule sans le sien.

| | | | |
|---|---|---|---|
| `[D]` Démontré | `[M]` Mesuré | `[C]` Conditionnel | `[H]` Hypothèse |
| `[P]` Probatoire | `[O]` Ouvert | `[F]` Falsifié | `[T]` Transmis |

(plus `[Q]` quarantaine). Un `[D]` peut être *local* ou *computationnel* : la maturité d'un
claim — artefact public relié, log, date — n'est pas son statut épistémique, et le dépôt
distingue les deux.

Registre canonique v54.7 — **34 claims** : 14 `[D]`, 4 `[M-solide]`, 2 `[P]`, 1 `[P|H]`,
1 `[C]`, 6 `[O]`, 6 `[Réfuté]`. C'est le portrait exact du programme : vaste, et franc sur ce
qui, dans ce vaste, est démontré.

---

## Compilation & attestation

```bash
lake build CouretUnification.Frozen   # 3569 jobs, 0 sorry, 0 warn
lake build CouretUnification.All      # 3753 jobs, 10 sorry documentés
```

### Audit d'intégrité

```bash
make audit-imports          # détecte les imports cassés
make audit-reachability     # vérifie les modules atteints depuis All
make checksums              # manifeste SHA-256 des sources + toolchain
make verify-checksums       # vérification tierce en une commande
```

Le manifeste atteste l'**identité des sources** ; la propriété « 0 sorry » de la couche
fermée est attestée par `lake build CouretUnification.Frozen` contre le toolchain épinglé
(`lean-toolchain`, `lake-manifest.json`). La vérification se rejoue à l'identique ; elle ne
demande la permission de personne.

---

## Scripts numériques

```bash
gp < scripts/test_veff.gp              # V_eff par PARI/GP
python3 scripts/evidence_veff.py       # V_eff version Python
python3 scripts/compute_moments.py     # moments spectraux sur la tour
python3 scripts/channel_bridge_v3.py   # défaut δ₁₉−δ₂₉ + Guinand-Weil
```

---

## Documents

- `docs/PRESENTATION_PROGRAMME.md` — présentation du programme (architecture, socle
  démontré, no-go, dispositif méthodologique, horizon).
- `docs/arxiv/ARTICLE_titre_et_introduction_FR.md` — titre & introduction de la publication.
- `docs/ETAT_DEFINITIF_v5_INTEGRAL.md`, `docs/PASSAGE_LOCAL_GLOBAL.md`,
  `docs/RAPPORT_DEMONSTRATION_v5_FINAL.md` — manifestes doctrinaux antérieurs.

---

## Phrase de référence

> **Le noyau fini est exact et compilé ; l'éventail de composition est en place ;
> le pont global reste ouvert. RHClaimed = false.**

*Prouver ce qui est prouvable. Corriger ce qui est faux. Nommer ce qui est ouvert.*

---

- Dépôt : `github.com/couret-interia/CouretUnification`
- Site : `couret-interia.fr`
- Contact : par [courriel](https://couret-interia.fr/contact) via le site

---

## Licence

MIT — voir `LICENSE`.

Alexandre Couret — Rasiguères — 2026.
Programme dédié à la mémoire de Bernard Couret (1928–1999), dont les manuscrits sur les
distributions de premiers modulo 30 et la géométrie triangulaire ont inspiré le programme.

*Nous n'avons fait qu'observer, mon grand-père et moi, le « déjà là ».*
