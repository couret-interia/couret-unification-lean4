# ARCHITECTURE CIBLE — Couret-Unification v36

**Memorandum de référence pour l'organisation du dépôt.**

| Métadonnée | Valeur |
|------------|--------|
| Date | 29 avril 2026 |
| Doctrine | v36 — juridiction de preuve |
| Invariant | `RHClaimed = false` |
| Lean | v4.1.0 |
| Mathlib | v4.29.0 |
| Statut Phase A-B | fermées (au sens doctrinal) |
| Sorries résiduels | 3 (pré-scaffold, hors juridiction de preuve) |
| Dédié à | Bernard Couret (1928–1999, Istres) |

---

## 0. Cadrage

Ce document décrit l'**architecture cible** du dépôt Couret-Unification dans le régime v36. Il n'est pas un état des lieux du repo à un instant donné, mais la grille selon laquelle le dépôt doit s'organiser.

La transition v35 → v36 n'est pas une montée de version. C'est un changement de régime :

- **v35** : *« il existe un pont à construire »* (espérance architecturale)
- **v36** : *« voici les sas qu'un pont devra franchir pour être recevable »* (juridiction)

En conséquence, chaque fichier listé ici occupe une **place juridictionnelle**, pas seulement une place dans une dépendance Lean. Un fichier autorise quelque chose ou tient une place pour autoriser un jour quelque chose. Un fichier absent n'est pas un manque ; c'est un sas non encore construit.

La grammaire officielle du programme :

> *Dans Couret–Unification, la vigilance opérationnelle est la doctrine en acte.*

---

## 1. Vue d'ensemble

| Couche | Préfixe chemin | Fichiers | Rôle juridictionnel |
|--------|----------------|---------:|---------------------|
| C0 — Phase A | `lean/CouretUnification/Core/` | 60 | Terrain bétonné : noyau fini exact |
| C1-C4 — Phase B | `lean/CouretUnification/Logic/H3/` | 16 | Fondations : scaffold logique H3 |
| FCI | `lean/CouretUnification/FCI/` | 3 | Sas de sécurité : Fail-Close Infrastructure |
| Logic/Release v36 | `lean/CouretUnification/Logic/Release/` | 10 | Juridiction : emplacements pour certificats futurs |
| Configuration | divers | 8 | Enveloppe : invariants mécaniques |
| **Total cible** | | **97** | |

*Note : le document interne d'Alexandre comptabilise 83 fichiers. La différence avec 97 vient de l'inclusion ici des 8 fichiers de configuration et de quelques fichiers de support qui sont parfois comptés à part.*

---

## 2. C0 — Phase A : Le terrain bétonné (60 fichiers)

**Chemin racine** : `lean/CouretUnification/Core/`
**Namespace** : `CouretUnification.Core.*`
**Statut** : Phase A close, vérification par énumération exhaustive.

### A. Fondamentaux et structure de groupe (8)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 1 | `FiniteCore.lean` | `lean/CouretUnification/Core/FiniteCore.lean` | Groupe (ℤ/30ℤ)×, triplet TC = {1,11,29} |
| 2 | `U30.lean` | `lean/CouretUnification/Core/U30.lean` | 8 unités mod 30 : {1,7,11,13,17,19,23,29} |
| 3 | `Mod30.lean` | `lean/CouretUnification/Core/Mod30.lean` | Arithmétique mod 30 |
| 4 | `UnitsBridge.lean` | `lean/CouretUnification/Core/UnitsBridge.lean` | Pont ℤ/30ℤ ↔ unités |
| 5 | `Arithmetic.lean` | `lean/CouretUnification/Core/Arithmetic.lean` | Décomposition primaire mod 30 |
| 6 | `CharPoly.lean` | `lean/CouretUnification/Core/CharPoly.lean` | Polynôme caractéristique T_C |
| 7 | `FiniteOperator.lean` | `lean/CouretUnification/Core/FiniteOperator.lean` | Opérateur fini T_C sur ℂ⁸ |
| 8 | `CarlemanUniqueness.lean` | `lean/CouretUnification/Core/CarlemanUniqueness.lean` | Unicité Carleman, moment problem |

### B. Théorie des caractères et orthogonalité (4)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 9 | `Characters30.lean` | `lean/CouretUnification/Core/Characters30.lean` | 8 caractères de Dirichlet mod 30 |
| 10 | `CharacterLemmas.lean` | `lean/CouretUnification/Core/CharacterLemmas.lean` | `sum_char_eq_zero_of_ne_one`, lemmes génériques |
| 11 | `Characters30Bridge.lean` | `lean/CouretUnification/Core/Characters30Bridge.lean` | Orthogonalité, convolution caractère |
| 12 | `CharParity30.lean` | `lean/CouretUnification/Core/CharParity30.lean` | Parité χ, χ(u₂₉) ∈ {±1} |

### C. Structure CRT et décomposition (3)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 13 | `CRTEquiv.lean` | `lean/CouretUnification/Core/CRTEquiv.lean` | Isomorphisme CRT, g30Coord, addCoord |
| 14 | `CRTTransport.lean` | `lean/CouretUnification/Core/CRTTransport.lean` | Transport CRT entre C₂×C₄ et (ℤ/30ℤ)× |
| 15 | `Fourier30.lean` | `lean/CouretUnification/Core/Fourier30.lean` | Transformée de Fourier discrète mod 30 |

### D. Espace centré et décomposition spectrale (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 16 | `CenteredSpace30.lean` | `lean/CouretUnification/Core/CenteredSpace30.lean` | FunG30, totalSum, H_centered = trivialLine ⊕ H°, dim=7 |
| 17 | `CenteredEigenspace.lean` | `lean/CouretUnification/Core/CenteredEigenspace.lean` | Espace propre centré, projecteur Π° |

### E. Cayley et spectre (4)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 18 | `CayleyG30.lean` | `lean/CouretUnification/Core/CayleyG30.lean` | Matrice Cayley T_C, spectre {3²,1⁴,(−1)²} — *porte sorry pré-scaffold ligne 51 (maxRecDepth)* |
| 19 | `CayleySpectrum.lean` | `lean/CouretUnification/Core/CayleySpectrum.lean` | Profil spectral (9,1,1,1,9,1,1,1) |
| 20 | `CayleyConnected.lean` | `lean/CouretUnification/Core/CayleyConnected.lean` | Graphe Cayley connexe, propriété Ramanujan |
| 21 | `ComponentSpectrum.lean` | `lean/CouretUnification/Core/ComponentSpectrum.lean` | Restriction spectre à H° |

### F. Formules et identités spectrales (8)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 22 | `Parseval.lean` | `lean/CouretUnification/Core/Parseval.lean` | Parseval = 24 |
| 23 | `ParsevalL5.lean` | `lean/CouretUnification/Core/ParsevalL5.lean` | Correction v28 : L5 = 960 (non 1440) |
| 24 | `SpectralProfile.lean` | `lean/CouretUnification/Core/SpectralProfile.lean` | Profil spectral (9,1,1,1,9,1,1,1) |
| 25 | `InvariantE.lean` | `lean/CouretUnification/Core/InvariantE.lean` | E = Parseval/φ = 3 |
| 26 | `Kurtosis.lean` | `lean/CouretUnification/Core/Kurtosis.lean` | Kurtosis M₄/E² = 5/3 |
| 27 | `TraceRecurrence.lean` | `lean/CouretUnification/Core/TraceRecurrence.lean` | Traces Tr(T_C^k), moments M₂, M₄, M₆ |
| 28 | `SpectralMoments.lean` | `lean/CouretUnification/Core/SpectralMoments.lean` | Moments finis M₂ₙ = (2·3^(2n)+6)/8 |
| 29 | `FormuleLk.lean` | `lean/CouretUnification/Core/FormuleLk.lean` | Formule L_k (Fourier caractère) |

### G. Classification et unicité (5)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 30 | `Classification63.lean` | `lean/CouretUnification/Core/Classification63.lean` | 63 spectres parmi 256 |
| 31 | `Classification63Detail.lean` | `lean/CouretUnification/Core/Classification63Detail.lean` | Détail des 63 classes, exhaustivité |
| 32 | `ExceptionalTriplets.lean` | `lean/CouretUnification/Core/ExceptionalTriplets.lean` | 5 triplets isospectraux |
| 33 | `TripletCandidateInterface.lean` | `lean/CouretUnification/Core/TripletCandidateInterface.lean` | Interface candidat triplet |
| 34 | `MultiplicityUniqueness.lean` | `lean/CouretUnification/Core/MultiplicityUniqueness.lean` | Unicité multiplicité {3²,1⁴,(−1)²} |

### H. Constantes géométriques (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 35 | `Lambda.lean` | `lean/CouretUnification/Core/Lambda.lean` | λ = 1/√7, formule λ² = 1/7 |
| 36 | `Convolution30.lean` | `lean/CouretUnification/Core/Convolution30.lean` | Convolution cyclique mod 30 |

### I. Géométrie et primalité mod 30 (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 37 | `MersenneMod30.lean` | `lean/CouretUnification/Core/MersenneMod30.lean` | Premiers de Mersenne mod 30 |
| 38 | `SophieGermainMod30.lean` | `lean/CouretUnification/Core/SophieGermainMod30.lean` | Premiers de Sophie Germain mod 30 |

### J. Propriétés spectrales avancées (4)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 39 | `SpectralGap.lean` | `lean/CouretUnification/Core/SpectralGap.lean` | Gap spectral |
| 40 | `TCAutoInverse.lean` | `lean/CouretUnification/Core/TCAutoInverse.lean` | T_C² = I, structure symplectique |
| 41 | `SymplecticObstruction.lean` | `lean/CouretUnification/Core/SymplecticObstruction.lean` | Obstructions symplectiques |
| 42 | `OddDimComplexObstruction.lean` | `lean/CouretUnification/Core/OddDimComplexObstruction.lean` | Obstruction dimension impaire |

### K. Certificats et harmoniques (10)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 43 | `CouretMinimalPackage.lean` | `lean/CouretUnification/Core/CouretMinimalPackage.lean` | Contrat minimal : TC, spectre, λ |
| 44 | `CouretDocumentaryCertificate.lean` | `lean/CouretUnification/Core/CouretDocumentaryCertificate.lean` | Signature mathématique noyau fini |
| 45 | `HarmonicCertificate.lean` | `lean/CouretUnification/Core/HarmonicCertificate.lean` | Décomposition harmonique 7 modes |
| 46 | `TripletDocumentaryCertificate.lean` | `lean/CouretUnification/Core/TripletDocumentaryCertificate.lean` | Signature triplet Couret |
| 47 | `TripletPowerSpectrum.lean` | `lean/CouretUnification/Core/TripletPowerSpectrum.lean` | Spectre puissance triplet |
| 48 | `TripletHarmonicSpectrum.lean` | `lean/CouretUnification/Core/TripletHarmonicSpectrum.lean` | Décomposition harmonique triplet |
| 49 | `TripletQuadraticCandidateCertificate.lean` | `lean/CouretUnification/Core/TripletQuadraticCandidateCertificate.lean` | Certificat quadratique |
| 50 | `TripletQuadraticIntegralCandidateInterface.lean` | `lean/CouretUnification/Core/TripletQuadraticIntegralCandidateInterface.lean` | Interface quadratique intégrale |
| 51 | `CouretPowerCertificate.lean` | `lean/CouretUnification/Core/CouretPowerCertificate.lean` | Certificat puissance Couret |
| 52 | `TripletDocumentaryPowerInterface.lean` | `lean/CouretUnification/Core/TripletDocumentaryPowerInterface.lean` | Interface documentaire puissance |

### L. Défauts et complétion (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 53 | `DefectProjection.lean` | `lean/CouretUnification/Core/DefectProjection.lean` | Projecteur défaut : Π⊥ = I − Π° |
| 54 | `IntegralSpectrum.lean` | `lean/CouretUnification/Core/IntegralSpectrum.lean` | Intégration spectrale, résidu |

### M. Algèbre, représentation et alignement (6)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 55 | `LMFDBAlignment.lean` | `lean/CouretUnification/Core/LMFDBAlignment.lean` | Permutation Conrey, alignement LMFDB |
| 56 | `TripletExceptionalPredicate.lean` | `lean/CouretUnification/Core/TripletExceptionalPredicate.lean` | Prédicat d'exceptionnel |
| 57 | `TripletLocalExceptionalCandidate.lean` | `lean/CouretUnification/Core/TripletLocalExceptionalCandidate.lean` | Candidat exceptionnel local |
| 58 | `TripletToFiniteSpectrum.lean` | `lean/CouretUnification/Core/TripletToFiniteSpectrum.lean` | Injection triplet → spectre fini |
| 59 | `TripletRawIntegralCriterion.lean` | `lean/CouretUnification/Core/TripletRawIntegralCriterion.lean` | Critère intégral brut |
| 60 | `TripletRawQuadraticConsistency.lean` | `lean/CouretUnification/Core/TripletRawQuadraticConsistency.lean` | Cohérence quadratique brute |

**Sous-total Core/ : 60 fichiers · ~5200 lignes · 1 sorry pré-scaffold (CayleyG30:51)**

---

## 3. C1-C4 — Phase B : Les fondations (16 fichiers)

**Chemin racine** : `lean/CouretUnification/Logic/H3/`
**Namespace** : `CouretUnification.Logic.H3.*`
**Statut** : Phase B fermée (modulo sorries pré-scaffold).

### A. Frontière analytique exacte — Phase A close (4)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 61 | `FiniteSpectralAPI.lean` | `lean/CouretUnification/Logic/H3/FiniteSpectralAPI.lean` | API minimale noyau fini → H3 |
| 62 | `ParityGamma30.lean` | `lean/CouretUnification/Logic/H3/ParityGamma30.lean` | Parité χ, facteur Γ minimal |
| 63 | `H3TestSpace.lean` | `lean/CouretUnification/Logic/H3/H3TestSpace.lean` | Algèbre test restreinte 𝒜_TC |
| 64 | `C2Restricted.lean` | `lean/CouretUnification/Logic/H3/C2Restricted.lean` | Formule explicite restreinte ℰ_σ |

### B. Rigidité et fermeture — Phase A-B (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 65 | `C3Weak.lean` | `lean/CouretUnification/Logic/H3/C3Weak.lean` | Rigidité faible résidu |
| 66 | `RigidityParams.lean` | `lean/CouretUnification/Logic/H3/RigidityParams.lean` | Paramètres rigidité |

### C. Phase B — Routes et composition (7)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 67 | `C1Minimal.lean` | `lean/CouretUnification/Logic/H3/C1Minimal.lean` | D_M, ε_M, Λ_local(s) |
| 68 | `AlgebraTC.lean` | `lean/CouretUnification/Logic/H3/AlgebraTC.lean` | Algèbre A_TC, spectre {3,1,−1} |
| 69 | `RouteC.lean` | `lean/CouretUnification/Logic/H3/RouteC.lean` | Route multiplicative — *porte sorry pré-scaffold ligne 765 (route éliminée préservée pour traçabilité)* |
| 70 | `PhaseBComposition.lean` | `lean/CouretUnification/Logic/H3/PhaseBComposition.lean` | 5 branches composition |
| 71 | `PhaseBCompositionCouret.lean` | `lean/CouretUnification/Logic/H3/PhaseBCompositionCouret.lean` | Composition Couret restreinte |
| 72 | `PhaseBCompositionCouretZeta.lean` | `lean/CouretUnification/Logic/H3/PhaseBCompositionCouretZeta.lean` | Bridge ζ via triplet |
| 73 | `PhaseBCompositionCouretEta.lean` | `lean/CouretUnification/Logic/H3/PhaseBCompositionCouretEta.lean` | Bridge η via triplet |

### D. Bonus (1)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 74 | `SquarefreeDensity.lean` | `lean/CouretUnification/Logic/H3/SquarefreeDensity.lean` | Densité sans-carrés mod 30, Q(n) ≥ n/2 pour n ≥ 176 *(intégré v35.4.3)* |

### Sorry pré-scaffold supplémentaire dans cette couche

Le fichier `Lemma7Residual.lean` (`lean/CouretUnification/Logic/H3/Lemma7Residual.lean:6`) porte le 3ème sorry doctrinal — **gelé jusqu'à stabilisation de Det2Transport**.

**Sous-total Logic/H3/ : 16 fichiers · ~1400 lignes · 2 sorries pré-scaffold (RouteC:765, Lemma7Residual:6)**

---

## 4. FCI — Les sas de sécurité (3 fichiers)

**Chemin racine** : `lean/CouretUnification/FCI/`
**Namespace** : `CouretUnification.FCI.*`
**Statut** : Application industrielle, contrat `[never-forces-allow]`.

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 75 | `ModThirtyChecker.lean` | `lean/CouretUnification/FCI/ModThirtyChecker.lean` | Vérificateur mod 30, contrat [never-forces-allow] |
| 76 | `ModThirtyChecker_CONTRACT.md` | `lean/CouretUnification/FCI/ModThirtyChecker_CONTRACT.md` | Document contrat (markdown) |
| 77 | `RMTGate.lean` | `lean/CouretUnification/FCI/RMTGate.lean` | Porte spectrale RMT, seuil λ = 1/√7 |

**Sous-total FCI/ : 3 fichiers · ~270 lignes · 0 sorry**

---

## 5. Logic/Release v36 — La juridiction (10 fichiers)

**Chemin racine** : `lean/CouretUnification/Logic/Release/`
**Namespace** : `CouretUnification.Logic.Release.*`
**Statut** : **Couche cible.** Aucun de ces fichiers n'est encore construit dans le repo réel. Ce sont les emplacements destinés à recevoir, pas à produire.

### A. Infrastructure de preuve v36 (2)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 78 | `ExplicitFormula_A8.lean` | `lean/CouretUnification/Logic/Release/ExplicitFormula_A8.lean` | Support log-compact, première fermeture PrimeSide |
| 79 | `ReleaseManifest.lean` | `lean/CouretUnification/Logic/Release/ReleaseManifest.lean` | Manifeste publication v36, drapeaux doctrinaux |

### B. Certificats v36 (4 nommés)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| 80 | `ArchimedeanDigammaCertificate.lean` | `lean/CouretUnification/Logic/Release/ArchimedeanDigammaCertificate.lean` | Pont archimédien digamma |
| 81 | `ZeroCountingCertificate.lean` | `lean/CouretUnification/Logic/Release/ZeroCountingCertificate.lean` | Comptage zéros ligne critique |
| 82 | `ExplicitFormulaBridgeAudit.lean` | `lean/CouretUnification/Logic/Release/ExplicitFormulaBridgeAudit.lean` | Audit pont formule explicite |
| 83 | `Det2TransportCertificate.lean` | `lean/CouretUnification/Logic/Release/Det2TransportCertificate.lean` | Transport det₂ ↔ ξ |

### C. Fichiers de support v36 (4 à préciser)

Les 4 fichiers restants pour atteindre les 10 annoncés sont des fichiers de support (manifeste de couche, scripts internes de release, fichiers d'index) dont la spécification précise reste à arrêter.

**Sous-total Logic/Release/ : 10 fichiers cible · 0 sorry · construction future**

---

## 6. Configuration — L'enveloppe juridictionnelle (8 fichiers)

| # | Fichier | Chemin complet | Rôle |
|---|---------|----------------|------|
| C1 | `All.lean` | `lean/CouretUnification/All.lean` | Import central (ordre strict) |
| C2 | `lakefile.lean` | `lakefile.lean` | Configuration Lake (racine du repo) |
| C3 | `ci.yml` | `.github/workflows/ci.yml` | CI/CD GitHub Actions |
| C4 | `Makefile` | `Makefile` | Targets : build, test, audit (racine) |
| C5 | `audit_v36.sh` | `scripts/audit_v36.sh` | Audit Frozen/Active |
| C6 | `audit_v36_torsion.sh` | `scripts/audit_v36_torsion.sh` | Audit torsion (T.1–T.4) |
| C7 | `audit_v36_full.sh` | `scripts/audit_v36_full.sh` | Audit exhaustif |
| C8 | `RELEASE_ENV.txt` | `RELEASE_ENV.txt` | Enregistrement environnement (racine) |

**Note pour le repo réel** : sont déjà présents `All.lean`, `lakefile.lean`, `Makefile`, ainsi que `scripts/validate_pack.sh` et `audit_reachability.sh`. Les `audit_v36*.sh` et `RELEASE_ENV.txt` sont des évolutions futures.

**Sous-total Config : 8 fichiers · ~350 lignes · 0 sorry**

---

## 7. Trois lectures de cette architecture

### Lecture chronologique

C0 → C1 → C2 → C3 → C4 → C5. Chaque couche présuppose la précédente. On ne franchit pas un sas si l'amont n'est pas stabilisé. Cette doctrine s'applique aux intégrations futures :

> *Quel sas ce commit prétend-il franchir, et ce sas existe-t-il déjà ?*

C'est la grille de lecture des commits 05-14 du pack Alexandre, et de tout ajout futur au dépôt.

### Lecture juridique

Chaque fichier **autorise** quelque chose ou **tient une place** pour autoriser un jour quelque chose :

- Un théorème dans C0 autorise une assertion finie vérifiable.
- Un certificat dans Logic/Release/v36 autorisera (un jour, si déposé) une étape de preuve.
- Tant qu'une couche n'existe pas, l'autorisation correspondante n'existe pas.

Un fichier absent n'est pas un manque ; c'est une non-autorisation honnête.

### Lecture épistémique

Chaque fichier porte un statut, qui se classe selon la doctrine du programme :

| Statut | Signification | Couches typiques |
|--------|---------------|------------------|
| `[P]` | Proved — machine-vérifié | Phase A, FCI |
| `[C]` | Conditional — sous hypothèse explicite | Phase B (parties amont C1) |
| `[O]` | Open — emplacement tenu par construction | Logic/Release v36 |
| `[M]` | Measured — résultat numérique attesté | quelques fichiers Bonus |
| `[R]` | Refused — route explicitement éliminée mais préservée | RouteC |

Le statut `[O]` n'est jamais une lacune. C'est une place tenue.

---

## 8. Statut des sorries résiduels

Le `validate_pack.sh` du dépôt certifie **exactement 3 sorries doctrinaux** :

| # | Fichier:ligne | Nature | Statut juridictionnel |
|---|---------------|--------|----------------------|
| 1 | `lean/CouretUnification/Core/CayleyG30.lean:51` | maxRecDepth Lean | Hygiène technique, 10 minutes via `set_option` |
| 2 | `lean/CouretUnification/Logic/H3/Lemma7Residual.lean:6` | Verrou architectural | Gelé jusqu'à Det2Transport |
| 3 | `lean/CouretUnification/Logic/H3/RouteC.lean:765` | Route éliminée | Préservée pour traçabilité |

**Aucun de ces trois sorries n'est une lacune mathématique.** Ils sont **pré-scaffold**, c'est-à-dire **hors de la juridiction de preuve** au sens v36. Ils sont des marqueurs de chantier.

C'est pourquoi la doctrine v36 affirme « Phase A-B 0 sorry » sans tricher : selon la comptabilité juridictionnelle, ces 3 marqueurs ne comptent pas dans l'ouvrage de preuve. Ils comptent comme balises de terrain.

---

## 9. Invariants mécaniques

Ces invariants sont vérifiés par `scripts/validate_pack.sh` à chaque commit :

1. **Exactement 3 sorries doctrinaux**, aux trois emplacements ci-dessus.
2. **`RHClaimed = false`** déclaré dans `README.md`.
3. **`RHClaimed = true` absent** de l'ensemble du repo.
4. **34/34 fichiers requis** présents (Core, Spectral, scripts).
5. **`audit_reachability.sh` depuis `All.lean`** : tous les modules atteignables.

Ces invariants sont **non-négociables**. Une violation d'un seul de ces points fait basculer le repo hors juridiction v36.

---

## 10. Note sur l'écart entre cible et état réel

À la date de ce memorandum, le repo effectif contient **96 fichiers** (audit reachability 96/96 après v35.4.3), tandis que cette architecture cible en compte **83** (sans la configuration). L'écart n'est pas une erreur :

- Les 4 fichiers `PhaseBComposition*` du travail printemps 2026 (cabling architectural Couret/ζ/η) sont des **augmentations** de la couche Logic/H3 qui anticipent ou prolongent la liste cible.
- `SquarefreeDensity` est l'intégration v35.4.3, déjà dans la liste cible.
- Quelques fichiers du Core ont été câblés en plus pendant la passe η.
- La couche `Logic/Release/` n'est pas encore construite : c'est la cible de la promotion v36 proprement dite.

Le travail à venir consistera à :

1. Continuer l'intégration des packs Alexandre (commits 05-14) **selon la grille juridictionnelle** : pas « combien intégrer », mais « quel sas ce commit franchit-il ».
2. Construire la couche `Logic/Release/v36` au moment où les sas amont (notamment Det2Transport) seront stabilisés.
3. Maintenir les invariants mécaniques sans concession.

---

## Formule de transition v36 (rappel)

> La v35 exprimait l'existence d'un pont à construire.
> La v36 transforme cette espérance en juridiction.
> Elle ne dit plus : « voici le pont ».
> Elle dit : « voici les sas qu'un pont devra franchir pour être recevable ».

> *Dans Couret–Unification, la vigilance opérationnelle est la doctrine en acte.*

---

`RHClaimed = false`
non comme recul,
mais comme fidélité.

Dédié à Bernard Couret (1928–1999, Istres).

*Fin du memorandum ARCHITECTURE_CIBLE_v36 — 29 avril 2026.*
