# Core

Le dossier `Core/` contient le **noyau fini exact** du projet
Couret-Unification, ainsi que l'**arithmétique fondamentale** dont il
dépend.

Ici, la règle est simple :

- pas de faux “proved” ;
- pas de `Prop := True` pour simuler une preuve ;
- les `sorry` sont **strictement doctrinaux** et explicitement déclarés ;
- les axiomes sont **strictement documentés** ;
- toutes les autres constructions sont des définitions, lemmes et
  théorèmes effectivement compilés.

`RHClaimed = false`. Aucune revendication globale n'est portée par ce
dossier.

## Rôle du dossier

`Core/` porte les objets finis, explicites et contrôlés au niveau du
modèle mod 30, ainsi que l'arithmétique fondamentale qui les relie aux
fonctions classiques de la théorie analytique des nombres.

On y trouve, organisés en quatre familles :

### 1. Structure du groupe et de l'opérateur fini

- groupe des unités `(ℤ/30ℤ)×` (`U30`, `Mod30`, `UnitsBridge`) ;
- caractères de Dirichlet mod 30 et leurs lemmes
  (`Characters30`, `Characters30Bridge`, `CharacterLemmas`,
  `CharParity30`) ;
- recollement Cayley du triplet distingué (`CayleyG30`,
  `CayleyConnected`, `CayleySpectrum`) ;
- transport CRT vers ℤ/2 × ℤ/3 × ℤ/5 (`CRTEquiv`, `CRTTransport`) ;
- couche Fourier minimale (`Fourier30`, `Convolution30`) ;
- restrictions modulaires élémentaires
  (`SophieGermainMod30`, `MersenneMod30`).

### 2. Spectre fini exact

- spectre `{3², 1⁴, (−1)²}` du triplet distingué et profil
  quadratique associé (`TripletSpectrum`, `TripletPowerSpectrum`,
  `TripletHarmonicSpectrum`, `TripletToFiniteSpectrum`) ;
- masse de Parseval `= 24` (`Parseval`, `ParsevalL5`) ;
- gap spectral fini (`SpectralGap`) ;
- moments spectraux et récurrence de trace
  (`SpectralMoments`, `TraceRecurrence`) ;
- profil et couches intermédiaires
  (`SpectralProfile`, `ComponentSpectrum`, `CenteredSpace30`,
  `CenteredEigenspace`) ;
- polynôme caractéristique (`CharPoly`) ;
- opérateur fini (`FiniteOperator`, `FiniteCore`) ;
- formule `L_k` et calcul de kurtosis (`FormuleLk`, `Kurtosis`) ;
- invariant `λ` (`Lambda`) et invariant `E(q)` (`InvariantE`) ;
- automorphisme du triplet centré (`TCAutoInverse`) ;
- projection de défaut (`DefectProjection`).

### 3. Classification et certificats Couret

- 21 triplets exacts centrés sur l'identité, classification 63/255
  (`Classification63`, `Classification63Detail`, `ExceptionalTriplets`) ;
- ordre documentaire des huit caractères et certificat harmonique
  (`HarmonicCertificate`) ;
- spectre intégral (`IntegralSpectrum`) ;
- prédicat exceptionnel local et son dépaquetage
  (`TripletExceptionalPredicate`,
  `TripletLocalExceptionalCandidate`) ;
- recollement harmonique du cas Couret (façades canoniques :
  `CouretDocumentaryCertificate`, `CouretPowerCertificate`,
  `CouretMinimalPackage`) ;
- certificat fini de double admissibilité du triplet Couret (`TripletTCDoubleAdmissibility`) :
  `T_C = {1} ∪ ({11,29})`, où `{11,29}` est le noyau non neutre doublement
  admissible pour les filtres jumeaux et Sophie-Germain modulo 30 ;
- bornes de cohérence quadratique et candidates
  (`TripletCandidateInterface`, `TripletDocumentaryCertificate`,
  `TripletDocumentaryPowerInterface`,
  `TripletQuadraticCandidateCertificate`,
  `TripletQuadraticIntegralCandidateInterface`,
  `TripletRawIntegralCriterion`,
  `TripletRawQuadraticConsistency`) ;
- unicité de la multiplicité (`MultiplicityUniqueness`) ;
- unicité de Carleman (`CarlemanUniqueness`) ;
- obstructions structurelles (`OddDimComplexObstruction`,
  `SymplecticObstruction`).

### 4. Arithmétique fondamentale

- fonction de Möbius par division minimale, fonction de Mertens
  `M(n) = Σ μ(k)`, équivalence `μ(n) ≠ 0 ↔ Squarefree(n)` ;
- second moment restreint `K(q) = Σ M(a)²` sur les coprimes,
  normalisation `κ(q)² = K(q)/φ(q)` (`Arithmetic`).

Le module `Core/Arithmetic.lean` porte le namespace court
`CouretUnification.Arithmetic` (dérogation documentée à la convention
`namespace = chemin`). Il est consommé par `Logic/H3/RouteC`.

## Discipline

Le dossier `Core/` ne doit contenir que des résultats :

- finis ;
- exacts ;
- compilés ;
- explicitement justifiés.

En particulier, `Core/` ne doit pas contenir :

- de pont analytique non fermé ;
- de revendication Hilbert-Pólya globale ;
- d'identification non démontrée avec la théorie complète de `ζ` ;
- de placeholders logiques.

### Sorries doctrinaux dans Core/

Un seul `sorry` doctrinal est actuellement présent dans `Core/` :

- `CayleyG30.lean:51` — limitation de profondeur récursive sur le
  recollement Cayley de `G₃₀` (limitation `maxRecDepth` du tactique
  `decide` sur une vérification finie de grande taille). Ce sorry
  est **doctrinal au sens où il marque une obstruction technique
  Lean / Mathlib, pas une lacune mathématique** : la vérification
  est calculable et exacte, seul son passage par le noyau de
  décision dépasse la borne par défaut.

Aucun autre `sorry` n'est admis dans `Core/`.

### Axiomes dans Core/

Aucun axiome non documenté n'est présent dans `Core/`.

## Insertion dans le dépôt

Le dossier `Core/` est consommé par les couches suivantes :

- `Finite/Foundations.lean` et `FiniteDefect/T1_to_T7.lean`
  (théorèmes T1 à T7 sur les projecteurs et la pythagoréité) ;
- `Spectral/FiniteCore.lean` et `Spectral/T2Gap.lean` (analyse fine
  du gap spectral) ;
- `Logic/H3/*.lean`, et en particulier
  `Logic/H3/PhaseBComposition.lean` (éventail à cinq branches
  agrégeant les résultats substantiels de la phase H3) ;
- `Logic/H3/RouteC.lean` (consomme l'arithmétique fondamentale
  μ, M(n), κ(q) pour la borne raffinée
  `Σ|E_d| ≤ θ · (φ/q) · S₁`).

Pour la vue stratifiée minimale du dépôt voir `CouretUnification.lean`.
Pour l'agrégation exhaustive voir `CouretUnification/All.lean`.

## Résumé structurel

- `Core/` = noyau fini exact + arithmétique fondamentale ;
- `Finite/`, `FiniteDefect/`, `Spectral/` = couches dérivées du
  noyau fini (projecteurs, gap, T1-T7) ;
- `Logic/H3/` = pont H3 conditionnel et éventail de composition
  Phase B (cinq branches structurellement disjointes) ;
- `Analytic/`, `FunctionalFoundation/` = couches analytiques et
  fondations fonctionnelles (Abel pondéré, intervalles vérifiés,
  axiomes de densité de zéros, chemins discrets).

Dédié à la mémoire de Bernard Couret (1928–1999).