# Couret–Unification — Architecture canonique du dépôt

- **Dépôt :** `CouretUnification`
- **Branche doctrinale :** v38.5x
- **État courant :** v38.5x — ResGold intégré
- **Mainteneur dépôt :** Thomas
- **Programme :** Couret–Unification, Alexandre Couret
- **Hommage :** Bernard Couret (1928–1999, Istres)

---

## 0. Invariants de programme

Le dépôt est gouverné par les invariants suivants :

* `RHClaimed = false`
* `HilbertPolyaClaimed = false`
* `SpectralCoincidenceClaimed = false`
* `ExplicitFormulaClosed = false`
* `Det2IdentityClaimed = false`
* `RiemannVonMangoldtClaimed = false`
* `CandidateCClaimed = false`
* `MotherTheoremClaimed = false`

Ces invariants ne sont pas des slogans éditoriaux : ils structurent l’architecture, les audits, les imports, les rapports et la discipline de release.

> Le noyau fini est exact.
> Le pont global reste ouvert.
> Le conditionnel se nomme.
> L’ouvert se reconnaît.

---

## 1. Objet de ce document

Ce fichier décrit l’architecture officielle du dépôt `CouretUnification` à l’état `v38.5x`.

Il remplace les anciens documents de cible ou de transition, notamment les documents de type :

* `ARCHITECTURE_CIBLE_v36.md`
* brouillons exhaustifs post-v36
* notes de roadmap FCI non encore intégrées comme fichiers Lean

La règle éditoriale est la suivante :

> Ce document décrit d’abord ce qui est réellement dans le dépôt et dans le build.
> Les extensions prévues sont mentionnées séparément comme roadmap, jamais comme arborescence actuelle.

---

## 2. Vue d’ensemble

Le dépôt est organisé en couches strictement séparées.

| Couche                                      | Rôle                                             | Statut                                     | Juridiction         |
| ------------------------------------------- | ------------------------------------------------ | ------------------------------------------ | ------------------- |
| `Core/`                                     | Noyau fini modulo 30, structures exactes         | démontré / fini                            | Frozen              |
| `Finite/`, `FiniteDefect/`, `Spectral/`     | support fini, défaut, spectre                    | démontré / fini                            | Frozen              |
| `FunctionalFoundation/`, `Geometry/`        | chemins discrets, géométrie finie                | démontré / fini                            | Frozen              |
| `Logic/ExplicitFormula/`                    | contrats typés de formule explicite              | structurel / conditionnel                  | Frozen ou frontière |
| `Logic/H3/`                                 | pyramide H3, ponts analytiques                   | conditionnel / ouvert                      | Active              |
| `Logic/Lock3/`                              | verrou final, garde RH                           | ouvert                                     | Active              |
| `AnalyticHorizon/`                          | certificats analytiques typés                    | obligations                                | Active              |
| `FCI/`                                      | Fail-Close Integrity                             | fermé localement                           | Frozen local        |
| `Meta/`, `EpistemicDiscipline/`, `Residue/` | doctrine, invariants, fondation résiduelle       | structurel                                 | Frozen              |
| `ResGold.lean`                              | intégration v38.5 ResGold et invariants associés | audit / gouvernance                        | Frozen local        |
| `Attic/`                                    | archives retirées du chemin canonique            | hors build canonique sauf import explicite | Archive             |

La séparation centrale est :

> `Core/` ne dépend pas de `Logic/H3/`, `AnalyticHorizon/`, `Lock3/`, `Bridges/` ni d’aucune couche globale.

---

## 3. Principe architectural fondamental

Le dépôt distingue quatre statuts épistémiques.

| Badge | Signification                                        | Exemple                            |
| ----- | ---------------------------------------------------- | ---------------------------------- |
| `[D]` | Demonstrated : démontré ou vérifié dans Lean         | calcul fini, table, classification |
| `[M]` | Measured : mesuré par script ou rapport              | métrique empirique, audit externe  |
| `[H]` | Hypothesized : hypothèse ou réduction conditionnelle | pont det₂ ↔ ξ                      |
| `[O]` | Open : ouvert, non fermé                             | RH, Hilbert–Pólya global           |

Aucune couche `[H]` ou `[O]` ne doit être présentée comme `[D]`.

---

## 4. Version doctrinale et version opérationnelle

Le dépôt conserve une doctrine issue de la stabilisation v36, mais l’état opérationnel courant est v38.5x.

Il faut donc distinguer :

| Niveau | Sens                                                                   |
| ------ | ---------------------------------------------------------------------- |
| v36    | juridiction Frozen / Active, discipline des claims                     |
| v38    | consolidation FCI, audits, intégration des couches de sûreté           |
| v38.5x | intégration ResGold, hygiene des imports, synchronisation des rapports |

La version v38.5x ne modifie pas la doctrine centrale :

> `RHClaimed = false`.

Elle renforce surtout la cohérence entre le build, les rapports, les audits et les fichiers de gouvernance.

---

## 5. Règle d’import

L’architecture doit rester un DAG doctrinal.

Vue simplifiée :

```text
Mathlib
  │
  ▼
Core/ ── Finite/ ── FiniteDefect/ ── Spectral/
  │
  ├── FunctionalFoundation/
  ├── Geometry/
  ├── Residue/
  ├── Meta/
  └── EpistemicDiscipline/
        │
        ▼
Logic/ExplicitFormula/
        │
        ▼
AnalyticHorizon/
        │
        ▼
Logic/H3/
        │
        ▼
Logic/Lock3/
```

La règle pratique est :

* les couches finies peuvent être utilisées par les couches analytiques ;
* les couches analytiques ne doivent jamais être réimportées dans le noyau fini ;
* les fichiers Frozen ne doivent pas absorber d’obligation Active en silence ;
* les claims globaux restent bloqués par les gardes doctrinaux.

---

## 6. Arborescence canonique

Cette section décrit l’arborescence des fichiers `lean` réelle du dépôt à l’état `v38.5.0 / ResGold intégré`, d’après :

```text
tree -P '*.lean' -I 'Attic' --gitignore --prune --filesfirst
```

`Attic/` est volontairement exclu de cette vue : il s’agit d’une zone d’archive, non du chemin canonique courant.

```text
.
├── lakefile.lean
└── lean
    ├── CouretUnification.lean
    └── CouretUnification
        ├── Active.lean
        ├── All.lean
        ├── Frozen.lean
        ├── ResGold.lean
        ├── SophieGermainUmbrella.lean
        ├── Active
        │   ├── PrimeSideRealClosure.lean
        │   └── TraceObjectEnriched.lean
        ├── Analytic
        │   ├── AbelTailCompare.lean
        │   ├── AbelTailCore.lean
        │   ├── GammaFactor.lean
        │   ├── Integration.lean
        │   ├── VerifiedIntervals.lean
        │   └── ZeroDensityAxioms.lean
        ├── AnalyticHorizon
        │   ├── A8ArchimedeanAbsorption.lean
        │   ├── ActiveLayerFullAudit.lean
        │   ├── AdmissibleSigmaBand.lean
        │   ├── ArchimedeanDigammaCertificate.lean
        │   ├── ArchimedeanTorsionCertificate.lean
        │   ├── DefectOperator30.lean
        │   ├── Det2Obligations.lean
        │   ├── Det2TransportCertificate.lean
        │   ├── Det2Transport.lean
        │   ├── ExplicitFormulaBridgeAudit.lean
        │   ├── L6Stirling.lean
        │   ├── LegendreChannelCalibration.lean
        │   ├── MomentRigidity30.lean
        │   ├── PerturbedSpectralIsolation.lean
        │   ├── PhaseStabilityTargets.lean
        │   ├── ProtectedMinusTraceTargets.lean
        │   ├── SoinInterface.lean
        │   ├── TorsionZeroTransferCertificate.lean
        │   ├── TraceFormulaTargets.lean
        │   └── ZeroCountingCertificate.lean
        ├── Audit
        │   └── PrintAxioms.lean
        ├── Core
        │   ├── Arithmetic.lean
        │   ├── CarlemanUniqueness.lean
        │   ├── CayleyConnected.lean
        │   ├── CayleyG30.lean
        │   ├── CayleySpectrum.lean
        │   ├── CenteredCoordinates.lean
        │   ├── CenteredEigenspace.lean
        │   ├── CenteredSpace30.lean
        │   ├── CharacterLemmas.lean
        │   ├── Characters30Bridge.lean
        │   ├── Characters30.lean
        │   ├── CharParity30.lean
        │   ├── CharPoly.lean
        │   ├── Classification63Detail.lean
        │   ├── Classification63.lean
        │   ├── ComponentSpectrum.lean
        │   ├── Convolution30.lean
        │   ├── CouretDocumentaryCertificate.lean
        │   ├── CouretMinimalPackage.lean
        │   ├── CouretPowerCertificate.lean
        │   ├── CRTEquiv.lean
        │   ├── CRTTransport.lean
        │   ├── DefectProjection.lean
        │   ├── Doctrine.lean
        │   ├── ExceptionalTriplets.lean
        │   ├── FiniteCore.lean
        │   ├── FiniteOperator.lean
        │   ├── FormuleLk.lean
        │   ├── Fourier30.lean
        │   ├── HarmonicCertificate.lean
        │   ├── IntegralSpectrum.lean
        │   ├── InvariantE.lean
        │   ├── Kurtosis.lean
        │   ├── Lambda.lean
        │   ├── LMFDBAlignment.lean
        │   ├── MersenneMod30.lean
        │   ├── Mod30.lean
        │   ├── MultiplicityUniqueness.lean
        │   ├── OddDimComplexObstruction.lean
        │   ├── ParsevalL5.lean
        │   ├── Parseval.lean
        │   ├── SophieGermainHecke.lean
        │   ├── SophieGermain.lean
        │   ├── SophieGermainMod30.lean
        │   ├── SophieGermainTowerLift.lean
        │   ├── SpectralGap.lean
        │   ├── SpectralMoments.lean
        │   ├── SpectralProfile.lean
        │   ├── SymplecticObstruction.lean
        │   ├── TCAutoInverse.lean
        │   ├── TraceRecurrence.lean
        │   ├── TripletCandidateInterface.lean
        │   ├── TripletDocumentaryCertificate.lean
        │   ├── TripletDocumentaryPowerInterface.lean
        │   ├── TripletExceptionalPredicate.lean
        │   ├── TripletHarmonicSpectrum.lean
        │   ├── TripletLocalExceptionalCandidate.lean
        │   ├── TripletPowerSpectrum.lean
        │   ├── TripletQuadraticCandidateCertificate.lean
        │   ├── TripletQuadraticIntegralCandidateInterface.lean
        │   ├── TripletRawIntegralCriterion.lean
        │   ├── TripletRawQuadraticConsistency.lean
        │   ├── TripletSpectrum.lean
        │   ├── TripletToFiniteSpectrum.lean
        │   ├── U30.lean
        │   └── UnitsBridge.lean
        ├── Empirical
        │   ├── SophieGermainExpected.lean
        │   └── SophieGermainTransitions.lean
        ├── EpistemicDiscipline
        │   ├── BridgeStatus.lean
        │   └── DoctrinalInvariants.lean
        ├── Experimental
        │   ├── TowerLift.lean
        │   └── TowerLift
        │       └── ToyModelSpec.lean
        ├── FCI
        │   ├── CausalSupportImmunity.lean
        │   ├── CausalSupportMeasureBridge.lean
        │   ├── FCI.lean
        │   ├── ModThirtyCheckerBridge.lean
        │   └── ModThirtyChecker.lean
        ├── Finite
        │   ├── Defect.lean
        │   └── Foundations.lean
        ├── FiniteDefect
        │   └── T1_to_T7.lean
        ├── FunctionalFoundation
        │   ├── DiscreteConnection.lean
        │   └── DiscretePaths.lean
        ├── Logic
        │   ├── C3Weak_Gram.lean
        │   ├── C3Weak.lean
        │   ├── ChiralityFinite.lean
        │   ├── ChiralityLinear.lean
        │   ├── CriticalLineTransferSpec.lean
        │   ├── Doctrine.lean
        │   ├── EulerBridgeInfiniteCompat.lean
        │   ├── EulerBridgeInfinite.lean
        │   ├── EulerBridgeInfiniteReal.lean
        │   ├── FEnriched30.lean
        │   ├── FEnrichedSpec.lean
        │   ├── L10NoGoTheorem.lean
        │   ├── L6Analytic.lean
        │   ├── L6Bridge.lean
        │   ├── L6Interface.lean
        │   ├── L6RatioEstimateDerived.lean
        │   ├── OpenLocks.lean
        │   ├── C2
        │   │   ├── Umbrella.lean
        │   │   └── Window.lean
        │   ├── ExplicitFormula
        │   │   ├── ArchimedeanKernelBound.lean
        │   │   ├── ArchimedeanSide.lean
        │   │   ├── ArithmeticWeight.lean
        │   │   ├── ExplicitFormulaBridge.lean
        │   │   ├── PrimeSideCompactSupport.lean
        │   │   ├── PrimeSide.lean
        │   │   ├── StatusFlags.lean
        │   │   ├── TestFunctions.lean
        │   │   ├── TestPair.lean
        │   │   ├── TraceObject.lean
        │   │   ├── ZeroCounting.lean
        │   │   └── ZeroSideObligation.lean
        │   ├── H3
        │   │   ├── AbelWeightedBound.lean
        │   │   ├── AlgebraTC.lean
        │   │   ├── ArithmeticBridge.lean
        │   │   ├── C2Restricted.lean
        │   │   ├── C3Weak_Gram.lean
        │   │   ├── C3Weak.lean
        │   │   ├── CriticalLineTransferSpec.lean
        │   │   ├── FiniteSpectralAPI.lean
        │   │   ├── FunctionalFoundation.lean
        │   │   ├── H3TestSpace.lean
        │   │   ├── HPCertificate.lean
        │   │   ├── L10Bridge.lean
        │   │   ├── L10_MassPersistence.lean
        │   │   ├── Lemma7Residual.lean
        │   │   ├── LocalFactor.lean
        │   │   ├── LocalSquarefreeBridge.lean
        │   │   ├── Lock2Conditional.lean
        │   │   ├── MoebiusBridge.lean
        │   │   ├── ParityGamma30.lean
        │   │   ├── PhaseBCompositionCouretEta.lean
        │   │   ├── PhaseBCompositionCouret.lean
        │   │   ├── PhaseBCompositionCouretZeta.lean
        │   │   ├── PhaseBComposition.lean
        │   │   ├── RigidityParams.lean
        │   │   ├── RouteC.lean
        │   │   ├── SpectralBridge.lean
        │   │   ├── SpectralSpatial.lean
        │   │   ├── SquarefreeDensity.lean
        │   │   ├── SquarefreeSupport.lean
        │   │   ├── T5Weak.lean
        │   │   └── ZeroMatching.lean
        │   ├── Lock3
        │   │   ├── LocalDebiasing.lean
        │   │   ├── ProtectedTraceGate.lean
        │   │   └── RHGuard.lean
        │   └── TimeBridge
        │       ├── B2Calibration.lean
        │       ├── Basic.lean
        │       ├── BostConnesMod30Spec.lean
        │       └── ModularFlowSpec.lean
        ├── Meta
        │   ├── AuditHints.lean
        │   ├── Doctrine.lean
        │   ├── Layer.lean
        │   ├── ProofJurisdiction.lean
        │   └── SnapshotSentinel.lean
        ├── Numerics
        │   ├── ScanSummary.lean
        │   └── UseScanSummary.lean
        ├── Release
        │   └── ReleaseManifest.lean
        ├── ResGold
        │   ├── L0_LocalLemma.lean
        │   ├── L1_ConductorOne.lean
        │   ├── L2_MertensAsymptotic.lean
        │   └── Status.lean
        ├── Residue
        │   ├── ClosureTC.lean
        │   ├── CycleCoset.lean
        │   ├── PuncturedKlein30.lean
        │   ├── SGShiftSpectrum.lean
        │   ├── SGShiftSqrt2.lean
        │   ├── TorsionLift210.lean
        │   └── Bridge
        │       └── DefectOperatorBridge.lean
        ├── Spectral
        │   ├── FiniteCore.lean
        │   └── T2Gap.lean
        └── Speculative
            ├── AnalogyMTF.lean
            └── Ontology.lean
```

### 6.1 Sous-arbres Lean principaux

Pour la lecture architecturale, les sous-arbres Lean se regroupent ainsi :

| Sous-arbre              | Rôle architectural                                                         |
| ----------------------- | -------------------------------------------------------------------------- |
| `Active/`               | extensions actives de contrat, notamment côté réel / enrichi               |
| `Analytic/`             | outils analytiques généraux, gamma, intégration, intervalles, densité zéro |
| `AnalyticHorizon/`      | obligations et certificats analytiques typés                               |
| `Audit/`                | instrumentation Lean d’audit, notamment impression d’axiomes               |
| `Core/`                 | noyau fini modulo 30 et objets spectraux finis                             |
| `Empirical/`            | encodage Lean de résultats ou attentes empiriques                          |
| `EpistemicDiscipline/`  | invariants doctrinaux et statuts de pont                                   |
| `Experimental/`         | prototypes expérimentaux, notamment TowerLift                              |
| `FCI/`                  | Fail-Close Integrity, fermé localement dans son périmètre courant          |
| `Finite/`               | fondations finies minimales                                                |
| `FiniteDefect/`         | théorèmes finis T1 à T7                                                    |
| `FunctionalFoundation/` | chemins discrets et connexions discrètes                                   |
| `Logic/`                | couches conditionnelles, H3, formule explicite, Lock3, TimeBridge          |
| `Meta/`                 | doctrine, couches, juridiction, sentinelles d’audit                        |
| `Numerics/`             | résumés numériques encodés côté Lean                                       |
| `Release/`              | manifeste de release                                                       |
| `ResGold/`              | intégration ResGold v38.5                                                  |
| `Residue/`              | structures résiduelles, torsion, shifts Sophie Germain                     |
| `Spectral/`             | façade spectrale finie                                                     |
| `Speculative/`          | analogies et ontologie, explicitement non probatoire                       |

### 6.2 Scripts réellement présents

Les scripts réellement présents dans le dépôt sont :

```text
scripts/audit_doctrine.sh
scripts/audit_orphans.sh
scripts/audit_reachability.sh
scripts/audit_structure_collisions.sh
scripts/audit_v36.0.sh
scripts/audit_v36.1.sh
scripts/audit_v36.9.sh
scripts/audit_v36_torsion.sh
scripts/audit_v37_aggregation.sh
scripts/channel_bridge_v3.py
scripts/check_frozen_invariants.sh
scripts/compute_moments.py
scripts/evidence_veff.py
scripts/gate_no_frozen_imports_residue.sh
scripts/lintWhitespace.sh
scripts/run_all_tests.sh
scripts/SG_HL_matrix_calculation.py
scripts/sorry_audit.sh
scripts/test_cayley_connectivity.py
scripts/test_euler_defect.py
scripts/test_finite_core.py
scripts/test_guinand_weil.py
scripts/test_klmn_bound.py
scripts/test_negative_results.py
scripts/test_parseval_tower.py
scripts/test_sigma_matching.py
scripts/test_vchi_channels.py
scripts/validate_pack.sh
```

Sous-répertoires de scripts :

```text
scripts/lib/lean_strip_comments.awk
scripts/towerlift/delta7_sophie_germain.py
scripts/towerlift/dimensional_test.py
scripts/towerlift/information_analysis.py
scripts/towerlift/README.md
scripts/towerlift/sophie_germain_analysis.py
scripts/towerlift/toymodel_validation.py
```

### 6.3 Conséquence documentaire

Les anciens noms suivants ne doivent pas être cités comme scripts actuels, sauf s’ils sont réintroduits dans le dépôt :

```text
scripts/audit_finitecore.sh
scripts/audit_imports.sh
scripts/audit_v36_full.sh
scripts/build_frozen.sh
scripts/check_jurisdiction.sh
scripts/seal_v36.sh
```

Ils peuvent rester mentionnés uniquement comme anciens noms, scripts historiques, ou
équivalents conceptuels remplacés par les scripts actuels.

La liste mainteneur actuelle doit donc s’appuyer sur :

```text
make build
make report
scripts/validate_pack.sh
scripts/check_frozen_invariants.sh
scripts/audit_doctrine.sh
scripts/audit_reachability.sh
scripts/audit_structure_collisions.sh
scripts/sorry_audit.sh
scripts/gate_no_frozen_imports_residue.sh
```

en fonction des cibles réellement déclarées dans le `Makefile`.

---

## 7. Couche `Core/`

### 7.1 Rôle

`Core/` contient le noyau fini exact du programme.

Il formalise les structures modulo 30, les objets finis associés, les tables, les classifications,
les opérateurs finis, les caractères et les spectres finis.

Il ne contient pas de preuve globale de RH, de Hilbert–Pólya, de formule explicite complète, ni d’identité det₂ ↔ ξ.

### 7.2 Objets acceptés dans `Core/`

`Core/` peut contenir :

* résidus modulo 30 ;
* unités modulo 30 ;
* groupe fini `G30`;
* équivalences finies ;
* tables de multiplication et d’inversion ;
* fonctions finies sur `G30`;
* espace centré de dimension 7 ;
* invariant géométrique `λ = 1 / √7`, interne au simplexe centré ;
* convolution finie ;
* caractères finis ;
* Fourier fini ;
* Parseval / Plancherel finis ;
* matrices finies ;
* spectres finis ;
* polynômes caractéristiques finis ;
* classifications exactes ;
* défaut spectral fini ;
* signatures modulaires ;
* chiralité finie ;
* exemples calculables par énumération ou `native_decide`.

### 7.3 Objets refusés dans `Core/`

`Core/` ne doit pas contenir :

* ζ(s) ou ξ(s) comme objets analytiques globaux ;
* `det₂` comme identité globale ;
* produit d’Euler global ;
* formule explicite globale ;
* formule de trace globale ;
* Hilbert–Pólya global ;
* GUE comme résultat mathématique ;
* revendication RH ;
* limite asymptotique non finie ;
* import depuis `Logic/H3/`, `Logic/Lock3/`, `AnalyticHorizon/` ou `Bridges/`.

### 7.4 Critère d’admission

Un fichier appartient à `Core/` seulement si toutes les réponses suivantes sont positives :

1. Les objets manipulés sont finis ou explicitement décidables.
2. La preuve ne dépend pas d’une fermeture analytique globale.
3. Le fichier ne revendique aucun résultat sur les zéros de ζ.
4. Le fichier ne dépend pas d’un pont det₂ ↔ ξ.
5. Le fichier ne dépend pas de H3, Lock3 ou AnalyticHorizon.
6. Les imports restent dans Mathlib et les couches finies autorisées.
7. Les éventuels marqueurs techniques sont explicitement documentés.

---

## 8. Couche `Logic/ExplicitFormula/`

`Logic/ExplicitFormula/` porte le contrat typé de formule explicite.

Son rôle n’est pas de déclarer la formule explicite fermée, mais de fournir une interface où
les obligations futures peuvent être déposées.

Cette couche contient notamment :

* objets abstraits de trace ;
* côté premier ;
* côté zéros ;
* bornes archimédiennes ;
* drapeaux de statut ;
* ponts architecturaux ;
* absorption archimédienne en annexe.

Statut :

> structurel, contractuel, non assimilable à une preuve globale de RH.

---

## 9. Couche `AnalyticHorizon/`

`AnalyticHorizon/` contient les certificats analytiques typés.

Ces fichiers localisent les dettes analytiques sans les déclarer payées.

Ils couvrent notamment :

* pont archimédien ;
* comptage des zéros ;
* audit de formule explicite ;
* transport det₂ ;
* interface Soin ;
* torsion archimédienne ;
* transfert torsion-zéros ;
* audit de cohérence Active ;
* cibles de formule de trace ;
* rigidité de moments ;
* opérateurs de défaut ;
* calibration de canaux ;
* isolation spectrale perturbée.

Statut :

> Active.
> Les obligations sont nommées, typées et auditables.
> Elles ne sont pas automatiquement démontrées.

---

## 10. Couche `Logic/H3/`

`Logic/H3/` constitue le mur analytique central du programme.

Cette couche organise les branches conditionnelles qui relient le noyau fini à des objets analytiques plus ambitieux.

Elle contient notamment :

* paramètres de rigidité ;
* API spectrale finie ;
* algèbre `A_TC`;
* espaces de test ;
* rigidité faible ;
* ponts arithmétiques ;
* résidu critique ;
* propagation conditionnelle ;
* zéro matching ;
* localisation de Schur ;
* ponts de type Cauchy–Schwarz ;
* blocs spectraux ;
* densité squarefree ;
* route C ;
* composition Phase B.

Statut :

> conditionnel / ouvert.
> H3 ne doit pas être présenté comme fermé.

La règle courte est :

> H3 est une architecture de fermeture possible, pas une fermeture acquise.

---

## 11. Couche `Logic/Lock3/`

`Logic/Lock3/` représente le verrou final.

Elle contient les gardes empêchant de transformer une structure conditionnelle en revendication RH.

Elle documente notamment :

* protection de trace ;
* garde RH ;
* débiaisage local.

Statut :

> ouvert.
> Aucun fichier de cette couche ne doit être utilisé pour déclarer RH prouvée.

---

## 12. Couche `FCI/`

`FCI/` signifie **Fail-Close Integrity**.

En v38.5x, cette couche est fermée localement dans son périmètre actuel.

Modules présents :

* `FCI.lean`
* `ModThirtyChecker.lean`
* `ModThirtyCheckerBridge.lean`
* `CausalSupportImmunity.lean`
* `CausalSupportMeasureBridge.lean`

Doctrine FCI :

* le checker ne force jamais une autorisation globale ;
* un état critique force le refus fail-close ;
* une anomalie force la modulation ;
* la Gate agit sur le support causal de l’action, pas sur la conscience ou l’intention ;
* la Gate est un témoin mécanique délégué, non un observateur conscient ;
* les reconstructions analytiques plus fortes sont différées à des bridges ultérieurs.

Point important :

> Le sous-arbre `FCI/Math/...` appartient à la roadmap s’il n’est pas réellement intégré comme fichiers Lean.
> Il ne doit pas être listé comme arborescence actuelle tant qu’il n’existe pas dans le dépôt.

---

## 13. `ResGold.lean`

`ResGold.lean` appartient à la stabilisation v38.5x.

Son rôle est double :

1. importer la chaîne locale ResGold `L0 → L1 → L2`, désormais fermée localement ;
2. exposer les statuts et invariants empêchant toute surpromotion globale.

ResGold fournit donc une intégration locale démontrée et une gouvernance doctrinale.
Il ne transforme pas un verrou ouvert en théorème global fermé.

La règle de lecture est :

> ResGold renforce l’auditabilité du dépôt.
> ResGold ne transforme pas un verrou ouvert en théorème fermé.
> ResGold conserve `RHClaimed = false`.

---

## 14. `Meta/`, `EpistemicDiscipline/`, `Residue/`

### 14.1 `Meta/`

`Meta/Doctrine.lean` porte la doctrine générale du dépôt.

Il définit ou centralise les notions de couche, statut, identité de fichier et garde anti-claim.

C’est la version doctrinale à privilégier lorsqu’il existe plusieurs fichiers `Doctrine.lean`.

### 14.2 `EpistemicDiscipline/`

Cette couche encode la discipline de raisonnement :

* pas de glissement local → global ;
* pas de promotion d’un statut `[H]` en `[D]` ;
* pas de claim RH implicite ;
* pas de confusion entre preuve, mesure, heuristique et programme ouvert.

### 14.3 `Residue/`

`Residue/` fournit une fondation résiduelle utilisée par les couches supérieures.

Elle peut servir de base à des certificats ou audits, mais ne ferme pas par elle-même les ponts analytiques globaux.

---

## 15. `Attic/`

`Attic/` contient les modules archivés.

Un fichier dans `Attic/` n’est pas considéré comme appartenant au chemin canonique, sauf import explicite et assumé.

Règles :

* ne pas citer `Attic/` comme preuve active ;
* ne pas fonder un claim de release sur `Attic/` ;
* ne pas réintroduire un fichier d’archive sans audit d’import ;
* conserver l’historique utile, mais distinguer archive et couche active.

---

## 16. Validation, audits et rapports

La validation officielle du dépôt passe par le `Makefile`.

Aucun script externe ne doit être cité dans ce document s’il n’est pas appelé par une cible `make` ou réellement présent dans `scripts/`.

### 16.1 Cibles de build

```makefile
make build
make build-all
```

* `make build` exécute `lake build`.
* `make build-all` exécute `lake build CouretUnification.All`.

### 16.2 Génération de l’arborescence

```makefile
make tree
```

Cette cible génère :

```text
build_reports/ARCHITECTURE-tree.txt
```

Elle exécute :

```sh
tree --gitignore
```

### 16.3 Build complet avec log

```makefile
make build-log-all
```

Cette cible exécute :

```sh
lake build CouretUnification.All
```

et produit notamment :

```text
build_reports/build.log
build_reports/errors_unique.txt
build_reports/warnings_unique.txt
```

### 16.4 Audits internes sans script externe

Ces audits sont définis directement dans le `Makefile`.

```makefile
make audit-imports
make audit-axioms
make audit-sorries
make audit-warnings
make audit-axiom-declarations
make audit-true-statements
make audit-invariants
```

Détail :

| Cible                      | Rôle                                                                             | Sortie principale          |
| -------------------------- | -------------------------------------------------------------------------------- | -------------------------- |
| `audit-imports`            | détecte les imports `CouretUnification.*` cassés                                 | `broken_imports.txt`       |
| `audit-axioms`             | build du module Lean `CouretUnification.Audit.PrintAxioms`                       | `audit-axioms.log`         |
| `audit-sorries`            | extrait les déclarations utilisant `sorry` depuis le build log                   | `sorries_declarations.txt` |
| `audit-warnings`           | extrait les warnings non liés aux `sorry`                                        | `warnings_non_sorry.txt`   |
| `audit-axiom-declarations` | grep des déclarations `axiom` dans le code                                       | `axiom_declarations.txt`   |
| `audit-true-statements`    | repère les théorèmes de forme `: True := ...`                                    | `true_statements.txt`      |
| `audit-invariants`         | vérifie les invariants `RHClaimed`, `HilbertPolyaClaimed`, `Det2IdentityClaimed` | `invariants.txt`           |

### 16.5 Audits via scripts externes réels

Ces cibles appellent des scripts présents dans `scripts/`.

```makefile
make audit-collisions
make audit-collisions-basic
make check-frozen
make gate-frozen
make audit-orphans
make audit-reachability
make audit-doctrine
make audit-scripts
make audit-v37
```

Correspondance exacte :

| Cible `make`             | Script appelé                                    | Sortie principale          |
| ------------------------ | ------------------------------------------------ | -------------------------- |
| `audit-collisions`       | `scripts/audit_structure_collisions.sh`          | `collisions.log`           |
| `audit-collisions-basic` | `scripts/audit_structure_collisions.sh --basic`  | `collisions.log`           |
| `check-frozen`           | `scripts/check_frozen_invariants.sh`             | `frozen_invariants.log`    |
| `gate-frozen`            | `scripts/gate_no_frozen_imports_residue.sh`      | `gate_frozen.log`          |
| `audit-orphans`          | `scripts/audit_orphans.sh`                       | `audit_orphans.log`        |
| `audit-reachability`     | `scripts/audit_reachability.sh`                  | `audit_reachability.log`   |
| `audit-doctrine`         | `scripts/audit_doctrine.sh lean`                 | `audit_doctrine.log`       |
| `audit-scripts`          | `scripts/sorry_audit.sh`, exécuté depuis `lean/` | `sorry_audit_detailed.log` |
| `audit-v37`              | `scripts/audit_v37_aggregation.sh`               | `audit_v37.log`            |

### 16.6 Méta-audit complet

```makefile
make audit-all
```

Cette cible lance :

```text
build-log-all
audit-imports
audit-axioms
audit-sorries
audit-warnings
audit-axiom-declarations
audit-true-statements
audit-invariants
audit-collisions
check-frozen
gate-frozen
audit-orphans
audit-reachability
audit-doctrine
audit-scripts
```

Elle ne lance pas automatiquement :

```text
audit-v37
validate
test-all
python-moments
python-gw
python-tests
python-defect
```

Ces cibles restent disponibles séparément.

### 16.7 Validation pack

```makefile
make validate
```

Cette cible exécute :

```sh
bash scripts/validate_pack.sh
```

Elle sert à vérifier la cohérence de pack documentaire / release.

Point de vigilance :

> Les anciens documents legacy peuvent bloquer `validate_pack.sh` s’ils contiennent des formes sensibles comme `RHClaimed` `=` `true`.
> Lorsqu’un document legacy doit seulement citer une forme interdite, il faut l’écrire de manière non ambiguë mais
  non capturée par les greps de validation, par exemple en séparant les tokens dans le texte explicatif.

### 16.8 Tests globaux

```makefile
make test-all
```

Cette cible exécute :

```sh
cd scripts && bash run_all_tests.sh
```

### 16.9 Scripts Python

```makefile
make python-moments
make python-gw
make python-tests
make python-defect
```

Correspondance :

| Cible `make`     | Script appelé                        |
| ---------------- | ------------------------------------ |
| `python-moments` | `scripts/compute_moments.py`         |
| `python-gw`      | `python/guinand_weil_channelwise.py` |
| `python-tests`   | `python/couret_full_tests.py`        |
| `python-defect`  | `python/couret_defect_lab.py`        |

Ces scripts appartiennent à l’écosystème expérimental / reporting.
Ils ne doivent pas être confondus avec une certification Lean.

### 16.10 Rapport consolidé

```makefile
make report
```

Cette cible exécute :

```text
tree
audit-all
```

puis imprime un résumé doctrinal v38.x comprenant :

* état du build `CouretUnification.All` ;
* nombre de déclarations utilisant `sorry` ;
* nombre de warnings non-sorry ;
* nombre d’imports cassés ;
* nombre d’axiomes déclarés ;
* nombre de théorèmes de forme `: True := ...`.

Les rapports sont placés dans :

```text
build_reports/
```

### 16.11 Snapshot

```makefile
make snapshot
```

Cette cible exécute d’abord `make report`, puis copie les rapports dans :

```text
build_reports/snapshots/YYYY-MM-DD/
```

### 16.12 Doctrine check rapide

```makefile
make doctrine-check
```

Cette cible lance :

```text
audit-axiom-declarations
audit-true-statements
audit-invariants
check-frozen
```

Elle sert à vérifier rapidement les points doctrinaux sensibles avant commit.

---

## 17. Critères minimaux avant commit

Avant un commit de maintenance ordinaire :

```sh
make build-all
make report
```

Avant une livraison ou une bascule majeure :

```sh
make clean-reports
make report
make snapshot
```

Avant une correction spécifiquement doctrinale :

```sh
make doctrine-check
make validate
```

Avant une intervention sur les imports :

```sh
make audit-imports
make audit-reachability
make audit-orphans
```

Avant une intervention sur les couches Frozen / Active :

```sh
make check-frozen
make gate-frozen
make audit-doctrine
```

---

## 18. Scripts explicitement reconnus par l’architecture

À l’état du `Makefile` courant, les scripts externes officiellement appelés sont :

```text
scripts/audit_structure_collisions.sh
scripts/check_frozen_invariants.sh
scripts/gate_no_frozen_imports_residue.sh
scripts/audit_orphans.sh
scripts/audit_reachability.sh
scripts/audit_doctrine.sh
scripts/sorry_audit.sh
scripts/audit_v37_aggregation.sh
scripts/validate_pack.sh
scripts/run_all_tests.sh
scripts/compute_moments.py
python/guinand_weil_channelwise.py
python/couret_full_tests.py
python/couret_defect_lab.py
```

Les noms suivants peuvent être présents comme scripts legacy ou historiques,
mais ne sont pas des scripts officiels de validation courante s’ils ne sont
pas appelés par le `Makefile` ou par `make report` :

```text
scripts/audit_finitecore.sh
scripts/audit_v36_full.sh
scripts/audit_v36_torsion.sh
scripts/audit_soin.sh
scripts/audit_v36.9.sh
scripts/build_frozen.sh
scripts/check_jurisdiction.sh
scripts/seal_v36.sh
```

Ces noms peuvent appartenir à l’historique documentaire v36 ou à d’anciennes notes ou anciens scripts, ils peuvent êtres
appelés par le `Makefile` fourni avec des commandes dédiées (héritage et tests).

---

## 19. Sorries, axiomes et obligations

La politique générale est :

* aucun `sorry` ne doit être banalisé ;
* un `sorry` peut être toléré seulement s’il est explicitement localisé, documenté et doctrinalement classé ;
* un `axiom` nouveau doit être traité comme une dette majeure ou refusé ;
* les axiomes Mathlib standards ne sont pas assimilés à des axiomes projet ;
* les obligations Active ne sont pas des preuves.

Le rapport courant du dépôt fait autorité pour le comptage exact.

Si un document mentionne un nombre de `sorry`, il doit préciser :

* la date ou version du rapport ;
* s’il s’agit du build complet ou d’un sous-arbre ;
* s’il distingue les sorries doctrinaux, techniques et Active ;
* si `Attic/` est inclus ou exclu.

Formulation recommandée :

> Le nombre exact de `sorry` est un indicateur de rapport, non un invariant doctrinal stable.
> L’invariant stable est que les obligations non fermées doivent rester visibles, localisées et non promues en preuve.

---

## 20. Mots-clés sensibles

Les mots-clés suivants sont sensibles dans les couches finies :

```text
RHClaimed                   = true
HilbertPolyaClaimed         = true
SpectralCoincidenceClaimed  = true
ExplicitFormulaClosed       = true
Det2IdentityClaimed         = true
RiemannVonMangoldtClaimed   = true
CandidateCClaimed           = true
MotherTheoremClaimed        = true
```

Dans `Core/`, les familles suivantes doivent être évitées sauf justification strictement documentaire et auditée :

```text
riemannZeta
completedRiemannZeta
det2
EulerProduct
eulerProduct
HilbertPolya
explicitFormula
GUE
Trainable
```

---

## 21. Roadmap non intégrée

Les éléments suivants peuvent appartenir à une roadmap, mais ne doivent pas être présentés comme fichiers actuels tant qu’ils ne sont pas réellement présents dans le dépôt :

```text
FCI/Math/Measure/Interval.lean
FCI/Math/Hilbert/L2Interval.lean
FCI/Math/Spectral/Staircase.lean
FCI/Math/Spectral/AffineSubspace.lean
FCI/Math/Spectral/Delta3.lean
FCI/Math/Invariants/SpectralRigidity.lean
FCI/Math/Checker/Invariants/SpectralRigidityGate.lean
RMTGate.lean
EADXPipeline.lean
GoldenSet.lean
```

La règle officielle est :

> Une roadmap peut être décrite, mais elle ne doit pas polluer l’arborescence canonique.

---

## 22. Règles de modification de ce document

Toute modification de `docs/ARCHITECTURE.md` doit préserver :

1. `RHClaimed = false`.
2. La distinction Frozen / Active.
3. La séparation fini / analytique global.
4. La distinction réalité du dépôt / roadmap.
5. La non-promotion des obligations Active.
6. La fermeture locale FCI seulement dans son périmètre réel.
7. L’intégration de ResGold comme couche de gouvernance, non comme fermeture RH.
8. La compatibilité avec `make report`.

Avant commit, vérifier :

```text
lake build
make report
make validate
```

Si un ancien document legacy contient volontairement une chaîne sensible séparée pour éviter les faux positifs, l’intention doit être documentée localement.

---

## 23. Formulation officielle courte

Pour README, release notes ou communication externe :

> Couret–Unification v38.5x est un dépôt Lean 4 structuré autour d’un noyau fini modulo 30, de couches conditionnelles analytiques explicitement séparées, d’une discipline épistémique Frozen / Active, et d’une couche FCI fail-close localement fermée.
> La version `v38.5.0 ResGold` consolide les invariants et les rapports de gouvernance.
> Aucune preuve de l’Hypothèse de Riemann, de Hilbert–Pólya, d’une identité det₂ ↔ ξ, ni d’une formule explicite globale fermée n’est revendiquée.

---

## 24. Formulation mainteneur

> Ce dépôt n’est pas une annonce de fermeture globale.
> C’est une architecture de séparation : le fini est prouvé, le conditionnel est typé, l’ouvert est gardé ouvert, et les claims sont empêchés par construction.

---

*Document maintenu dans `docs/ARCHITECTURE.md`.*
*État : v38.5x — ResGold intégré.*
*Invariant final : `RHClaimed = false`.*
*Pour Bernard Couret (1928–1999, Istres).*
