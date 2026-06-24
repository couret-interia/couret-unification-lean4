# État Lean 4 — Couret-Unification v38.5.13

## Invariant général

Le dépôt `CouretUnification` formalise en Lean 4 un noyau arithmético-spectral fini autour de la structure modulo 30, avec une architecture stratifiée vers des couches analytiques supérieures.

Le projet ne revendique aucune preuve globale.

```text
RHClaimed = false
HilbertPolyaClaimed = false
Det2IdentityClaimed = false
GoldbachProofClaimed = false
EngineeringVerdictClaimed = false
ScopeExpansionClaimed = false
```

La règle de lecture demeure :

> le noyau fini est exact et compilé ;
> les couches analytiques sont séparées ;
> le pont global reste ouvert.

---

## Toolchain

État de référence partagé :

```text
Lean    : 4.29.1
Mathlib : 4.29.1
```

La source de vérité opérationnelle reste :

```bash
cat lean-toolchain
lake-manifest.json
```

Aucune migration Lean / Mathlib ne doit être supposée souhaitable sans décision explicite et audit de compilation.

---

## Couches principales

Le dépôt est organisé par couches :

```text
CouretUnification.Frozen
CouretUnification.Active
CouretUnification.All
```

### `Frozen`

Couche fermée, rejouable, sans `sorry`.

État partagé :

```bash
lake build CouretUnification.Frozen
```

Résultat observé :

```text
Build completed successfully
0 sorry
```

Rôle : conserver les modules stabilisés, principalement le noyau fini exact, les fermetures arithmétiques prouvées et les interfaces gelées.

### `Active`

Couche de travail. Elle contient les fronts analytiques, les verrous ouverts et les obligations encore documentées.

État doctrinal :

```text
Active ≠ Frozen
Active peut contenir des sorry documentés
Active ne doit pas contaminer Frozen
```

### `All`

Agrégat global du dépôt.

État partagé :

```bash
lake build CouretUnification.All
```

Résultat observé :

```text
Build completed successfully
11 sorry documentés
```

Le build `All` atteste la cohérence globale du dépôt ; il ne transforme pas les obligations ouvertes en résultats démontrés.

---

## Audit actuel

Commande canonique :

```bash
make audit-scripts
```

État confirmé :

```text
Total sorry : 11
Total axiom : 9
```

Ces nombres sont des indicateurs d’audit. Ils ne remplacent pas le registre scientifique des claims.

---

## Les 11 `sorry` documentés

Les `sorry` appartiennent aux couches actives, hors `Frozen`.

Ventilation actuelle par module :

```text
Logic/L10NoGoTheorem.lean        : 3 sorry
Logic/H3/Lemma7Residual.lean     : 1 sorry
Logic/H3/RouteC.lean             : 1 sorry
Logic/L6RatioEstimateDerived.lean: 1 sorry
AnalyticHorizon/Det2Transport.lean: 1 sorry
Analytic/GammaFactor.lean        : 4 sorry
```

Total :

```text
3 + 1 + 1 + 1 + 1 + 4 = 11
```

### Verrou central

Le verrou central est :

```text
Logic/H3/Lemma7Residual.lean
```

Statut :

```text
[O] / obligation globale
```

Il porte l’annulation du résidu sur la ligne critique et intervient dans la branche β.2 de `PhaseBComposition`.

Il ne doit pas être présenté comme fermé.

---

## Les 9 axiomes recensés

État confirmé par audit :

```text
Total axiom : 9
```

Inventaire attendu :

```text
Logic/H3/ArithmeticBridge.lean : Det2IdentifiesXi
Logic/H3/ArithmeticBridge.lean : ZeroMatching
Logic/H3/AlgebraTC.lean        : mellinConvolve_comm
Logic/H3/C2Restricted.lean     : restricted_explicit_formula_old
Logic/H3/C2Restricted.lean     : restricted_explicit_formula_holds
Logic/H3/C2Restricted.lean     : mainTermPositive_of_positiveBias
Logic/H3/RigidityParams.lean   : sigma_G_critical_pos
Logic/H3/Lock2Conditional.lean : local_bridge_to_det2_xi
Logic/H3/ZeroMatching.lean     : spectral_id_to_zero_matching
```

Interprétation :

```text
Ces axiomes appartiennent aux interfaces analytiques ou conditionnelles.
Ils ne ferment pas RH.
Ils doivent rester nommés, localisés et audités.
```

---

## C3Weak v38.5.13

Le changement doctrinal majeur de `v38.5.13` est la suppression de l’axiome local :

```lean
axiom R_sigma_linear_left ...
```

remplacé par une proposition conditionnelle nommée :

```lean
def RSigmaLinearLeftBridge : Prop :=
  ∀ (σ : ℝ) (a b : ℂ) (f g : H3TestFunction),
    ∃ (h : H3TestFunction),
      R_sigma σ h = a * R_sigma σ f + b * R_sigma σ g
```

Statut :

```text
Logic/C3Weak.lean
0 sorry
0 axiom local
bridge conditionnel explicite
Active, non Frozen strict
```

Interprétation :

```text
Lean ne suppose plus la compatibilité linéaire.
Il nomme une condition à fournir.
```

C’est une amélioration de confiance : une hypothèse admise devient une obligation visible.

---

## Frozen — modules stabilisés

État issu de `audit_proved` :

```text
Imports Frozen : 23
Theorem/lemma dans Frozen : 126
```

Imports `Frozen` recensés :

```text
CouretUnification.Core.CharacterSubgroupSums
CouretUnification.Core.G30Classification
CouretUnification.Core.G30ClassificationFromPointDefect
CouretUnification.Core.PointDefectLemma
CouretUnification.Core.QuadraticResonance

CouretUnification.Logic.ChiralityFinite
CouretUnification.Logic.ChiralityLinear
CouretUnification.Logic.EulerBridgeInfinite
CouretUnification.Logic.EulerBridgeInfiniteCompat

CouretUnification.Logic.H3.C3Weak_Gram
CouretUnification.Logic.H3.CriticalLineTransferSpec
CouretUnification.Logic.H3.LocalFactor
CouretUnification.Logic.H3.MoebiusBridge
CouretUnification.Logic.H3.SquarefreeDensityC04aClosed
CouretUnification.Logic.H3.SquarefreeDensityC04bClosed
CouretUnification.Logic.H3.SquarefreeSupport

CouretUnification.Logic.L6Bridge
CouretUnification.Logic.L6Interface
CouretUnification.Logic.OpenLocks

CouretUnification.Logic.TimeBridge.B2Calibration
CouretUnification.Logic.TimeBridge.Basic
CouretUnification.Logic.TimeBridge.ModularFlowSpec

CouretUnification.Meta.Doctrine
```

Note de statut :

```text
Un theorem Lean technique ne vaut pas automatiquement claim [D].
Un module Frozen peut contenir plusieurs résultats techniques.
Le registre scientifique reste manuel et relu.
```

---

## Audit des candidats `[D]`

Commande :

```bash
make audit-proved
```

État confirmé :

```text
Marqueurs documentaires [D]/proved : 168
Theorem/lemma Lean globaux         : 1784
Imports Frozen                     : 23
Theorem/lemma dans Frozen          : 126
```

Interprétation :

```text
1784 theorem/lemma Lean globaux = inventaire technique.
126 theorem/lemma dans Frozen = périmètre stable audité.
Cela ne signifie pas 1784 claims [D].
```

La règle est :

```text
résultat Lean compilé ≠ claim scientifique autonome
claim [D] = résultat nommé, relu, situé, et inscrit dans le registre
```

---

## Résultats formels centraux `[D]`

### 1. Sommes de caractères sur noyau quadratique

Fichier :

```text
Core/CharacterSubgroupSums.lean
```

Statut :

```text
[D-formal]
kernel-pure
0 sorry
```

Résultat : lemmas généraux de sommes de caractères sur le noyau d’un caractère d’ordre 2 dans un groupe abélien fini.

---

### 2. Lemme du défaut ponctuel

Fichier :

```text
Core/PointDefectLemma.lean
```

Statut :

```text
[D-formal]
kernel-pure
0 sorry
```

Résultat :

```text
Si G est un groupe abélien fini et χ un caractère d’ordre 2,
alors la fibre ker χ privée d’un point possède un spectre d’énergie à deux niveaux :
dominante (|ker χ| − 1)^2 sur χ,
secondaire 1 sur les autres caractères non triviaux.
```

Ligne sémantique :

```text
La forme montre : un défaut ponctuel dans une fibre quadratique crée une signature spectrale exacte.
Elle ne doit pas surdire : elle ne donne aucun résultat sur les premiers réels ni sur RH.
Hypothèse philosophique possible : une perte locale peut révéler une structure globale interne au fini.
```

La troisième ligne est retranchable sans affecter la validité mathématique.

---

### 3. Classification complète des triplets de `G₃₀`

Fichier :

```text
Core/G30Classification.lean
```

Statut :

```text
[D-computational]
native_decide
0 sorry
```

Résultat :

```text
Les 56 triplets de G₃₀ se répartissent entièrement en :
24 triplets de type Q
32 triplets de type C
aucun autre profil.
```

Profils :

```text
Type Q : spectre (9,1^6)
Type C : spectre (5,5,1^5)
```

Certification :

```text
native_decide
Lean.ofReduceBool dans la base de confiance
```

Ce n’est pas une faiblesse, mais une certification computationnelle distincte du noyau pur.

---

### 4. Pont classification ↔ défaut ponctuel

Fichier :

```text
Core/G30ClassificationFromPointDefect.lean
```

Statut :

```text
[D-formal local]
0 sorry
```

Résultat : raccord entre la classification énumérative de `G₃₀` et le mécanisme abstrait du défaut ponctuel.

---

### 5. Squarefree C-04b

Fichier :

```text
Logic/H3/SquarefreeDensityC04bClosed.lean
```

Statut :

```text
[D]
0 sorry
```

Résultat :

```text
squarefreeCount N / N → 6 / π²
```

Statut précis :

```text
fermeture asymptotique C-04b
RHClaimed = false
```

---

### 6. Squarefree C-04a

Fichier :

```text
Logic/H3/SquarefreeDensityC04aClosed.lean
```

Statut :

```text
[D]
0 sorry
```

Résultat :

```lean
∀ {N : ℕ}, 176 ≤ N → (N : ℚ) / 2 ≤ squarefreeCount N
```

Statut précis :

```text
fermeture effective C-04a
RHClaimed = false
```

Ligne sémantique :

```text
La forme montre : une densité minimale effective de squarefree au-delà de N = 176.
Elle ne doit pas surdire : elle ne ferme aucun pont det₂ ↔ ξ et ne prouve pas RH.
Hypothèse philosophique possible : une borne honnête vaut mieux qu’une promesse globale.
```

La troisième ligne est retranchable sans affecter la validité mathématique.

---

## Phase B — état Lean

Fichier principal :

```text
Logic/H3/PhaseBComposition.lean
```

Statut :

```text
architecture conditionnelle
non fermée globalement
```

Branches :

```text
α Smooth Bump      : conditionnelle à axiomes analytiques
β Pont arithmétique: ouverte / conditionnelle
γ Bridge L²        : inconditionnelle
δ Annulation bloc  : inconditionnelle
η Statut Schur     : marqueur structurel
```

La branche β.2 consomme :

```text
Lemma7Residual
```

Conclusion :

```text
PhaseBComposition organise le passage.
Elle ne le ferme pas.
```

---

## SquarefreeDensity — état final

Dossier :

```text
Logic/H3/SquarefreeDensity*
```

État :

```text
C-04a : fermé [D]
C-04b : fermé [D]
```

Modules clés :

```text
SquarefreeDensity.lean              : interface stable
SquarefreeDensityHalf.lean          : laboratoire de fermeture C-04a
SquarefreeDensityC04aClosed.lean    : façade stable C-04a
SquarefreeDensityAsymptotic.lean    : laboratoire C-04b
SquarefreeDensityC04bClosed.lean    : façade stable C-04b
```

Statut :

```text
0 sorry sur les façades fermées
RHClaimed = false
```

---

## Non-transport spectral

Résultat fini :

```text
Dans G₃₀, le type Q porte une dominance énergétique 9/15 = 3/5.
```

Statut :

```text
[D] dans le fini
```

Mais :

```text
3/5 n’est pas une densité de nombres premiers.
```

Pour les trois classes correspondantes parmi les huit classes réduites modulo 30 :

```text
densité naturelle attendue = 3/8
```

Statut :

```text
[M] / conséquence arithmétique standard selon le cadre cité
```

Conclusion :

```text
La dominance spectrale finie ne se transporte pas aux premiers réels.
```

---

## Ce qui reste ouvert

### Verrou analytique central

```text
det₂ ↔ ξ
```

Statut :

```text
[O]
```

Modules liés :

```text
Logic/H3/Lemma7Residual.lean
AnalyticHorizon/Det2Transport.lean
Logic/H3/ArithmeticBridge.lean
Logic/H3/ZeroMatching.lean
```

### Zéros / appariement global

```text
ZeroMatching
```

Statut :

```text
[O] / conditionnel
```

### Hilbert–Pólya

```text
HilbertPolyaClaimed = false
```

Statut :

```text
horizon nommé
non revendiqué
```

### RH

```text
RHClaimed = false
```

Statut :

```text
aucune preuve
aucune fermeture globale
aucune revendication directe ou indirecte
```

---

## État documentaire associé

Documents récents ajoutés ou stabilisés :

```text
docs/PRESENTATION_PROGRAMME.md
docs/registry/RESULTATS_D_FORMELS.md
docs/arxiv/ARTICLE_titre_et_introduction_FR.md
docs/notes-techniques/Petit_vocabulaire_lean.md
```

Métadonnées actualisées :

```text
CITATION.cff
.zenodo.json
```

Audit ajouté :

```text
scripts/audit_proved.sh
make audit-proved
```

---

## Commandes de vérification recommandées

Avant tag ou gel :

```bash
lake build CouretUnification.Frozen
lake build CouretUnification.Active
lake build CouretUnification.All
make audit-scripts
make audit-proved
git diff --check
```

Pour l’état documentaire :

```bash
make audit-doctrine
make audit-reachability
```

Si les scripts de checksum sont actifs :

```bash
make checksums
make verify-checksums
```

---

## Statut synthétique

```text
Frozen : stable, compilé, 0 sorry
Active : fronts ouverts, 11 sorry documentés
All    : compile, agrège le dépôt entier
Axioms : 9, localisés dans les couches analytiques / conditionnelles
RH     : non revendiquée
HP     : non revendiqué
det₂ ↔ ξ : ouvert
```

Formule de fermeture :

> L’arithmétique donne le relief.
> InterIA multiplie les lectures.
> Alexandre Couret garde le seuil.
> Le statut décide.

Et pour le dépôt Lean :

> Le noyau fini compile.
> Les verrous sont nommés.
> Le global reste ouvert.
> `RHClaimed = false`.
