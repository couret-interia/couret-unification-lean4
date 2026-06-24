# Roadmap Lean 4 — fermeture contrôlée des `sorry`

## Principe général

Objectif : réduire la dette Lean sans modifier indûment le statut scientifique du programme.

```text
Frozen = 0 sorry
Active = obligations ouvertes documentées
RHClaimed = false
```

La fermeture d’un `sorry` n’est acceptable que si elle ne transforme pas une hypothèse analytique, un pont conditionnel ou un verrou global en théorème prétendument démontré.

---

## État initial

```text
Total sorry : 11
Frozen      : 0 sorry
Active      : 11 sorry
Axiomes     : 9, localisés dans les couches analytiques / conditionnelles
```

Ventilation :

| Bloc                                 | Nombre | Nature                              |
| ------------------------------------ | -----: | ----------------------------------- |
| `Logic/L10NoGoTheorem.lean`          |      3 | obligations techniques locales      |
| `Logic/H3/RouteC.lean`               |      1 | route arithmético-analytique active |
| `Logic/L6RatioEstimateDerived.lean`  |      1 | estimation analytique locale        |
| `Analytic/GammaFactor.lean`          |      4 | interface archimédienne lourde      |
| `AnalyticHorizon/Det2Transport.lean` |      1 | horizon `det₂`                      |
| `Logic/H3/Lemma7Residual.lean`       |      1 | verrou central F3                   |

---

# Phase 0 — Audit de départ

## Objectif

Fixer l’état exact avant toute fermeture.

## Commandes

```bash
make audit-scripts
make audit-proved
lake build CouretUnification.Frozen
lake build CouretUnification.All
```

## Sortie attendue

```text
Frozen : 0 sorry
All    : 11 sorry
```

## Livrable

Créer ou mettre à jour :

```text
docs/registry/ETAT_LEAN4_v38.5.13.md
```

avec :

```text
- table exacte des 11 sorry ;
- distinction Frozen / Active ;
- verrou central identifié ;
- RHClaimed = false.
```

## Statut

```text
[Audit]
```

---

# Phase 1 — Fermer `L10NoGoTheorem`

## Cible

```text
Logic/L10NoGoTheorem.lean
```

## Nombre de `sorry`

```text
3
```

## Priorité

```text
P1 — premier chantier
```

## Pourquoi

C’est le bloc le plus probablement technique et le moins susceptible de modifier le statut global du programme.

## Travail

1. Isoler les trois énoncés.
2. Vérifier s’ils relèvent de :

   * séparation réelle ;
   * irrationalité ;
   * obstruction discrète ;
   * calcul fini ;
   * inégalité élémentaire.
3. Créer des lemmes intermédiaires courts.
4. Éviter les preuves monolithiques.
5. Compiler uniquement le module, puis `All`.

## Critère d’acceptation

```bash
lake build CouretUnification.Logic.L10NoGoTheorem
make audit-scripts
```

Le total doit passer :

```text
11 sorry → 8 sorry
```

## Statut visé

```text
[O technique] → [D local]
```

## Commit recommandé

```bash
git commit -m "L10: ferme les obligations techniques du no-go"
```

---

# Phase 2 — Auditer puis fermer ou borner `RouteC`

## Cible

```text
Logic/H3/RouteC.lean
```

## Nombre de `sorry`

```text
1
```

## Priorité

```text
P2
```

## Pourquoi

`RouteC` peut bénéficier des fermetures récentes `SquarefreeDensity C-04a / C-04b`.

## Travail

1. Lire l’énoncé exact du `sorry`.
2. Vérifier s’il peut consommer :

   * `C04a_squarefree_half_promoted`;
   * `C04b_squarefree_density_promoted`;
   * un lemme squarefree déjà fermé.
3. Distinguer deux cas :

   * cas local fermable ;
   * cas analytique à convertir en bridge conditionnel.

## Critère d’acceptation

Si fermeture réelle :

```text
8 sorry → 7 sorry
```

Si non fermable :

```text
sorry → bridge conditionnel nommé
```

Dans ce second cas, le nombre de `sorry` baisse aussi, mais le statut devient `[C]`, pas `[D]`.

## Statut visé

```text
[D local]
```

ou :

```text
[C bridge explicite]
```

## Commit recommandé

Si preuve :

```bash
git commit -m "RouteC: ferme l'obligation locale via les bornes squarefree"
```

Si bridge :

```bash
git commit -m "RouteC: remplace le sorry par un bridge conditionnel explicite"
```

---

# Phase 3 — Traiter `L6RatioEstimateDerived`

## Cible

```text
Logic/L6RatioEstimateDerived.lean
```

## Nombre de `sorry`

```text
1
```

## Priorité

```text
P3
```

## Pourquoi

Ce bloc peut être localisable autour de résultats déjà présents dans les modules L6 / Stirling.

## Travail

1. Identifier si le `sorry` est un simple raccord.
2. Chercher les lemmes disponibles dans :

   * `L6Bridge`;
   * `L6Interface`;
   * éventuels modules Stirling / ratio.
3. Si le résultat est bien un wrapper, fermer.
4. Si l’API analytique manque, convertir en bridge conditionnel.

## Critère d’acceptation

```text
7 sorry → 6 sorry
```

ou bien :

```text
sorry remplacé par hypothèse nommée, documentée, non promue
```

## Statut visé

```text
[D local]
```

ou :

```text
[C analytique]
```

## Commit recommandé

```bash
git commit -m "L6: clarifie l'estimation de ratio derivee"
```

---

# Phase 4 — Refactoriser `GammaFactor`

## Cible

```text
Analytic/GammaFactor.lean
```

## Nombre de `sorry`

```text
4
```

## Priorité

```text
P4
```

## Pourquoi

Ce bloc est archimédien et lourd. Il ne faut pas chercher à le fermer en un patch rapide.

## Diagnostic

L’un des `sorry` est dans une définition :

```lean
noncomputable def D_M (s : ℂ) : ℂ := sorry
```

Ce n’est pas seulement une preuve manquante : c’est une définition-placeholder.

## Travail

Découper le fichier en trois niveaux :

```text
1. Définitions réellement disponibles
2. Interfaces opaques assumées comme objets de travail
3. Bridges conditionnels pour équations fonctionnelles
```

## Stratégie

Remplacer les définitions impossibles par des interfaces explicites :

```lean
opaque D_M : ℂ → ℂ
```

ou par une structure de données conditionnelle :

```lean
structure GammaBridge where
  D_M : ℂ → ℂ
  functional_equation : Prop
  growth_bound : Prop
```

Ne pas déclarer vraie une équation fonctionnelle non prouvée.

## Critère d’acceptation

```text
6 sorry → 2 sorry
```

ou idéalement :

```text
6 sorry → 2/1/0 sorry
```

mais avec statut :

```text
[C interface archimédienne]
```

et non `[D]`.

## Statut visé

```text
[sorry] → [C propre]
```

## Commit recommandé

```bash
git commit -m "GammaFactor: remplace les placeholders par des interfaces conditionnelles"
```

---

# Phase 5 — Isoler `Det2Transport`

## Cible

```text
AnalyticHorizon/Det2Transport.lean
```

## Nombre de `sorry`

```text
1
```

## Priorité

```text
P5
```

## Pourquoi

Ce fichier touche au transport spectral global et à l’horizon `det₂`.

## Règle

Ne pas fermer mécaniquement.

## Travail

1. Lire l’énoncé exact.
2. Vérifier s’il dépend de :

   * `Det2IdentifiesXi`;
   * `ZeroMatching`;
   * une trace formula globale ;
   * une équation fonctionnelle non formalisée.
3. Si oui, convertir en théorème conditionnel.
4. Garder hors `Frozen`.

## Critère d’acceptation

Le meilleur résultat à court terme n’est pas forcément un théorème `[D]`, mais :

```text
sorry supprimé
condition explicite ajoutée
horizon non franchi
```

## Statut visé

```text
[O] → [C explicite]
```

## Commit recommandé

```bash
git commit -m "Det2Transport: explicite les conditions du transport spectral"
```

---

# Phase 6 — Conserver `Lemma7Residual` comme verrou central

## Cible

```text
Logic/H3/Lemma7Residual.lean
```

## Nombre de `sorry`

```text
1
```

## Priorité

```text
P6 — dernier, non technique
```

## Pourquoi

Ce `sorry` est le verrou central F3 : annulation du résidu sur la ligne critique.

Il ne doit pas être traité comme une dette technique ordinaire.

## Options acceptables

```text
1. Le laisser ouvert et nommé.
2. Le transformer en bridge conditionnel explicite.
3. Le prouver réellement, avec audit scientifique séparé.
```

## Option recommandée à court terme

```text
Le laisser nommé comme verrou central.
```

## Critère d’acceptation

Aucun changement de statut global sans preuve réelle.

## Statut

```text
[O central]
```

## Commit éventuel

Si clarification documentaire seulement :

```bash
git commit -m "H3: documente Lemma7Residual comme verrou central F3"
```

---

# Roadmap chiffrée

| Étape | Action                                   | Sorry restants attendus | Statut               |
| ----: | ---------------------------------------- | ----------------------: | -------------------- |
|     0 | état initial                             |                      11 | audité               |
|     1 | fermer `L10NoGoTheorem`                  |                       8 | probable `[D local]` |
|     2 | fermer / borner `RouteC`                 |                       7 | `[D local]` ou `[C]` |
|     3 | fermer / borner `L6RatioEstimateDerived` |                       6 | `[D local]` ou `[C]` |
|     4 | refactoriser `GammaFactor`               |                       2 | `[C archimédien]`    |
|     5 | borner `Det2Transport`                   |                       1 | `[C horizon]`        |
|     6 | conserver `Lemma7Residual`               |                       1 | `[O central]`        |

Objectif réaliste :

```text
11 sorry → 1 sorry
```

Mais le dernier `sorry` restant serait alors assumé :

```text
Lemma7Residual = verrou central F3
```

Objectif maximal seulement si preuve réelle :

```text
11 sorry → 0 sorry
```

Mais cela impliquerait un changement scientifique majeur si `Lemma7Residual` est fermé.

---

# Ordre recommandé des branches Git

```text
spring-2026/v38x-L10-close
spring-2026/v38x-RouteC-clean
spring-2026/v38x-L6-ratio
spring-2026/v38x-GammaFactor-interface
spring-2026/v38x-Det2Transport-conditional
spring-2026/v38x-H3-F3-documentation
```

Chaque branche doit être fusionnée séparément.

---

# Commandes de contrôle après chaque phase

```bash
lake build CouretUnification.Frozen
lake build CouretUnification.Active
lake build CouretUnification.All
make audit-scripts
make audit-proved
git diff --check
```

Critère minimal :

```text
Frozen reste 0 sorry
RHClaimed reste false
aucun nouvel axiom non documenté
```

---

# Règle finale

```text
Fermer ce qui est technique.
Conditionner ce qui est analytique.
Nommer ce qui est ouvert.
Ne jamais promouvoir le verrou central par fatigue.
```

Formule courte :

> L10 protège.
> RouteC raffine.
> L6 raccorde.
> GammaFactor doit être typé.
> Det2Transport reste conditionnel.
> Lemma7Residual garde le seuil.
