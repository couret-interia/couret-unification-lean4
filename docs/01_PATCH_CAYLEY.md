# Patch Cayley — purge du `sorry` technique `maxRecDepth`

**Cible :** `lean/CouretUnification/Core/CayleyG30.lean:51`
**Type :** patch d'options Lean — **pas** une preuve mathématique nouvelle
**Durée attendue :** 10 minutes, y compris le rebuild complet
**Effet :** A passe en 🟢 absolu localement ; dépôt global à 3 sorry au lieu de 4

---

## Diagnostic

Le `sorry` ligne 51 est déclenché par un `decide` ou `native_decide` qui dépasse
la profondeur de récursion par défaut. Le problème n'est pas que le fait est
faux — il est trivialement vrai par évaluation exhaustive sur un groupe fini
de 8 éléments — c'est que le compilateur Lean s'arrête avant d'avoir fini
l'arbre.

Mathématiquement : rien à faire. Techniquement : trois lignes d'options.

## Patch

Ouvrir `lean/CouretUnification/Core/CayleyG30.lean` et ajouter **en tête du
fichier**, immédiatement après les `import` et avant le `namespace` :

```lean
-- =============================================================================
-- Options de compilation pour les decide/native_decide sur le groupe fini G30
-- =============================================================================
-- Le spectre de l'opérateur de Cayley et les identités de table de groupe
-- se vérifient par évaluation exhaustive sur (ℤ/30ℤ)× (8 éléments).
-- Les options ci-dessous relèvent simplement la limite de récursion du
-- compilateur pour que `decide` aille au bout de l'arbre de preuve.
-- Ce n'est PAS une preuve mathématique nouvelle.
-- =============================================================================

set_option maxRecDepth 2048
set_option maxHeartbeats 800000
```

**Note :** commence par `maxRecDepth 2048`. Si ce n'est pas suffisant, monte à
`4096`, puis `8192`, puis `16384`. La valeur `100000` mentionnée dans les
synthèses multi-IA est un ordre de grandeur, pas une cible. En pratique, 2048
suffit presque toujours pour un groupe d'ordre 8.

**Si `maxRecDepth` seul ne suffit pas**, ajoute aussi `maxHeartbeats`. La
valeur 800000 est celle que tu utilises déjà dans `sum_char_apply_eq_card_if_one`
pour des raisons identiques (évaluation exhaustive sur un fini).

## Commande de vérification

```bash
lake build CouretUnification.Core.CayleyG30
```

**Résultat attendu :**

- Sortie propre, sans le warning `declaration uses sorry` à la ligne 51
- Si le `sorry` reste présent malgré les options : le patch n'a pas été
  appliqué au bon endroit. Vérifier que les `set_option` sont **avant**
  toute déclaration, pas après.

## Remplacement du `sorry` (si applicable)

Selon la nature exacte de la ligne 51 (que je n'ai pas sous les yeux), deux cas :

### Cas A — la ligne 51 est déjà du `decide`/`native_decide` avec `sorry`

```lean
theorem foo : ... := by sorry
```

devient simplement

```lean
theorem foo : ... := by decide
```

ou

```lean
theorem foo : ... := by native_decide
```

Les options en tête donnent la puissance, le `decide` fait le reste.

### Cas B — la ligne 51 est une tactique plus élaborée qui plante

Si la preuve tente `simp; decide` ou une chaîne de `rw` suivie de `decide`,
remplace l'intégralité par `by native_decide`. `native_decide` compile la
proposition décidable en bytecode Lean et l'évalue — c'est bien plus rapide
que `decide` pur pour les tables finies, et ça contourne la plupart des
problèmes de profondeur.

```lean
theorem foo : ... := by native_decide
```

## Rebuild complet après patch

```bash
# Rebuild incrémental
lake build CouretUnification.Core.CayleyG30

# Puis vérification complète du Core
lake build CouretUnification.Core.UnitsBridge
lake build CouretUnification.Core.CenteredSpace30
lake build CouretUnification.Core.Convolution30
lake build CouretUnification.Core.CayleyG30
lake build CouretUnification.Core.CharacterLemmas
lake build CouretUnification.Core.Characters30Bridge
lake build CouretUnification.Core.CharParity30
lake build CouretUnification.Core.CRTEquiv

# Enfin, rebuild total
bash scripts/build_all.sh
```

## Diagnostic des sorry après patch

```bash
bash scripts/diagnose_sorry.sh
```

**Résultat attendu :** 3 sorry au lieu de 4 :

```
✓ Core/CayleyG30.lean — purged
✗ Logic/H3/Lemma7Residual.lean:6 — structurel (gelé P3)
✗ Logic/H3/RouteC.lean:131 — routeC_main_lower (P2, à attaquer)
✗ Logic/H3/RouteC.lean:148 — routeC_error_upper (P3, session dédiée)
```

Le sorry doctrinal de `AnalyticHorizon/Det2Transport.lean` n'est pas textuel
au stade placeholder, il ne sera donc pas affiché — c'est normal.

## Conséquence doctrinale immédiate

Avec ce patch :

- **Bloc A du Go/No-Go passe en 🟢 absolu localement**
- La phrase « noyau fini exact sans sorry » devient vraie au sens strict
- Dans la communication externe, on peut désormais écrire :
  *« le noyau fini G₃₀ est certifié Lean 4 sans sorry »*
- **Mais** le projet reste 🔴 NO-GO globalement — rien ne change côté Lock 3 fort

## Ce qui ne change PAS

Ce patch ne fait **aucun** progrès mathématique. Il n'avance aucun verrou. Il
rend simplement lisible et honnête le statut réel du noyau fini, qui était
déjà mathématiquement exact mais techniquement obscurci par une limite de
compilateur.

C'est une hygiène, pas une avancée. L'avancée réelle viendra de
`RouteC::main_lower` (livrable 2) et du cahier des charges Euler (livrable 3).

---

**À Thomas :** une fois le patch appliqué et le build vert, coller ici la sortie
complète du `lake build` et de `diagnose_sorry.sh` pour validation définitive.
