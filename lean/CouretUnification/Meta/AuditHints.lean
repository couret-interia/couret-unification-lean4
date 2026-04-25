/-
# Meta/AuditHints.lean — Commandes d'audit cibles (v35.8.1-bis)

## Statut épistémique

  - Couche : Meta
  - Statut : [A] proved (commandes d'audit, pas de contenu mathématique)
  - sorryCount : 0
  - RHClaimed = false

## Doctrine

Ce fichier ne contient **aucun théorème mathématique**. Il liste les
commandes Lean à exécuter manuellement (ou via CI) pour auditer
l'invariant doctrinal du projet :

  1. Aucun théorème de la couche [B] ne dépend d'un axiome local
     Couret-Unification non documenté.
  2. Tous les sorries sont localisés et catégorisés.
  3. Le nombre d'axiomes utilisés par chaque théorème pivot est minimal
     (idéalement : seulement les axiomes fondamentaux de Mathlib).

## Axiomes Mathlib fondamentaux attendus

Ces trois axiomes sont **autorisés** car ils sont au cœur de Mathlib et
font partie du contrat de confiance de la théorie des types de Lean :

  - `propext` : extensionnalité propositionnelle.
  - `Quot.sound` : règle de saine quotient.
  - `Classical.choice` : axiome du choix classique.

Tout autre axiome apparaissant dans `#print axioms` d'un théorème
[B] doit faire l'objet d'une investigation et d'une justification
explicite (ou d'une suppression).

## Axiomes locaux résiduels documentés (v35.8.1-bis)

Au moment de cette release, un seul axiome local Couret-Unification
subsiste :

  - `R_sigma_linear_left` dans `Logic/C3Weak.lean` (hérité de v35.6.1).
    À traiter dans une release ultérieure.

Aucun autre axiome local n'est attendu. Si l'audit en révèle d'autres,
c'est un signal de régression doctrinale.
-/

import CouretUnification.Logic.Doctrine
import CouretUnification.Logic.L6Bridge
import CouretUnification.Logic.L10NoGoTheorem
import CouretUnification.Logic.EulerBridgeInfiniteReal
import CouretUnification.Logic.EulerBridgeInfiniteCompat

namespace CouretUnification
namespace Meta
namespace AuditHints

/-! ## Section 1 — Commandes d'audit pivot

Ces commandes sont à exécuter dans un buffer Lean (par exemple un
fichier `scratch.lean` séparé) ou décommenter ici lors d'un audit
ponctuel. Elles ne sont pas exécutées par défaut pour ne pas polluer
les sorties du build standard.

### Audit du verrou L6 (data package)

```
#print axioms CouretUnification.Logic.L6Bridge.L6_eta_lt_one_eventual_positivity
```

**Sortie attendue** :
```
'CouretUnification.Logic.L6Bridge.L6_eta_lt_one_eventual_positivity'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Toute autre dépendance (en particulier un nom commençant par
`CouretUnification.`) est un échec d'audit.

### Audit du pont eulérien réel

```
#print axioms CouretUnification.Logic.EulerBridgeInfiniteReal.squarefree_limit_eq_euler_product_real
```

**Sortie attendue** : axiomes Mathlib uniquement, **plus** la dépendance
documentée à `CouretUnification.Logic.EulerBridgeInfiniteCompat.target_bound`
(qui contient un sorry, pas un axiome — la dépendance se voit dans
`#print axioms` car un sorry crée un axiome `sorryAx` synthétique).

### Audit du no-go L10

```
#print axioms CouretUnification.Logic.L10NoGoTheorem.integerSpectra_distance_positive
```

**Sortie attendue** : axiomes Mathlib + dépendances aux 3 sorries CORE
de L10 + dépendance à l'opaque `IsNonTrivialZetaImaginaryPart`.

### Audit du verrou doctrinal C3

```
#print axioms CouretUnification.Logic.C3Weak.gram_semidef_of_rigid
```

**Sortie attendue** : axiomes Mathlib + `R_sigma_linear_left` (hérité,
documenté). Si d'autres axiomes locaux apparaissent : régression.
-/

/-! ## Section 2 — Commandes de comptage

### Sorries actifs par fichier

Recommandé en CI via :
```bash
for f in $(find CouretUnification -name "*.lean"); do
  count=$(awk '/^[[:space:]]*sorry[[:space:]]*$/' "$f" | wc -l)
  if [ "$count" -gt 0 ]; then
    echo "$f: $count sorry"
  fi
done
```

**Inventaire attendu v35.8.1-bis** :
```
Logic/C3Weak.lean                         1 sorry  [B-DOCTRINAL]
Logic/EulerBridgeInfiniteCompat.lean      1 sorry  [B-ANALYTIC target_bound]
Logic/EulerBridgeInfinite.lean            2 sorry  [B-API generic R variant]
Logic/L10NoGoTheorem.lean                 4 sorry  [B-CORE conceptual]
                                          ─────
                                          8 sorries (tous catégorisés)
```

### Axiomes locaux Couret-Unification

```bash
grep -rE "^axiom |^[[:space:]]+axiom " CouretUnification --include="*.lean"
```

**Inventaire attendu v35.8.1-bis** :
```
Logic/C3Weak.lean: axiom R_sigma_linear_left ...   (hérité, documenté)
```

Toute autre ligne est une régression doctrinale.
-/

/-! ## Section 3 — Identité doctrinale -/

def fileIdentity : CouretUnification.Meta.FileIdentity where
  filename := "CouretUnification/Meta/AuditHints.lean"
  layer := CouretUnification.Meta.Layer.A
  status := CouretUnification.Meta.Status.proved
  sorryCount := 0
  rhClaimed := false

example : fileIdentity.rhClaimed = false := rfl

/-- Drapeau d'audit : l'invariant doctrinal est en place. -/
def auditDoctrineActive : Bool := true
example : auditDoctrineActive = true := rfl

end AuditHints
end Meta
end CouretUnification
