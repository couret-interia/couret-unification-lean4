# SquarefreeDensity — fermeture C-04a v38.5.12

## Résumé

Le jalon `v38.5.12` ferme le verrou C-04a du dossier `SquarefreeDensity` : la minoration effective des entiers squarefree est désormais disponible comme résultat prouvé dans l’architecture Lean du dépôt.

Formellement, le théorème promu est :

```lean
∀ {N : ℕ}, 176 ≤ N → (N : ℚ) / 2 ≤ squarefreeCount N
```

Autrement dit :

```text
pour N ≥ 176, au moins la moitié des entiers ≤ N sont squarefree.
```

## Statut après promotion

```text
C-04a squarefreeCount_ge_half      : [D] prouvé via SquarefreeDensityC04aClosed
C-04b densité 6 / π²               : [D] prouvé via SquarefreeDensityC04bClosed
SquarefreeDensity.lean             : interface stable, sans sorry
SquarefreeDensityHalf.lean         : lab de fermeture complète C-04a
SquarefreeDensityC04aClosed.lean   : façade de promotion stable
RHClaimed                          : false
```

## Fichiers concernés

### `SquarefreeDensity.lean`

Ce fichier reste l’interface stable historique du bloc C. Il contient notamment :

* `squarefreeCount`
* le bridge public `SquarefreeCountGeHalfBridge`
* le consommateur public `squarefreeCount_ge_half`
* le bridge public `SquarefreeAsymptoticDensityBridge`
* le consommateur public `squarefree_asymptotic_density`

Son statut est désormais clarifié : C-04a et C-04b sont prouvés dans le projet global via des façades séparées, sans créer de cycle d’import.

### `SquarefreeDensityHalf.lean`

Ce fichier joue le rôle de laboratoire de fermeture de C-04a. Il construit progressivement la preuve effective :

```text
non-squarefree count
→ couverture par carrés premiers
→ somme des multiples de p²
→ petits premiers + queue entière
→ coefficients rationnels
→ télescopage de la queue
→ borne finale N/2
```

Il aboutit notamment à :

```lean
squarefreeCountGeHalfBridge_proved
squarefreeCount_ge_half_final
```

### `SquarefreeDensityC04aClosed.lean`

Ce fichier est la façade de promotion stable. Il importe le laboratoire `SquarefreeDensityHalf.lean` et transforme le bridge public de `SquarefreeDensity.lean` en résultat prouvé.

Il fournit notamment :

```lean
squarefreeCountGeHalfBridge_promoted
squarefreeCount_ge_half_unconditional
C04a_squarefree_half_promoted
squarefreeDensityC04aClosure_proved
```

## Structure de la preuve

La fermeture repose sur une chaîne de réductions explicites.

### 1. Passage aux non-squarefree

On utilise la décomposition exacte :

```lean
squarefreeCount N + nonSquarefreeCount N = N
```

Ainsi, il suffit de montrer :

```text
nonSquarefreeCount N ≤ N / 2.
```

### 2. Couverture par carrés premiers

Tout entier non-squarefree possède un diviseur de la forme `p²`, avec `p` premier. On obtient donc une majoration par surcomptage :

```text
nonSquarefreeCount N
≤ ∑_{p ≤ √N, p premier} ⌊N / p²⌋.
```

La preuve Lean ferme séparément :

* l’inclusion dans l’union des multiples de carrés premiers ;
* la majoration du cardinal d’une union finie par la somme des cardinaux ;
* le cardinal exact des multiples de `p²`.

### 3. Séparation petits premiers + queue

La somme sur les premiers est majorée par :

```text
∑_{p ∈ {2,3,5,7,11,13,17}} ⌊N / p²⌋
+
∑_{19 ≤ d ≤ √N} ⌊N / d²⌋.
```

La première partie est finie et explicite. La seconde oublie la primalité et majore la queue par une somme entière.

### 4. Contrôle coefficientiel

Les planchers sont majorés rationnellement :

```text
⌊N / q⌋ ≤ N / q.
```

On obtient donc :

```text
petits premiers ≤ N · ∑_{p ∈ {2,3,5,7,11,13,17}} 1/p²
```

et :

```text
queue ≤ N · ∑_{19 ≤ d ≤ √N} 1/d².
```

### 5. Télescopage de la queue

La queue est contrôlée par :

```text
1/d² ≤ 1/(d-1) - 1/d,  pour d ≥ 2.
```

Donc :

```text
∑_{19 ≤ d ≤ √N} 1/d² ≤ 1/18.
```

La somme télescopique exacte utilisée dans Lean est :

```lean
largeSquareTailTelescopingIcc_eq
```

### 6. Coefficient final

Le coefficient total est vérifié explicitement :

```text
∑_{p ∈ {2,3,5,7,11,13,17}} 1/p² + 1/18 ≤ 1/2.
```

La fermeture numérique est assurée par :

```lean
smallTailCoefficientLeHalfBridge_proved
```

## Doctrine

Cette fermeture ne revendique aucune implication concernant RH, Hilbert–Pólya, det₂, ou l’appariement global des zéros.

Elle concerne uniquement une minoration effective classique sur la densité des entiers squarefree dans les intervalles initiaux `[1, N]`.

Invariant conservé :

```text
RHClaimed = false
```

Le statut correct est donc :

```text
[D] résultat arithmético-effectif local prouvé
[O] aucun passage global RH / Hilbert–Pólya revendiqué
```

## Audit de validation

Le jalon est validé par :

```bash
lake build CouretUnification.Logic.H3.SquarefreeDensityC04aClosed
lake build CouretUnification.All
grep -n "sorry\|axiom\|admit" lean/CouretUnification/Logic/H3/SquarefreeDensityC04aClosed.lean
grep -n "sorry\|axiom\|admit" lean/CouretUnification/Logic/H3/SquarefreeDensityHalf.lean
```

Résultat attendu :

```text
Build completed successfully
0 occurrence locale de sorry / axiom / admit dans SquarefreeDensityC04aClosed.lean
0 occurrence locale de sorry / axiom / admit dans SquarefreeDensityHalf.lean
```

Les warnings globaux restants du dépôt concernent d’autres fichiers et d’autres verrous analytiques. Ils ne sont pas introduits par C-04a.

## Conclusion

Le jalon `v38.5.12` transforme C-04a d’un bridge conditionnel en résultat prouvé, sans nouvel axiome, sans `sorry`, sans glissement doctrinal, et sans revendication RH.

La formule canonique à retenir est :

```text
C-04a est fermé. C-04b est fermé. RHClaimed = false.
```
