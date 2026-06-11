# SquarefreeDensity — fermeture C-04b v38.5.11

## Résumé

Le jalon `v38.5.11` ferme le verrou C-04b du dossier `SquarefreeDensity` : la densité asymptotique classique des entiers squarefree est désormais disponible comme résultat prouvé dans l’architecture Lean du dépôt.

Formellement, le théorème promu est :

```lean
Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
  (nhds (6 / (Real.pi^2)))
```

Autrement dit :

```text
squarefreeCount(N) / N → 6 / π².
```

## Statut après promotion

```text
C-04a squarefreeCount_ge_half      : conditional bridge / ouvert
C-04b densité 6 / π²               : [D] prouvé via SquarefreeDensityC04bClosed
SquarefreeDensity.lean             : interface stable, sans sorry
SquarefreeDensityAsymptotic.lean   : lab de fermeture complète C-04b
SquarefreeDensityC04bClosed.lean   : façade de promotion stable
RHClaimed                          : false
```

## Fichiers concernés

### `SquarefreeDensity.lean`

Ce fichier reste l’interface stable historique du bloc C. Il contient notamment :

* `squarefreeCount`
* `sum_squarefree_fubini`
* `div_eucl_real_error`
* `error_term_isBigO`
* le bridge public `SquarefreeAsymptoticDensityBridge`
* le consommateur public `squarefree_asymptotic_density`

Son statut est désormais clarifié : C-04b est prouvé dans le projet global via une façade séparée, sans créer de cycle d’import.

### `SquarefreeDensityAsymptotic.lean`

Ce fichier joue le rôle de laboratoire de fermeture. Il contient la construction complète ayant transformé l’identité de Möbius filtrée et les composants analytiques disponibles en preuve de la densité asymptotique.

Il aboutit notamment à :

```lean
squarefree_asymptotic_density_six_over_pi_squared
```

et à l’alias doctrinal :

```lean
C04b_squarefree_density_closed
```

### `SquarefreeDensityC04bClosed.lean`

Ce fichier est la façade de promotion stable. Il importe le laboratoire `SquarefreeDensityAsymptotic.lean` et transforme le bridge public de `SquarefreeDensity.lean` en résultat prouvé.

Il fournit notamment :

```lean
squarefreeAsymptoticDensityBridge_proved
squarefree_asymptotic_density_unconditional
C04b_squarefree_density_promoted
```

## Doctrine

Cette fermeture ne revendique aucune implication concernant RH, Hilbert–Pólya, det₂, ou l’appariement global des zéros.

Elle concerne uniquement la densité asymptotique classique des entiers squarefree.

Invariant conservé :

```text
RHClaimed = false
```

Le statut correct est donc :

```text
[D] résultat arithmético-analytique local prouvé
[O] aucun passage global RH / Hilbert–Pólya revendiqué
```

## Audit de validation

Le jalon est validé par :

```bash
lake build CouretUnification.Logic.H3.SquarefreeDensityC04bClosed
lake build CouretUnification.All
grep -n "sorry\|axiom\|admit" lean/CouretUnification/Logic/H3/SquarefreeDensityC04bClosed.lean
```

Résultat attendu :

```text
Build completed successfully
0 occurrence locale de sorry / axiom / admit dans SquarefreeDensityC04bClosed.lean
```

Les warnings globaux restants du dépôt concernent d’autres fichiers et d’autres verrous analytiques. Ils ne sont pas introduits par C-04b.

## Ce qui reste ouvert

Le verrou C-04a reste séparé :

```lean
SquarefreeCountGeHalfBridge
```

Il correspond à la minoration effective :

```text
pour N ≥ 176, squarefreeCount(N) ≥ N / 2.
```

Ce verrou n’est pas fermé par `v38.5.11`. Il doit rester explicitement marqué comme conditionnel/ouvert tant qu’une preuve effective ou une certification formelle du seuil n’est pas fournie.

## Conclusion

Le jalon `v38.5.11` transforme C-04b d’un bridge conditionnel en résultat prouvé, sans nouvel axiome, sans `sorry`, sans glissement doctrinal, et sans revendication RH.

La formule canonique à retenir est :

```text
C-04b est fermé. C-04a reste ouvert. RHClaimed = false.
```
