# CouretUnification

Prototype spectral fini pour la structure active de \((\mathbb{Z}/30\mathbb{Z})^\times\), formalisé en Lean 4.

## Statut actuel

**v26.3-core** correspond à un noyau fini minimal, compilable et discipliné.

Cette version fige proprement :

- l’espace actif des 8 résidus modulo 30 ;
- l’opérateur fini distingué associé au triplet \(T_C = \{1,11,29\}\) ;
- le spectre documentaire gelé ;
- la couche harmonique minimale ;
- le recollement harmonique du seul cas Couret.

Le dépôt sépare volontairement :

- le **noyau fini certifié** ;
- les **extensions harmoniques générales** ;
- les **filtres globaux** ;
- le **Bridge** analytique / arithmétique.

## Compatibilité

Testé avec :

- **Lean** `v4.29.0`
- **mathlib** `v4.29.0`

Dans cette configuration, le noyau `v26.3-core` compile avec :

```bash
lake update
lake build
```

## Ce que garantit `v26.3-core`

À ce stade, le dépôt garantit un noyau `Core/` avec les propriétés suivantes :

* aucun `sorry` dans la partie noyau visée ;
* aucun axiome ajouté ;
* aucun placeholder du type `Prop := True` ;
* séparation stricte entre données documentaires, calcul harmonique minimal et extensions futures ;
* dépendances structurelles propres dans la branche `Core/`.

## Architecture du noyau

L’ordre logique actuel est le suivant :

1. `Core/Mod30.lean`
2. `Core/FiniteOperator.lean`
3. `Core/SpectralProfile.lean`
4. `Core/ExceptionalTriplets.lean`
5. `Core/Characters30.lean`
6. `Core/Fourier30.lean`
7. `Core/TripletSpectrum.lean`
8. `Core/IntegralSpectrum.lean`
9. `Core/TripletHarmonicSpectrum.lean`
10. `Core/TripletToFiniteSpectrum.lean`

## Contenu mathématique figé dans cette version

### 1. Base active modulo 30

Le noyau travaille sur les 8 résidus inversibles actifs :

[
[1,7,11,13,17,19,23,29].
]

### 2. Triplet distingué

Le triplet central du noyau est :

[
T_C = {1,11,29}.
]

### 3. Spectre documentaire gelé

Le multiensemble brut visé est :

[
{3,3,1,1,1,1,-1,-1}.
]

L’ordre documentaire choisi est :

[
[3,1,1,1,3,1,-1,-1].
]

Le profil quadratique historique correspondant est :

[
[9,1,1,1,9,1,1,1].
]

### 4. Couche harmonique minimale

La couche Fourier dans `Core/Fourier30.lean` reste volontairement minimale :

* calcul des coefficients ;
* ordre documentaire gelé ;
* pas de DFT générale fermée ;
* pas d’orthogonalité complète publique ;
* pas de Parseval global réintroduit trop tôt.

### 5. Recollement du cas Couret

Le point actuellement fermé est le suivant :

* le calcul harmonique complexe du triplet distingué redonne bien le spectre historique gelé ;
* ce calcul recolle avec le `FiniteSpectrum` documentaire déjà fixé.

Autrement dit, pour le seul cas (T_C), le passage

[
\text{triplet harmonique} \longrightarrow \text{spectre documentaire fini}
]

est maintenant validé dans le noyau.

## Ce que cette version ne prétend pas encore faire

**v26.3-core** ne prétend pas encore :

* définir une DFT générale fermée sur tous les triplets ;
* construire un `FiniteSpectrum` entier pour un triplet arbitraire ;
* filtrer globalement les 21 triplets ;
* démontrer le théorème `5/21` dans cette branche minimale ;
* introduire le `Bridge/` analytique complet ;
* établir un lien de type Hilbert–Pólya ;
* prouver RH.

Cette retenue est volontaire. Elle fait partie de la discipline du projet.

## Doctrine de séparation

Le dépôt suit une règle simple :

* **Core/** : seulement le noyau fini exact, documentaire et harmonique minimal ;
* **Bridge/** : seulement après stabilisation complète du noyau ;
* **opérateur sur (\ell^2(\mathbb P))** : branche expérimentale séparée ;
* **chaîne analytique globale** : explicitement ouverte tant que non fermée.

## Prochaines étapes naturelles

Une fois `v26.3-core` stabilisé, les suites possibles sont :

### Branche A — stabilisation du noyau

* nettoyage final des imports ;
* documentation module par module ;
* gel de version du noyau minimal ;
* note de compatibilité Lean/mathlib.

### Branche B — extension harmonique finie

* spectre harmonique d’un triplet arbitraire ;
* conversion contrôlée vers un `FiniteSpectrum` fini ;
* filtrage global seulement après cette étape.

### Branche C — expérimentation opératorielle

En parallèle du noyau Lean, une branche expérimentale peut étudier des opérateurs réels symétriques sur les premiers :

[
(S_N f)(p_i)=\sum_{j=1}^N K_N(p_i,p_j)f(p_j),
]

avec comparaison prudente entre :

* spectres finis réels ;
* statistiques d’espacements ;
* fenêtres de zéros de (\zeta).

Cette branche reste expérimentale et n’est pas confondue avec le noyau fini certifié.

## Ajustement doctrinal recommandé pour `Bridge/`

Quand `Bridge/` sera réintroduit, il est recommandé d’utiliser un statut explicite des énoncés, par exemple :

```lean
inductive ClaimStatus
  | formalized
  | constructed
  | conditional
  | open_
  | roadmap
```

Cela évite de sur-vendre le statut des résultats et garde une lecture épistémique claire.

## Résumé

**v26.3-core** doit être lu comme :

* un **noyau spectral fini minimal** ;
* **compilable** sous Lean 4.29.0 / mathlib 4.29.0 ;
* **strictement séparé** des extensions analytiques ;
* suffisamment fermé pour fixer les objets de base ;
* volontairement incomplet sur tout ce qui relèverait d’une théorie globale.

---

## Commandes

```bash
lake update
lake build
```

## Philosophie du dépôt

Mieux vaut un noyau fini exact, modeste et proprement séparé,
qu’une architecture ambitieuse où les couches documentaires,
harmoniques et analytiques sont mélangées trop tôt.
