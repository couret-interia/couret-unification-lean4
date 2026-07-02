# Interactions des Sorries

Voici la lecture des **interactions entre les 11 `sorry`**. Le point essentiel : ils ne forment pas une seule chaîne linéaire. Ils se répartissent en **trois blocs presque indépendants**, avec un seul bloc vraiment dangereux : le couple `Lemma7Residual` / `Det2Transport`.

## Carte générale

```text id="6jqfzk"
L10NoGoTheorem
   └── bloc de garde / obstruction locale
       presque indépendant du passage global

RouteC
   └── route arithmético-analytique active
       peut soutenir des bornes, mais ne ferme pas F3 seule

L6RatioEstimateDerived
GammaFactor
   └── bloc archimédien / analytique
       fournit des interfaces de croissance, facteur Γ, ratios

Det2Transport
Lemma7Residual
   └── bloc horizon global
       zone dangereuse : det₂ ↔ ξ, résidu critique, ZeroMatching
```

## Tableau des interactions

| Bloc                     | Interagit avec                                      | Nature de l’interaction                                              | Risque de surclaim |
| ------------------------ | --------------------------------------------------- | -------------------------------------------------------------------- | ------------------ |
| `L10NoGoTheorem`         | surtout lui-même                                    | établit une obstruction / séparation ; ne nourrit pas directement RH | faible             |
| `RouteC`                 | `SquarefreeDensity`, `S1`, `κ`, contrôle d’erreur   | peut renforcer une route arithmétique active                         | moyen              |
| `L6RatioEstimateDerived` | `L6Stirling`, croissance archimédienne              | dépend de lemmes asymptotiques / ratio                               | moyen              |
| `GammaFactor`            | `L6`, facteur archimédien, équations fonctionnelles | interface analytique lourde ; peut nourrir l’horizon Γ/ξ             | élevé              |
| `Det2Transport`          | `Det2IdentifiesXi`, obligations det₂, horizon ξ     | transport spectral global conditionnel                               | très élevé         |
| `Lemma7Residual`         | `PhaseBComposition` branche β.2, `det₂ ↔ ξ`         | verrou central du résidu critique                                    | maximal            |

## 1. `L10NoGoTheorem` : bloc presque indépendant

Les trois `sorry` de `L10NoGoTheorem` ne semblent pas être des briques qui ferment le programme. Ils servent plutôt à **interdire un faux passage**, ou à formaliser une séparation.

Interaction principale :

```text id="2k8enc"
L10NoGoTheorem → garde-fou / obstruction
```

Il ne faut pas attendre de leur fermeture une avancée vers RH. Leur rôle est plutôt hygiénique : empêcher qu’une cible irrationnelle ou spectrale soit atteinte par un objet entier/discret mal typé.

Donc :

```text id="t6acz0"
fermer L10NoGoTheorem diminue la dette technique,
mais ne rapproche pas directement det₂ ↔ ξ.
```

C’est probablement le bloc le plus sain à attaquer en premier.

## 2. `RouteC` : route active, mais non centrale seule

`RouteC` interagit avec les résultats de type squarefree, `S1`, `κ`, contrôle d’erreur, sommes pondérées.

Interaction probable :

```text id="eo8kid"
SquarefreeDensity C-04a/C-04b
        ↓
RouteC
        ↓
contrôle arithmético-analytique local
        ↓
bornes / positivité / route κ
```

Mais attention : même si `RouteC` est fermé, cela ne ferme pas le verrou global. Cela améliore une route, pas le pont `det₂ ↔ ξ`.

Statut sain :

```text id="1th7y3"
RouteC peut devenir [D] localement,
sans promouvoir H3, det₂ ↔ ξ, ou RH.
```

## 3. `L6RatioEstimateDerived` et `GammaFactor` : bloc archimédien

Ces deux-là sont conceptuellement liés, même s’il faut vérifier les imports exacts.

`L6RatioEstimateDerived` porte une estimation de ratio, probablement raccordée à Stirling / croissance archimédienne.

`GammaFactor` porte le facteur Γ, les équations fonctionnelles, et même une définition-placeholder :

```lean id="hv40kg"
noncomputable def D_M (s : ℂ) : ℂ := sorry
```

Interaction conceptuelle :

```text id="9em1f0"
GammaFactor
   ↓
facteur archimédien / équation fonctionnelle
   ↓
L6 / ratios / croissance
   ↓
horizon analytique
```

Ce bloc est dangereux à fermer trop vite, car il touche à la partie archimédienne de l’architecture analytique.

La bonne stratégie n’est pas forcément de “prouver tout GammaFactor” d’un coup, mais de séparer :

```text id="gbuzp9"
définitions disponibles
interfaces opaques
bridges conditionnels
théorèmes réellement prouvés
```

## 4. `Det2Transport` et `Lemma7Residual` : le vrai couplage critique

C’est ici que l’interaction est la plus forte.

Le verrou central est :

```text id="qul9kh"
Logic/H3/Lemma7Residual.lean
```

Il intervient dans la branche β.2 de `PhaseBComposition`.

Le transport det₂ appartient à :

```text id="cuwbti"
AnalyticHorizon/Det2Transport.lean
```

Le couple dangereux est :

```text id="2yo5h0"
Lemma7Residual
        ↓
branche β.2 de PhaseBComposition
        ↓
Det2 / ZeroMatching / ξ
        ↓
horizon RH
```

Ce ne sont pas deux dettes techniques ordinaires. Leur fermeture pourrait changer le statut du programme si elle n’est pas strictement bornée.

Lecture saine :

```text id="vw0da5"
Lemma7Residual = verrou du résidu critique
Det2Transport = verrou de transport spectral global
```

Ils doivent rester **nommés, isolés, et hors Frozen** tant qu’ils ne sont pas prouvés réellement.

## Graphe de dépendance statutaire

```text id="hwfdhp"
[D] noyau fini G30
   ├── CharacterSubgroupSums
   ├── PointDefectLemma
   ├── G30Classification
   └── QuadraticResonance

[D] squarefree
   ├── C-04a
   └── C-04b
        ↓
   peut soutenir RouteC
        ↓
[O]/[C] RouteC active

[D]/[C] interfaces archimédiennes locales
   ├── L6Stirling / L6Bridge
   ├── L6RatioEstimateDerived  [sorry]
   └── GammaFactor             [sorry]
        ↓
[O]/[C] Det2Transport          [sorry]
        ↓
[O] det₂ ↔ ξ

[O central] Lemma7Residual      [sorry]
        ↓
PhaseBComposition β.2
        ↓
ZeroMatching / horizon RH
```

## Ce qui est indépendant

Ces blocs peuvent être travaillés sans toucher au verrou global :

```text id="hyh518"
L10NoGoTheorem
RouteC, si l’énoncé reste local
L6RatioEstimateDerived, si borné à L6
certaines parties de GammaFactor, si transformées en interfaces propres
```

## Ce qui ne doit pas être fermé mécaniquement

Ces deux-là ne doivent pas être traités comme des “sorries à éliminer” :

```text id="9tmc8d"
Lemma7Residual
Det2Transport
```

Ils sont des **seuils**, pas seulement des trous.

## Ordre d’attaque recommandé selon les interactions

| Priorité | Cible                    | Pourquoi                                     |
| -------: | ------------------------ | -------------------------------------------- |
|        1 | `L10NoGoTheorem`         | isolé, faible risque, probablement technique |
|        2 | `RouteC`                 | peut bénéficier des fermetures squarefree    |
|        3 | `L6RatioEstimateDerived` | localisable autour de L6/Stirling            |
|        4 | `GammaFactor`            | à nettoyer en interfaces avant preuve        |
|        5 | `Det2Transport`          | horizon global, à garder conditionnel        |
|        6 | `Lemma7Residual`         | verrou central, ne pas forcer                |

## Formule courte

```text id="6nsw81"
L10 protège.
RouteC raffine.
L6 et Gamma portent l’archimédien.
Det2Transport ouvre l’horizon.
Lemma7Residual garde le seuil.
```

Le plus important : **les 11 `sorry` ne se valent pas**. En fermer 9 peut améliorer fortement la propreté du dépôt sans changer le statut global. En fermer `Lemma7Residual` ou `Det2Transport`, en revanche, serait un changement de statut majeur et demanderait un audit scientifique séparé.
