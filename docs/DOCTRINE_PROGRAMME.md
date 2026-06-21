# DOCTRINE_PROGRAMME.md

## Couret–Unification — Doctrine du programme

**Programme :** Couret–Unification
**État doctrinal :** v38.5x
**État opérationnel :** v38.5x — ResGold intégré
**Rôle du document :** invariants, statuts, règles de promotion et garde anti-surrevendication

---

## 0. Principe directeur

Le dépôt Couret–Unification distingue strictement :

1. le fini démontré ;
2. le conditionnel typé ;
3. le mesuré reproductible ;
4. l’heuristique ;
5. l’ouvert.

Aucune couche ne doit promouvoir un résultat local, fini, mesuré ou conditionnel en résultat global démontré.

> Le noyau fini est exact.
> Le pont global reste ouvert.
> Le conditionnel se nomme.
> L’ouvert se reconnaît.

---

## 1. Invariants cardinaux

Les invariants suivants sont non négociables dans l’état courant du programme :

```text
RHClaimed                  = false
HilbertPolyaClaimed        = false
SpectralCoincidenceClaimed = false
ExplicitFormulaClosed      = false
Det2IdentityClaimed        = false
RiemannVonMangoldtClaimed  = false
CandidateCClaimed          = false
MotherTheoremClaimed       = false
EulerCompletionClosed      = false
MobiusCorrelationClosed    = false
```

Aucun de ces invariants ne peut basculer à `true` sans preuve formelle, auditée et explicitement reliée au verrou correspondant.

Aucun résultat numérique, aucune intuition, aucune analogie, aucun diagramme, aucune coïncidence spectrale locale et aucune prose mathématique ne suffit à changer ces valeurs.

---

## 2. Statuts épistémiques

| Code  | Sens                                                                                              | Règle de promotion                         |
| ----- | ------------------------------------------------------------------------------------------------- | ------------------------------------------ |
| `[D]` | Demonstrated : démontré par Lean, par calcul fini exhaustif intégré, ou par audit formel du build | preuve ou build vérifiable uniquement      |
| `[M]` | Measured : mesuré par script, rapport ou expérimentation reproductible                            | ne devient pas `[D]` sans preuve           |
| `[C]` | Conditional : vrai sous hypothèses nommées                                                        | les hypothèses doivent rester visibles     |
| `[H]` | Heuristic : plausible, interprétatif ou exploratoire                                              | reste `[H]` tant qu’aucune preuve n’existe |
| `[I]` | Identified : structure repérée, typée ou isolée                                                   | étape préparatoire, non preuve             |
| `[N]` | Negative : voie écartée par obstruction ou contre-test                                            | empêche une promotion abusive              |
| `[R]` | Refuted : contradiction, faux positif ou route réfutée                                            | élimination forte                          |
| `[O]` | Open : verrou non fermé                                                                           | statut par défaut des verrous globaux      |

Règle centrale :

> `[M] + [H] + [C]` ne donne jamais `[D]` par accumulation rhétorique.

---

## 3. Local et global

Le noyau fini modulo 30 est une structure locale exacte.

Il peut servir de base, de témoin, de modèle, de prototype spectral ou de contrainte de cohérence.

Il ne suffit pas à prouver :

* l’Hypothèse de Riemann ;
* Hilbert–Pólya global ;
* l’identité `det₂ ↔ ξ` ;
* la formule explicite globale ;
* la formule de trace globale ;
* l’appariement spectre ↔ zéros ;
* la complétion eulérienne globale.

Formule canonique :

```text
local fermé ≠ global fermé
fini exact ≠ analytique global
spectre local ≠ zéros de ζ
```

---

## 4. Doctrine de λ

Toute occurrence de `λ = 1 / √7` doit préciser son statut.

Lectures autorisées :

1. `λ_simplex` : invariant géométrique interne au simplexe centré de dimension 7.
2. `λ_TDA` ou `λ_transport` : invariant de transport ou de lecture topologique locale, lorsque défini.
3. `λ_spec` : valeur ou échelle spectrale locale, seulement si l’opérateur correspondant est explicitement donné.
4. `λ_info` : lecture informationnelle ou asymptotique, uniquement comme hypothèse ou interprétation, jamais comme résultat fini automatique.

Règle :

> Ces lectures ne doivent pas être fusionnées.
> Une égalité numérique locale ne constitue pas une identité mathématique globale.

En particulier, `λ = 1 / √7` ne doit jamais être présenté comme une constante universelle des zéros de ζ.

---

## 5. H3 et verrous globaux

L’architecture H3 sépare trois niveaux :

| Niveau | Description                                          | Statut                                 |
| ------ | ---------------------------------------------------- | -------------------------------------- |
| H3.A   | fermeture fonctionnelle locale ou opératorielle      | partiellement encodée / conditionnelle |
| H3.B   | identification structurelle, locale ou archimédienne | identifiée / conditionnelle            |
| H3.C   | pont arithmétique global `det₂ ↔ ξ`                  | ouvert                                 |

Règle :

> Promouvoir H3.A ou H3.B en H3.C est interdit.

Le verrou global reste ouvert tant que les étapes suivantes ne sont pas formellement fermées :

* complétion eulérienne globale ;
* identification déterminantielle ;
* correspondance trace / formule explicite ;
* appariement global des zéros ;
* contrôle du résidu critique.

---

## 6. ResGold v38.5

`v38.5.0 ResGold` est intégré dans le dépôt.

Son rôle est de renforcer :

* la gouvernance des invariants ;
* la discipline des statuts ;
* la cohérence des rapports ;
* la séparation local / global ;
* la lisibilité des verrous restants.

ResGold ne transforme pas un verrou ouvert en théorème fermé.

Formule de gouvernance :

```text
ResGold intégré ≠ RH prouvée
ResGold intégré ≠ det₂ ↔ ξ fermé
ResGold intégré ≠ complétion eulérienne globale
```

---

## 7. FCI — Fail-Close Integrity

La couche `FCI/` est fermée localement dans son périmètre actuel.

Elle formalise une discipline fail-close :

* un état critique force le refus ;
* une anomalie force la modulation ;
* le checker ne force jamais une autorisation globale ;
* la Gate agit sur le support causal déclaré ;
* la Gate n’est pas un observateur conscient ;
* elle est un témoin mécanique délégué.

La couche FCI ne doit pas être utilisée pour fermer RH, Hilbert–Pólya, `det₂ ↔ ξ` ou la formule explicite globale.

---

## 8. Garde Davenport–Heilbronn

Le test Davenport–Heilbronn est une garde méthodologique contre les faux critères de RH.

Principe :

> Un candidat de type “condition suffisante pour RH” doit distinguer RH d’un objet connu pour satisfaire des propriétés fonctionnelles similaires mais ne satisfaisant pas RH.

Si une condition candidate est satisfaite par un analogue de Davenport–Heilbronn non-RH, elle ne peut pas être promue comme critère RH.

Statuts possibles :

```text
PASS_GATE
WATCH_GATE
FAIL_GATE
```

Tant que ce gate n’est pas implémenté dans les scripts ou dans Lean, il reste une règle méthodologique, non un audit automatique.

---

## 9. Règles de promotion

### Règle 1 — Pas de promotion numérique

Un résultat mesuré `[M]` ne devient jamais `[D]` sans preuve.

### Règle 2 — Pas de promotion heuristique

Une explication plausible `[H]` ne devient jamais `[D]` par accumulation de cohérence narrative.

### Règle 3 — Pas de promotion conditionnelle

Un théorème conditionnel `[C]` ne devient `[D]` que lorsque toutes ses hypothèses sont fermées.

### Règle 4 — Pas de promotion locale-global

Un résultat fini ou local ne devient jamais un résultat analytique global sans pont formel.

### Règle 5 — Pas d’axiome analytique global sur `main`

Aucun axiome analytique global ne doit être introduit pour fermer artificiellement un verrou.

Si Mathlib bloque, l’obligation doit être nommée, isolée et documentée.

### Règle 6 — Pas de claim implicite

Toute formulation équivalente à RH, Hilbert–Pólya, `det₂ ↔ ξ`, formule explicite globale ou appariement spectre-zéros doit rester explicitement conditionnelle ou ouverte.

---

## 10. Verrous principaux

| Verrou | Description                                     | Statut courant              |
| ------ | ----------------------------------------------- | --------------------------- |
| V1     | opérateur global, domaine, fermeture analytique | `[O]` / `[C]` selon modules |
| V2     | identité `det₂ ↔ ξ`                             | `[O]`                       |
| V3     | complétion eulérienne globale                   | `[O]`                       |
| V4     | appariement spectre ↔ zéros                     | `[O]`                       |
| V5     | corrélations de Möbius / estimées globales      | `[M]` ou `[H]`, non `[D]`   |
| V_W    | positivité de Weil / critère global             | `[O]`                       |

Le registre exact des verrous ouverts doit rester synchronisé avec les fichiers `OpenLocks`, `Lock3`, `AnalyticHorizon` et les rapports générés par `make report`.

---

## 11. Rapports et métriques

Les métriques de build ne doivent pas être figées dans ce fichier sauf comme snapshot daté.

La source courante est :

```text
make report
build_reports/invariants.txt
```

Règle :

> Le nombre de jobs Lean, de modules, de warnings ou de sorries est une métrique de rapport, pas un invariant doctrinal permanent.

Toute mention chiffrée doit préciser :

* la date ;
* le tag ou commit ;
* le périmètre ;
* si `Attic/` est inclus ou exclu ;
* si les couches Active sont incluses.

---

## 12. Phrases interdites sans preuve

Les formulations suivantes sont interdites dans les documents officiels, sauf si explicitement niées ou citées comme contre-exemples :

```text
RH est prouvée
Hilbert–Pólya est fermé
det₂ identifie ξ
la formule explicite est fermée
les zéros sont appariés au spectre
λ = 1/√7 est une constante universelle des zéros
ResGold ferme le pont global
FCI prouve RH
```

Formulation autorisée :

```text
Le dépôt construit une architecture de réduction, de séparation et d’audit.
Le noyau fini est exact.
Les ponts globaux restent ouverts.
```

---

## 13. Mission scientifique

La mission du programme est de produire une architecture rigoureuse reliant :

* un noyau fini modulo 30 ;
* une géométrie spectrale locale ;
* des ponts conditionnels explicitement nommés ;
* des audits de statut ;
* des verrous analytiques globaux non masqués.

La cible n’est pas une annonce prématurée de RH.

La cible est :

> une réduction structurée, auditée, maintenable, où chaque seuil entre fini, mesuré, conditionnel et global reste visible.

---

## 14. Pour Bernard

Le programme est dédié à la mémoire de Bernard Couret (1928–1999), mathématicien autodidacte d’Istres, dont les manuscrits sur les structures modulo 30 ont inspiré le noyau historique du projet.

> La structure préexiste ; la machine atteste ; l’observateur consigne et transmet.

---

*Document maintenu dans `docs/DOCTRINE_PROGRAMME.md`.*
*État : v38.5x — ResGold intégré.*
*Invariant final : `RHClaimed = false`.*
*Pour Bernard Couret.*
