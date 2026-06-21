# Note technique — Pourquoi `Z30` avant `(ZMod 30)ˣ`

**Programme Couret–Unification · v37**
**Couche `Residue/` — modules `ClosureTC.lean`, `CycleCoset.lean`, à venir `UnitsBridge.lean` et `Isospectrality.lean`**

---

## Objet

Cette note documente la décision prise dans les modules v37
`ClosureTC.lean` et `CycleCoset.lean` : travailler d'abord dans

```lean
abbrev Z30 := ZMod 30
```

plutôt que dans le groupe des unités

```lean
(ZMod 30)ˣ
```

Cette décision est volontaire. Elle ne nie pas que l'objet
mathématique naturel soit

$$G_{30} = (\mathbb{Z}/30\mathbb{Z})^\times.$$

Elle sépare simplement deux niveaux :

- **niveau calculatoire local** : `ZMod 30` ;
- **niveau spectral / caractériel** : `(ZMod 30)ˣ`.

---

## 1. Motivation

Les Tickets 1 et 2 portent uniquement sur des faits finis,
locaux et calculatoires :

- $TC = \{1, 11, 29\}$
- $K_4 = \{1, 11, 19, 29\}$
- $\rho(TC) = \{19\}$
- $\text{Cycle} = \{1, 7, 19, 13\}$
- $\text{Coset} = \{11, 17, 29, 23\}$
- $TC = \{1\} \cup (K_4 \cap \text{Coset})$

Ces énoncés ne nécessitent pas la structure complète de groupe
des unités. Ils nécessitent seulement :

- `ZMod 30`
- `Finset Z30`
- multiplication modulo 30
- décidabilité des égalités finies

Dans ce cadre, les preuves se ferment naturellement par

```lean
decide
```

ou, si nécessaire,

```lean
native_decide
```

---

## 2. Pourquoi éviter les Units au début

Le type `(ZMod 30)ˣ` est mathématiquement plus fidèle à $G_{30}$,
mais il introduit une complexité technique Lean supplémentaire :

- coercions entre `Nat`, `ZMod 30` et `Units` ;
- preuves de coprimalité ;
- constructeurs comme `ZMod.unitOfCoprime` ;
- noms de lemmes Mathlib dépendants de la version ;
- friction sur les égalités de Units (deux unités peuvent être
  égales en valeur mais pas définitionnellement identiques selon
  comment elles ont été construites).

Or les Tickets 1 et 2 ne gagnent rien à cette complexité.

Le choix `Z30` permet donc de fermer rapidement un noyau local
robuste, sans exposer les fichiers `ClosureTC.lean` et
`CycleCoset.lean` aux variations de Mathlib.

---

## 3. Dette technique assumée

Cette décision crée une dette technique contrôlée.

Pour les modules combinatoires :

- `ClosureTC.lean`
- `CycleCoset.lean`

le type `Z30` suffit.

Mais pour le Ticket 3 :

- `Isospectrality.lean`

le passage à `(ZMod 30)ˣ` deviendra probablement nécessaire,
car les objets spectraux naturels sont :

- caractères multiplicatifs $\chi : G_{30} \to \mathbb{C}^\times$ ;
- opérateurs de convolution sur $\text{Fun}(G_{30}, \mathbb{C})$ ;
- sommes de caractères $\lambda_\chi(S) = \sum_{s \in S} \chi(s)$ ;
- diagonalisation par les caractères.

Ces constructions vivent plus naturellement sur le groupe
`(ZMod 30)ˣ` et non sur tout l'anneau `ZMod 30`. La théorie
des caractères de Mathlib (`MulChar`) attend un groupe en entrée,
pas un anneau, et les théorèmes d'orthogonalité s'énoncent
sur les caractères du groupe des unités.

---

## 4. Principe architectural

La décision suit la doctrine v37 :

> **statut de vérité ≠ position architecturale**
> **`[P]` local ≠ Frozen Core automatiquement**

Les résultats de `ClosureTC.lean` et `CycleCoset.lean` sont
localement prouvables, mais restent dans la couche

```
Residue/  : Active
```

Ils ne sont pas promus au Frozen Core.

De même, le choix `Z30` n'est pas une revendication structurelle
globale. C'est un choix de **robustesse locale**, cohérent avec
le principe que la position architecturale d'un résultat est
distincte de son statut de vérité.

---

## 5. Rôle futur de `UnitsBridge.lean`

Le module futur

```
Residue/UnitsBridge.lean
```

devra servir de passerelle entre les deux mondes :

```
Finset Z30  ←→  Finset (ZMod 30)ˣ
```

Son rôle sera de relier les résidus inversibles explicites

```lean
{1, 7, 11, 13, 17, 19, 23, 29} : Finset Z30
```

aux unités correspondantes de `(ZMod 30)ˣ`, et de fournir des
théorèmes de cohérence permettant de réutiliser les résultats
combinatoires de `ClosureTC.lean` et `CycleCoset.lean` dans le
contexte spectral d'`Isospectrality.lean`.

Il devra être écrit **seulement après confirmation de la
configuration Lean/Mathlib utilisée par Thomas**, pour que les
noms exacts des constructions Mathlib (`ZMod.unitOfCoprime`,
`Units.mk`, `Units.val`, etc.) soient ceux qui existent réellement
dans la branche utilisée, et non des approximations.

---

## 6. Règle de prudence

Tant que les Tickets 1 et 2 ne sont pas confirmés par build :

- ne pas ajouter de complexité Units ;
- ne pas anticiper les noms exacts Mathlib ;
- ne pas ouvrir `Isospectrality.lean` ;
- ne pas déplacer les résultats vers Frozen Core.

Après validation de Thomas, on pourra ouvrir proprement :

- `Residue/UnitsBridge.lean`
- `Residue/Isospectrality.lean`

---

## 7. Formule synthétique

`Z30` sert à fermer les faits combinatoires locaux.
`(ZMod 30)ˣ` servira à porter les caractères et le spectre.
`UnitsBridge` sera le pont, mais seulement après validation du socle.

> **Calcul local d'abord ; structure de groupe ensuite ; spectre en dernier.**

---

Cette note protège un point fragile : elle explique que `Z30`
n'est pas un contournement mathématique, mais une stratégie de
**staging Lean**. Elle formalise la dette technique avant qu'elle
ne devienne implicite, et fournit un cahier des charges minimal
pour `UnitsBridge.lean` quand viendra le moment de l'écrire.
