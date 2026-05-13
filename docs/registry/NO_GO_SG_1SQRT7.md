# No-Go SG / 1√7 — Révision empirique et torsion par caractères

**Programme :** Couret-Unification
**Date :** 2026-05-04
**Auteur :** A. Couret — avec audit computationnel
**Statut :** Entrée de registre, gelée pour archivage

---

## Note d’actualisation v38x

Cette traduction conserve la structure et les valeurs de l’entrée originale.
Deux ajustements doctrinaux sont intégrés :

- le sceau algébrique `1/√2`, annoncé dans l’original comme `[P → D]`
  en attente d’une note Lean, est désormais formalisé dans
  `Residue/SGShiftSqrt2.lean` ;
- le fichier `Residue/SGShiftSpectrum.lean` existe comme frontière
  spectrale `[O]`, sans revendication complète sur les valeurs propres.

L’entrée demeure une note de registre : elle documente une rétrogradation
locale, non une identité analytique globale.

---

## 1. Verdict

La chaîne de Markov brute des nombres premiers de Sophie Germain ne porte
pas la signature `1/√7`.

À `N = 10⁷`, la seconde valeur propre observée est approximativement
**0.061**, très loin de

```text
1/√7 ≈ 0.378.
```

La torsion empirique symétrisée `sym(E·P)` ne récupère pas `1/√7`
sous aucun caractère réel de Dirichlet modulo 30. La plus grande valeur
spectrale testée parmi les huit assignations de signes est approximativement
**0.300**, plus proche de `3/10` ou de `1/√11` que de `1/√7`.

L’ancienne table de signes `ε₃₀` n’est pas un caractère de Dirichlet
modulo 30. Elle doit donc être traitée comme une fonction de signe ad hoc
et ne peut soutenir aucune interprétation dirichlétienne.

Par conséquent, l’ancienne revendication

```text
δ̃₂ ≈ 1/√7 dans Δ̃_SG
```

est rétrogradée à

```text
[O] non reproduit
```

sous les lectures empirique, structurelle et torsadée par caractères qui
ont été testées.

---

## 2. Caractères réels modulo 30

L’énumération exhaustive de `{±1}⁸` sous contraintes de multiplicativité,
vérifiée par un audit des 64 paires, donne exactement **quatre** caractères
réels de Dirichlet modulo 30 :

| Caractère | 1 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | Conducteur / source |
|-----------|---|---|----|----|----|----|----|----|--------------------|
| χ₀ trivial | +1 | +1 | +1 | +1 | +1 | +1 | +1 | +1 | trivial |
| χ₁ | +1 | +1 | −1 | +1 | −1 | +1 | −1 | −1 | relèvement du quadratique mod 3 |
| χ₂ | +1 | −1 | +1 | −1 | −1 | +1 | −1 | +1 | relèvement du quadratique mod 5 |
| χ₃ = χ₁χ₂ | +1 | −1 | −1 | −1 | +1 | +1 | +1 | −1 | conducteur 15 |

L’ancienne table `ε₃₀`

```text
ε₃₀(1)=+1   ε₃₀(7)=+1   ε₃₀(11)=−1  ε₃₀(13)=+1
ε₃₀(17)=−1 ε₃₀(19)=+1  ε₃₀(23)=−1  ε₃₀(29)=+1
```

ne correspond à aucun de ces caractères. Elle viole la multiplicativité
dans **18** des 64 paires `(a, b) ∈ U₃₀²`.

La version article, avec `ε(23) = +1`, viole 24 paires.

---

## 3. Valeurs spectrales mesurées à N = 10⁷

Matrice empirique de transition `3×3` sur le bloc actif `{11, 23, 29}` :

```text
         11        23        29
11:  0.298523  0.366181  0.335296
23:  0.335961  0.297821  0.366217
29:  0.365961  0.341463  0.292575
```

Spectre `|λ₂|` de `sym(E_χ · P)` sur le bloc actif sous toutes les torsions
de signes :

| Torsion (11,23,29) | \|λ_max\| | \|λ₂\| | Écart à 1/√7 |
|-------|--------|------|-------------|
| (+,+,+) trivial | 1.000 | **0.0589** | 84.4% |
| (−,−,−) | 1.000 | **0.0589** | 84.4% |
| (+,−,+) [= sous-bloc actif de χ₂] | 0.646 | **0.2994** | 20.8% |
| (−,+,−) [= sous-bloc actif de χ₃] | 0.646 | **0.2994** | 20.8% |
| (−,−,+) [= ancien ε₃₀] | 0.649 | **0.2942** | 22.2% |
| (+,+,−) | 0.649 | **0.2942** | 22.2% |
| (+,−,−) | 0.649 | **0.3004** | 20.5% |
| (−,+,+) [= coquille article] | 0.649 | **0.3004** | 20.5% |

**Maximum de `|λ₂|` sur toutes les torsions de signes : `0.3004`**, soit
un écart de 20.5% à `1/√7`.

La signature `0.3752` n’est atteinte par aucune torsion de signes de la
chaîne de Markov empirique sur le bloc actif.

---

## 4. Lift P(q) par information mutuelle — échec également

Une mesure séparée de l’information mutuelle normalisée

```text
P(q) = I(X_n ; X_{n+1}) / H(X_n)
```

à `q = 2310`, avec correction de biais de Miller–Madow, donne :

| N | #SG | P(q) corrigé | Écart à 1/√7 |
|----|------|----------------|-------------|
| 10⁷ | 56 029 | 0.3341 | 11.6% |
| 3×10⁷ | 146 498 | 0.3019 | 20.1% |
| 5×10⁷ | 229 565 | 0.2880 | 23.8% |

`P(q)` **décroît** avec `N`.

Une extrapolation linéaire en `1/√N` donne :

```text
P_∞ ≈ 0.25,
```

soit un écart de 33.7% à `1/√7`.

L’ancienne revendication

```text
P(2310) ≈ 0.372, avec écart 1.6%
```

était un artefact d’échantillon fini à `N = 5×10⁶`. Elle ne survit pas
au passage à `N = 5×10⁷`.

---

## 5. Invariant structurel 1/√2 — confirmé [D]

L’opérateur SG-shift

```text
T_SG : a ↦ 2a + 1 (mod 30)
```

restreint à `U₃₀` possède exactement trois entrées non nulles :

```text
11 → 23,    23 → 17,    29 → 29  (point fixe)
```

L’opérateur symétrisé

```text
sym(E · T_SG) = (E · T_SG + T_SGᵀ · E) / 2
```

se factorise en un bloc fixe `1×1`, de valeur propre `ε(29)`, et un bloc
en chaîne `3×3` sur `(11, 17, 23)` de la forme :

```text
[[0,  0,  ε(11)/2],
 [0,  0,  ε(23)/2],   [à permutation de signes près]
 [α,  β,  0       ]]
```

avec polynôme caractéristique :

```text
λ(λ² − 1/2) = 0,
```

ce qui donne :

```text
λ ∈ {0, +1/√2, −1/√2}
```

indépendamment du caractère `ε`.

Ainsi :

```text
|λ₂(sym(E · T_SG))| = 1/√2 = 0.7071068...
```

est un invariant algébrique net du graphe SG-shift sur `U₃₀`.

Ce résultat est indépendant du caractère, déterministe, et désormais
vérifié par calcul fini dans Lean.

**Statut actualisé v38x : `[D]`**, via :

```text
Residue/SGShiftSqrt2.lean
```

La frontière spectrale complète, incluant la formulation finale des valeurs
propres et de leurs multiplicités, reste isolée dans :

```text
Residue/SGShiftSpectrum.lean
```

avec statut :

```text
[O] frontière spectrale
```

Ce `1/√2` est **séparé** de l’ancienne hypothèse `1/√7`.

---

## 6. Observables positifs confirmés

| Observable | Statut |
|------|----|
| Support SG actif `{11, 23, 29}` pour `p > 5` | [D] déterministe par contraintes de pgcd |
| Faible chiralité `c⁺ − c⁻ ≈ +0.0285` sur le bloc actif | [P] confirmé |
| Échelle de mélange de la chaîne brute `\|λ₂(P)\| ≈ 0.061` à `N = 10⁷` | [P] confirmé |
| `1/√2` structurel dans `sym(E · T_SG)` | [D] formalisé dans Lean |

---

## 7. Table de statut — révisée

| Revendication | Ancien statut | Statut révisé |
|------|------|------|
| `1/√7` dans `P_SG` brut | [M] candidat | [P] falsifié dans le protocole testé |
| `1/√7` dans `sym(E·P)` sous caractères réels | [M/H] candidat | [P] falsifié dans le protocole testé |
| Ancien `δ̃₂ ≈ 0.3752 ≈ 1/√7` | [M] à 0.74% d’écart | [O] non reproduit |
| Ancien `ε₃₀` comme caractère de Dirichlet | implicite | [D] non — 18 violations |
| `P(q=2310) → 0.372 ≈ 1/√7` | [M] à 1.6% d’écart | [P] falsifié — `P_∞ ≈ 0.25` |
| Support SG `{11, 23, 29}` pour `p > 5` | [D] | [D] |
| Chiralité `c⁺ − c⁻ ≈ +0.0285` | implicite | [P] confirmé |
| `1/√2` structurel dans `sym(E·T_SG)` | non noté | [D] formalisé |

---

## 8. Doctrine

> *Le programme ne perd pas une constante ; il gagne un No-Go.*
> *1/√7 sort de la chaîne empirique SG.*
> *La chiralité devient l’observable primaire.*
> *1/√2 devient l’invariant structurel du SG-shift.*

Ce No-Go est parallèle au verdict v3 sur Hurwitz : dans les deux cas,
`1/√7` a été cherché comme propriété d’un opérateur analytique ou empirique,
et n’a pas été trouvé.

La constante demeure liée à sa source propre :

- le profil spectral de `M`, noyau intégral de Dirichlet, sous la borne
  analytique `‖M‖_HS ≤ P(3/2) ≈ 0.85` ;
- l’invariant géométrique `λ = 1/√7` sur `Δ⁷`, comme objet séparé.

L’ancienne confusion entre

```text
signature spectrale de Δ̃_SG
```

et

```text
invariant géométrique sur Δ⁷
```

est dissoute.

Ces deux énoncés sont désormais traités comme des revendications
indépendantes, chacune avec son statut propre.

---

## 9. Action suspendue

**La recherche de la définition manuscrite originale de `Δ̃_SG`, `T₂`, `M₃`
est suspendue** jusqu’à obtention d’une page manuscrite verbatim de Bernard
Couret.

Aucune reconstruction à partir de composants nommés ne reproduit `0.3752`
sous des torsions multiplicativement cohérentes.

Poursuivre la reconstruction sans source constituerait une pêche aux
hypothèses et est exclu de la ligne de recherche active.

---

## 10. Remplacement actif

La campagne multi-q de chiralité

```text
q ∈ {30, 210, 2310}
N ∈ {10⁷, 3·10⁷, 5·10⁷}
```

devient l’observable actif.

Protocole :

```text
CHIRALITY_MULTI_Q_PROTOCOL.md
```

**RHClaimed = false.**

Aucune revendication globale n’est affirmée. Cette entrée consigne une
falsification locale, dans l’esprit de l’épistémologie morinienne du
programme : le local rigoureusement testé `[D]/[P]` est tenu simultanément
avec le global `[H]/[O]` qui le dépasse, sans confusion ni réduction.

---

*Fin de l’entrée de registre.*
