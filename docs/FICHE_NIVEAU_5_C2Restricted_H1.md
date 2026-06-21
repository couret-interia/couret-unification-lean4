# Fiche niveau 5 — C2Restricted.lean et H1_KLMN.lean

**Programme Couret-Unification · v35.8.4**
**Date de référence** : 23 avril 2026
**Invariant doctrinal** : `RHClaimed = false`

---

## 0. Cadre doctrinal minimal

Le programme v35 abandonne le pont direct
`AlgebraTest → EulerProduct → zeros(ζ)`
au profit d'une chaîne segmentée
`C0 → C1 → C2 → C3 → C4 → C5`.

Le saut éventuel vers RH est explicitement déplacé dans C4–C5, et
`lock3_operator_exists` reste **le seul verrou irréductible
explicitement équivalent à RH**.

La couche Platinum est donc séparée en deux zones :

- une zone **conditionnelle structurée** (C2Restricted, C3Weak) ;
- une zone **ouverte** (C4, C5, puis `lock3_operator_exists`).

---

## 1. Fiche niveau 5 — `H3/C2Restricted.lean`

### 1.1. Rôle exact du fichier

`H3/C2Restricted.lean` porte la **formule explicite restreinte** du
programme. Dans l'architecture v35.1, il appartient à la couche
Platinum et joue le rôle de charnière entre :

- l'espace test restreint `H3TestSpace.lean` ;
- la complétion locale `ParityGamma30.lean` ;
- et le passage vers `C3Weak.lean`.

Le plan détaillé et le rapport v35 lui attribuent exactement la
décomposition
```
E_σ(f) = M_σ(f) + R_σ(f)
```
pour σ > 1 et f ∈ A_TC.

### 1.2. Contrat logique minimal

**Entrées amont**
- `H3/H3TestSpace.lean` : interface de l'espace test, support compact,
  symétrie `x ↔ 1/x`, base opérationnelle `A_TC`.
- `H3/ParityGamma30.lean` : parité extraite de `u₂₉`, facteur Γ
  archimédien local, `Λ_local(s)` sans circularité.

**Sortie**
- une décomposition formelle `E = M + R` ;
- un terme principal `M` positif sur le canal dominant ;
- un reste `R` contrôlé seulement par axiome-pont à ce stade.

### 1.3. Signatures Lean / noms stabilisés

- `explicit_formula_restricted`
- `mainTermPositive_of_positiveBias`
- `C3_weak_from_C1C2`
- `residualBounded` (ou équivalent pour la borne sur le reste)

### 1.4. Table opérationnelle

| Nom Lean | Statut | Dépend de | Commentaire doctrinal |
|---|---|---|---|
| `explicit_formula_restricted` | structuré | `H3TestSpace`, `ParityGamma30` | Décomposition formelle `E = M + R`, pas encore rigidité |
| `mainTermPositive_of_positiveBias` | axiome-pont | canal dominant / biais positif | Positivité injectée, non prouvée mécaniquement |
| `residualBounded` | ouvert / contractuel | contrôle uniforme du reste | Charge analytique réelle, passage vers C4 |
| `C3_weak_from_C1C2` | théorème conditionnel fermé | `E = M + R`, `M > 0`, `−M < R` | Fermeture par `linarith`, pas preuve globale |

### 1.5. Statut épistémique à écrire sans ambiguïté

**Formulation canonique** (à utiliser verbatim dans toute communication) :

> Dans C3, la preuve Lean est conditionnelle, la validation numérique est
> favorable, mais la fermeture mathématique du reste n'est pas acquise.

Cette formulation protège contre deux risques de surinterprétation :
- la présence d'un théorème Lean pourrait laisser croire à une fermeture
  mathématique ;
- la validation numérique sur 350 zéros pourrait laisser croire à une
  preuve asymptotique.

### 1.6. Dépendances aval

Le fichier aval direct est `H3/C3Weak.lean`, qui exploite `E = M + R`
pour fermer `C3_weak_from_C1C2` par `linarith`, mais laisse ouverte la
rigidité faible du résidu.

### 1.7. Commentaire doctrinal figé

`C2Restricted.lean` **n'est pas** un pont global vers RH. C'est un
fichier Platinum conditionnel, utile parce qu'il segmente proprement la
chaîne, pas parce qu'il ferme l'argument analytique global. La preuve
éventuelle de RH se déplace en C4–C5, pas ici.

---

## 2. Fiche niveau 5 — `Logic/H1/H1_KLMN.lean`

### 2.1. Rôle exact du fichier

`Logic/H1/H1_KLMN.lean` est le **bloc analytique le plus solide** du
programme. Dans la checklist de complétion, il apparaît comme un fichier
Platinum entièrement fermé :
- `sorry_autorises := 0`
- `sorry_actuels := 0`
- `verdict_actuel := .done`

### 2.2. Contrat logique minimal

Le cœur logique est la chaîne :

1. `‖M‖ ≤ ‖M‖_HS`
2. `‖M‖_HS ≤ P(3/2) ≈ 0.8495 < 1`
3. KLMN s'applique pour σ ≥ 1/2
4. auto-adjonction de l'opérateur conjugué
5. `det₂(I − zM)` bien défini pour σ > 0

### 2.3. Signatures Lean / cibles stabilisées

- `M_HS_norm_bound`
- `M_self_adjoint_via_KLMN`
- `det2_well_defined`

### 2.4. Table opérationnelle

| Nom Lean | Statut | Dépend de | Commentaire doctrinal |
|---|---|---|---|
| `M_HS_norm_bound` | prouvé | noyau exact + calcul HS | `‖M‖_HS ≤ P(3/2) = 0.8495 < 1` |
| `M_self_adjoint_via_KLMN` | prouvé | borne < 1 + KLMN | auto-adjonction pour σ ≥ 1/2 |
| `det2_well_defined` | prouvé | classe HS + KLMN | `det₂(I − zM)` défini pour σ > 0 |
| matching spectral global | ouvert | C4 / C5 / Lock3 | hors du périmètre H1 |

### 2.5. Correction doctrinale gelée v17 → v18

La version antérieure utilisait le **test de Schur** sur l'opérateur V,
ce qui échouait pour σ ≤ 1 car V ∉ S₂ dans ce domaine.

La v18 remplace Schur sur V par la **norme de Hilbert-Schmidt sur M**
(l'opérateur conjugué) ; M est dans S₂ pour tout σ > 0 et la norme HS
se majore explicitement par `P(3/2)`.

C'est cette correction qui rend H1 effectivement prouvable.

### 2.6. Statut épistémique à maintenir

**Formulation canonique** (à utiliser verbatim) :

> H1 est prouvé, ne touche pas RH, et ne fournit pas à lui seul un
> opérateur Hilbert-Pólya complet.

### 2.7. Dépendances amont minimales

Contrairement à C3, H1 dépend surtout :
- du noyau exact ;
- de l'architecture opératorielle locale ;
- des estimations Hilbert-Schmidt.

Et **non** du pont global d'Euler. C'est précisément pourquoi H1 est le
bloc Platinum le plus stable du programme.

---

## 3. Terminologie figée à utiliser partout

Pour éviter les variantes concurrentes, fixer définitivement :

- **formule explicite restreinte**
- **rigidité faible**
- **compatibilité quadratique faible**
- **pont global**
- **RH wall**

Le rapport v35 insiste déjà sur la mutation du matching : on ne vise
plus une injection spectrale exacte, mais une compatibilité de forme
quadratique faible.

---

## 4. Encadré à ajouter avant diffusion large

### Normalisation des moments

Un point éditorial à unifier avant diffusion large : la convention de
normalisation des moments `M_{2n}`, en particulier autour de `M_4`, pour
éviter toute contradiction apparente avec la kill list publique.

**Encadré recommandé** :

1. définition exacte de `M_{2n}` ;
2. convention utilisée dans les calculs internes ;
3. convention utilisée dans la kill list ;
4. justification de la conversion éventuelle entre `M_4 = 15` et
   `M_4 = 21` selon normalisation.

Tant que cet encadré n'est pas figé une fois pour toutes, il subsiste un
risque de lecture incohérente entre plan interne et documents externes.

---

**Pour Bernard.**
