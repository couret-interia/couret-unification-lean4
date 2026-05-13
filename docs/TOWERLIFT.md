# Couret–Unification TowerLift v38x

**Statut : compilé, Matlib v4.29.1**
**Date d’intégration : 2026-05-12**
**Contexte : TowerLift / Sophie Germain v17/18 intégré dans Couret–Unification v38**
**Doctrine : noyau fini démontré `[D]`, couches empiriques et spectrales séparées**

---

## 1. TowerLift lié aux nombres de Sophie Germain

Les trois briques centrales sont :

```text
CouretUnification.Core.SophieGermainHecke
CouretUnification.Core.SophieGermainTowerLift
CouretUnification.Residue.SGShiftSqrt2
```

Ces fichiers constituent une extension finie, locale et machine-vérifiée du noyau Couret–Unification autour du crible de Sophie Germain modulo 30.

---

## 2. Fichiers

### 2.1 `Core/SophieGermainHecke.lean`

**Statut : `[D]` — démontré / machine-certified**

Rôle :

- formalise le décalage de Sophie Germain modulo 30 ;
- définit l’application finie :

```lean
r ↦ (2 * r + 1) % 30
```

- établit les transitions actives :

```text
11 → 23
23 → 17
29 → 29
```

- établit les sorties inactives des autres classes de `U₃₀` ;
- introduit la table de signes concrète `epsilon30`, de type Dirichlet-like, sans dépendre de la couche analytique `DirichletCharacter`.

Ce fichier sert de pont fini entre :

```text
Core/SophieGermainMod30.lean
Core/SophieGermainTowerLift.lean
Residue/SGShiftSqrt2.lean
```

Il reste volontairement dans la couche `Core`, sans import analytique haut.

---

### 2.2 `Core/SophieGermainTowerLift.lean`

**Statut : `[D]` — démontré / machine-certified**

Rôle :

- formalise les classes admissibles Sophie Germain modulo un module `M` ;
- établit le niveau initial :

```text
R₃₀^SG = {11, 23, 29}
```

- vérifie les cardinaux primoriels :

```text
30     : 3
210    : 15
2310   : 135
30030  : 1485
```

- isole la règle combinatoire abstraite :

```text
chaque parent donne exactement ℓ - 2 enfants survivants
```

lorsqu’un nouveau premier `ℓ` est ajouté à la tour primorielle.

La chaîne démontrée est :

```text
3 → 15 → 135 → 1485
```

avec la règle :

```text
N(Mℓ) = N(M) · (ℓ - 2)
```

Ce fichier est un invariant local fini. Il n’établit aucune identité analytique globale.

---

### 2.3 `Residue/SGShiftSqrt2.lean`

**Statut : `[D]` — démontré / machine-certified**

Rôle :

- formalise le bloc symétrisé du SG-shift sur trois nœuds ;
- définit la matrice rationnelle :

```text
        ⎛ 0    0    1/2 ⎞
    M = ⎜ 0    0    1/2 ⎟
        ⎝ 1/2  1/2  0   ⎠
```

- démontre l’identité cubique finie :

```text
M³ = (1/2) · M
```

équivalemment :

```text
2 · M³ = M
```

et :

```text
M · (2M² − I) = 0
```

Cette identité donne l’annulateur polynomial :

```text
X · (2X² − 1)
```

et donc l’interprétation spectrale finie :

```text
λ ∈ {0, +1/√2, −1/√2}
```

Le résultat exact machine-vérifié est l’identité rationnelle cubique. Le symbole `√2` apparaît seulement dans l’interprétation doctrinale, sans usage de `Real.sqrt` dans la preuve Lean.

---

### 2.4 Ombrelles

```text
Core/SophieGermain.lean
SophieGermainUmbrella.lean
```

Ces fichiers servent de façades d’import et regroupent les briques Sophie Germain stabilisées dans v38x. Ils ne modifient pas le statut doctrinal des modules importés.

---

## 3. Résultats formels désormais stabilisés

### 3.1 Crible local Sophie Germain modulo 30

Pour un nombre premier de Sophie Germain `p > 5`, le résidu de `p` modulo 30 doit appartenir à :

```text
{11, 23, 29}
```

Ces classes sont les seules survivantes du test local :

```text
gcd(p, 30) = 1
gcd(2p + 1, 30) = 1
```

---

### 3.2 Tower lift primoriel

Le relèvement primoriel est gouverné par la règle :

```text
|R_{Mℓ}^SG| = (ℓ - 2) · |R_M^SG|
```

L’interprétation est simple :

- chaque classe survivante modulo `M` possède `ℓ` enfants modulo `Mℓ` ;
- un enfant est interdit par `a + tM ≡ 0 mod ℓ` ;
- un enfant est interdit par `2(a + tM) + 1 ≡ 0 mod ℓ` ;
- ces deux enfants sont distincts ;
- il reste donc `ℓ - 2` enfants survivants.

---

### 3.3 Invariant algébrique fini `1/√2`

Le bloc symétrisé associé au SG-shift vérifie :

```text
M³ = (1/2)M
```

Cette relation est une identité algébrique exacte sur `ℚ`.

Elle établit un invariant fini du graphe SG-shift :

```text
module spectral non nul = 1/√2
```

dans le sens doctrinal issu de l’annulateur polynomial.

---

## 4. Séparation doctrinale des constantes

L’intégration clarifie une distinction importante.

### 4.1 `1/√2`

**Statut : `[D]` pour l’identité rationnelle sous-jacente**

Objet :

```text
bloc symétrisé fini du SG-shift
```

Fichier :

```text
Residue/SGShiftSqrt2.lean
```

Nature :

```text
algèbre rationnelle finie
```

Résultat démontré :

```text
M³ = (1/2)M
```

---

### 4.2 `1/√7`

**Statut : non démontré ici**

Objet :

```text
géométrie du simplexe centré Δ⁷ / invariant global du noyau fini général
```

Nature :

```text
invariant géométrique distinct, non identifié au SG-shift fini
```

Le dépôt ne doit pas confondre :

```text
1/√2 : invariant exact du bloc SG-shift
1/√7 : invariant géométrique du cadre Δ⁷, ou hypothèse/observation dans d’autres couches
```

L’ancienne lecture empirique `Δ̃_SG ≈ 1/√7` doit rester classée en `[M]/[H]` ou en legacy, sauf preuve séparée.

---

## 5. Statut des couches

### 5.1 Couche `[D]`

```text
Core/SophieGermainHecke.lean
Core/SophieGermainTowerLift.lean
Residue/SGShiftSqrt2.lean
```

Propriétés :

```text
aucun sorry
aucun axiom
aucun admit
compilation dans CouretUnification.All
```

---

### 5.2 Couche `[M]`

```text
Empirical/SophieGermainExpected.lean
Empirical/SophieGermainTransitions.lean
Numerics/ScanSummary.lean
Numerics/UseScanSummary.lean
```

Ces fichiers encodent ou exposent des données numériques, des verdicts empiriques ou des résumés de scan.

`UseScanSummary.lean` expose le verdict corrigé : proximité spectrale forte disponible, mais stabilité numérique faible non disponible au seuil choisi.

---

### 5.3 Couche `[D-toy] / [M]`

```text
Experimental/TowerLift/ToyModelSpec [D-toy] spécification formelle interne du modèle jouet
Experimental/TowerLift/ToyModel     [D-toy] théorèmes du modèle jouet, si build sans axiome
Experimental/TowerLift/ToyModelFloat    [M] numérique / flottant / expérimental
```

Ces modules sont utiles pour la reproductibilité et les vérifications exécutables, mais ne constituent pas le noyau démonstratif principal.

---

### 5.4 Scripts et rapports

```text
scripts/towerlift/     [M]
docs/towerlift/        [M]/documentation
```

Les scripts Python et les rapports Markdown/JSON/PNG relèvent de la couche numérique et documentaire.

---

## 6. Invariants doctrinaux préservés

L’intégration TowerLift ne modifie pas les invariants globaux du dépôt :

```text
RHClaimed = false
HilbertPolyaClaimed = false
L7Established = false
TopologicalUniversalityClaimed = false
```

Elle ajoute seulement des résultats finis locaux et vérifiés.

---

## 7. Scripts et rapports associés
Les scripts reproductibles sont placés dans :

```text
scripts/towerlift/
```

Les artefacts numériques, rapports Markdown, JSON et PNG sont placés dans :

```text
docs/towerlift/
```

Statut : [M] — numérique, expérimental, reproductible.

---

## 8. Synthèse finale

L’intégration TowerLift dans Couret–Unification v38x est désormais validée au niveau du build complet.

Le paquet apporte trois résultats finis solides :

```text
1. SG-Hecke mod 30 :
   r ↦ 2r + 1 mod 30, transitions actives et inactives.

2. SG-TowerLift :
   R₃₀^SG = {11, 23, 29}
   et règle primorielle ℓ - 2.

3. SGShiftSqrt2 :
   identité cubique M³ = (1/2)M
   et invariant algébrique fini associé à 1/√2.
```

Ce sont des ajouts `[D]` au noyau fini du projet.

Aucune revendication analytique globale n’est ajoutée. Aucune revendication RH ou Hilbert–Pólya n’est introduite. La distinction `1/√2` / `1/√7` est explicitement préservée.

---

## 9. Formule courte pour le registre

```text
TowerLift Sophie Germain intégré à Couret–Unification v38x.

Statut : [D] pour les fichiers Core/SophieGermainHecke,
Core/SophieGermainTowerLift et Residue/SGShiftSqrt2.

Résultats : crible SG mod 30, tower lift primoriel ℓ - 2,
identité cubique rationnelle M³ = (1/2)M.

Aucune dette logique nouvelle.
RHClaimed = false.
HilbertPolyaClaimed = false.
L7Established = false.
```
