# No-Go SG / 1√7 — Révision empirique et torsion par caractères

**Programme :** Couret-Unification
**Date :** 2026-05-04
**Auteur :** A. Couret — avec audit computationnel
**Statut :** Entrée de registre, gelée pour archivage
**Nature :** Reconstruction française consolidée à partir du fragment récupéré et des résultats formels associés

---

## ⚠ Note de reconstruction

Ce document a été partiellement reconstitué après expiration des uploads.
Les sections 1 à 3 proviennent du fragment récupéré. Les sections suivantes
sont une reconstruction doctrinale prudente, fondée sur :

- la matrice empirique Sophie Germain `M3` formalisée dans
  `CouretUnification.Core.SophieGermain`,
- les valeurs spectrales mentionnées dans le fragment récupéré,
- la transition vers l’invariant algébrique `1/√2` formalisé dans
  `SGShiftSqrt2.lean`.

Cette version ne prétend pas être l’original exact. Elle sert de version
de registre restaurée, lisible et cohérente, jusqu’à récupération éventuelle
du fichier source complet.

---

## 1. Verdict

La chaîne de Markov brute des nombres premiers de Sophie Germain ne porte
pas la signature `1/√7`.

À `N = 10⁷`, la seconde valeur propre observée est approximativement
`0.061–0.062`, très loin de

```text
1/√7 ≈ 0.377964.
```

La torsion empirique symétrisée `sym(E·P)` ne permet pas non plus de
retrouver `1/√7` sous les caractères réels de Dirichlet modulo 30 testés.
La plus grande valeur spectrale pertinente observée dans les assignations
de signes testées est approximativement

```text
0.300,
```

valeur plus proche de `3/10` ou de `1/√11` que de `1/√7`.

L’ancienne table de signes `ε₃₀` n’est pas un caractère de Dirichlet
modulo 30. Elle doit donc être traitée comme une fonction de signe ad hoc,
sans interprétation dirichlétienne.

Par conséquent, l’ancienne revendication

```text
δ̃₂ ≈ 1/√7 dans Δ̃_SG
```

est rétrogradée au statut :

```text
[O] non reproduit
```

sous les lectures empirique, structurelle et torsadée par caractères qui
ont été testées.

---

## 2. Caractères réels modulo 30

L’énumération exhaustive de `{±1}⁸` avec contraintes de multiplicativité,
vérifiée par audit sur les 64 paires `(a, b) ∈ U₃₀²`, donne exactement
quatre caractères réels de Dirichlet modulo 30 :

| Caractère | 1 | 7 | 11 | 13 | 17 | 19 | 23 | 29 | Conducteur / source |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| χ₀ trivial | +1 | +1 | +1 | +1 | +1 | +1 | +1 | +1 | trivial |
| χ₁ | +1 | +1 | −1 | +1 | −1 | +1 | −1 | −1 | relèvement du caractère quadratique mod 3 |
| χ₂ | +1 | −1 | +1 | −1 | −1 | +1 | −1 | +1 | relèvement du caractère quadratique mod 5 |
| χ₃ = χ₁χ₂ | +1 | −1 | −1 | −1 | +1 | +1 | +1 | −1 | conducteur 15 |

L’ancienne table `ε₃₀`

```text
ε₃₀(1)=+1   ε₃₀(7)=+1   ε₃₀(11)=−1  ε₃₀(13)=+1
ε₃₀(17)=−1 ε₃₀(19)=+1  ε₃₀(23)=−1  ε₃₀(29)=+1
```

ne coïncide avec aucun de ces caractères.

Elle viole la multiplicativité dans 18 des 64 paires `(a, b) ∈ U₃₀²`.
La variante présente dans l’ancienne version article, avec `ε(23)=+1`,
viole 24 des 64 paires.

Conclusion :

```text
ε₃₀ est une fonction de signe ad hoc.
ε₃₀ n’est pas un caractère de Dirichlet modulo 30.
```

---

## 3. Valeurs spectrales mesurées à N = 10⁷

La matrice empirique `3×3` des transitions sur le bloc actif
`{11, 23, 29}` est :

```text
        vers 11   vers 23   vers 29
11       3042      3738      3427
23       3431      3072      3787
29       3733      3481      2942
```

Les sommes de lignes sont :

```text
R₁₁ = 10207
R₂₃ = 10290
R₂₉ = 10156
```

Le total est :

```text
N = 30653.
```

La matrice de transition normalisée par lignes est donc approximativement :

```text
P ≈
[ 0.29803   0.36622   0.33575 ]
[ 0.33343   0.29854   0.36803 ]
[ 0.36757   0.34275   0.28968 ]
```

Ses valeurs propres sont de la forme :

```text
1,
-0.05687 + 0.02531 i,
-0.05687 - 0.02531 i.
```

Le module spectral non trivial vaut donc approximativement :

```text
|λ₂| ≈ 0.06225.
```

Comparaison :

```text
|λ₂| ≈ 0.06225
1/√7 ≈ 0.37796
```

La signature `1/√7` n’est donc pas présente dans la chaîne SG brute.

---

## 4. Torsions symétrisées par signes

On considère des matrices de signes `E`, puis l’opérateur symétrisé :

```text
sym(E·P) = (E·P + Pᵀ·E) / 2.
```

Cette opération vise à tester si une chiralité cachée, ou une lecture
par caractère, permettrait de faire émerger une valeur spectrale proche
de `1/√7`.

Les tests effectués montrent :

```text
aucune torsion réelle de Dirichlet modulo 30 ne récupère 1/√7.
```

La valeur spectrale pertinente maximale observée dans les assignations
testées est approximativement :

```text
0.300.
```

Cette valeur est numériquement proche de :

```text
3/10 = 0.300
1/√11 ≈ 0.30151
```

mais elle reste éloignée de :

```text
1/√7 ≈ 0.37796.
```

Cette observation ne suffit pas à établir une nouvelle constante
structurelle. Elle sert seulement de diagnostic négatif contre l’ancienne
lecture SG / `1√7`.

---

## 5. Rétrogradation de l’ancien scénario SG / 1√7

L’ancien scénario postulait l’existence d’un opérateur `Δ̃_SG` dont le
second défaut spectral ou la seconde valeur propre normalisée aurait été
proche de :

```text
1/√7.
```

Les audits empiriques et algébriques imposent désormais la rétrogradation
suivante :

| Élément | Ancien statut | Nouveau statut |
|---|---|---|
| `δ̃₂ ≈ 1/√7` dans `Δ̃_SG` | hypothèse positive | `[O] non reproduit` |
| `ε₃₀` comme caractère | implicite / supposé | faux : non multiplicatif |
| Lecture Dirichlet de `ε₃₀` | candidate | rejetée |
| Signal SG brut | candidat `1/√7` | absent |
| Signal torsadé | candidat `1/√7` | absent |
| Chiralité SG | empirique | conservée comme observable |
| Invariant algébrique SG | non isolé | remplacé localement par `1/√2` |

La conclusion est volontairement restrictive :

```text
Le programme SG ne valide pas 1/√7.
Il conserve une chiralité empirique.
Il admet un invariant algébrique local distinct : 1/√2.
```

---

## 6. Transition vers l’invariant 1/√2

Le résultat positif propre au sous-programme SG n’est pas `1/√7`, mais
`1/√2`.

Le fichier :

```text
lean/CouretUnification/Residue/SGShiftSqrt2.lean
```

isole le bloc non trivial du SG-shift symétrisé et prouve l’identité
algébrique :

```text
M³ = (1/2) M
```

ou, de manière équivalente :

```text
2 M³ = M.
```

Ainsi, toute valeur propre `λ` de ce bloc vérifie :

```text
2λ³ − λ = 0
```

c’est-à-dire :

```text
λ · (2λ² − 1) = 0.
```

Les racines réelles sont :

```text
0, +1/√2, −1/√2.
```

Le module spectral non nul du bloc est donc :

```text
1/√2.
```

Ce résultat est :

```text
fini,
rationnel dans sa preuve,
indépendant de Real.sqrt dans Lean,
indépendant de RH,
indépendant de toute continuation analytique.
```

---

## 7. Séparation doctrinale : 1/√2 versus 1/√7

Il faut désormais séparer strictement deux invariants :

| Invariant | Lieu | Statut | Interprétation |
|---|---|---|---|
| `1/√7` | géométrie centrée de `Δ⁷` | conservé hors SG | invariant géométrique du noyau fini global |
| `1/√2` | bloc SG-shift symétrisé | prouvé algébriquement | invariant structurel local du sous-programme SG |

Le sous-programme SG ne récupère pas `1/√7`.

Il révèle au contraire un invariant local différent :

```text
1/√2.
```

Cette séparation évite une confusion doctrinale importante :

```text
1/√7 n’est pas une constante universelle du programme.
1/√7 appartient à la géométrie Δ⁷.
1/√2 appartient au bloc SG-shift symétrisé.
```

---

## 8. Conséquence pour le registre

**Acquis négatifs :**

- `δ̃₂ ≈ 1/√7` dans `Δ̃_SG` est rétrogradé à `[O] non reproduit`.
- `ε₃₀` n’est pas un caractère de Dirichlet modulo 30.
- La lecture dirichlétienne de l’ancienne table de signes est rejetée.
- La chaîne brute SG ne porte pas la signature `1/√7`.
- Les torsions testées ne restaurent pas `1/√7`.

**Acquis positifs :**

- La chiralité SG demeure un observable empirique réel du programme.
- La matrice de transitions SG est formalisable comme donnée finie.
- Les invariants combinatoires de `M3` sont vérifiables dans Lean.
- Le bloc SG-shift symétrisé possède un invariant algébrique local `1/√2`.
- L’identité `2 M³ = M` est prouvée dans Lean.

**Doctrine maintenue :**

```text
RHClaimed = false
HilbertPolyaClaimed = false
Det2IdentityClaimed = false
TopologicalUniversalityClaimed = false
```

---

## 9. Formulation finale du no-go

Le résultat de ce fichier n’est pas une défaite du sous-programme SG.
C’est une clarification.

L’ancien chemin :

```text
SG → Δ̃_SG → 1/√7
```

n’est pas reproduit.

Le chemin désormais conservé est :

```text
SG empirique → chiralité mesurée
SG algébrique fini → bloc symétrisé → 1/√2
Δ⁷ global → géométrie centrée → 1/√7
```

Le no-go protège donc le programme contre une fausse identification :

```text
1/√2 ≠ 1/√7.
```

Et il précise la bonne localisation des deux constantes :

```text
1/√2 : invariant SG local.
1/√7 : invariant géométrique Δ⁷ global.
```

---

## 10. Statut final

Cette entrée de registre gèle la rétrogradation suivante :

```text
SG / 1√7 : [O] non reproduit.
```

Elle autorise en revanche le remplacement doctrinal :

```text
SG / 1√2 : [P → D] sceau algébrique local.
```

Le fichier compagnon positif est :

```text
SGShiftSqrt2.lean
```

Le fichier spectral complet reste ouvert :

```text
SGShiftSpectrum.lean
```

`RHClaimed = false`.