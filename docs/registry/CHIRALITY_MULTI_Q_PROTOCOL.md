# Protocole multi-q de chiralité SG

**Programme :** Couret-Unification
**Date :** 2026-05-04
**Statut :** Protocole de recherche actif

---

## 1. Objectif

Mesurer si la chiralité Sophie Germain observée modulo 30 persiste,
se dissout ou se transforme sous les relèvements primoriels :

```text
q = 30 → 210 → 2310.
```

Ce protocole remplace la ligne d’investigation suspendue

```text
δ̃₂ → 1/√7
```

voir `NO_GO_SG_1SQRT7.md`, par un observable **mesuré, stable et propre** :
la composante antisymétrique de l’opérateur de transition SG.

---

## 2. Définitions

Soit `q` un primoriel, `U_q = (ℤ/qℤ)*`, et définissons le support actif SG
modulo `q` par :

```text
A_q = { r ∈ U_q : gcd(2r + 1, q) = 1 }.
```

Pour `r ∈ A_q`, les nombres premiers `p ≡ r (mod q)` donnent
`2p + 1` premier avec `q`, condition nécessaire pour que `p` soit un
nombre premier de Sophie Germain lorsque `q ≤ 2p`.

Pour les nombres premiers de Sophie Germain `p ≤ N`, on définit la matrice
empirique de transition sur `A_q` :

```text
T_q[i, j] = #{ k : sg[k] ≡ A_q[i] (mod q), sg[k+1] ≡ A_q[j] (mod q) }
P_q       = T_q normalisée par lignes.
```

**Chiralité native** — intrinsèque à `q` :

```text
χ_q^native = ‖(P_q − P_q^T) / 2‖_F
```

où `‖·‖_F` désigne la norme de Frobenius de la partie antisymétrique.

**Chiralité projetée** — relèvement modulo 30 :

Pour `q > 30`, on projette chaque résidu `r ∈ A_q` vers

```text
r mod 30 ∈ {11, 23, 29}.
```

On construit alors la matrice de transition `3×3` projetée `P_q→30`, puis
on mesure :

```text
c⁺(q) = (P_q→30[0,1] + P_q→30[1,2] + P_q→30[2,0]) / 3
c⁻(q) = (P_q→30[0,2] + P_q→30[1,0] + P_q→30[2,1]) / 3
χ_q^proj = c⁺(q) − c⁻(q)
```

Ce test vérifie si la chiralité modulo 30 survit lorsqu’elle est projetée
depuis un module plus fin.

---

## 3. Ligne de base — q = 30, N = 10⁷

Mesure à `N = 10⁷` :

```text
56 029 nombres premiers de Sophie Germain,
100% dans les classes actives.
```

- Bloc actif : `{11, 23, 29}`
- Préférence de cycle direct : `c⁺ ≈ 0.36612`
- Cycle rétrograde : `c⁻ ≈ 0.33757`
- Chiralité : `χ ≈ +0.02855`
- Excès relatif `(c⁺ − c⁻) / c⁻` : environ **+8.5%**
- Norme de Frobenius antisymétrique : `0.03505`

La chiralité est **petite mais nettement au-dessus du plancher de biais** :
le bruit d’indépendance pour `n_active = 3` avec 56k échantillons est très
inférieur à `10⁻³`.

Elle constitue donc un trait arithmétique réel des nombres premiers de
Sophie Germain consécutifs, et non un artefact d’échantillonnage.

---

## 4. Niveaux à tester

| q | n_active | Position dans la tour |
|---|----------|-----------------------|
| 30 | 3 | 1er primoriel |
| 210 | 15 | 2e primoriel |
| 2310 | 135 | 3e primoriel |

Tailles d’échantillon :

```text
N ∈ {10⁷, 3·10⁷, 5·10⁷}.
```

---

## 5. Sorties par paire (q, N)

Pour chaque paire `(q, N)`, enregistrer :

| Champ | Type |
|----|---|
| q | entier |
| N | entier |
| # nombres premiers SG ≤ N | entier |
| n_active | entier |
| Comptages de transition `T_q` | matrice |
| `P_q` | matrice |
| `χ_q^native` — norme de Frobenius de la partie antisymétrique | flottant |
| `χ_q^proj` — projection modulo 30 | flottant |
| `c⁺(q→30)` | flottant |
| `c⁻(q→30)` | flottant |
| `‖A‖_F / ‖P − Π‖_F` — fraction chirale | flottant |
| `\|λ₂(P_q)\|` | flottant |
| Partie imaginaire de `λ₂` — mode rotationnel | flottant |

---

## 6. Issues possibles et interprétations

**Issue A — La chiralité persiste sous projection :**

```text
χ_q^proj ≈ +0.029 ± bruit
```

à tous les niveaux `q`.

Interprétation : l’orientation modulo 30 est un **trait projeté stable**
de la tour primorielle. La chiralité est intrinsèque à la distribution SG
modulo 30 et survit au raffinement.

---

**Issue B — La chiralité se dissout sous relèvement :**

```text
χ_q^proj → 0
```

quand `q` croît et lorsque `N` croît.

Interprétation : le signal modulo 30 est un **résidu basse résolution**
d’une aléa plus profond. Les primoriels supérieurs le lavent.

---

**Issue C — Une chiralité native émerge à q = 210 ou q = 2310 :**

```text
χ_q^native augmente avec q
χ_q^proj diminue
```

Interprétation : la tour primorielle porte une **torsion d’ordre supérieur**
invisible à `q = 30`. C’est un nouvel observable, qui demande sa propre
caractérisation.

---

**Issue D — Toutes les chiralités décroissent avec N à q fixé :**

```text
χ_q^native → 0
χ_q^proj   → 0
```

lorsque `N → ∞`.

Interprétation : les transitions SG sont asymptotiquement indépendantes.
La chiralité modulo 30 à petit `N` était un artefact d’échantillon fini.

Ce serait le No-Go le plus fort et il doit être testé explicitement.

---

## 7. Critères d’acceptation de la chiralité comme observable primaire

La chiralité `χ_q` est promue au statut d’observable **[P] confirmé** si et
seulement si :

1. `χ_30` reste dans l’intervalle `[+0.025, +0.032]` pour
   `N ∈ {10⁷, 3·10⁷, 5·10⁷}`.
2. `χ_q`, native ou projetée, reste significativement au-dessus du plancher
   de bruit d’indépendance aux trois niveaux `q`, avec un seuil `≥ 5σ`,
   où `σ` est estimé par bootstrap.
3. Le signe de la chiralité reste cohérent et positif à toutes les paires
   `(q, N)`.

L’échec d’un seul des points (1) à (3) rétrograde l’observable au statut
`[M]` candidat ou `[O]`.

---

## 8. Protocole bootstrap pour les intervalles de confiance

Pour distinguer le signal du bruit à une échelle de faible amplitude
environ `0.03` :

1. Pour chaque paire `(q, N)`, rééchantillonner la suite SG avec remise,
   avec `B = 200` répliques bootstrap.
2. Calculer `χ_q` sur chaque réplique.
3. Rapporter : moyenne, écart-type, intervalle de confiance à 95%.
4. Comparer au plancher d’indépendance :

```text
χ_indep = ‖A‖_F
```

lorsque les transitions sont i.i.d. uniformes sur `A_q`.

---

## 9. Séparation Phase 0 / Phase 1

**Phase 0 — aujourd’hui :**

Mesurer `χ_q` pour :

```text
(q, N) ∈ {30, 210, 2310} × {10⁷, 3·10⁷, 5·10⁷}.
```

Cela donne 9 points de données, sans bootstrap.

Objectif : analyse de direction de tendance uniquement.

---

**Phase 1 — ultérieurement :**

- intervalles de confiance bootstrap rigoureux ;
- comparaison au plancher d’indépendance ;
- extrapolation affinée des tendances en `(q, N)`.

Ce document spécifie la Phase 0. La Phase 1 est conditionnelle au fait que
les résultats de Phase 0 soient non triviaux.

---

## 10. Contexte doctrinal

Ce protocole remplace une hypothèse falsifiée :

```text
1/√7 dans Δ̃_SG
```

par un observable **mesuré, stable, propre**.

Il ne suppose aucune convergence vers une constante donnée.

Il demande seulement si la chiralité persiste ou se dissout sous raffinement
primoriel : une question de **direction de tendance**, non une question
d’identification de constante.

**RHClaimed = false. Aucune inférence globale n’est affirmée.**

---

*Fin du protocole.*