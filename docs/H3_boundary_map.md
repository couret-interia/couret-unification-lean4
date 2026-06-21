# H3/L12 — Carte du mur terminal (boundary map)

**Version :** v35.8.2
**Statut :** Cartographie, pas chantier de preuve.
**Fichier doctrinal :** `CouretUnification/Logic/OpenLocks.lean` → `L12_H3.status = .rh_wall`

## Règle de gouvernance

> Tant que `target_bound`, `gram_semidef_of_rigid`, les 3 CORE de L10 et
> la preuve analytique consommée par `L6Bridge` ne sont pas soldés, H3
> ne doit pas devenir un chantier de preuve, seulement un chantier de
> cartographie.

Ce document ne prétend pas **résoudre** H3. Il vise à rendre son résidu
résiduel **exactement localisable**.

## 1. Structure tripartite

H3 se décompose en trois sous-verrous indépendants. La résolution
partielle de chacun est possible sans impliquer RH ; c'est seulement leur
**conjonction simultanée** qui équivaudrait à RH.

| Sous-verrou | Objet | Statut actuel | Condition de fermeture |
|-------------|-------|---------------|------------------------|
| Archimédien | facteur gamma $\gamma(s, \chi) = \pi^{-(s+a)/2}\Gamma((s+a)/2)$ | `conditional` | identification complète avec un facteur spectral |
| Eulérien | produit complet $\prod_p (1 - \chi(p)/p^s)^{-1}$ | `candidate` | complétion globale justifiée au-delà de la primorialité |
| Zéros | identité $\det_2(I - zM) \leftrightarrow \xi$ | `candidate` | matching global des zéros préservant les multiplicités |

## 2. Sous-verrou Archimédien

### 2.1 Objet exact

Facteur $\gamma(s, \chi) = \pi^{-(s+a)/2} \Gamma((s+a)/2)$ où :
- $\chi$ caractère primitif modulo $q$ ;
- $a \in \{0, 1\}$ parité.

### 2.2 Dépendances

- Consomme : `L6RatioEstimate` (asymptotique de $\chi(s) = \gamma(1-s)/\gamma(s)$).
- Alimente : l'identification spectrale de H3.

### 2.3 Verrou résiduel

Identifier **exactement** comment le facteur gamma apparaît comme
contribution spectrale d'un opérateur auto-adjoint candidat. Deux
approches :

  1. **Berry–Keating** (éliminée par L10 — route R4) : $H = xp + px$.
  2. **Connes** (éliminée par L10 — route R3) : formule de trace adélique.
  3. **Couret–Unification** (active) : opérateur via la rigidité de Gram +
     représentation spectrale de la tour primorielle.

### 2.4 Statut : `conditional`

Dépend de `L6RatioEstimate` **et** d'une identification spectrale nouvelle
non présente dans la littérature Berry–Keating / Connes.

## 3. Sous-verrou Eulérien

### 3.1 Objet exact

Produit d'Euler $L(s, \chi) = \prod_p (1 - \chi(p)/p^s)^{-1}$ restreint
aux niveaux primoriels $P_k = \prod_{p \le p_k} p$.

### 3.2 Dépendances

- Consomme : `target_bound` (convergence absolue du produit partiel).
- Consomme : `gram_semidef_of_rigid` (positivité des contributions).
- Alimente : l'identité $\det_2 \leftrightarrow \xi$ globale.

### 3.3 Verrou résiduel

Passage du produit partiel $E_k(s) = \prod_{p \le p_k} (1 - \chi(p)/p^s)^{-1}$
au produit global $L(s, \chi)$.

Le gap est le **tail** :
$$T_k(s) = \prod_{p > p_k} (1 - \chi(p)/p^s)^{-1}$$

Pour $\operatorname{Re}(s) > 1$, $|\log T_k(s)| \le \sum_{p > p_k} 1/p^\sigma \to 0$.
Pour $\sigma \le 1$ (bande critique), la somme **diverge** — c'est
précisément l'obstruction arithmétique.

### 3.4 Statut : `candidate`

Justification de la complétion globale reste ouverte dans la bande
critique.

## 4. Sous-verrou Zéros

### 4.1 Objet exact

Identité $\det_2(I - zM_\chi) = C \cdot \xi(s, \chi)$ où :
- $M_\chi$ opérateur rigide construit depuis la tour primorielle ;
- $\det_2$ déterminant régularisé de Hilbert–Carleman ;
- $\xi$ fonction zêta complétée.

### 4.2 Dépendances

- Consomme : `gram_semidef_of_rigid` (structure rigide de M).
- Consomme : `L10_obstruction` (absence d'alternative structurelle).
- Consomme : sous-verrou Archimédien (identification du facteur gamma).
- Consomme : sous-verrou Eulérien (complétion globale).

### 4.3 Verrou résiduel

**Matching global des zéros** préservant les multiplicités.

Deux options :

  1. **Matching ponctuel** : chaque zéro de $\det_2$ correspond
     bijectivement à un zéro non trivial de $\xi$, avec multiplicité
     préservée.
  2. **Matching asymptotique** : les distributions de zéros coïncident
     à l'infini (GUE / Hilbert–Pólya).

### 4.4 Statut : `candidate`

Équivalent à RH : fermer ce verrou **est** fermer RH.

## 5. Statut combinatoire

| État | Description |
|------|-------------|
| `absent` | Aucun élément du verrou n'existe dans le code. |
| `candidate` | Structure nommée, preuve absente. |
| `conditional` | Preuve existe sous hypothèses non encore justifiées. |
| `established` | Preuve inconditionnelle. |

### 5.1 Assignment v35.8.2

| Sous-verrou | État |
|-------------|------|
| Archimédien | `conditional` (sur L6) |
| Eulérien | `candidate` |
| Zéros | `candidate` |

### 5.2 Critère de maturité

> Quand H3 sera prêt à être attaqué, tu devras pouvoir dire :
>
> « Le verrou résiduel exact n'est plus vague : il est localisé. »

**Actuellement atteint pour :** rien.
**Atteindra-t-on ce critère ?** Dépend de :
  1. Clôture de `target_bound` (bientôt).
  2. Clôture de `gram_semidef_of_rigid` (bientôt via C3Weak_Gram).
  3. Clôture des 3 CORE de L10 (demande `specTarget_irrational`).
  4. Clôture de L6 (demande la note analytique rédigée).

## 6. Ce que ce document n'est PAS

- Ce n'est pas une preuve de RH.
- Ce n'est pas une stratégie active de fermeture.
- Ce n'est pas une revendication que Couret–Unification résoudra H3.

C'est une cartographie précise du mur terminal, conçue pour que le
résidu exact soit **localisable** plutôt que flou.

## 7. Ce que H3 deviendra quand le socle sera sec

Une fois target_bound, gram_semidef_of_rigid, L10-CORE et L6 fermés,
H3 deviendra :

> « Il reste à identifier un opérateur spectral concret $M_\chi$ tel que
> $\det_2(I - zM_\chi) = C \cdot \xi(s, \chi)$, avec matching des zéros,
> en utilisant la rigidité structurelle (C3Weak), la non-existence
> d'alternatives entières (L10), les estimées asymptotiques (L6) et la
> sommabilité locale (target_bound). »

Ce n'est pas une preuve. C'est une spécification précise.

Le reste est le programme de Hilbert–Pólya (1912), qui reste ouvert
depuis 114 ans.
