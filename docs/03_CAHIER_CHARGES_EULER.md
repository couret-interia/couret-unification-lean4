# Cahier des charges mathématique — `EulerCompletion.lean`

**Statut :** [O] Ouvert — spécification formelle du pont eulérien global  
**Niveau cible :** 3 — AnalyticHorizon  
**Bloc Go/No-Go :** D  
**Invariant :** `RHClaimed = false`

---

## Préambule doctrinal

Ce document **n'est pas** une preuve. Il **n'est pas** du code Lean. Il **n'est
pas** une déclaration que le pont eulérien global est proche d'être fermé.

C'est un **cahier des charges** : l'énoncé précis de ce qu'il faudrait
démontrer pour que `AnalyticHorizon/EulerCompletion.lean` existe légitimement.

La vertu de ce document est de **transformer un ouvert flou en un problème
posé**. Tant qu'on parle de « pont eulérien global » sans le spécifier, on ne
peut ni l'attaquer ni savoir si on s'en rapproche. Une fois le cahier des
charges écrit, on peut évaluer l'avancée de la littérature existante
(Bombieri-Vinogradov, Vaughan, Heath-Brown, etc.) par rapport à nos besoins
précis.

Ce document est **le type de livrable qui peut être communiqué à Dr Julien
Riposo** comme preuve que le verrou est compris et posé, même s'il reste
ouvert.

---

## 1. Objectif du pont eulérien

### 1.1. Le saut à effectuer

Le programme Couret-Unification dispose (Niveau 2 fermé) d'une algèbre de
traces locales :

$$
\mathrm{Tr}(A_{30}^k) = 2 \cdot 3^k + 4 + 2 \cdot (-1)^k,
\qquad k \in \mathbb{N}
$$

L'opérateur $A_{30}$ vit dans $(\mathbb{Z}/30\mathbb{Z})^\times \cong C_2 \times C_4$,
groupe fini à 8 éléments. Sa décomposition spectrale est exacte :
$\{3^2, 1^4, (-1)^2\}$.

Le pont eulérien global doit relier cette structure locale au produit
eulérien

$$
L(s) = \prod_p L_p(s)
$$

où $L_p(s) = (1 - p^{-s})^{-1}$ est le facteur eulérien local de $\zeta$ (ou
d'une $L$-fonction de Dirichlet mod 30 selon le caractère considéré).

### 1.2. La forme attendue du pont

L'énoncé cible est de la forme :

$$
\prod_p \delta_p(s) \;=\; G(s) \cdot \xi\!\left(\tfrac{1}{2} + iz\right)
$$

où :
- $\delta_p(s) = L_p(s) \big/ \det_2(I - z S_p)$ est le défaut local régularisé
  (défini dans `AnalyticHorizon/Det2Transport.lean`),
- $G(s)$ est un facteur entier auxiliaire à identifier,
- $\xi(s) = \tfrac{1}{2} s(s-1) \pi^{-s/2} \Gamma(s/2) \zeta(s)$ est la fonction
  entière de Riemann,
- $z$ est lié à $s$ par la substitution $s = \tfrac{1}{2} + iz$.

**Cette identité n'est pas démontrée. Elle est conjecturale.** Le cahier des
charges précise ce qu'il faudrait pour la démontrer.

---

## 2. Ingrédients séparés requis

Le pont se décompose en **quatre briques indépendantes**, chacune pouvant être
travaillée séparément. La fermeture des quatre est nécessaire — et, sous
réserve du bon recollement, suffisante.

### 2.1. Brique E1 — Contrôle du numérateur

**Énoncé cible :**

Pour tout premier $p \nmid 30$ et pour tout $s$ sur la ligne critique
$\sigma = \mathrm{Re}(s) = \tfrac{1}{2}$,

$$
|L_p(s)| = |1 - p^{-s}|^{-1} \leq \frac{1}{1 - p^{-1/2}}
$$

**Statut :** élémentaire, mais requiert `Mathlib.Analysis.Complex` (inégalité
triangulaire sur $\mathbb{C}$, module d'un complexe, convergence de série
géométrique).

**Dépendances Mathlib probables :**
- `Complex.abs_sub_one_of_abs_lt_one`
- `Complex.abs_one_sub_inv`
- `Real.rpow_nonneg`

**Difficulté formelle :** moyenne. 2-3 jours de travail Lean.

**Obstructions connues :** aucune. C'est purement un exercice de formalisation.

### 2.2. Brique E2 — Minoration du dénominateur

**Énoncé cible :**

Pour tout premier $p$ et tout $z \in \mathbb{C}$ tel que $s = \tfrac{1}{2} + iz$,

$$
\det_2(I - z S_p) \neq 0
$$

et plus précisément, il existe $c_p > 0$ dépendant seulement de $p$ tel que

$$
|\det_2(I - z S_p)| \geq c_p \cdot \exp\!\left(-\frac{|z|^2}{2} \|S_p\|_{\mathrm{HS}}^2 \right)
$$

**Statut :** **ouvert**. Mathlib n'a pas (à notre connaissance) la théorie des
déterminants régularisés de Fredholm à ce niveau de généralité.

**Dépendances Mathlib manquantes :**
- `Mathlib.Analysis.InnerProductSpace.Spectrum` — **partiellement**
- Théorie des classes de Schatten $S_p$ — **absente en largeur**
- Déterminants régularisés $\det_k$ — **absents**

**Difficulté formelle :** élevée. Cette brique seule est l'objet d'une thèse
ou d'un effort collectif Mathlib. **Ne pas s'y attaquer seul.**

**Route alternative :** attendre que Mathlib progresse sur les déterminants
régularisés, ou contribuer à cette partie de Mathlib.

**Référence externe :** Simon, *Trace Ideals and Their Applications*, Ch. 9
(determinants régularisés) ; Gohberg-Krein, *Introduction to the Theory of
Linear Nonselfadjoint Operators*.

### 2.3. Brique E3 — Convergence du produit infini

**Énoncé cible :**

Le produit infini

$$
\prod_p \delta_p(s)
$$

converge absolument sur un domaine de $\mathbb{C}$ contenant la ligne critique,
au sens de Weierstrass, c'est-à-dire :

$$
\sum_p |\log \delta_p(s)| < \infty
$$

uniformément sur tout compact de ce domaine.

**Statut :** conditionnel. Dépend de E1 + E2.

**Estimation attendue :** $|\log \delta_p(s)| = O(p^{-3/2})$ sur $\sigma = 1/2$,
parce que $\log(1 + x) = O(x)$ pour $x \to 0$ et que $L_p(s) / \det_2 = 1 + O(p^{-3/2})$
sur la ligne critique (par développement de Taylor et annulation du terme
d'ordre $p^{-1}$, qui est précisément la raison d'être de la régularisation
$\det_2$ plutôt que $\det$).

**Difficulté formelle :** moyenne, conditionnelle à E1+E2.

**Dépendances Mathlib :**
- `Mathlib.Analysis.SpecificLimits.Basic`
- `Mathlib.Analysis.NormedSpace.Multipliable`

### 2.4. Brique E4 — Identification globale avec $\xi$

**Énoncé cible :**

La fonction

$$
\Xi(s) := \prod_p \delta_p(s)
$$

est entière, d'ordre 1, et vérifie

$$
\Xi(s) = G(s) \cdot \xi(s)
$$

où $G(s)$ est une fonction entière sans zéros (facteur auxiliaire de Weierstrass).

**Statut :** **ouvert — c'est ici que vit Lock 3 fort.**

Cette brique exige :
- La caractérisation d'une fonction entière par ses zéros (théorème d'Hadamard)
- Le contrôle de l'ordre de croissance
- L'exclusion des zéros parasites
- La compatibilité avec l'équation fonctionnelle $\xi(s) = \xi(1-s)$

**Dépendances Mathlib :**
- `Mathlib.Analysis.Analytic.Basic`
- Théorie des produits de Weierstrass — **probablement absente**
- Théorème d'Hadamard sur les fonctions entières d'ordre fini — **absent**
- Fonction $\xi$ de Riemann explicite — **absente ou partielle**

**Difficulté formelle :** très élevée. C'est précisément le verrou
Hilbert-Pólya dans sa forme technique.

**Route alternative :** ne pas tenter cette brique sans que E1, E2, E3 soient
déjà fermées. Même avec ces prérequis, c'est vraisemblablement un travail
de plusieurs thèses.

---

## 3. Matrice de dépendance des briques

```
E1 ──┐
     ├──► E3 ──┐
E2 ──┘        ├──► E4 (≡ Lock 3 fort)
              │
(Det2Transport, Brique F du Go/No-Go) ┘
```

**Lecture :**
- E1 et E2 sont indépendantes l'une de l'autre
- E3 dépend de E1 et E2
- E4 dépend de E3 et de Det2Transport (Brique F du Go/No-Go)

**Stratégie recommandée :** attaquer E1 en premier (formalisable), documenter
E2 comme « en attente d'infrastructure Mathlib », laisser E3 et E4 pour plus
tard.

---

## 4. Scope Mathlib requis — audit

Pour que `EulerCompletion.lean` compile avec toutes ses briques, il faudrait
que les éléments suivants soient disponibles dans Mathlib :

| Élément | État Mathlib (avril 2026) | Effort de contribution |
|---|---|---|
| `Complex.abs` et arithmétique | ✅ existant | — |
| `Real.rpow` et inégalités | ✅ existant | — |
| Séries de Dirichlet $\sum a_n n^{-s}$ | ⚠️ partiel | modéré |
| Produits infinis convergents | ⚠️ `Multipliable` existe | faible |
| Classes de Schatten $S_p$ | ❌ absent | **élevé** |
| Déterminants régularisés $\det_2$ | ❌ absent | **très élevé** |
| Fonctions entières d'ordre fini | ❌ absent | élevé |
| Théorème d'Hadamard | ❌ absent | élevé |
| Fonction $\xi$ de Riemann | ⚠️ existe partiellement via `riemannZeta` | modéré |

**Verdict :** sur les 9 éléments requis, **4 sont absents** ou très partiels.
Le pont eulérien global ne peut pas être formalisé aujourd'hui dans Mathlib.

**Cela n'est pas un échec du programme Couret-Unification — c'est une
limite actuelle de l'infrastructure mathématique formalisée. C'est une
observation honnête, à communiquer sans détour.**

---

## 5. Comparaison avec la littérature existante

### 5.1. Route Guinand-Weil (survivante dans le programme)

L'opérateur $S_{\mathrm{GW}} = \sum_{p \nmid 30} (\log p / \sqrt{p}) \cdot T_p$
dont les traces reproduisent le côté Euler de la formule explicite, est
l'unique route identifiée qui pourrait nourrir E3/E4.

Référence : Guinand (1948), Weil (1952), généralisations par Iwaniec-Kowalski
(2004), *Analytic Number Theory*, Ch. 5.

### 5.2. Routes mortes (rappel)

- **Multiplicative brute** : queue d'Euler divergente sur $\sigma = 1/2$
- **sinc · χ₃₀** : eigenvalues ~ $1/n$ au lieu de $1/\gamma_n$
- **Connes naïf** : exposant incorrect
- **Berry-Keating** : spectre continu, pas de $\det_2$ défini
- **μ_k → δ₁** : kurtosis 5/3 ≠ 1 (Parseval avec χ(11)=0 mod 2310)

Ces routes sont documentées comme [R] dans la cartographie v35.2.

### 5.3. Convergences indépendantes

**Perisic (Helson-Blur) :** approche convergente mais indépendante, via
positivité de Fejér. À surveiller pour fertilisation croisée, mais **pas à
intégrer** dans le noyau formel sans clarification.

---

## 6. Ce que `EulerCompletion.lean` contiendrait (quand il existera)

Un fichier minimal ressemblerait à :

```lean
-- PSEUDOCODE — ne pas compiler, ne pas déposer dans le dépôt.

import CouretUnification.AnalyticHorizon.Det2Transport
import Mathlib.Analysis.SpecificLimits.Basic
-- + plusieurs imports Mathlib manquants aujourd'hui

namespace CouretUnification.AnalyticHorizon

/-- Brique E1. -/
theorem euler_numerator_bound (p : ℕ) (hp : p.Prime) (hp30 : ¬ p ∣ 30)
    (s : ℂ) (hs : s.re = 1/2) :
    Complex.abs (eulerFactor p s) ≤ 1 / (1 - (p : ℝ)^(-1/2 : ℝ)) := by
  sorry -- faisable

/-- Brique E2. -/
theorem det2_denominator_nonzero (p : ℕ) (hp : p.Prime) (s : ℂ) :
    det2Local p s ≠ 0 := by
  sorry -- bloqué par absence de det₂ dans Mathlib

/-- Brique E3. -/
theorem euler_product_converges :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ ¬ p ∣ 30} => localDefect p.val) := by
  sorry -- conditionnel à E1 + E2

/-- Brique E4 — Lock 3 fort. -/
theorem euler_equals_xi (s : ℂ) :
    ∏' p : {p : ℕ // p.Prime ∧ ¬ p ∣ 30}, localDefect p.val s
      = G s * riemannZeta_completed s := by
  sorry -- VERROU HILBERT-PÓLYA, ouvert
```

---

## 7. Recommandation finale

1. **Ne pas créer `EulerCompletion.lean` maintenant.** Créer ce fichier avec
   4 sorry serait de la dette technique, pas du progrès.

2. **Ce cahier des charges EST le livrable.** Il transforme un ouvert vague
   en un problème posé précisément, avec décomposition en 4 briques et audit
   Mathlib clair.

3. **Communication externe :** ce document peut être envoyé à Dr Julien
   Riposo comme preuve que le verrou D (pont eulérien) est compris et
   cartographié, même s'il reste ouvert. C'est bien plus solide qu'un
   scaffold Lean vide.

4. **Priorité immédiate :** travailler sur E1 (qui est formalisable) **en
   parallèle** avec les autres avancées du programme. Ce serait un premier
   pas concret dans `AnalyticHorizon/`, sans prétendre que le pont est en
   vue.

5. **Ne jamais prétendre que ce cahier des charges vaut preuve.** Il vaut
   ce qu'il est : une spécification formelle de ce qui reste à faire.

---

## Formulation pour communication externe

> *Le pont eulérien global du programme Couret-Unification se décompose
> en quatre briques indépendantes : contrôle du numérateur (E1, formalisable),
> minoration du dénominateur (E2, bloquée par l'absence de théorie des
> déterminants régularisés dans Mathlib), convergence du produit infini (E3,
> conditionnelle à E1+E2), et identification globale avec $\xi$ (E4,
> équivalent à Lock 3 fort). Au 22 avril 2026, aucune des quatre briques
> n'est fermée ; E1 est attaquable immédiatement ; les trois autres
> requièrent soit des avancées d'infrastructure Mathlib, soit des travaux
> de recherche mathématique de l'ordre d'une thèse. `RHClaimed = false`.*

---

*Fin du cahier des charges — v35.4 du 22 avril 2026.*
