# Note analytique — L6 Ratio Estimate

**Version :** v35.8.2
**Statut :** Contrat mathématique ouvert.
**Fichier associé :** `CouretUnification/Logic/L6RatioEstimateDerived.lean`

## Objectif

Fournir la base analytique pour fermer les trois hypothèses
conditionnelles consommées par `L6Bridge.lean` :

  1. `L6RatioEstimate χ`
  2. `ZtotPositiveEventually χ`
  3. `EpsAsymptoticBound χ η T0 C`

## 1. Définitions (amont, de L6Bridge.lean)

### 1.1 Caractère primitif

$\chi$ : caractère de Dirichlet primitif modulo $q$, de conducteur $q$
et de parité $a \in \{0, 1\}$ (pair/impair).

### 1.2 Facteur local archimédien

$$
\gamma(s, \chi) = \pi^{-(s+a)/2}\,\Gamma\!\left(\frac{s+a}{2}\right)
$$

### 1.3 Ratio Gamma

$$
\chi(s) = \frac{\gamma(1-s, \chi)}{\gamma(s, \chi)}
       = \pi^{s - 1/2}\,\frac{\Gamma((1-s+a)/2)}{\Gamma((s+a)/2)}
$$

### 1.4 Contributions absorbées

- **Aarch(χ, T)** : intégrale archimédienne le long de la droite critique
  jusqu'à la hauteur $T$, $\operatorname{Re}(s) = 1/2$.
- **Ztot(χ, T)** : somme des contributions des zéros non triviaux
  $\rho = 1/2 + i\gamma_n$ avec $|\gamma_n| \le T$.
- **eps(χ, T)** : correction asymptotique telle que
  $\operatorname{Aarch}(χ, T) = (1/2 + \operatorname{eps}(χ, T)) \cdot \operatorname{Ztot}(χ, T)$.

## 2. Contenu des trois lemmes

### 2.1 L6RatioEstimate χ

**Énoncé (Lean) :**
$\exists T_0, C > 0,\ \forall T \ge T_0,\ \operatorname{Aarch}(χ, T) = (1/2 + \operatorname{eps}(χ, T)) \cdot \operatorname{Ztot}(χ, T) \land |\operatorname{eps}(χ, T)| \le C / \log T$.

**Arguments analytiques requis :**

  1. **Stirling** pour $\log \Gamma$ : pour $|s| \to \infty$ dans le
     demi-plan $\operatorname{Re}(s) > 0$ :
     $$\log \Gamma(s) = s \log s - s - \frac{1}{2}\log s + \frac{1}{2}\log(2\pi) + O(1/|s|)$$
  2. **Évaluation au point s = 1/2 + iT** :
     $$\log \chi(1/2 + iT) = -iT\log(T/2\pi) + iT + i\pi/4 + O(1/T)$$
  3. **Intégration de Aarch** par contour de Riemann–Siegel, absorption
     du facteur gamma principal.
  4. **Extraction de ε** : différence entre l'intégrale archimédienne
     et la contribution dominante 1/2 × Ztot.

**Dépendance de l'erreur :** $|\operatorname{eps}| \le C / \log T$ provient
de la borne uniforme de Stirling au ordre supérieur.

### 2.2 ZtotPositiveEventually χ

**Énoncé (Lean) :**
$\exists T_0 > 0,\ \forall T \ge T_0,\ \operatorname{Ztot}(χ, T) > 0$.

**Arguments analytiques requis :**

  1. **Riemann–von Mangoldt** : $N(T) = \frac{T}{2\pi}\log\frac{T}{2\pi e} + O(\log T)$.
  2. **Contribution positive dominante** : chaque zéro $\rho = 1/2 + i\gamma_n$
     contribue $> 0$ à Ztot sous les hypothèses standard (RH non requise).
  3. **Borne inférieure** : $\operatorname{Ztot}(χ, T) \ge \alpha \cdot N(T)$ pour
     un $\alpha > 0$ constant et $T$ grand.
  4. **Positivité effective** : $N(T) \to \infty$, donc Ztot > 0 à partir
     d'un certain $T_0$.

### 2.3 EpsAsymptoticBound χ η T0 C

**Énoncé (Lean) :**
Si $|\operatorname{eps}(χ, T)| \le C / \log T$ pour $T \ge T_0$,
alors pour $\eta \in (1/2, 1)$ il existe $T_1 \ge T_0$ tel que pour tout
$T \ge T_1$, $\eta (1/2 + \operatorname{eps}(χ, T)) < 1$.

**Preuve (semi-mécanique) :**

  1. $\eta < 1 \Rightarrow \eta/2 < 1/2$, donc $1 - \eta/2 > 1/2$.
  2. Choisir $T_1$ tel que $C / \log T_1 < (1 - \eta/2)/\eta$.
  3. Pour $T \ge T_1$ : $\eta(1/2 + \operatorname{eps}) \le \eta/2 + \eta \cdot C/\log T < 1$.

**Statut :** Fermeture directe par calcul algébrique + `Real.log_pos`
+ argument ε→0 standard.

## 3. Plan de fermeture Lean

### Étape 1 — Rédiger Stirling approprié

Identifier dans Mathlib les lemmes disponibles :

  - `Complex.Gamma` : fonction gamma complexe.
  - `Complex.Gamma_ne_zero` : non-annulation.
  - `Real.Gamma_eq_tendsto` : formule limite.

Identifier si `Complex.log_Gamma_asymptotic` existe ou s'il faut le
contribuer.

### Étape 2 — Définir Aarch, Ztot, eps de manière calculable

Dans `L6Bridge.lean` ou dans un fichier auxiliaire, fournir des
définitions explicites pour `Aarch χ T`, `Ztot χ T`, `eps χ T` en termes
de la fonction zêta de Riemann / fonction L de Dirichlet.

### Étape 3 — Fermer les trois lemmes dérivés

  1. `stirling_ratio_asymptotic` dans `L6RatioEstimateDerived.lean`.
  2. `L6RatioEstimate_derived` (signature à fournir depuis L6Bridge).
  3. `ZtotPositiveEventually_derived` (idem).
  4. `EpsAsymptoticBound_derived` (semi-mécanique).

### Étape 4 — Injecter dans L6Bridge

Appeler `L6_eta_lt_one_eventual_positivity` avec les preuves dérivées :

```lean
theorem L6_positivity_proved (χ : PrimitiveCharacter)
    {η : ℝ} (hη_half : 1/2 < η) (hη1 : η < 1) :
    ∃ Tη : ℝ, 0 < Tη ∧ ∀ T : ℝ, T ≥ Tη → 0 < Wdef χ η T :=
  L6_eta_lt_one_eventual_positivity χ
    (L6RatioEstimate_derived χ)
    (ZtotPositiveEventually_derived χ)
    hη_half hη1
    (EpsAsymptoticBound_derived_contract χ)
```

### Critère de fermeture

- `#print axioms L6_positivity_proved` ne montre que les axiomes Mathlib
  standards (pas de `sorryAx`, pas d'axiome local Couret-Unification).
- Statut dans `OpenLocks.lean` peut passer de `open_` à `conditional`
  (dépend toujours de L10, mais L6 lui-même est fermé).

## 4. Doctrine — Ce que ce fichier n'est PAS

Ce n'est pas une preuve de RH. La fermeture complète de L6 n'implique
**en rien** RH. Elle implique simplement que l'outil asymptotique L6
devient inconditionnellement exploitable dans les couches supérieures
(L10 en particulier).

H3/L12 reste le mur terminal, indépendant de L6.
