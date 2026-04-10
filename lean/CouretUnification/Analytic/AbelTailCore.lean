import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic

namespace CouretUnification.Analytic.AbelTailCore

open Real Asymptotics Filter MeasureTheory Set

/-!
# AbelTailCore
## Brique analytique locale pour la queue d’Abel associée à `log(t) / t^3`

Ce fichier formalise une chaîne d’analyse réelle courte mais structurante :
on part de l’intégrande

`log(t) / t^3`

on exhibe une primitive explicite, puis on contrôle la queue impropre
associée ainsi que son ordre asymptotique.

## Vision "Couret–Unification"

Cette brique ne porte **aucune revendication globale**.
Elle joue un rôle de **pont analytique local** :

- **entrée** : une intégrande explicite ;
- **mécanisme** : dérivation, FTC, intégrale impropre, comparaison asymptotique ;
- **sortie** : une estimation `O(log T / T^2)`.

Autrement dit :
ce fichier ne prouve rien de "spectral" à lui seul,
mais il fournit un module réel propre, stable, et réutilisable
dans une architecture plus large.

## Rythme logique du fichier

1. dérivée exacte de la primitive ;
2. extinction de `log(t)/t^2` à l’infini ;
3. extinction de la primitive ;
4. formule de Newton–Leibniz sur intervalle fini ;
5. passage à la queue impropre ;
6. majoration auxiliaire `1/t^2 = O(log t / t^2)` ;
7. majoration de la primitive ;
8. majoration de la queue.

## Statut

- fichier **local** ;
- preuve **élémentaire mais rigoureuse** ;
- **0 sorry** ;
- **0 axiome** ;
- **aucune prétention RH**.
-/

/-- Intégrande principal : `log(t) / t^3`. -/
noncomputable def abelIntegrand (t : ℝ) : ℝ := Real.log t / t ^ 3

/--
Primitive explicite de `abelIntegrand`.

### Rôle analytique
Cette primitive est choisie pour que sa dérivée redonne exactement
`log(t) / t^3` sur le domaine `t > 0`.

### Lecture humaine
Le terme `-(log t)/(2 t^2)` produit la structure principale,
et `-1/(4 t^2)` corrige exactement le terme résiduel.
-/
noncomputable def abelPrimitive (t : ℝ) : ℝ :=
  -(Real.log t) / (2 * t ^ 2) - 1 / (4 * t ^ 2)

/--
Queue impropre de référence.

### Interprétation
`abelReferenceTail T` mesure la masse restante de l’intégrande
au-delà du seuil `T`.
-/
noncomputable def abelReferenceTail (T : ℝ) : ℝ :=
  ∫ t in Set.Ioi T, abelIntegrand t

-- ============================================================
-- SECTION 1
-- Dérivation explicite : la primitive redonne l’intégrande
-- ============================================================

/--
## Théorème de dérivation locale

Sur `t > 0`, la fonction `abelPrimitive` a pour dérivée `abelIntegrand t`.

### Rôle analytique
C’est la clef du fichier :
tout ce qui suit repose sur cette identification exacte.

### Pont logique
Primitive explicite → FTC sur intervalle fini → intégrale impropre → asymptotique.

### Sortie exploitable
Une preuve Lean de la relation différentielle locale.
-/
theorem hasDerivAt_abelPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt abelPrimitive (abelIntegrand t) t := by
  -- Sur `t > 0`, le logarithme est dérivable car `t ≠ 0`.
  have ht0 : t ≠ 0 := ht.ne'

  -- Dérivée de `x ↦ x^2`.
  have hpow2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t)

  -- Dérivée de `log`.
  have hlog : HasDerivAt Real.log (1 / t) t := by
    simpa using Real.hasDerivAt_log ht0

  -- Bloc A : dérivation du morceau `-(log x)/(2 x^2)`.
  have hA :
      HasDerivAt (fun x : ℝ => -Real.log x / (2 * x ^ 2))
        ((-(1 / t) * (2 * t ^ 2) - (-Real.log t) * (2 * (2 * t))) /
          (2 * t ^ 2) ^ 2) t := by
    simpa using
      (hlog.neg).div (hpow2.const_mul 2)
        (by exact mul_ne_zero two_ne_zero (pow_ne_zero 2 ht0))

  -- Bloc B : dérivation du morceau `1 / (4 x^2)`.
  have hB :
      HasDerivAt ((fun x : ℝ => 1) / (fun y : ℝ => 4 * y ^ 2))
        (-(4 * (2 * t)) / (4 * t ^ 2) ^ 2) t := by
    simpa using
      (hasDerivAt_const t (1 : ℝ)).div (hpow2.const_mul 4)
        (by exact mul_ne_zero four_ne_zero (pow_ne_zero 2 ht0))

  -- Recollage différentiel.
  have hsub := hA.sub hB

  -- Nettoyage final : la dérivée obtenue se simplifie exactement en `log(t)/t^3`.
  convert hsub using 1
  · dsimp [abelIntegrand]
    field_simp [ht0]
    ring

-- ============================================================
-- SECTION 2
-- Extinction de `log(t) / t²` à l’infini
-- ============================================================

/--
## Lemme de décroissance logarithmique

`log(t) / t^2 → 0` quand `t → +∞`.

### Rôle analytique
Ce lemme sert de moteur à l’extinction de la primitive.

### Stratégie
On part du résultat standard `log(t)/t → 0`,
puis on redécale par une division supplémentaire par `t`.
-/
lemma tendsto_log_div_sq_atTop :
    Tendsto (fun t : ℝ => Real.log t / t ^ 2) atTop (nhds 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 one_ne_zero
  have h := h0.div_atTop tendsto_id
  simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

-- ============================================================
-- SECTION 3
-- Extinction de la primitive à l’infini
-- ============================================================

/--
## La primitive s’éteint à l’infini

`abelPrimitive(t) → 0` quand `t → +∞`.

### Rôle analytique
C’est le passage décisif pour transformer une primitive locale
en formule de queue impropre.

### Décomposition
- terme logarithmique : contrôlé via `tendsto_log_div_sq_atTop`,
- terme rationnel : contrôlé via `1 / (4 t^2) → 0`.
-/
theorem tendsto_abelPrimitive_atTop :
    Tendsto abelPrimitive atTop (nhds 0) := by
  -- Premier terme : multiple constant de `log(t) / t^2`.
  have h1 : Tendsto (fun t : ℝ => -(Real.log t) / (2 * t ^ 2)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (tendsto_log_div_sq_atTop.const_mul (-(1 : ℝ) / 2))

  -- Le carré diverge vers `+∞`.
  have hpow2 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (α := ℝ) (n := 2) (show (2 : ℕ) ≠ 0 by decide)

  -- Donc `4 * t^2` aussi.
  have hden : Tendsto (fun t : ℝ => 4 * t ^ 2) atTop atTop :=
    hpow2.const_mul_atTop (show (0 : ℝ) < 4 by norm_num)

  -- Inversion : `-1 / (4 * t^2) → 0`.
  have h2 : Tendsto (fun t : ℝ => -1 / (4 * t ^ 2)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using (Filter.Tendsto.const_div_atTop hden (-1 : ℝ))

  -- Recomposition de la primitive.
  have hsum := h1.add h2
  convert hsum using 1
  · funext t
    simp [abelPrimitive, div_eq_mul_inv, sub_eq_add_neg,
      mul_assoc, mul_left_comm, mul_comm]
  · simp

-- ============================================================
-- SECTION 4
-- Version compacte du théorème fondamental du calcul
-- ============================================================

/--
## FTC sur intervalle fini

Pour `0 < T` et `0 < U`,
on a

`∫ t in T..U, abelIntegrand t = abelPrimitive U - abelPrimitive T`.

### Rôle analytique
C’est le chaînon fini avant le passage à la queue impropre.

### Architecture logique
dérivée locale + continuité + intégrabilité → identité intégrale.
-/
theorem intervalIntegral_eq {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    ∫ t in T..U, abelIntegrand t = abelPrimitive U - abelPrimitive T := by
  -- Continuité de l’intégrande sur l’intervalle compact orienté.
  have hcont : ContinuousOn abelIntegrand (Set.uIcc T U) := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le (lt_min hT hU) hx.1).ne'
    simpa [abelIntegrand] using
      ((Real.continuousAt_log hx0).div
        (continuousAt_id.pow 3)
        (pow_ne_zero 3 hx0)).continuousWithinAt

  -- Donc intégrabilité sur l’intervalle.
  have hint : IntervalIntegrable abelIntegrand volume T U := hcont.intervalIntegrable

  -- Application du FTC.
  exact
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        hasDerivAt_abelPrimitive (lt_of_lt_of_le (lt_min hT hU) hx.1))) hint

-- ============================================================
-- SECTION 5
-- Passage à la queue impropre
-- ============================================================

/--
## Formule exacte pour la queue impropre

Si `T > 1`, alors

`abelReferenceTail T = -abelPrimitive T`.

### Rôle analytique
Cette identité transforme la queue impropre en objet explicite.

### Idée
- l’intégrande est positive au-delà de `1`,
- la primitive tend vers `0`,
- donc la borne à l’infini disparaît.
-/
theorem abelReferenceTail_eq {T : ℝ} (hT : 1 < T)
    (hderiv : ∀ x ∈ Set.Ici T, HasDerivAt abelPrimitive (abelIntegrand x) x) :
    abelReferenceTail T = -abelPrimitive T := by
  have hnonneg : ∀ x ∈ Set.Ioi T, 0 ≤ abelIntegrand x := by
    intro x hx
    dsimp [abelIntegrand]
    have hx1 : 1 < x := lt_of_lt_of_le hT (le_of_lt hx)
    have hx0 : 0 < x := lt_trans zero_lt_one hx1
    refine div_nonneg ?_ ?_
    · exact le_of_lt (Real.log_pos hx1)
    · positivity
  simpa [abelReferenceTail] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg tendsto_abelPrimitive_atTop

-- ============================================================
-- SECTION 6
-- Lemme auxiliaire de comparaison
-- ============================================================

/--
## Comparaison de base

`1 / t^2 = O(log t / t^2)` à l’infini.

### Rôle analytique
Ce lemme sert de borne auxiliaire pour le terme rationnel
de la primitive.

### Intuition
Pour `t ≥ exp(1)`, on a `1 ≤ log t`,
donc le quotient `1/t^2` est dominé par `log t / t^2`.
-/
private lemma inv_sq_isBigO_log_div_sq :
    (fun t : ℝ => 1 / t ^ 2) =O[atTop] (fun t => Real.log t / t ^ 2) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
  have ht_pos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have ht2_pos : 0 < t ^ 2 := by positivity
  have hlog_ge : 1 ≤ Real.log t := by
    exact (Real.le_log_iff_exp_le ht_pos).2 (by simpa using ht)
  have hlog_nonneg : 0 ≤ Real.log t := le_trans (by norm_num) hlog_ge
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by norm_num) ht2_pos.le),
      abs_of_nonneg (div_nonneg hlog_nonneg ht2_pos.le)]
  simpa [one_mul] using
    (div_le_div_of_nonneg_right hlog_ge ht2_pos.le)

-- ============================================================
-- SECTION 7
-- Contrôle asymptotique de la primitive
-- ============================================================

/--
## La primitive est en `O(log T / T^2)`

### Rôle analytique
C’est la sortie asymptotique locale principale du fichier.

### Décomposition
- le terme logarithmique est un multiple constant du bon profil ;
- le terme rationnel est dominé par ce profil ;
- la somme hérite du même ordre.
-/
theorem abelPrimitive_isBigO :
    abelPrimitive =O[atTop] (fun T => Real.log T / T ^ 2) := by
  change (fun T : ℝ => -(Real.log T) / (2 * T ^ 2) - 1 / (4 * T ^ 2)) =O[atTop]
    (fun T => Real.log T / T ^ 2)
  refine IsBigO.sub ?_ ?_
  · have hEq :
      (fun t : ℝ => -(Real.log t) / (2 * t ^ 2)) =
        (fun t => (-1 / 2 : ℝ) * (Real.log t / t ^ 2)) := by
      ext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp [ht]

    simpa [hEq] using
      ((isBigO_refl (fun t : ℝ => Real.log t / t ^ 2) atTop).const_mul_left (-1 / 2 : ℝ))

  · have hEq :
      (fun t : ℝ => 1 / (4 * t ^ 2)) =
        (fun t => (1 / 4 : ℝ) * (1 / t ^ 2)) := by
      ext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp [ht]

    simpa [hEq, mul_comm, mul_left_comm, mul_assoc] using
      (inv_sq_isBigO_log_div_sq.const_mul_left (1 / 4 : ℝ))

-- ============================================================
-- SECTION 8
-- Contrôle asymptotique final de la queue impropre
-- ============================================================

/--
## La queue impropre est en `O(log T / T^2)`

### Rôle analytique
C’est la sortie finale du fichier.

### Pont logique
égalité éventuelle avec `-abelPrimitive`
+
`Big-O` de la primitive
=
`Big-O` de la queue.
-/
theorem abelReferenceTail_isBigO
    (hderiv_global : ∀ x > 0, HasDerivAt abelPrimitive (abelIntegrand x) x) :
    abelReferenceTail =O[atTop] (fun T => Real.log T / T ^ 2) := by
  have heq : abelReferenceTail =ᶠ[atTop] (fun T => -abelPrimitive T) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact abelReferenceTail_eq hT (fun x hx =>
      hderiv_global x (lt_of_lt_of_le (lt_trans zero_lt_one hT) hx))
  have hEqO : abelReferenceTail =O[atTop] (fun T => -abelPrimitive T) := heq.isBigO
  have hNeg : (fun T => -abelPrimitive T) =O[atTop] (fun T => Real.log T / T ^ 2) := by
    simpa using abelPrimitive_isBigO.const_mul_left (-1 : ℝ)
  exact hEqO.trans hNeg

-- ============================================================
-- Indicateurs documentaires / doctrinaux
-- ============================================================

/--
Compteur documentaire :
ce fichier ne contient aucun `sorry`.
-/
def sorryCount : Nat := 0

/--
Compteur documentaire :
ce fichier n’introduit aucun axiome.
-/
def axiomCount : Nat := 0

/--
Marqueur doctrinal :
ce fichier reste une brique locale d’analyse réelle
et ne revendique aucune fermeture globale de type RH.
-/
def RHClaimed : Bool := false

/-- Vérification minimale de cohérence doctrinale. -/
theorem rh_not_claimed : RHClaimed = false := rfl

end CouretUnification.Analytic.AbelTailCore