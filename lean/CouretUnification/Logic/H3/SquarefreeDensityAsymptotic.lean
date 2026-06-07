/-
Couret-Unification — v38.5.10-lab
Logic/H3/SquarefreeDensityAsymptotic.lean

Laboratoire compilable de fermeture C-04b.
Status     : lab / no sorry
RHClaimed  : false
Claim      : aucune fermeture [D] nouvelle à ce stade
-/

import CouretUnification.Logic.H3.SquarefreeDensity
import CouretUnification.Logic.H3.MoebiusBridge
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.Defs

open Filter
open ArithmeticFunction

namespace CouretUnification.Logic.H3

/-!
# SquarefreeDensityAsymptotic — laboratoire de fermeture C-04b

Objectif :
remplacer progressivement `SquarefreeAsymptoticDensityBridge`
par une preuve interne de la densité asymptotique

    squarefreeCount N / N → 6 / π².

Statut initial :
aucune revendication [D] globale. Les étapes sont isolées, nommées,
et promues seulement lorsqu'elles compilent sans `sorry`.
-/

/-- Fermeture eulérienne attendue pour la densité squarefree :
    la L-série de Möbius au point `2` vaut `6 / π²`.

    Forme sans notation Unicode fragile, alignée avec les fonctions
    publiques `ArithmeticFunction.moebius` et `Real.pi`. -/
def MoebiusZetaTwoClosure : Prop :=
  LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ)
    = (6 / (Real.pi ^ 2) : ℂ)

/-- Première cible laboratoire : le bridge asymptotique est le but final
    du front C-04b. -/
theorem squarefree_asymptotic_density_lab_target
    (H : SquarefreeAsymptoticDensityBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density H

/-- Fermeture analytique complète attendue pour C-04b.

    Elle regroupe :
    1. le passage du comptage squarefree à la série de Möbius ;
    2. le contrôle asymptotique déjà préparé par C-03 ;
    3. la fermeture eulérienne `MoebiusZetaTwoClosure`.

    À raffiner progressivement jusqu'à remplacer
    `SquarefreeAsymptoticDensityBridge`. -/
def SquarefreeAsymptoticClosureFromMoebius : Prop :=
  MoebiusZetaTwoClosure → SquarefreeAsymptoticDensityBridge

/-- Consommation du rail conditionnel `SquarefreeAsymptoticClosureFromMoebius`.

    Si le verrou eulérien `MoebiusZetaTwoClosure` est fourni, et si l'on
    dispose du rail analytique complet qui transforme ce verrou en
    `SquarefreeAsymptoticDensityBridge`, alors on récupère la densité
    asymptotique canonique des entiers squarefree.

    Ce théorème ne ferme pas encore C-04b ; il explicite la manière
    dont C-04b sera consommée une fois les deux verrous intermédiaires
    établis. -/
theorem squarefree_asymptotic_density_of_moebius_closure
    (H : SquarefreeAsymptoticClosureFromMoebius)
    (HZ : MoebiusZetaTwoClosure) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density (H HZ)

/-- La sommabilité de la série de Möbius à `s = 2` est disponible
    depuis le bridge public `MoebiusBridge`. -/
lemma moebius_two_summable_for_asymptotic :
    LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ) :=
  moebius_LSeriesSummable_two

/-- À `s = 2`, le produit de la L-série de ζ arithmétique
    et de la L-série de Möbius vaut `1`.

    C'est le pivot Mathlib `LSeries_zeta_mul_Lseries_moebius`
    spécialisé au point réel `2`. -/
lemma zeta_mul_moebius_two :
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ) *
      LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ) = 1 := by
  simpa using
    (ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius
      (s := (2 : ℂ)) (by norm_num))

/-- La L-série de ζ arithmétique ne s'annule pas en `s = 2`.

    Cette non-annulation permettra d'isoler `LSeries(μ,2)` à partir de
    `LSeries(ζ,2) * LSeries(μ,2) = 1`. -/
lemma zeta_two_ne_zero_for_moebius :
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ) ≠ 0 := by
  simpa using
    (ArithmeticFunction.LSeries_zeta_ne_zero_of_one_lt_re
      (s := (2 : ℂ)) (by norm_num))

/-- Valeur de la L-série de ζ arithmétique en `s = 2`,
    sous la forme complexe native de Mathlib. -/
lemma zeta_LSeries_two_eq_pi_sq_div_six_complex :
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ) =
      ((Real.pi : ℂ) ^ 2) / 6 := by
  have hs : 1 < ((2 : ℂ).re) := by norm_num
  calc
    LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ)
        = riemannZeta (2 : ℂ) := by
            simpa using
              (ArithmeticFunction.LSeries_zeta_eq_riemannZeta
                (s := (2 : ℂ)) hs)
    _ = ((Real.pi : ℂ) ^ 2) / 6 := by
            simpa using riemannZeta_two

end CouretUnification.Logic.H3
