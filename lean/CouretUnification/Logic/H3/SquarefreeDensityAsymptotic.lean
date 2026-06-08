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

/-- Non-annulation de `π` après coercion dans `ℂ`. -/
lemma complex_pi_ne_zero : ((Real.pi : ℂ) ≠ 0) := by
  exact_mod_cast (ne_of_gt Real.pi_pos)

/-- Le facteur `π² / 6` est non nul dans `ℂ`. -/
lemma complex_pi_sq_div_six_ne_zero :
    (((Real.pi : ℂ) ^ 2) / 6) ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 complex_pi_ne_zero) (by norm_num)

/-- Identité algébrique élémentaire :
    `(π² / 6) * (6 / π²) = 1` dans `ℂ`. -/
lemma complex_pi_sq_div_six_mul_six_div_pi_sq :
    (((Real.pi : ℂ) ^ 2) / 6) * ((6 : ℂ) / ((Real.pi : ℂ) ^ 2)) = 1 := by
  field_simp [complex_pi_ne_zero]

/-- Fermeture eulérienne native complexe :
    `L(μ, 2) = 6 / π²`.

    Preuve : on combine `L(ζ,2) * L(μ,2) = 1`,
    la valeur `L(ζ,2) = π²/6`, et la non-annulation de `π²/6`. -/
lemma moebius_zeta_two_closure_complex :
    LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ) =
      (6 : ℂ) / ((Real.pi : ℂ) ^ 2) := by
  let Z : ℂ := LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (2 : ℂ)
  let M : ℂ := LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ)

  have hmul : Z * M = 1 := by
    simpa [Z, M] using zeta_mul_moebius_two

  have hZ : Z = ((Real.pi : ℂ) ^ 2) / 6 := by
    simpa [Z] using zeta_LSeries_two_eq_pi_sq_div_six_complex

  have hA_mul_M :
      (((Real.pi : ℂ) ^ 2) / 6) * M = 1 := by
    simpa [hZ] using hmul

  have hA_mul_target :
      (((Real.pi : ℂ) ^ 2) / 6) * ((6 : ℂ) / ((Real.pi : ℂ) ^ 2)) = 1 :=
    complex_pi_sq_div_six_mul_six_div_pi_sq

  have hM :
      M = (6 : ℂ) / ((Real.pi : ℂ) ^ 2) := by
    exact mul_left_cancel₀ complex_pi_sq_div_six_ne_zero
      (by
        calc
          (((Real.pi : ℂ) ^ 2) / 6) * M = 1 := hA_mul_M
          _ = (((Real.pi : ℂ) ^ 2) / 6) *
                ((6 : ℂ) / ((Real.pi : ℂ) ^ 2)) := hA_mul_target.symm)

  simpa [M] using hM

/-- Fermeture du verrou `MoebiusZetaTwoClosure`.

    Cette version reformate la fermeture complexe native dans la forme
    publique du lab, où la constante est écrite comme coercion de
    `6 / Real.pi²`. -/
lemma moebius_zeta_two_closure_from_mathlib :
    MoebiusZetaTwoClosure := by
  unfold MoebiusZetaTwoClosure
  calc
    LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 : ℂ)
        = (6 : ℂ) / ((Real.pi : ℂ) ^ 2) :=
            moebius_zeta_two_closure_complex
    _ = (6 / (Real.pi ^ 2) : ℂ) := by
            simp

/-- Le verrou eulérien `MoebiusZetaTwoClosure` est désormais fermé localement.

    Ainsi, toute preuve du rail analytique
    `SquarefreeAsymptoticClosureFromMoebius` fournit directement le bridge
    final `SquarefreeAsymptoticDensityBridge`.

    Il ne reste donc plus, pour C-04b, que le passage asymptotique :
    comptage squarefree via Möbius + contrôle d'erreur + passage à la limite. -/
theorem squarefree_asymptotic_bridge_of_moebius_closure
    (H : SquarefreeAsymptoticClosureFromMoebius) :
    SquarefreeAsymptoticDensityBridge :=
  H moebius_zeta_two_closure_from_mathlib

/-- Consommation finale du rail C-04b après fermeture eulérienne.

    Ce théorème ne prouve pas encore le passage asymptotique complet ;
    il montre que la dépendance à `MoebiusZetaTwoClosure` a disparu grâce
    à `moebius_zeta_two_closure_from_mathlib`. -/
theorem squarefree_asymptotic_density_of_moebius_mathlib
    (H : SquarefreeAsymptoticClosureFromMoebius) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density
    (squarefree_asymptotic_bridge_of_moebius_closure H)

/-- Pont asymptotique restant pour C-04b.

    Il ne contient plus le verrou eulérien `L(μ,2)=6/π²`, désormais fermé
    localement par `moebius_zeta_two_closure_from_mathlib`.

    Il reste uniquement le passage analytique/combinatoire :
    le quotient `squarefreeCount N / N` tend vers la partie réelle de
    la L-série de Möbius au point `2`. -/
def SquarefreeDensityToMoebiusLSeriesBridge : Prop :=
  Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
    (nhds
      ((LSeries
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 : ℂ)).re))

/-- Le pont `squarefreeCount/N → Re(L(μ,2))`, combiné à la fermeture
    eulérienne déjà prouvée, fournit directement
    `SquarefreeAsymptoticDensityBridge`.

    Ce théorème réduit C-04b au seul verrou encore ouvert :
    établir l'asymptotique de comptage vers la L-série de Möbius. -/
theorem squarefree_asymptotic_bridge_of_density_to_moebius_LSeries
    (H : SquarefreeDensityToMoebiusLSeriesBridge) :
    SquarefreeAsymptoticDensityBridge := by
  unfold SquarefreeDensityToMoebiusLSeriesBridge at H
  unfold SquarefreeAsymptoticDensityBridge

  have hμ := moebius_zeta_two_closure_from_mathlib
  unfold MoebiusZetaTwoClosure at hμ

  have hμ_re :
      ((LSeries
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 : ℂ)).re) =
        6 / (Real.pi ^ 2) := by
    rw [hμ]
    have hcast :
        (6 : ℂ) / ((Real.pi : ℂ) ^ 2) =
          ((6 / (Real.pi ^ 2) : ℝ) : ℂ) := by
      simp [Complex.ofReal_pow]
    exact (congrArg (fun z : ℂ => z.re) hcast).trans (by simp)

  simpa [hμ_re] using H

/-- Le nouveau pont asymptotique suffit à produire le rail conditionnel
    `SquarefreeAsymptoticClosureFromMoebius`.

    La dépendance à `MoebiusZetaTwoClosure` est devenue formelle :
    elle est déjà fermée localement dans ce fichier. -/
theorem squarefree_asymptotic_closure_from_density_to_moebius_LSeries
    (H : SquarefreeDensityToMoebiusLSeriesBridge) :
    SquarefreeAsymptoticClosureFromMoebius := by
  intro _HZ
  exact squarefree_asymptotic_bridge_of_density_to_moebius_LSeries H

/-- Consommation finale : si le pont asymptotique vers `L(μ,2)` est fourni,
    alors la densité asymptotique squarefree `6/π²` est obtenue.

    C'est la formulation la plus réduite actuelle du verrou C-04b. -/
theorem squarefree_asymptotic_density_of_density_to_moebius_LSeries
    (H : SquarefreeDensityToMoebiusLSeriesBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density
    (squarefree_asymptotic_bridge_of_density_to_moebius_LSeries H)

end CouretUnification.Logic.H3
