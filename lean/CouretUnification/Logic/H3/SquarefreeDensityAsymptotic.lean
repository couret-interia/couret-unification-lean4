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

namespace CouretUnification.Logic.H3

open Filter
open ArithmeticFunction
open Asymptotics

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

/-- Quotient de densité empirique des entiers squarefree. -/
noncomputable def squarefreeDensityQuotient (N : ℕ) : ℝ :=
  (squarefreeCount N : ℝ) / (N : ℝ)

/-- Terme principal Möbius tronqué attendu dans la preuve de densité.

    Formellement :
      `∑_{d ≤ √N} μ(d) / d²`

    Ce terme est celui qui doit converger vers `L(μ,2)` tandis que
    l'erreur de comptage doit disparaître après division par `N`. -/
noncomputable def moebiusMainTermPartial (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2))

/-- Partie réelle de la L-série de Möbius au point `2`. -/
noncomputable def moebiusLSeriesTwoReal : ℝ :=
  (LSeries
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
    (2 : ℂ)).re

/-- Sous-verrou A : l'erreur entre le quotient de comptage squarefree
    et le terme principal Möbius tronqué tend vers `0`.

    C'est ici que devront entrer :
    - l'identité indicatrice squarefree via Möbius ;
    - la réindexation C-01 ;
    - le contrôle d'erreur C-03 divisé par `N`. -/
def SquarefreeCountToMoebiusMainTermErrorBridge : Prop :=
  Tendsto
    (fun N : ℕ => squarefreeDensityQuotient N - moebiusMainTermPartial N)
    atTop
    (nhds 0)

/-- Sous-verrou B : le terme principal Möbius tronqué converge vers
    la partie réelle de `L(μ,2)`.

    C'est ici que devront entrer :
    - la sommabilité de Möbius à `s = 2` ;
    - l'identification de la somme infinie avec `LSeries`;
    - le passage des sommes tronquées `d ≤ √N` à la série complète. -/
def MoebiusMainTermTendsToLSeriesBridge : Prop :=
  Tendsto moebiusMainTermPartial atTop (nhds moebiusLSeriesTwoReal)

/-- Les deux sous-verrous analytiques A+B impliquent le pont restant
    `SquarefreeDensityToMoebiusLSeriesBridge`.

    Cette étape est purement topologique :
    si `(Q_N - M_N) → 0` et `M_N → L`, alors `Q_N → L`. -/
theorem squarefree_density_to_moebius_LSeries_of_error_and_main
    (Herr : SquarefreeCountToMoebiusMainTermErrorBridge)
    (Hmain : MoebiusMainTermTendsToLSeriesBridge) :
    SquarefreeDensityToMoebiusLSeriesBridge := by
  unfold SquarefreeDensityToMoebiusLSeriesBridge
  unfold SquarefreeCountToMoebiusMainTermErrorBridge at Herr
  unfold MoebiusMainTermTendsToLSeriesBridge at Hmain

  have hsum := Herr.add Hmain

  simpa [
    squarefreeDensityQuotient,
    moebiusMainTermPartial,
    moebiusLSeriesTwoReal,
    sub_add_cancel
  ] using hsum

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
    calc
      ((6 : ℂ) / ((Real.pi : ℂ) ^ 2)).re
          = (((6 / (Real.pi ^ 2) : ℝ) : ℂ).re) := by
              exact congrArg (fun z : ℂ => z.re) hcast
      _ = 6 / (Real.pi ^ 2) := by
              exact Complex.ofReal_re _

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

/-- Somme partielle réelle de la série de Möbius au point `2`.

    Formellement :
      `∑_{d ≤ M} μ(d) / d²`

    C'est la version à borne libre `M`, contrairement à
    `moebiusMainTermPartial`, qui utilise la borne `Nat.sqrt N`. -/
noncomputable def moebiusPartialSumReal (M : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 M) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2))

/-- Sous-verrou B1 : les sommes partielles de Möbius convergent vers
    la partie réelle de `L(μ,2)`.

    C'est ici que devront entrer :
    - `moebius_two_summable_for_asymptotic` ;
    - l'identification de `LSeries` avec la somme infinie ;
    - le passage des sommes finies `Icc 1 M` à la série complète. -/
def MoebiusPartialSumTendsToLSeriesBridge : Prop :=
  Tendsto moebiusPartialSumReal atTop (nhds moebiusLSeriesTwoReal)

/-- Sous-verrou B2 : la fonction `N ↦ Nat.sqrt N` tend vers l'infini.

    Ce verrou est élémentaire mais utile à isoler : il permet de transporter
    la convergence des sommes partielles en `M` vers les sommes tronquées
    en `Nat.sqrt N`. -/
def NatSqrtAtTopBridge : Prop :=
  Tendsto (fun N : ℕ => Nat.sqrt N) atTop atTop

/-- Fermeture élémentaire du sous-verrou B2 :
    `Nat.sqrt N → ∞` lorsque `N → ∞`.

    Pour atteindre un seuil `M`, il suffit de prendre `N ≥ M²`,
    puis `M ≤ sqrt N` par `Nat.le_sqrt'.2`. -/
theorem natSqrtAtTopBridge_proved : NatSqrtAtTopBridge := by
  unfold NatSqrtAtTopBridge
  rw [Filter.tendsto_atTop_atTop]
  intro M
  exact ⟨M ^ 2, fun N hN => Nat.le_sqrt'.2 hN⟩

/-- Les sous-verrous B1+B2 impliquent le sous-verrou B actuel.

    Si les sommes partielles de Möbius convergent vers `Re(L(μ,2))`,
    et si `Nat.sqrt N → ∞`, alors les sommes tronquées à `√N`
    convergent vers la même limite. -/
theorem moebius_mainTerm_tends_to_LSeries_of_partial_and_sqrt
    (Hpartial : MoebiusPartialSumTendsToLSeriesBridge)
    (Hsqrt : NatSqrtAtTopBridge) :
    MoebiusMainTermTendsToLSeriesBridge := by
  unfold MoebiusPartialSumTendsToLSeriesBridge at Hpartial
  unfold NatSqrtAtTopBridge at Hsqrt
  unfold MoebiusMainTermTendsToLSeriesBridge

  simpa [moebiusMainTermPartial, moebiusPartialSumReal]
    using Hpartial.comp Hsqrt

/-- Consommation combinée actuelle de C-04b.

    Si l'on dispose :
    - du sous-verrou A : erreur de comptage normalisée tendant vers `0` ;
    - du sous-verrou B1 : convergence des sommes partielles de Möbius ;
    - du sous-verrou B2 : `Nat.sqrt N → ∞` ;

    alors on obtient directement la densité asymptotique squarefree `6/π²`. -/
theorem squarefree_asymptotic_density_of_error_partial_and_sqrt
    (Herr : SquarefreeCountToMoebiusMainTermErrorBridge)
    (Hpartial : MoebiusPartialSumTendsToLSeriesBridge)
    (Hsqrt : NatSqrtAtTopBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_density_to_moebius_LSeries
    (squarefree_density_to_moebius_LSeries_of_error_and_main
      Herr
      (moebius_mainTerm_tends_to_LSeries_of_partial_and_sqrt Hpartial Hsqrt))

/-- Version sans hypothèse B2 explicite :
    B2 est maintenant fermé par `natSqrtAtTopBridge_proved`.

    Il ne reste donc, pour le sous-verrou B, que la convergence des
    sommes partielles de Möbius vers `Re(L(μ,2))`. -/
theorem moebius_mainTerm_tends_to_LSeries_of_partial
    (Hpartial : MoebiusPartialSumTendsToLSeriesBridge) :
    MoebiusMainTermTendsToLSeriesBridge :=
  moebius_mainTerm_tends_to_LSeries_of_partial_and_sqrt
    Hpartial
    natSqrtAtTopBridge_proved

/-- Consommation C-04b avec B2 fermé :
    il suffit désormais du sous-verrou A et du sous-verrou B1.

    Autrement dit :
    - erreur de comptage normalisée `→ 0`,
    - sommes partielles de Möbius `→ Re(L(μ,2))`,

    impliquent la densité squarefree `6 / π²`. -/
theorem squarefree_asymptotic_density_of_error_and_partial
    (Herr : SquarefreeCountToMoebiusMainTermErrorBridge)
    (Hpartial : MoebiusPartialSumTendsToLSeriesBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_error_partial_and_sqrt
    Herr
    Hpartial
    natSqrtAtTopBridge_proved

/-- Somme partielle complexe de la série de Möbius au point `2`.

    On la définit comme coercion complexe de la somme réelle déjà normalisée.
    Ce choix évite les frottements d'API sur la partie réelle des sommes finies,
    tout en gardant un objet de type `ℂ` raccordable à `LSeries`. -/
noncomputable def moebiusPartialSumComplex (M : ℕ) : ℂ :=
  (moebiusPartialSumReal M : ℂ)

/-- Sous-verrou B1a : les parties réelles des sommes partielles complexes
    convergent vers la partie réelle de la L-série de Möbius au point `2`.

    Cette formulation est volontairement robuste : elle évite de dépendre
    d'un lemme de continuité spécifique pour `Complex.re`, et correspond
    exactement au verrou réel nécessaire pour la densité squarefree. -/
def MoebiusPartialSumComplexTendsToLSeriesBridge : Prop :=
  Tendsto
    (fun M : ℕ => (moebiusPartialSumComplex M).re)
    atTop
    (nhds
      ((LSeries
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 : ℂ)).re))

/-- Les sommes partielles réelles sont les parties réelles
    des sommes partielles complexes.

    Avec la définition coercitive de `moebiusPartialSumComplex`,
    ce lemme devient purement définitionnel. -/
lemma moebiusPartialSumReal_eq_complex_re (M : ℕ) :
    moebiusPartialSumReal M = (moebiusPartialSumComplex M).re := by
  simp [moebiusPartialSumComplex]

/-- Si les parties réelles des sommes partielles complexes convergent vers
    `Re(L(μ,2))`, alors les sommes partielles réelles convergent vers
    `Re(L(μ,2))`.

    Ce wrapper ne contient plus de friction analytique : il ne fait que
    remplacer `moebiusPartialSumReal` par sa forme complexe coercitive. -/
theorem moebius_partial_real_tends_to_LSeries_of_complex
    (H : MoebiusPartialSumComplexTendsToLSeriesBridge) :
    MoebiusPartialSumTendsToLSeriesBridge := by
  unfold MoebiusPartialSumComplexTendsToLSeriesBridge at H
  unfold MoebiusPartialSumTendsToLSeriesBridge
  unfold moebiusLSeriesTwoReal
  simpa [moebiusPartialSumReal_eq_complex_re] using H

/-- Consommation C-04b avec B2 fermé et B1 ramené à la convergence
    des parties réelles des sommes partielles complexes.

    Il reste :
    - le sous-verrou A : erreur de comptage normalisée ;
    - le sous-verrou B1a : convergence vers la partie réelle de `L(μ,2)`. -/
theorem squarefree_asymptotic_density_of_error_and_complex_partial
    (Herr : SquarefreeCountToMoebiusMainTermErrorBridge)
    (Hcomplex : MoebiusPartialSumComplexTendsToLSeriesBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_error_and_partial
    Herr
    (moebius_partial_real_tends_to_LSeries_of_complex Hcomplex)

/-- Sous-verrou B1b : les sommes partielles réelles de Möbius au point `2`
    convergent vers la partie réelle de la série infinie associée.

    Cette formulation est le prochain point de raccord avec l'API Mathlib
    `LSeriesSummable` / `LSeriesHasSum`. -/
def MoebiusPartialSumRealTendsToLSeriesBridge : Prop :=
  Tendsto moebiusPartialSumReal atTop (nhds moebiusLSeriesTwoReal)

/-- Le bridge réel B1b est exactement le bridge B1 déjà utilisé.

    Ce wrapper sert surtout à documenter que le verrou `B1` est maintenant
    le raccord aux sommes partielles standards de la L-série de Möbius. -/
theorem moebius_partial_complex_bridge_of_real_bridge
    (H : MoebiusPartialSumRealTendsToLSeriesBridge) :
    MoebiusPartialSumComplexTendsToLSeriesBridge := by
  unfold MoebiusPartialSumComplexTendsToLSeriesBridge
  unfold MoebiusPartialSumRealTendsToLSeriesBridge at H
  unfold moebiusPartialSumComplex
  simpa using H

/-- Somme partielle réelle native `range`, mieux adaptée à `HasSum.tendsto_sum_nat`.

    Comme le terme `d = 0` est nul pour la L-série via `LSeries.term`,
    cette forme sera plus facile à raccorder à l'API Mathlib des séries. -/
noncomputable def moebiusPartialSumRealRange (M : ℕ) : ℝ :=
  Finset.sum (Finset.range (M + 1)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2))

/-- La somme partielle `range (M+1)` coïncide avec la somme partielle
    `Icc 1 M`.

    La différence avec `Icc 1 M` est absorbée par la convention de division
    totale de Lean au terme `d = 0`. Cette forme est seulement une passerelle
    technique vers les sommes `range`. -/
lemma moebiusPartialSumRealRange_eq_Icc (M : ℕ) :
    moebiusPartialSumRealRange M = moebiusPartialSumReal M := by
  unfold moebiusPartialSumRealRange moebiusPartialSumReal
  induction M with
  | zero =>
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_Icc_succ_top]
      · omega

/-- Une convergence des sommes partielles `range` implique la convergence
    des sommes partielles `Icc 1 M`.

    C'est une passerelle technique vers l'API `HasSum.tendsto_sum_nat`. -/
theorem moebius_partial_Icc_tends_of_range_tends
    (H :
      Tendsto moebiusPartialSumRealRange atTop
        (nhds moebiusLSeriesTwoReal)) :
    MoebiusPartialSumTendsToLSeriesBridge := by
  unfold MoebiusPartialSumTendsToLSeriesBridge
  convert H using 1
  · funext M
    exact (moebiusPartialSumRealRange_eq_Icc M).symm
/-- Somme partielle native de la L-série de Möbius au point `2`.

    Cette version utilise directement `LSeries.term`, donc elle est alignée
    avec l'API Mathlib `LSeriesHasSum` et `HasSum.tendsto_sum_nat`.

    Elle sert de passerelle avant de prouver que ce terme natif coïncide
    avec l'expression élémentaire `μ(d)/d²`. -/
noncomputable def moebiusLSeriesTermPartialRange (M : ℕ) : ℂ :=
  Finset.sum (Finset.range (M + 1)) (fun d =>
    LSeries.term
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (2 : ℂ)
      d)

/-- Les sommes partielles natives de la L-série de Möbius convergent vers
    `L(μ,2)`.

    Preuve directe :
    `moebius_two_summable_for_asymptotic.LSeriesHasSum`
    donne un `HasSum`, puis `HasSum.tendsto_sum_nat` donne la convergence
    des sommes sur `range n`. On compose ensuite avec `M ↦ M + 1`. -/
theorem moebius_LSeries_term_partial_tends :
    Tendsto moebiusLSeriesTermPartialRange atTop
      (nhds
        (LSeries
          (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          (2 : ℂ))) := by
  have hHas :
      HasSum
        (fun d : ℕ =>
          LSeries.term
            (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (2 : ℂ)
            d)
        (LSeries
          (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          (2 : ℂ)) := by
    simpa [LSeriesHasSum] using
      moebius_two_summable_for_asymptotic.LSeriesHasSum

  have htendsto :
      Tendsto
        (fun M : ℕ =>
          Finset.sum (Finset.range M) (fun d =>
            LSeries.term
              (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
              (2 : ℂ)
              d))
        atTop
        (nhds
          (LSeries
            (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (2 : ℂ))) :=
    hHas.tendsto_sum_nat

  unfold moebiusLSeriesTermPartialRange
  exact htendsto.comp (tendsto_add_atTop_nat 1)

/-- Pont ponctuel entre le terme natif `LSeries.term` de Möbius au point `2`
    et l'expression réelle élémentaire `μ(d) / d²`.

    Ce lemme est le raccord local entre l'API Mathlib des L-séries et
    la somme arithmétique réelle utilisée dans `moebiusPartialSumRealRange`. -/
lemma moebius_LSeries_term_re_eq_real_term (d : ℕ) :
    (LSeries.term
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (2 : ℂ)
      d).re =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2) := by
  by_cases hd : d = 0
  · subst d
    simp [LSeries.term]
  · have hcast :
        (((ArithmeticFunction.moebius d : ℤ) : ℂ) / ((d : ℂ) ^ 2)) =
          (((((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2)) : ℝ) : ℂ) := by
      simp [Complex.ofReal_div, Complex.ofReal_pow]
    calc
      (LSeries.term
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 : ℂ)
        d).re
          = ((((ArithmeticFunction.moebius d : ℤ) : ℂ) / ((d : ℂ) ^ 2)).re) := by
              simp [LSeries.term, hd]
      _ = (((((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2)) : ℝ) : ℂ).re := by
              exact congrArg (fun z : ℂ => z.re) hcast
      _ = ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2) := by
              exact Complex.ofReal_re _

/-- Les sommes partielles `range` de l'expression réelle élémentaire
    sont les parties réelles des sommes partielles natives `LSeries.term`. -/
lemma moebiusPartialSumRealRange_eq_LSeriesTerm_re (M : ℕ) :
    moebiusPartialSumRealRange M =
      (moebiusLSeriesTermPartialRange M).re := by
  unfold moebiusPartialSumRealRange moebiusLSeriesTermPartialRange

  let fR : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((d : ℝ) ^ 2)

  let fC : ℕ → ℂ := fun d =>
    LSeries.term
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
      (2 : ℂ)
      d

  have hsum : ∀ s : Finset ℕ,
      Finset.sum s fR = (Finset.sum s fC).re := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [fR, fC]
    | insert d s hds ih =>
        rw [Finset.sum_insert hds, Finset.sum_insert hds, Complex.add_re]
        rw [← ih]
        dsimp [fR, fC]
        rw [moebius_LSeries_term_re_eq_real_term d]

  simpa [fR, fC] using hsum (Finset.range (M + 1))

/-- Fermeture de B1 à partir de la convergence native `LSeries.term`.

    Les sommes réelles `μ(d)/d²` convergent vers `Re(L(μ,2))`, car elles
    sont les parties réelles des sommes partielles natives de la L-série. -/
theorem moebius_partial_range_tends_to_LSeriesReal :
    Tendsto moebiusPartialSumRealRange atTop
      (nhds moebiusLSeriesTwoReal) := by
  have hComplex := moebius_LSeries_term_partial_tends
  have hRe :
      Tendsto
        (fun M : ℕ => (moebiusLSeriesTermPartialRange M).re)
        atTop
        (nhds moebiusLSeriesTwoReal) := by
    unfold moebiusLSeriesTwoReal
    exact (Complex.continuous_re.tendsto _).comp hComplex

  convert hRe using 1
  · funext M
    exact (moebiusPartialSumRealRange_eq_LSeriesTerm_re M)

/-- Fermeture du sous-verrou B1 : les sommes partielles de Möbius
    convergent vers `Re(L(μ,2))`. -/
theorem moebiusPartialSumTendsToLSeriesBridge_proved :
    MoebiusPartialSumTendsToLSeriesBridge :=
  moebius_partial_Icc_tends_of_range_tends
    moebius_partial_range_tends_to_LSeriesReal

/-- Consommation C-04b avec B1 et B2 fermés :
    il ne reste plus que le sous-verrou A, l'erreur de comptage normalisée. -/
theorem squarefree_asymptotic_density_of_error_only
    (Herr : SquarefreeCountToMoebiusMainTermErrorBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_error_and_partial
    Herr
    moebiusPartialSumTendsToLSeriesBridge_proved

/-!
## Sous-verrou A — erreur de comptage normalisée

Après fermeture de B1 et B2, C-04b est réduite au seul verrou A :
montrer que le quotient de comptage squarefree est asymptotique au
terme principal de Möbius tronqué.
-/

/-- Terme de comptage exact attendu via Möbius et division entière.

    Formellement :
      `∑_{d≤√N} μ(d) * ⌊N / d²⌋`

    C'est la version discrète avant passage au terme principal réel
    `∑ μ(d)/d²`. -/
noncomputable def moebiusFloorCountTerm (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((N / d ^ 2 : ℕ) : ℝ))

/-- Terme de densité exact attendu via Möbius et division entière. -/
noncomputable def moebiusFloorDensityTerm (N : ℕ) : ℝ :=
  moebiusFloorCountTerm N / (N : ℝ)

/-- Sous-verrou A1 : formule exacte de comptage squarefree via Möbius.

    Ce bridge encode l'identité discrète attendue :
      `squarefreeCount N / N = (1/N) * ∑_{d≤√N} μ(d)⌊N/d²⌋`.

    C'est ici que devront entrer :
    - l'identité indicatrice `1_squarefree(n) = ∑_{d²∣n} μ(d)` ;
    - la réindexation de type Fubini déjà préparée dans `SquarefreeDensity`;
    - les conventions aux petits cas, notamment `N = 0`. -/
def SquarefreeCountExactMoebiusFloorBridge : Prop :=
  ∀ N : ℕ,
    squarefreeDensityQuotient N = moebiusFloorDensityTerm N

/-- Sous-verrou A2 : l'erreur entre le terme discret à plancher
    et le terme principal réel tend vers `0`.

    C'est ici que doivent entrer :
    - le contrôle local de l'erreur euclidienne ;
    - le `O(√N)` déjà prouvé dans `SquarefreeDensity`;
    - la division par `N`, qui force l'erreur normalisée à tendre vers `0`. -/
def MoebiusFloorToMainTermErrorBridge : Prop :=
  Tendsto
    (fun N : ℕ => moebiusFloorDensityTerm N - moebiusMainTermPartial N)
    atTop
    (nhds 0)

/-- Les deux sous-verrous A1+A2 ferment le verrou A.

    Si le comptage squarefree coïncide exactement avec le terme discret
    de Möbius à plancher, et si l'erreur entre ce terme discret normalisé
    et le terme principal réel tend vers `0`, alors
    `SquarefreeCountToMoebiusMainTermErrorBridge` est établi. -/
theorem squarefree_count_to_moebius_main_error_of_floor
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Hfloor : MoebiusFloorToMainTermErrorBridge) :
    SquarefreeCountToMoebiusMainTermErrorBridge := by
  unfold SquarefreeCountToMoebiusMainTermErrorBridge
  unfold MoebiusFloorToMainTermErrorBridge at Hfloor
  unfold SquarefreeCountExactMoebiusFloorBridge at Hexact

  convert Hfloor using 1
  · funext N
    rw [Hexact N]

/-- Consommation finale de C-04b lorsque A1 et A2 sont fournis.

    À ce stade, les verrous eulérien, B1 et B2 sont fermés localement.
    Il suffit donc de fournir :
    - A1 : la formule exacte de comptage via Möbius ;
    - A2 : l'annulation asymptotique de l'erreur plancher normalisée. -/
theorem squarefree_asymptotic_density_of_floor_bridges
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Hfloor : MoebiusFloorToMainTermErrorBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_error_only
    (squarefree_count_to_moebius_main_error_of_floor Hexact Hfloor)

/-- Somme absolue des erreurs euclidiennes locales.

    C'est exactement le terme déjà contrôlé par `error_term_isBigO`
    dans `SquarefreeDensity.lean` :

      `∑_{d≤√N} |⌊N/d²⌋ - N/d²|`

    Il sert de majorant naturel pour l'erreur entre le terme discret
    de Möbius à plancher et le terme principal réel. -/
noncomputable def euclideanFloorErrorSum (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
    |((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2|)

/-- Erreur euclidienne normalisée par `N`.

    C'est cette quantité qui doit tendre vers `0` pour fermer A2. -/
noncomputable def normalizedEuclideanFloorError (N : ℕ) : ℝ :=
  euclideanFloorErrorSum N / (N : ℝ)

/-- Bridge déjà prouvé dans `SquarefreeDensity.lean` :
    l'erreur euclidienne totale est `O(√N)`. -/
def EuclideanFloorErrorIsBigOBridge : Prop :=
  IsBigO atTop euclideanFloorErrorSum
    (fun N : ℕ => Real.sqrt (N : ℝ))

/-- Fermeture locale du bridge `O(√N)` depuis `SquarefreeDensity.error_term_isBigO`.

    Cette étape ne ferme pas encore A2, mais elle raccorde explicitement
    le laboratoire asymptotique au résultat [D] déjà obtenu dans
    `SquarefreeDensity.lean`. -/
theorem euclideanFloorErrorIsBigOBridge_proved :
    EuclideanFloorErrorIsBigOBridge := by
  unfold EuclideanFloorErrorIsBigOBridge
  simpa [euclideanFloorErrorSum] using error_term_isBigO

/-- Sous-verrou A2a : l'erreur euclidienne normalisée tend vers `0`.

    Ce verrou doit être obtenu à partir de :
    - `euclideanFloorErrorIsBigOBridge_proved`,
    - `√N / N → 0`. -/
def NormalizedEuclideanFloorErrorTendsZeroBridge : Prop :=
  Tendsto normalizedEuclideanFloorError atTop (nhds 0)

/-- Bridge élémentaire attendu :
    `sqrt(N) / N → 0`.

    Ce verrou analytique standard permet de transformer
    `euclideanFloorErrorSum = O(√N)` en erreur normalisée tendant vers `0`. -/
def SqrtDivNatTendsZeroBridge : Prop :=
  Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / (N : ℝ)) atTop (nhds 0)

/-- Sous-verrou standard : `Real.sqrt N → ∞` quand `N → ∞`.

    C'est le pendant réel du lemme déjà fermé `Nat.sqrt N → ∞`.
    Une fois ce verrou fourni, `sqrt(N)/N → 0` se ramène à
    `1/sqrt(N) → 0`. -/
def RealSqrtNatAtTopBridge : Prop :=
  Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop

/-- Pour `N > 0`, on a `sqrt(N)/N = 1/sqrt(N)`.

    Ce lemme évite de laisser `field_simp` deviner la transformation
    dans les preuves de convergence. -/
lemma real_sqrt_div_nat_eq_inv_sqrt_eventually :
    (fun N : ℕ => Real.sqrt (N : ℝ) / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) := by
  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro N hN
  have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hsq :
      (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNpos.le
  calc
    Real.sqrt (N : ℝ) / (N : ℝ)
        = Real.sqrt (N : ℝ) / ((Real.sqrt (N : ℝ)) ^ 2) := by
            rw [hsq]
    _ = (Real.sqrt (N : ℝ))⁻¹ := by
            field_simp [hsqrt_ne, pow_two]

/-- Si `sqrt(N) → ∞`, alors `sqrt(N)/N → 0`.

    La preuve utilise l'identité éventuelle `sqrt(N)/N = 1/sqrt(N)`
    et `Tendsto.inv_tendsto_atTop`. -/
theorem sqrtDivNatTendsZero_of_realSqrtAtTop
    (Hsqrt : RealSqrtNatAtTopBridge) :
    SqrtDivNatTendsZeroBridge := by
  unfold RealSqrtNatAtTopBridge at Hsqrt
  unfold SqrtDivNatTendsZeroBridge

  have hinv :
      Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (nhds 0) :=
    Hsqrt.inv_tendsto_atTop

  exact hinv.congr' real_sqrt_div_nat_eq_inv_sqrt_eventually.symm

/-- Bridge de transfert `O(√N)` vers erreur normalisée nulle.

    Si l'erreur euclidienne totale est `O(√N)` et si `√N/N → 0`,
    alors l'erreur euclidienne normalisée tend vers `0`.

    Cette formulation isole le lemme asymptotique général
    `f = O(g)` et `g/N → 0` ⇒ `f/N → 0`. -/
def NormalizedEuclideanFloorErrorFromBigOBridge : Prop :=
  EuclideanFloorErrorIsBigOBridge →
  SqrtDivNatTendsZeroBridge →
  NormalizedEuclideanFloorErrorTendsZeroBridge

/-- Consommation de A2a à partir de `O(√N)` et de `√N/N → 0`. -/
theorem normalizedEuclideanFloorError_of_bigO_bridge
    (Htransfer : NormalizedEuclideanFloorErrorFromBigOBridge)
    (HsqrtDiv : SqrtDivNatTendsZeroBridge) :
    NormalizedEuclideanFloorErrorTendsZeroBridge :=
  Htransfer euclideanFloorErrorIsBigOBridge_proved HsqrtDiv

/-- Consommation de `sqrt(N)/N → 0` à partir de `Real.sqrt(N) → ∞`. -/
theorem normalizedEuclideanFloorError_of_bigO_and_realSqrtAtTop
    (Htransfer : NormalizedEuclideanFloorErrorFromBigOBridge)
    (Hsqrt : RealSqrtNatAtTopBridge) :
    NormalizedEuclideanFloorErrorTendsZeroBridge :=
  normalizedEuclideanFloorError_of_bigO_bridge
    Htransfer
    (sqrtDivNatTendsZero_of_realSqrtAtTop Hsqrt)

/-- Fermeture de `Real.sqrt(N) → ∞`.

    On compose le lemme Mathlib `Real.tendsto_sqrt_atTop`
    avec la convergence standard du cast naturel `N : ℝ` vers `atTop`. -/
theorem realSqrtNatAtTopBridge_proved :
    RealSqrtNatAtTopBridge := by
  unfold RealSqrtNatAtTopBridge
  exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

/-- Fermeture du bridge `sqrt(N)/N → 0`. -/
theorem sqrtDivNatTendsZeroBridge_proved :
    SqrtDivNatTendsZeroBridge :=
  sqrtDivNatTendsZero_of_realSqrtAtTop realSqrtNatAtTopBridge_proved

/-- A2a avec le verrou `sqrt(N)/N → 0` fermé.

    Il reste seulement le transfert asymptotique général depuis `O(√N)`. -/
theorem normalizedEuclideanFloorError_of_bigO_transfer
    (Htransfer : NormalizedEuclideanFloorErrorFromBigOBridge) :
    NormalizedEuclideanFloorErrorTendsZeroBridge :=
  normalizedEuclideanFloorError_of_bigO_bridge
    Htransfer
    sqrtDivNatTendsZeroBridge_proved

/-- Fermeture du transfert `O(√N)` vers erreur euclidienne normalisée nulle.

    Preuve spécialisée :
    si `euclideanFloorErrorSum = O(√N)`, alors, éventuellement,
    `|euclideanFloorErrorSum N| ≤ C * √N`.
    Après division par `N`, on domine l'erreur normalisée par
    `C * (√N / N)`, qui tend vers `0`.

    Cette preuve ferme A2a à partir du `O(√N)` déjà prouvé et du lemme
    `sqrt(N)/N → 0` fermé localement. -/
theorem normalizedEuclideanFloorErrorFromBigOBridge_proved :
    NormalizedEuclideanFloorErrorFromBigOBridge := by
  intro HbigO HsqrtDiv
  unfold NormalizedEuclideanFloorErrorTendsZeroBridge
  unfold normalizedEuclideanFloorError

  unfold EuclideanFloorErrorIsBigOBridge at HbigO
  unfold SqrtDivNatTendsZeroBridge at HsqrtDiv

  rw [Asymptotics.IsBigO] at HbigO
  rcases HbigO with ⟨C, hC_with⟩
  rw [Asymptotics.IsBigOWith] at hC_with

  have hbound :
      ∀ᶠ N in atTop,
        |euclideanFloorErrorSum N / (N : ℝ)| ≤
          C * (Real.sqrt (N : ℝ) / (N : ℝ)) := by
    filter_upwards [hC_with, Filter.eventually_atTop.2 ⟨1, by
      intro N hN
      have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
      exact hNpos⟩] with N hC hNpos

    have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
    have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg hNnonneg

    have hdiv :
        |euclideanFloorErrorSum N / (N : ℝ)| =
          |euclideanFloorErrorSum N| / (N : ℝ) := by
      rw [abs_div, hNabs]

    rw [hdiv]

    have hC' :
        |euclideanFloorErrorSum N| ≤ C * |Real.sqrt (N : ℝ)| := by
      simpa [Real.norm_eq_abs] using hC

    have hsqrt_nonneg : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hsqrt_abs : |Real.sqrt (N : ℝ)| = Real.sqrt (N : ℝ) :=
      abs_of_nonneg hsqrt_nonneg

    rw [hsqrt_abs] at hC'

    have hdiv_le := div_le_div_of_nonneg_right hC' hNnonneg

    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le

  have htendsto_majorant :
      Tendsto
        (fun N : ℕ => C * (Real.sqrt (N : ℝ) / (N : ℝ)))
        atTop
        (nhds 0) := by
    simpa using HsqrtDiv.const_mul C

  have hAbs :
      Tendsto
        (fun N : ℕ => |euclideanFloorErrorSum N / (N : ℝ)|)
        atTop
        (nhds 0) := by
    refine squeeze_zero'
      (Eventually.of_forall (fun N : ℕ => abs_nonneg _))
      hbound
      htendsto_majorant

  exact
    (tendsto_zero_iff_abs_tendsto_zero
      (l := atTop)
      (f := fun N : ℕ => euclideanFloorErrorSum N / (N : ℝ))).2 hAbs

/-- Fermeture de A2a : l'erreur euclidienne normalisée tend vers `0`. -/
theorem normalizedEuclideanFloorErrorTendsZeroBridge_proved :
    NormalizedEuclideanFloorErrorTendsZeroBridge :=
  normalizedEuclideanFloorErrorFromBigOBridge_proved
    euclideanFloorErrorIsBigOBridge_proved
    sqrtDivNatTendsZeroBridge_proved

/-- Sous-verrou A2b : l'erreur de Möbius à plancher est contrôlée
    par l'erreur euclidienne normalisée.

    Formellement, à partir d'un certain rang :
      `|floor-density - main-term| ≤ normalizedEuclideanFloorError`.

    C'est ici que devra entrer la borne élémentaire `|μ(d)| ≤ 1`. -/
def MoebiusFloorToMainControlledByEuclideanErrorBridge : Prop :=
  ∀ᶠ N in atTop,
    |moebiusFloorDensityTerm N - moebiusMainTermPartial N| ≤
      normalizedEuclideanFloorError N

/-- Fermeture abstraite de A2 par contrôle et annulation du majorant.

    Ce bridge isole le principe d'encadrement réel :
    si l'erreur de Möbius est dominée par une erreur normalisée qui tend
    vers `0`, alors `MoebiusFloorToMainTermErrorBridge` est établi.

    Il sera remplacé plus tard par une preuve directe lorsque l'API de
    squeeze/tendsto sera stabilisée dans ce fichier. -/
def MoebiusFloorToMainErrorSqueezeBridge : Prop :=
  MoebiusFloorToMainControlledByEuclideanErrorBridge →
  NormalizedEuclideanFloorErrorTendsZeroBridge →
  MoebiusFloorToMainTermErrorBridge

/-- Consommation de la fermeture abstraite de A2. -/
theorem moebiusFloorToMainError_of_squeeze_bridge
    (Hsqueeze : MoebiusFloorToMainErrorSqueezeBridge)
    (Hcontrol : MoebiusFloorToMainControlledByEuclideanErrorBridge)
    (Hzero : NormalizedEuclideanFloorErrorTendsZeroBridge) :
    MoebiusFloorToMainTermErrorBridge :=
  Hsqueeze Hcontrol Hzero

/-- Fermeture du principe de squeeze réel pour A2.

    Si l'erreur de Möbius à plancher est éventuellement dominée en valeur
    absolue par une erreur normalisée tendant vers `0`, alors cette erreur
    de Möbius tend elle-même vers `0`.

    Cette preuve est purement analytique : elle ne dépend pas encore
    de la structure arithmétique de Möbius. -/
theorem moebiusFloorToMainErrorSqueezeBridge_proved :
    MoebiusFloorToMainErrorSqueezeBridge := by
  intro Hcontrol Hzero
  unfold MoebiusFloorToMainTermErrorBridge
  unfold NormalizedEuclideanFloorErrorTendsZeroBridge at Hzero
  unfold MoebiusFloorToMainControlledByEuclideanErrorBridge at Hcontrol

  have hAbs :
      Tendsto
        (fun N : ℕ => |moebiusFloorDensityTerm N - moebiusMainTermPartial N|)
        atTop
        (nhds 0) := by
    refine squeeze_zero'
      (Eventually.of_forall (fun N : ℕ => abs_nonneg _))
      Hcontrol
      Hzero

  exact
    (tendsto_zero_iff_abs_tendsto_zero
      (l := atTop)
      (f := fun N : ℕ => moebiusFloorDensityTerm N - moebiusMainTermPartial N)).2 hAbs

/-- Version de consommation de A2 avec le squeeze réel désormais fermé.

    Il reste à fournir :
    - le contrôle de l'erreur de Möbius par l'erreur euclidienne ;
    - l'annulation de l'erreur euclidienne normalisée. -/
theorem moebiusFloorToMainError_of_control_and_zero
    (Hcontrol : MoebiusFloorToMainControlledByEuclideanErrorBridge)
    (Hzero : NormalizedEuclideanFloorErrorTendsZeroBridge) :
    MoebiusFloorToMainTermErrorBridge :=
  moebiusFloorToMainErrorSqueezeBridge_proved Hcontrol Hzero

/-- Fermeture de A2 dès que le contrôle A2b est fourni.

    A2a est maintenant fermé localement :
      `normalizedEuclideanFloorError → 0`.

    Il ne reste donc, pour établir `MoebiusFloorToMainTermErrorBridge`,
    qu'à prouver le contrôle algébrique A2b :
      `|floor-density - main-term| ≤ normalizedEuclideanFloorError`
    éventuellement. -/
theorem moebiusFloorToMainError_of_control_only
    (Hcontrol : MoebiusFloorToMainControlledByEuclideanErrorBridge) :
    MoebiusFloorToMainTermErrorBridge :=
  moebiusFloorToMainError_of_control_and_zero
    Hcontrol
    normalizedEuclideanFloorErrorTendsZeroBridge_proved

/-- Consommation finale de C-04b avec A1 et le seul contrôle A2b.

    À ce stade :
    - le verrou eulérien `L(μ,2)=6/π²` est fermé ;
    - B1 est fermé par `LSeries.term` ;
    - B2 est fermé par `Nat.sqrt → atTop` ;
    - A2a est fermé par `O(√N)` puis normalisation ;
    - il reste seulement A1 et A2b. -/
theorem squarefree_asymptotic_density_of_exact_and_control
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Hcontrol : MoebiusFloorToMainControlledByEuclideanErrorBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_floor_bridges
    Hexact
    (moebiusFloorToMainError_of_control_only Hcontrol)

/-!
## Sous-verrou A2b — contrôle algébrique de l'erreur pondérée par Möbius

A2b consiste à montrer que l'erreur discrète pondérée par `μ(d)`
est dominée par la somme absolue des erreurs euclidiennes.
-/

/-- Erreur euclidienne pondérée par Möbius avant normalisation.

    Formellement :
      `∑ μ(d) * (⌊N/d²⌋ - N/d²)`.

    C'est exactement la différence attendue entre le terme à plancher
    et le terme principal réel, avant division par `N`. -/
noncomputable def moebiusWeightedFloorErrorSum (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2))

/-- Sous-verrou A2b-1 : identité algébrique entre l'erreur de densité
    et l'erreur pondérée par Möbius normalisée.

    Cette identité doit venir simplement du développement :
      `(∑ μ(d)⌊N/d²⌋)/N - ∑ μ(d)/d²`
    puis factorisation terme à terme. -/
def MoebiusFloorDifferenceEqualsWeightedErrorBridge : Prop :=
  ∀ᶠ N in atTop,
    moebiusFloorDensityTerm N - moebiusMainTermPartial N =
      moebiusWeightedFloorErrorSum N / (N : ℝ)

/-- Sous-verrou A2b-2 : contrôle par la somme absolue euclidienne.

    C'est ici que doit entrer :
      `|μ(d)| ≤ 1`.

    Formellement :
      `|∑ μ(d) e_d| ≤ ∑ |e_d|`. -/
def MoebiusWeightedErrorAbsBoundBridge : Prop :=
  ∀ N : ℕ,
    |moebiusWeightedFloorErrorSum N| ≤ euclideanFloorErrorSum N

/-- A2b est fermé si l'erreur de densité est l'erreur pondérée
    normalisée, et si cette erreur pondérée est dominée par la somme
    absolue euclidienne.

    La seule subtilité est la division par `N`, traitée éventuellement
    pour `N ≥ 1`. -/
theorem moebiusFloorControl_of_weighted_error_bridges
    (Heq : MoebiusFloorDifferenceEqualsWeightedErrorBridge)
    (Hbound : MoebiusWeightedErrorAbsBoundBridge) :
    MoebiusFloorToMainControlledByEuclideanErrorBridge := by
  unfold MoebiusFloorToMainControlledByEuclideanErrorBridge
  unfold MoebiusFloorDifferenceEqualsWeightedErrorBridge at Heq
  unfold MoebiusWeightedErrorAbsBoundBridge at Hbound
  unfold normalizedEuclideanFloorError

  filter_upwards [Heq, Filter.eventually_atTop.2 ⟨1, by
    intro N hN
    have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    exact hNpos⟩] with N hEq hNpos

  rw [hEq]

  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg hNnonneg

  calc
    |moebiusWeightedFloorErrorSum N / (N : ℝ)|
        = |moebiusWeightedFloorErrorSum N| / (N : ℝ) := by
            rw [abs_div, hNabs]
    _ ≤ euclideanFloorErrorSum N / (N : ℝ) :=
            div_le_div_of_nonneg_right (Hbound N) hNnonneg

/-- Version finale : C-04b est consommée avec A1 et les deux sous-verrous
    algébriques de A2b. -/
theorem squarefree_asymptotic_density_of_exact_and_weighted_error
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Heq : MoebiusFloorDifferenceEqualsWeightedErrorBridge)
    (Hbound : MoebiusWeightedErrorAbsBoundBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_exact_and_control
    Hexact
    (moebiusFloorControl_of_weighted_error_bridges Heq Hbound)

/-- Borne élémentaire sur la fonction de Möbius.

    Elle sera ensuite fermée à partir du fait que `μ(d)` ne prend que
    les valeurs `-1`, `0`, `1`.

    Pour l'instant, on l'isole comme verrou très local :
      `|μ(d)| ≤ 1`. -/
def MoebiusAbsLeOneBridge : Prop :=
  ∀ d : ℕ, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1

/-- Si `|μ(d)| ≤ 1` pour tout `d`, alors l'erreur pondérée par Möbius
    est dominée par la somme absolue euclidienne.

    C'est le cœur de A2b-2 :
      `|∑ μ(d)e_d| ≤ ∑ |e_d|`.

    La preuve utilise seulement :
    - l'inégalité triangulaire pour les sommes finies ;
    - `|μ(d)e_d| = |μ(d)| |e_d|` ;
    - `|μ(d)| ≤ 1`. -/
theorem moebiusWeightedErrorAbsBound_of_moebius_abs_le_one
    (Hmu : MoebiusAbsLeOneBridge) :
    MoebiusWeightedErrorAbsBoundBridge := by
  unfold MoebiusWeightedErrorAbsBoundBridge
  intro N

  unfold moebiusWeightedFloorErrorSum
  unfold euclideanFloorErrorSum

  let s : Finset ℕ := Finset.Icc 1 (Nat.sqrt N)
  let e : ℕ → ℝ := fun d =>
    ((N / d^2 : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)^2
  let m : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

  calc
    |Finset.sum s (fun d => m d * e d)|
        ≤ Finset.sum s (fun d => |m d * e d|) := by
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.sum s (fun d => |e d|) := by
            refine Finset.sum_le_sum ?_
            intro d hd
            rw [abs_mul]
            have hm : |m d| ≤ 1 := by
              simpa [m] using Hmu d
            have he_nonneg : 0 ≤ |e d| := abs_nonneg _
            calc
              |m d| * |e d| ≤ 1 * |e d| :=
                mul_le_mul_of_nonneg_right hm he_nonneg
              _ = |e d| := by ring

/-- A2b-2 fermé à partir de la seule borne `|μ(d)| ≤ 1`. -/
theorem moebiusWeightedErrorAbsBoundBridge_of_moebius_abs_le_one
    (Hmu : MoebiusAbsLeOneBridge) :
    MoebiusWeightedErrorAbsBoundBridge :=
  moebiusWeightedErrorAbsBound_of_moebius_abs_le_one Hmu

/-- Fermeture de la borne élémentaire `|μ(d)| ≤ 1`.

    Mathlib fournit déjà :
      `ArithmeticFunction.abs_moebius_le_one`.

    On le transporte simplement de `ℤ` vers `ℝ`. -/
theorem moebiusAbsLeOneBridge_proved :
    MoebiusAbsLeOneBridge := by
  unfold MoebiusAbsLeOneBridge
  intro d
  have hZ :
      |(ArithmeticFunction.moebius d : ℤ)| ≤ (1 : ℤ) := by
    simpa using (ArithmeticFunction.abs_moebius_le_one (n := d))
  exact_mod_cast hZ

/-- Fermeture de A2b-2 : l'erreur pondérée par Möbius est dominée
    par la somme absolue euclidienne. -/
theorem moebiusWeightedErrorAbsBoundBridge_proved :
    MoebiusWeightedErrorAbsBoundBridge :=
  moebiusWeightedErrorAbsBoundBridge_of_moebius_abs_le_one
    moebiusAbsLeOneBridge_proved

/-- A2b est réduit à sa seule identité algébrique A2b-1.

    La borne A2b-2 est maintenant fermée par `|μ(d)| ≤ 1`. -/
theorem moebiusFloorControl_of_weighted_error_identity
    (Heq : MoebiusFloorDifferenceEqualsWeightedErrorBridge) :
    MoebiusFloorToMainControlledByEuclideanErrorBridge :=
  moebiusFloorControl_of_weighted_error_bridges
    Heq
    moebiusWeightedErrorAbsBoundBridge_proved

/-- Version finale : C-04b est consommée avec A1 et A2b-1 seulement.

    À ce stade, tout A2 est fermé sauf l'identité algébrique :
      `floor-density - main-term = weighted-error / N`. -/
theorem squarefree_asymptotic_density_of_exact_and_weighted_identity
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Heq : MoebiusFloorDifferenceEqualsWeightedErrorBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_exact_and_control
    Hexact
    (moebiusFloorControl_of_weighted_error_identity Heq)

/-- Terme principal mis à l'échelle par `N`.

    Formellement :
      `∑ μ(d) * (N / d²)`.

    Il sert d'intermédiaire algébrique entre :
    - le terme discret à plancher ;
    - le terme principal normalisé `∑ μ(d)/d²`. -/
noncomputable def moebiusScaledMainTerm (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((N : ℝ) / (d : ℝ)^2))

/-- Identité algébrique finie :
    l'erreur pondérée est la différence entre le terme à plancher
    et le terme principal mis à l'échelle par `N`.

    C'est une simple distributivité terme à terme :
      `μ(d) * (floor - real) = μ(d)*floor - μ(d)*real`. -/
theorem moebiusWeightedFloorErrorSum_eq_floor_minus_scaled
    (N : ℕ) :
    moebiusWeightedFloorErrorSum N =
      moebiusFloorCountTerm N - moebiusScaledMainTerm N := by
  unfold moebiusWeightedFloorErrorSum
  unfold moebiusFloorCountTerm
  unfold moebiusScaledMainTerm

  let s : Finset ℕ := Finset.Icc 1 (Nat.sqrt N)
  let m : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  let a : ℕ → ℝ := fun d =>
    ((N / d^2 : ℕ) : ℝ)
  let b : ℕ → ℝ := fun d =>
    (N : ℝ) / (d : ℝ)^2

  change
    Finset.sum s (fun d => m d * (a d - b d)) =
      Finset.sum s (fun d => m d * a d) -
        Finset.sum s (fun d => m d * b d)

  calc
    Finset.sum s (fun d => m d * (a d - b d))
        = Finset.sum s (fun d => m d * a d - m d * b d) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            ring
    _ = Finset.sum s (fun d => m d * a d) -
          Finset.sum s (fun d => m d * b d) := by
            rw [Finset.sum_sub_distrib]

/-- Sous-verrou A2b-1' :
    le terme principal mis à l'échelle, divisé par `N`, redonne
    le terme principal tronqué.

    Pour `N ≥ 1`, cela repose sur :
      `(μ(d) * (N/d²)) / N = μ(d)/d²`. -/
def MoebiusScaledMainTermDivBridge : Prop :=
  ∀ᶠ N in atTop,
    moebiusScaledMainTerm N / (N : ℝ) =
      moebiusMainTermPartial N

/-- A2b-1 est réduit à l'identité `scaled-main / N = main-term`.

    On utilise :
    - `weighted-error = floor-count - scaled-main`,
    - `scaled-main / N = main-term`,
    - l'identité algébrique
      `floor-count/N - scaled-main/N = (floor-count - scaled-main)/N`. -/
theorem moebiusFloorDifferenceEqualsWeightedError_of_scaled_main_div
    (Hscaled : MoebiusScaledMainTermDivBridge) :
    MoebiusFloorDifferenceEqualsWeightedErrorBridge := by
  unfold MoebiusFloorDifferenceEqualsWeightedErrorBridge
  unfold MoebiusScaledMainTermDivBridge at Hscaled

  filter_upwards [Hscaled, Filter.eventually_atTop.2 ⟨1, by
    intro N hN
    have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    exact hNpos⟩] with N hscaled hNpos

  unfold moebiusFloorDensityTerm

  rw [← hscaled]
  rw [moebiusWeightedFloorErrorSum_eq_floor_minus_scaled N]

  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos

  field_simp [hNne]

/-- Version finale : C-04b est consommée avec A1 et le seul bridge
    `scaled-main / N = main-term`.

    Le contrôle A2b-2 est déjà fermé par `|μ(d)| ≤ 1`. -/
theorem squarefree_asymptotic_density_of_exact_and_scaled_main
    (Hexact : SquarefreeCountExactMoebiusFloorBridge)
    (Hscaled : MoebiusScaledMainTermDivBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_exact_and_weighted_identity
    Hexact
    (moebiusFloorDifferenceEqualsWeightedError_of_scaled_main_div Hscaled)

/-- Fermeture de `scaled-main / N = main-term`.

    Pour `N ≥ 1`, on divise terme à terme :
      `(μ(d) * (N/d²)) / N = μ(d)/d²`.

    La restriction éventuelle à `N ≥ 1` évite uniquement la division
    par zéro. -/
theorem moebiusScaledMainTermDivBridge_proved :
    MoebiusScaledMainTermDivBridge := by
  unfold MoebiusScaledMainTermDivBridge

  refine Filter.eventually_atTop.2 ⟨1, ?_⟩
  intro N hN

  have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos

  unfold moebiusScaledMainTerm
  unfold moebiusMainTermPartial

  let s : Finset ℕ := Finset.Icc 1 (Nat.sqrt N)
  let m : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

  change
    (Finset.sum s (fun d => m d * ((N : ℝ) / (d : ℝ)^2))) / (N : ℝ) =
      Finset.sum s (fun d => m d / (d : ℝ)^2)

  calc
    (Finset.sum s (fun d => m d * ((N : ℝ) / (d : ℝ)^2))) / (N : ℝ)
        = Finset.sum s (fun d =>
            (m d * ((N : ℝ) / (d : ℝ)^2)) / (N : ℝ)) := by
            rw [Finset.sum_div]
    _ = Finset.sum s (fun d => m d / (d : ℝ)^2) := by
            refine Finset.sum_congr rfl ?_
            intro d hd

            have hd_mem : d ∈ Finset.Icc 1 (Nat.sqrt N) := by
              simpa [s] using hd
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem).1
            have hdpos_nat : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd1
            have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat
            have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos

            field_simp [hNne, hdne]

/-- Version finale : C-04b est consommée avec le seul verrou A1.

    Tout A2 est maintenant fermé :
    - A2a par `O(√N)` et normalisation ;
    - A2b-2 par `|μ(d)| ≤ 1` ;
    - A2b-1 par le calcul `scaled-main / N = main-term`.

    Il reste uniquement A1 :
      la formule exacte de comptage squarefree via Möbius. -/
theorem squarefree_asymptotic_density_of_exact_only
    (Hexact : SquarefreeCountExactMoebiusFloorBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_exact_and_scaled_main
    Hexact
    moebiusScaledMainTermDivBridge_proved

/-- Sous-verrou A1' : formule exacte non normalisée de comptage squarefree.

    C'est la forme arithmétique naturelle :
      `squarefreeCount N = ∑_{d≤√N} μ(d)⌊N/d²⌋`.

    Une fois cette identité prouvée, A1 s'obtient simplement en divisant
    les deux côtés par `N`. -/
def SquarefreeCountExactMoebiusFloorCountBridge : Prop :=
  ∀ N : ℕ,
    (squarefreeCount N : ℝ) = moebiusFloorCountTerm N

/-- La formule exacte non normalisée implique A1.

    Cette étape est purement formelle : on divise les deux côtés par `N`.
    Elle garde les conventions Lean aux petits cas, notamment `N = 0`,
    sans ajouter de traitement analytique. -/
theorem squarefreeCountExactMoebiusFloorBridge_of_count_bridge
    (Hcount : SquarefreeCountExactMoebiusFloorCountBridge) :
    SquarefreeCountExactMoebiusFloorBridge := by
  unfold SquarefreeCountExactMoebiusFloorBridge
  intro N
  unfold squarefreeDensityQuotient
  unfold moebiusFloorDensityTerm
  rw [Hcount N]

/-- Version finale : C-04b est consommée avec la seule formule exacte
    non normalisée de comptage squarefree.

    Tout le volet asymptotique A2 est fermé ; il reste uniquement
    l'identité arithmétique discrète :
      `squarefreeCount N = ∑ μ(d)⌊N/d²⌋`. -/
theorem squarefree_asymptotic_density_of_count_exact
    (Hcount : SquarefreeCountExactMoebiusFloorCountBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_exact_only
    (squarefreeCountExactMoebiusFloorBridge_of_count_bridge Hcount)

/-!
## Sous-verrou A1 — formule exacte de comptage squarefree

On réduit la formule exacte à deux ingrédients classiques :
1. l'identité indicatrice de Möbius ;
2. la réindexation finie des couples `(d,n)` avec `d² ∣ n`.
-/

/-- Somme des indicatrices squarefree jusqu'à `N`.

    Cette définition isole la version réelle du comptage :
      `∑_{n≤N} 1_{squarefree(n)}`. -/
noncomputable def squarefreeIndicatorCountReal (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) (fun n =>
    if Squarefree n then (1 : ℝ) else 0)

/-- Sous-verrou A1a : le comptage `squarefreeCount` coïncide avec
    la somme des indicatrices squarefree.

    Ce verrou dépend seulement de la définition locale de `squarefreeCount`. -/
def SquarefreeCountEqualsIndicatorSumBridge : Prop :=
  ∀ N : ℕ,
    (squarefreeCount N : ℝ) = squarefreeIndicatorCountReal N

/-- Somme double de Möbius sur les diviseurs carrés.

    Formellement :
      `∑_{n≤N} ∑_{d≤√N, d²∣n} μ(d)`.

    C'est la version développée de l'indicatrice squarefree. -/
noncomputable def moebiusSquareDivisorDoubleSum (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N) (fun n =>
    Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
      if d^2 ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0))

/-- Sous-verrou A1b : identité indicatrice de Möbius, sommée jusqu'à `N`.

    Elle encode :
      `1_squarefree(n) = ∑_{d²∣n} μ(d)`,

    avec une somme tronquée à `d ≤ √N`, suffisante pour `n ≤ N`. -/
def SquarefreeIndicatorEqualsMoebiusDoubleSumBridge : Prop :=
  ∀ N : ℕ,
    squarefreeIndicatorCountReal N = moebiusSquareDivisorDoubleSum N

/-- Sous-verrou A1c : réindexation finie/Fubini.

    Elle encode :
      `∑_{n≤N} ∑_{d≤√N, d²∣n} μ(d)
       = ∑_{d≤√N} μ(d) * ⌊N/d²⌋`.

    C'est la partie combinatoire de A1. -/
def MoebiusDoubleSumEqualsFloorCountBridge : Prop :=
  ∀ N : ℕ,
    moebiusSquareDivisorDoubleSum N = moebiusFloorCountTerm N

/-- Les trois sous-verrous A1a+A1b+A1c ferment la formule exacte A1'. -/
theorem squarefreeCountExactMoebiusFloorCount_of_A1_bridges
    (Hcount : SquarefreeCountEqualsIndicatorSumBridge)
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hfubini : MoebiusDoubleSumEqualsFloorCountBridge) :
    SquarefreeCountExactMoebiusFloorCountBridge := by
  unfold SquarefreeCountExactMoebiusFloorCountBridge
  intro N
  calc
    (squarefreeCount N : ℝ)
        = squarefreeIndicatorCountReal N := Hcount N
    _ = moebiusSquareDivisorDoubleSum N := Hindicator N
    _ = moebiusFloorCountTerm N := Hfubini N

/-- Version finale : C-04b est consommée avec les trois sous-verrous
    élémentaires de A1.

    Tout A2 est fermé ; il reste seulement :
    - A1a : définition du comptage ;
    - A1b : identité indicatrice de Möbius ;
    - A1c : réindexation finie vers les planchers. -/
theorem squarefree_asymptotic_density_of_A1_bridges
    (Hcount : SquarefreeCountEqualsIndicatorSumBridge)
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hfubini : MoebiusDoubleSumEqualsFloorCountBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_count_exact
    (squarefreeCountExactMoebiusFloorCount_of_A1_bridges
      Hcount Hindicator Hfubini)

/-- Fermeture de A1a lorsque `squarefreeCount` est défini comme
    le cardinal des entiers squarefree dans `Icc 1 N`.

    Cette preuve transforme simplement un cardinal filtré en somme
    d'indicatrices. -/
theorem squarefreeCountEqualsIndicatorSumBridge_proved :
    SquarefreeCountEqualsIndicatorSumBridge := by
  unfold SquarefreeCountEqualsIndicatorSumBridge
  intro N
  unfold squarefreeIndicatorCountReal
  unfold squarefreeCount

  rw [Finset.card_filter]
  simp

/-- Version finale : C-04b est consommée avec A1b et A1c seulement.

    A1a, c'est-à-dire l'identification du comptage avec la somme
    d'indicatrices, est maintenant fermée localement. -/
theorem squarefree_asymptotic_density_of_indicator_and_fubini
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hfubini : MoebiusDoubleSumEqualsFloorCountBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_A1_bridges
    squarefreeCountEqualsIndicatorSumBridge_proved
    Hindicator
    Hfubini

/-- Sous-verrou A1c-1 : comptage des multiples de `d²` dans `1..N`.

    Pour `d ≥ 1`, la somme des indicatrices `d² ∣ n` sur `1 ≤ n ≤ N`
    vaut exactement `⌊N / d²⌋`.

    On le garde en bridge local pour isoler la partie combinatoire
    du comptage des multiples. -/
def CountMultiplesSquareBridge : Prop :=
  ∀ N d : ℕ,
    1 ≤ d →
      Finset.sum (Finset.Icc 1 N) (fun n =>
        if d^2 ∣ n then (1 : ℝ) else 0)
        =
      ((N / d^2 : ℕ) : ℝ)

/-- A1c est réduit au comptage des multiples de `d²`.

    On échange les deux sommes finies, puis on applique le bridge
    `CountMultiplesSquareBridge` pour chaque `d ≤ √N`. -/
theorem moebiusDoubleSumEqualsFloorCount_of_count_multiples
    (Hmult : CountMultiplesSquareBridge) :
    MoebiusDoubleSumEqualsFloorCountBridge := by
  unfold MoebiusDoubleSumEqualsFloorCountBridge
  intro N

  unfold moebiusSquareDivisorDoubleSum
  unfold moebiusFloorCountTerm

  let sN : Finset ℕ := Finset.Icc 1 N
  let sD : Finset ℕ := Finset.Icc 1 (Nat.sqrt N)
  let m : ℕ → ℝ := fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

  change
    Finset.sum sN (fun n =>
      Finset.sum sD (fun d =>
        if d^2 ∣ n then m d else 0))
      =
    Finset.sum sD (fun d =>
      m d * ((N / d^2 : ℕ) : ℝ))

  calc
    Finset.sum sN (fun n =>
      Finset.sum sD (fun d =>
        if d^2 ∣ n then m d else 0))
        =
      Finset.sum sD (fun d =>
        Finset.sum sN (fun n =>
          if d^2 ∣ n then m d else 0)) := by
            rw [Finset.sum_comm]
    _ =
      Finset.sum sD (fun d =>
        m d *
          Finset.sum sN (fun n =>
            if d^2 ∣ n then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hdiv : d^2 ∣ n
            · simp [hdiv]
            · simp [hdiv]
    _ =
      Finset.sum sD (fun d =>
        m d * ((N / d^2 : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            have hd_mem : d ∈ Finset.Icc 1 (Nat.sqrt N) := by
              simpa [sD] using hd
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd_mem).1
            rw [Hmult N d hd1]

/-- Version finale : C-04b est consommée avec A1b et le seul bridge
    de comptage des multiples de carrés.

    A1a est fermée ; A1c est réduite à `CountMultiplesSquareBridge`. -/
theorem squarefree_asymptotic_density_of_indicator_and_count_multiples
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hmult : CountMultiplesSquareBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_fubini
    Hindicator
    (moebiusDoubleSumEqualsFloorCount_of_count_multiples Hmult)

/-- Version naturelle du comptage des multiples de `d²`.

    Cette formulation est plus proche du cœur combinatoire :
    le nombre d'entiers `n ∈ [1,N]` tels que `d² ∣ n`
    vaut `N / d²`.

    Le bridge réel `CountMultiplesSquareBridge` s'en déduit ensuite
    par transformation du cardinal filtré en somme d'indicatrices. -/
def CountMultiplesSquareNatBridge : Prop :=
  ∀ N d : ℕ,
    1 ≤ d →
      ((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card =
        N / d^2

/-- Le comptage naturel des multiples implique le bridge réel
    `CountMultiplesSquareBridge`.

    Cette étape ne contient plus la combinatoire des multiples :
    elle transforme seulement un cardinal filtré en somme d'indicatrices
    réelles. -/
theorem countMultiplesSquareBridge_of_nat_bridge
    (Hnat : CountMultiplesSquareNatBridge) :
    CountMultiplesSquareBridge := by
  unfold CountMultiplesSquareBridge
  unfold CountMultiplesSquareNatBridge at Hnat

  intro N d hd

  have hcard : ((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card =
      N / d^2 :=
    Hnat N d hd

  have hindicator_real :
      Finset.sum (Finset.Icc 1 N) (fun n =>
        if d^2 ∣ n then (1 : ℝ) else 0)
        =
      (((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card : ℝ) := by
    have hnat_indicator :
        ((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card =
          Finset.sum (Finset.Icc 1 N) (fun n =>
            if d^2 ∣ n then (1 : ℕ) else 0) := by
      rw [Finset.card_filter]
    have hreal_indicator :
        (((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card : ℝ) =
          Finset.sum (Finset.Icc 1 N) (fun n =>
            if d^2 ∣ n then (1 : ℝ) else 0) := by
      exact_mod_cast hnat_indicator
    exact hreal_indicator.symm

  calc
    Finset.sum (Finset.Icc 1 N) (fun n =>
      if d^2 ∣ n then (1 : ℝ) else 0)
        =
      (((Finset.Icc 1 N).filter (fun n => d^2 ∣ n)).card : ℝ) :=
        hindicator_real
    _ = ((N / d^2 : ℕ) : ℝ) := by
        exact_mod_cast hcard

/-- Version finale : C-04b est consommée avec A1b et le seul bridge
    naturel de comptage des multiples.

    A1a est fermée ; A1c est réduite à un cardinal filtré naturel. -/
theorem squarefree_asymptotic_density_of_indicator_and_count_multiples_nat
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hnat : CountMultiplesSquareNatBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_count_multiples
    Hindicator
    (countMultiplesSquareBridge_of_nat_bridge Hnat)

/-- Lemme général de comptage des multiples.

    Pour tout `q ≥ 1`, le nombre d'entiers `n ∈ [1,N]`
    divisibles par `q` vaut `N / q`.

    Le cas des carrés `q = d²` s'en déduit immédiatement. -/
def CountMultiplesNatBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card =
        N / q

/-- Le comptage général des multiples implique le comptage des multiples
    de carrés.

    C'est la spécialisation `q = d²`, avec `1 ≤ d²` dès que `1 ≤ d`. -/
theorem countMultiplesSquareNatBridge_of_general_multiples
    (Hmult : CountMultiplesNatBridge) :
    CountMultiplesSquareNatBridge := by
  unfold CountMultiplesSquareNatBridge
  unfold CountMultiplesNatBridge at Hmult

  intro N d hd

  have hd2 : 1 ≤ d^2 := by
    have hmul : 1 * 1 ≤ d * d := Nat.mul_le_mul hd hd
    simpa [pow_two] using hmul

  simpa using Hmult N (d^2) hd2

/-- Version finale : C-04b est consommée avec A1b et le lemme général
    de comptage des multiples.

    A1c est maintenant réduit à l'énoncé standard :
      `#{n ∈ [1,N] | q ∣ n} = N/q`. -/
theorem squarefree_asymptotic_density_of_indicator_and_general_multiples
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hmult : CountMultiplesNatBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_count_multiples_nat
    Hindicator
    (countMultiplesSquareNatBridge_of_general_multiples Hmult)

end CouretUnification.Logic.H3
