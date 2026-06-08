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

end CouretUnification.Logic.H3
