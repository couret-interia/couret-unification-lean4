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

/-- Forme bijective du comptage des multiples.

    Elle encode la bijection attendue :
      `n ∈ [1,N]`, `q ∣ n`  ↦  `n/q ∈ [1, N/q]`,
    avec inverse :
      `k ∈ [1,N/q]`  ↦  `q*k`.

    Cette formulation sépare la preuve de bijection proprement dite
    de la simple évaluation du cardinal de l'intervalle `[1, N/q]`. -/
def CountMultiplesNatBijectionBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card =
        (Finset.Icc 1 (N / q)).card

/-- La forme bijective implique le comptage général des multiples.

    Il reste seulement à utiliser :
      `card (Icc 1 M) = M`. -/
theorem countMultiplesNatBridge_of_bijection_bridge
    (Hbij : CountMultiplesNatBijectionBridge) :
    CountMultiplesNatBridge := by
  unfold CountMultiplesNatBridge
  unfold CountMultiplesNatBijectionBridge at Hbij

  intro N q hq

  calc
    ((Finset.Icc 1 N).filter (fun n => q ∣ n)).card
        = (Finset.Icc 1 (N / q)).card := Hbij N q hq
    _ = N / q := by
        rw [Nat.card_Icc]
        exact Nat.succ_sub_one (N / q)

/-- Version finale : C-04b est consommée avec A1b et la bijection
    naturelle de comptage des multiples.

    Le dernier verrou combinatoire est maintenant la bijection explicite
    entre les multiples de `q` dans `[1,N]` et l'intervalle `[1,N/q]`. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_bijection
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hbij : CountMultiplesNatBijectionBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_general_multiples
    Hindicator
    (countMultiplesNatBridge_of_bijection_bridge Hbij)

/-- Donnée explicite de la bijection de comptage des multiples.

    Pour `q ≥ 1`, on encode les trois propriétés de la carte :
      `n ↦ n / q`

    depuis les multiples de `q` dans `[1,N]` vers `[1,N/q]` :
    - elle envoie bien la source dans la cible ;
    - elle est injective sur la source ;
    - elle est surjective sur la cible.

    Le prochain pas consistera à prouver ces trois propriétés avec
    l'inverse explicite `k ↦ q*k`. -/
def CountMultiplesNatBijectionDataBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      (∀ n : ℕ,
        n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
          n / q ∈ Finset.Icc 1 (N / q))
      ∧
      (∀ n₁ : ℕ,
        n₁ ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
        ∀ n₂ : ℕ,
        n₂ ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
          n₁ / q = n₂ / q →
            n₁ = n₂)
      ∧
      (∀ k : ℕ,
        k ∈ Finset.Icc 1 (N / q) →
          ∃ n : ℕ,
            n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n)
              ∧ n / q = k)

/-- La donnée explicite de bijection implique l'égalité des cardinaux.

    Cette étape ne fait plus d'arithmétique : elle applique seulement
    `Finset.card_bij` à la carte `n ↦ n/q`. -/
theorem countMultiplesNatBijectionBridge_of_data
    (Hdata : CountMultiplesNatBijectionDataBridge) :
    CountMultiplesNatBijectionBridge := by
  unfold CountMultiplesNatBijectionBridge
  unfold CountMultiplesNatBijectionDataBridge at Hdata

  intro N q hq

  rcases Hdata N q hq with ⟨hmap, hinj, hsurj⟩

  exact Finset.card_bij
    (fun n _ => n / q)
    (fun n hn => hmap n hn)
    (fun n₁ hn₁ n₂ hn₂ h => hinj n₁ hn₁ n₂ hn₂ h)
    (fun k hk => by
      rcases hsurj k hk with ⟨n, hn, hnk⟩
      exact ⟨n, hn, hnk⟩)

/-- Version finale : C-04b est consommée avec A1b et les données
    explicites de la bijection des multiples.

    Le verrou restant est maintenant purement arithmétique :
    vérifier les trois propriétés de `n ↦ n/q` avec inverse `k ↦ q*k`. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_bijection_data
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hdata : CountMultiplesNatBijectionDataBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_multiples_bijection
    Hindicator
    (countMultiplesNatBijectionBridge_of_data Hdata)

/-- Partie "bonne définition" de la bijection des multiples :
    si `n ∈ [1,N]` et `q ∣ n`, alors `n/q ∈ [1,N/q]`. -/
def CountMultiplesNatMapBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      ∀ n : ℕ,
        n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
          n / q ∈ Finset.Icc 1 (N / q)

/-- Partie injective de la bijection :
    sur les multiples de `q`, l'application `n ↦ n/q` est injective. -/
def CountMultiplesNatInjectiveBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      ∀ n₁ : ℕ,
        n₁ ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
        ∀ n₂ : ℕ,
        n₂ ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n) →
          n₁ / q = n₂ / q →
            n₁ = n₂

/-- Partie surjective de la bijection :
    tout `k ∈ [1,N/q]` provient du multiple `q*k`. -/
def CountMultiplesNatSurjectiveBridge : Prop :=
  ∀ N q : ℕ,
    1 ≤ q →
      ∀ k : ℕ,
        k ∈ Finset.Icc 1 (N / q) →
          ∃ n : ℕ,
            n ∈ (Finset.Icc 1 N).filter (fun n => q ∣ n)
              ∧ n / q = k

/-- Les trois propriétés élémentaires de `n ↦ n/q` fournissent les
    données complètes de bijection. -/
theorem countMultiplesNatBijectionDataBridge_of_parts
    (Hmap : CountMultiplesNatMapBridge)
    (Hinj : CountMultiplesNatInjectiveBridge)
    (Hsurj : CountMultiplesNatSurjectiveBridge) :
    CountMultiplesNatBijectionDataBridge := by
  unfold CountMultiplesNatBijectionDataBridge
  unfold CountMultiplesNatMapBridge at Hmap
  unfold CountMultiplesNatInjectiveBridge at Hinj
  unfold CountMultiplesNatSurjectiveBridge at Hsurj

  intro N q hq
  exact ⟨Hmap N q hq, Hinj N q hq, Hsurj N q hq⟩

/-- Version finale : C-04b est consommée avec A1b et les trois propriétés
    élémentaires de la bijection des multiples. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_bijection_parts
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hmap : CountMultiplesNatMapBridge)
    (Hinj : CountMultiplesNatInjectiveBridge)
    (Hsurj : CountMultiplesNatSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_multiples_bijection_data
    Hindicator
    (countMultiplesNatBijectionDataBridge_of_parts Hmap Hinj Hsurj)
/-- Petit verrou arithmétique pour la surjectivité :
    si `k ≤ N/q`, alors `q*k ≤ N`.

    C'est exactement le contrôle qui garantit que l'antécédent
    `n = q*k` appartient bien à `[1,N]`. -/
def NatMulLeOfLeDivBridge : Prop :=
  ∀ N q k : ℕ,
    1 ≤ q →
    k ≤ N / q →
      q * k ≤ N

/-- Petit verrou arithmétique pour l'inverse :
    pour `q ≥ 1`, `(q*k)/q = k`. -/
def NatMulDivCancelLeftBridge : Prop :=
  ∀ q k : ℕ,
    1 ≤ q →
      (q * k) / q = k

/-- La surjectivité de la bijection des multiples est réduite aux deux
    lemmes élémentaires de division naturelle :
    - `k ≤ N/q → q*k ≤ N` ;
    - `(q*k)/q = k`.

    L'antécédent de `k` est explicitement `n = q*k`. -/
theorem countMultiplesNatSurjectiveBridge_of_nat_div_bridges
    (Hmul_le : NatMulLeOfLeDivBridge)
    (Hcancel : NatMulDivCancelLeftBridge) :
    CountMultiplesNatSurjectiveBridge := by
  unfold CountMultiplesNatSurjectiveBridge
  unfold NatMulLeOfLeDivBridge at Hmul_le
  unfold NatMulDivCancelLeftBridge at Hcancel

  intro N q hq k hk

  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkN⟩

  refine ⟨q * k, ?_, ?_⟩

  · rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · have hqk : 1 * 1 ≤ q * k := Nat.mul_le_mul hq hk1
        simpa using hqk
      · exact Hmul_le N q k hq hkN
    · exact ⟨k, rfl⟩

  · exact Hcancel q k hq

/-- Version finale : C-04b est consommée avec A1b, la bonne définition,
    l'injectivité, et les deux lemmes de division naturelle qui ferment
    la surjectivité. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_map_inj_div
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hmap : CountMultiplesNatMapBridge)
    (Hinj : CountMultiplesNatInjectiveBridge)
    (Hmul_le : NatMulLeOfLeDivBridge)
    (Hcancel : NatMulDivCancelLeftBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_multiples_bijection_parts
    Hindicator
    Hmap
    Hinj
    (countMultiplesNatSurjectiveBridge_of_nat_div_bridges Hmul_le Hcancel)

/-- Fermeture du verrou `k ≤ N/q → q*k ≤ N`.

    Mathlib fournit `Nat.le_div_iff_mul_le`, qui donne naturellement
    `k*q ≤ N`; on commute ensuite le produit. -/
theorem natMulLeOfLeDivBridge_proved :
    NatMulLeOfLeDivBridge := by
  unfold NatMulLeOfLeDivBridge
  intro N q k hq hk
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hmul : k * q ≤ N :=
    (Nat.le_div_iff_mul_le hqpos).1 hk
  simpa [Nat.mul_comm] using hmul

/-- Fermeture du verrou `(q*k)/q = k`.

    Mathlib fournit déjà `Nat.mul_div_cancel_left`. -/
theorem natMulDivCancelLeftBridge_proved :
    NatMulDivCancelLeftBridge := by
  unfold NatMulDivCancelLeftBridge
  intro q k hq
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  exact Nat.mul_div_cancel_left k hqpos

/-- Fermeture de la surjectivité de la bijection des multiples. -/
theorem countMultiplesNatSurjectiveBridge_proved :
    CountMultiplesNatSurjectiveBridge :=
  countMultiplesNatSurjectiveBridge_of_nat_div_bridges
    natMulLeOfLeDivBridge_proved
    natMulDivCancelLeftBridge_proved

/-- Version finale : C-04b est consommée avec A1b, la bonne définition
    et l'injectivité de la bijection des multiples.

    La surjectivité est maintenant fermée localement par les lemmes Nat
    de division. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_map_inj
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hmap : CountMultiplesNatMapBridge)
    (Hinj : CountMultiplesNatInjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_multiples_bijection_parts
    Hindicator
    Hmap
    Hinj
    countMultiplesNatSurjectiveBridge_proved

/-- Fermeture de la bonne définition de la carte `n ↦ n/q`.

    Si `n ∈ [1,N]` et `q ∣ n`, alors :
    - `n/q ≤ N/q` par monotonie de la division ;
    - `1 ≤ n/q` car `q ≤ n`, puisque `q ∣ n`, `q ≥ 1`, et `n ≥ 1`. -/
theorem countMultiplesNatMapBridge_proved :
    CountMultiplesNatMapBridge := by
  unfold CountMultiplesNatMapBridge

  intro N q hq n hn

  rw [Finset.mem_filter] at hn
  rcases hn with ⟨hnIcc, hdiv⟩
  rcases Finset.mem_Icc.mp hnIcc with ⟨hn1, hnN⟩

  rw [Finset.mem_Icc]
  constructor

  · have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1

    have hq_le_n : q ≤ n :=
      Nat.le_of_dvd hnpos hdiv

    exact (Nat.one_le_div_iff hqpos).2 hq_le_n

  · exact Nat.div_le_div_right hnN

/-- Version finale : C-04b est consommée avec A1b et l'injectivité
    de la bijection des multiples.

    La bonne définition et la surjectivité sont maintenant fermées
    localement. -/
theorem squarefree_asymptotic_density_of_indicator_and_multiples_inj
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge)
    (Hinj : CountMultiplesNatInjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_multiples_map_inj
    Hindicator
    countMultiplesNatMapBridge_proved
    Hinj

/-- Fermeture de l'injectivité de la carte `n ↦ n/q` sur les multiples
    de `q`.

    Si `q ∣ n₁` et `q ∣ n₂`, on écrit :
      `n₁ = q*t₁`, `n₂ = q*t₂`.

    Alors :
      `n₁/q = t₁` et `n₂/q = t₂`,
    donc l'égalité des quotients donne `t₁ = t₂`, puis `n₁ = n₂`. -/
theorem countMultiplesNatInjectiveBridge_proved :
    CountMultiplesNatInjectiveBridge := by
  unfold CountMultiplesNatInjectiveBridge

  intro N q hq n₁ hn₁ n₂ hn₂ hquot

  rw [Finset.mem_filter] at hn₁
  rw [Finset.mem_filter] at hn₂

  rcases hn₁ with ⟨_hn₁Icc, hdiv₁⟩
  rcases hn₂ with ⟨_hn₂Icc, hdiv₂⟩

  rcases hdiv₁ with ⟨t₁, ht₁⟩
  rcases hdiv₂ with ⟨t₂, ht₂⟩

  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq

  have hquot₁ : n₁ / q = t₁ := by
    rw [ht₁, Nat.mul_div_cancel_left t₁ hqpos]

  have hquot₂ : n₂ / q = t₂ := by
    rw [ht₂, Nat.mul_div_cancel_left t₂ hqpos]

  have ht : t₁ = t₂ := by
    rw [hquot₁, hquot₂] at hquot
    exact hquot

  rw [ht₁, ht₂, ht]

/-- Fermeture du comptage général des multiples.

    Les trois propriétés de la bijection `n ↦ n/q` sont maintenant
    fermées localement :
    - bonne définition ;
    - injectivité ;
    - surjectivité. -/
theorem countMultiplesNatBridge_proved :
    CountMultiplesNatBridge :=
  countMultiplesNatBridge_of_bijection_bridge
    (countMultiplesNatBijectionBridge_of_data
      (countMultiplesNatBijectionDataBridge_of_parts
        countMultiplesNatMapBridge_proved
        countMultiplesNatInjectiveBridge_proved
        countMultiplesNatSurjectiveBridge_proved))

/-- Fermeture du comptage des multiples de carrés. -/
theorem countMultiplesSquareNatBridge_proved :
    CountMultiplesSquareNatBridge :=
  countMultiplesSquareNatBridge_of_general_multiples
    countMultiplesNatBridge_proved

/-- Fermeture réelle du bridge de comptage des multiples de carrés. -/
theorem countMultiplesSquareBridge_proved :
    CountMultiplesSquareBridge :=
  countMultiplesSquareBridge_of_nat_bridge
    countMultiplesSquareNatBridge_proved

/-- Fermeture de A1c : réindexation finie/Fubini vers les planchers. -/
theorem moebiusDoubleSumEqualsFloorCountBridge_proved :
    MoebiusDoubleSumEqualsFloorCountBridge :=
  moebiusDoubleSumEqualsFloorCount_of_count_multiples
    countMultiplesSquareBridge_proved

/-- Version finale : C-04b est consommée avec le seul bridge A1b
    d'identité indicatrice de Möbius.

    A1a et A1c sont maintenant fermés localement. -/
theorem squarefree_asymptotic_density_of_indicator_only
    (Hindicator : SquarefreeIndicatorEqualsMoebiusDoubleSumBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_and_fubini
    Hindicator
    moebiusDoubleSumEqualsFloorCountBridge_proved

/-!
## Sous-verrou A1b — identité indicatrice de Möbius

A1b est maintenant séparé en deux parties :
1. une identité locale, au niveau de chaque `n` ;
2. une extension de troncature de `√n` vers `√N` lorsque `n ≤ N`.
-/

/-- Somme locale de Möbius sur les diviseurs carrés de `n`.

    C'est la forme naturelle de l'identité :
      `1_squarefree(n) = ∑_{d≤√n, d²∣n} μ(d)`. -/
noncomputable def moebiusSquareDivisorLocalSum (n : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt n)) (fun d =>
    if d^2 ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

/-- Sous-verrou A1b-local :
    identité indicatrice de Möbius au niveau d'un entier `n`.

    C'est le dernier cœur arithmétique :
      `1` si `n` est squarefree, `0` sinon,
    égal à la somme de Möbius sur les diviseurs carrés de `n`. -/
def SquarefreeIndicatorLocalMoebiusBridge : Prop :=
  ∀ n : ℕ,
    (if Squarefree n then (1 : ℝ) else 0)
      =
    moebiusSquareDivisorLocalSum n

/-- Sous-verrou A1b-troncature :
    pour `1 ≤ n ≤ N`, la somme locale tronquée à `√n`
    coïncide avec la somme tronquée à `√N`.

    Les termes ajoutés entre `√n` et `√N` sont nuls, car `d² ∣ n`
    impliquerait `d² ≤ n`. -/
def SquarefreeIndicatorMoebiusTruncationBridge : Prop :=
  ∀ N n : ℕ,
    n ∈ Finset.Icc 1 N →
      moebiusSquareDivisorLocalSum n
        =
      Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
        if d^2 ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)

/-- Les deux sous-verrous A1b-local et A1b-troncature ferment A1b. -/
theorem squarefreeIndicatorEqualsMoebiusDoubleSum_of_local_and_truncation
    (Hlocal : SquarefreeIndicatorLocalMoebiusBridge)
    (Htrunc : SquarefreeIndicatorMoebiusTruncationBridge) :
    SquarefreeIndicatorEqualsMoebiusDoubleSumBridge := by
  unfold SquarefreeIndicatorEqualsMoebiusDoubleSumBridge
  unfold squarefreeIndicatorCountReal
  unfold moebiusSquareDivisorDoubleSum

  intro N

  refine Finset.sum_congr rfl ?_
  intro n hn

  calc
    (if Squarefree n then (1 : ℝ) else 0)
        = moebiusSquareDivisorLocalSum n := Hlocal n
    _ =
      Finset.sum (Finset.Icc 1 (Nat.sqrt N)) (fun d =>
        if d^2 ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) :=
          Htrunc N n hn

/-- Version finale : C-04b est consommée avec les deux derniers
    sous-verrous arithmétiques de A1b. -/
theorem squarefree_asymptotic_density_of_local_moebius_and_truncation
    (Hlocal : SquarefreeIndicatorLocalMoebiusBridge)
    (Htrunc : SquarefreeIndicatorMoebiusTruncationBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_indicator_only
    (squarefreeIndicatorEqualsMoebiusDoubleSum_of_local_and_truncation
      Hlocal
      Htrunc)

/-- Fermeture de la troncature `√n → √N`.

    Pour `n ∈ [1,N]`, l'intervalle `Icc 1 √n` est inclus dans
    `Icc 1 √N`. Les termes ajoutés sont nuls : si `d² ∣ n` et
    `n > 0`, alors `d² ≤ n`, donc `d ≤ √n`. -/
theorem squarefreeIndicatorMoebiusTruncationBridge_proved :
    SquarefreeIndicatorMoebiusTruncationBridge := by
  unfold SquarefreeIndicatorMoebiusTruncationBridge

  intro N n hn

  unfold moebiusSquareDivisorLocalSum

  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩

  let f : ℕ → ℝ := fun d =>
    if d^2 ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0

  change
    Finset.sum (Finset.Icc 1 (Nat.sqrt n)) f =
      Finset.sum (Finset.Icc 1 (Nat.sqrt N)) f

  have hsubset :
      Finset.Icc 1 (Nat.sqrt n) ⊆ Finset.Icc 1 (Nat.sqrt N) := by
    intro d hd
    rcases Finset.mem_Icc.mp hd with ⟨hd1, hd_sqrt_n⟩
    have hd2_le_n : d^2 ≤ n := Nat.le_sqrt'.1 hd_sqrt_n
    have hd2_le_N : d^2 ≤ N := le_trans hd2_le_n hnN
    exact Finset.mem_Icc.mpr ⟨hd1, Nat.le_sqrt'.2 hd2_le_N⟩

  refine Finset.sum_subset hsubset ?_

  intro d hd_big hd_not_small

  have hd_big_parts := Finset.mem_Icc.mp hd_big
  rcases hd_big_parts with ⟨hd1, _hd_sqrt_N⟩

  by_cases hdiv : d^2 ∣ n
  · exfalso

    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1

    have hd2_le_n : d^2 ≤ n :=
      Nat.le_of_dvd hnpos hdiv

    have hd_sqrt_n : d ≤ Nat.sqrt n :=
      Nat.le_sqrt'.2 hd2_le_n

    exact hd_not_small (Finset.mem_Icc.mpr ⟨hd1, hd_sqrt_n⟩)

  · simp [hdiv]

/-- Version finale : C-04b est consommée avec le seul bridge local
    d'identité indicatrice de Möbius.

    La troncature `√n → √N` est maintenant fermée localement. -/
theorem squarefree_asymptotic_density_of_local_moebius_only
    (Hlocal : SquarefreeIndicatorLocalMoebiusBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_local_moebius_and_truncation
    Hlocal
    squarefreeIndicatorMoebiusTruncationBridge_proved

/-!
## Réduction entière de l'identité locale de Möbius

On évite les difficultés de coercion `ℤ → ℝ` en isolant d'abord
l'identité locale dans `ℤ`.
-/

/-- Indicatrice entière de la propriété squarefree. -/
noncomputable def squarefreeIndicatorLocalInt (n : ℕ) : ℤ :=
  if Squarefree n then (1 : ℤ) else 0

/-- Somme locale entière de Möbius sur les diviseurs carrés de `n`. -/
noncomputable def moebiusSquareDivisorLocalSumInt (n : ℕ) : ℤ :=
  Finset.sum (Finset.Icc 1 (Nat.sqrt n)) (fun d =>
    if d^2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0)

/-- Version entière du dernier verrou local. -/
def SquarefreeIndicatorLocalMoebiusIntBridge : Prop :=
  ∀ n : ℕ,
    squarefreeIndicatorLocalInt n =
      moebiusSquareDivisorLocalSumInt n

/-- La version entière implique le bridge réel déjà utilisé par C-04b. -/
theorem squarefreeIndicatorLocalMoebiusBridge_of_int
    (Hint : SquarefreeIndicatorLocalMoebiusIntBridge) :
    SquarefreeIndicatorLocalMoebiusBridge := by
  unfold SquarefreeIndicatorLocalMoebiusBridge
  unfold SquarefreeIndicatorLocalMoebiusIntBridge at Hint

  intro n

  have hZ := Hint n

  unfold squarefreeIndicatorLocalInt at hZ
  unfold moebiusSquareDivisorLocalSumInt at hZ
  unfold moebiusSquareDivisorLocalSum

  exact_mod_cast hZ

/-- Version filtrée entière de la somme locale.

    Elle remplace la somme avec `if d² ∣ n` par une somme sur le
    sous-ensemble filtré des diviseurs carrés. -/
noncomputable def moebiusSquareDivisorLocalFilteredSumInt (n : ℕ) : ℤ :=
  Finset.sum
    ((Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d^2 ∣ n))
    (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- La somme entière avec `if` coïncide avec la somme filtrée. -/
theorem moebiusSquareDivisorLocalSumInt_eq_filtered
    (n : ℕ) :
    moebiusSquareDivisorLocalSumInt n =
      moebiusSquareDivisorLocalFilteredSumInt n := by
  unfold moebiusSquareDivisorLocalSumInt
  unfold moebiusSquareDivisorLocalFilteredSumInt
  symm
  rw [Finset.sum_filter]

/-- Dernier verrou sous forme filtrée entière. -/
def SquarefreeIndicatorLocalMoebiusFilteredIntBridge : Prop :=
  ∀ n : ℕ,
    squarefreeIndicatorLocalInt n =
      moebiusSquareDivisorLocalFilteredSumInt n

/-- La forme filtrée entière implique la forme entière avec `if`. -/
theorem squarefreeIndicatorLocalMoebiusIntBridge_of_filtered
    (Hfiltered : SquarefreeIndicatorLocalMoebiusFilteredIntBridge) :
    SquarefreeIndicatorLocalMoebiusIntBridge := by
  unfold SquarefreeIndicatorLocalMoebiusIntBridge
  unfold SquarefreeIndicatorLocalMoebiusFilteredIntBridge at Hfiltered

  intro n

  calc
    squarefreeIndicatorLocalInt n
        = moebiusSquareDivisorLocalFilteredSumInt n := Hfiltered n
    _ = moebiusSquareDivisorLocalSumInt n :=
        (moebiusSquareDivisorLocalSumInt_eq_filtered n).symm

/-- Version finale : C-04b est consommée avec le seul dernier verrou
    filtré entier de l'identité de Möbius locale. -/
theorem squarefree_asymptotic_density_of_local_moebius_filtered_int
    (Hfiltered : SquarefreeIndicatorLocalMoebiusFilteredIntBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_local_moebius_only
    (squarefreeIndicatorLocalMoebiusBridge_of_int
      (squarefreeIndicatorLocalMoebiusIntBridge_of_filtered Hfiltered))

/-!
## Dernier verrou local — séparation squarefree / non-squarefree

On scinde l'identité locale filtrée entière en deux cas :
- si `n` est squarefree, la somme vaut `1` ;
- si `n` n'est pas squarefree, la somme vaut `0`.
-/

/-- Cas squarefree du dernier verrou local :
    si `n` est squarefree, la somme locale de Möbius sur les diviseurs
    carrés vaut `1`. -/
def SquarefreeMoebiusFilteredSumOneBridge : Prop :=
  ∀ n : ℕ,
    Squarefree n →
      moebiusSquareDivisorLocalFilteredSumInt n = 1

/-- Cas non-squarefree du dernier verrou local :
    si `n` n'est pas squarefree, la somme locale de Möbius sur les
    diviseurs carrés vaut `0`. -/
def NonSquarefreeMoebiusFilteredSumZeroBridge : Prop :=
  ∀ n : ℕ,
    ¬ Squarefree n →
      moebiusSquareDivisorLocalFilteredSumInt n = 0

/-- Les deux cas `squarefree` / `non-squarefree` ferment l'identité
    locale filtrée entière. -/
theorem squarefreeIndicatorLocalMoebiusFilteredIntBridge_of_cases
    (Hsf : SquarefreeMoebiusFilteredSumOneBridge)
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    SquarefreeIndicatorLocalMoebiusFilteredIntBridge := by
  unfold SquarefreeIndicatorLocalMoebiusFilteredIntBridge
  unfold SquarefreeMoebiusFilteredSumOneBridge at Hsf
  unfold NonSquarefreeMoebiusFilteredSumZeroBridge at Hnsf

  intro n

  unfold squarefreeIndicatorLocalInt

  by_cases hsf : Squarefree n
  · rw [if_pos hsf]
    exact (Hsf n hsf).symm
  · rw [if_neg hsf]
    exact (Hnsf n hsf).symm

/-- Version finale : C-04b est consommée avec les deux derniers cas
    arithmétiques locaux de l'identité de Möbius. -/
theorem squarefree_asymptotic_density_of_moebius_local_cases
    (Hsf : SquarefreeMoebiusFilteredSumOneBridge)
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_local_moebius_filtered_int
    (squarefreeIndicatorLocalMoebiusFilteredIntBridge_of_cases Hsf Hnsf)

/-!
## Cas squarefree — réduction au support `{1}`

Pour `n` squarefree, les seuls diviseurs carrés de `n` doivent être
triviaux. On isole donc le support filtré de la somme de Möbius.
-/

/-- Support du cas squarefree :
    si `n` est squarefree, alors les `d ∈ [1,√n]` tels que `d² ∣ n`
    forment exactement le singleton `{1}`. -/
def SquarefreeSquareDivisorSupportSingletonBridge : Prop :=
  ∀ n : ℕ,
    Squarefree n →
      ((Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d^2 ∣ n))
        =
      ({1} : Finset ℕ)

/-- Valeur de Möbius en `1`, dans `ℤ`. -/
def MoebiusOneIntBridge : Prop :=
  (ArithmeticFunction.moebius 1 : ℤ) = 1

/-- Fermeture locale de `μ(1)=1`. -/
theorem moebiusOneIntBridge_proved :
    MoebiusOneIntBridge := by
  unfold MoebiusOneIntBridge
  simp

/-- Le support `{1}` ferme le cas squarefree du dernier verrou local. -/
theorem squarefreeMoebiusFilteredSumOne_of_support_singleton
    (Hsupport : SquarefreeSquareDivisorSupportSingletonBridge) :
    SquarefreeMoebiusFilteredSumOneBridge := by
  unfold SquarefreeMoebiusFilteredSumOneBridge
  unfold SquarefreeSquareDivisorSupportSingletonBridge at Hsupport

  intro n hsf

  unfold moebiusSquareDivisorLocalFilteredSumInt

  rw [Hsupport n hsf]

  simp

/-- Version finale : C-04b est consommée avec le cas non-squarefree
    et le support singleton du cas squarefree.

    Le cas squarefree est maintenant réduit à :
      `{d ∈ [1,√n] | d² ∣ n} = {1}`. -/
theorem squarefree_asymptotic_density_of_squarefree_support_and_nonsquarefree
    (Hsupport : SquarefreeSquareDivisorSupportSingletonBridge)
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_moebius_local_cases
    (squarefreeMoebiusFilteredSumOne_of_support_singleton Hsupport)
    Hnsf

/-!
## Cas squarefree — réduction au diviseur carré trivial
-/

/-- Lemme arithmétique isolé :
    dans un entier squarefree, tout diviseur carré positif est trivial. -/
def SquarefreeSquareDivisorEqOneBridge : Prop :=
  ∀ n d : ℕ,
    Squarefree n →
    1 ≤ d →
    d^2 ∣ n →
      d = 1

/-- Version du support singleton sur les entiers positifs.

    On isole la positivité de `n`, car le support `{1}` exige
    `1 ∈ Icc 1 √n`, donc `√n ≥ 1`. -/
def SquarefreePositiveSquareDivisorSupportSingletonBridge : Prop :=
  ∀ n : ℕ,
    1 ≤ n →
    Squarefree n →
      ((Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d^2 ∣ n))
        =
      ({1} : Finset ℕ)

/-- Le lemme `d² ∣ n → d = 1` ferme le support singleton positif. -/
theorem squarefreePositiveSquareDivisorSupportSingleton_of_eq_one
    (Heq_one : SquarefreeSquareDivisorEqOneBridge) :
    SquarefreePositiveSquareDivisorSupportSingletonBridge := by
  unfold SquarefreePositiveSquareDivisorSupportSingletonBridge
  unfold SquarefreeSquareDivisorEqOneBridge at Heq_one

  intro n hn1 hsf

  ext d
  constructor

  · intro hd
    rw [Finset.mem_filter] at hd
    rcases hd with ⟨hdIcc, hdiv⟩
    rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, _hd_sqrt⟩

    have hd_eq_one : d = 1 :=
      Heq_one n d hsf hd1 hdiv

    rw [Finset.mem_singleton]
    exact hd_eq_one

  · intro hd
    rw [Finset.mem_singleton] at hd
    subst d

    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · rfl
      ·
        have hsq : 1^2 ≤ n := by
          simpa using hn1
        exact Nat.le_sqrt'.2 hsq
    · simp

/-- Dans C-04b, le support squarefree n'est utilisé que pour `n ≥ 1`.

    On garde donc cette version positive comme prochain verrou consommable. -/
theorem squarefreeMoebiusFilteredSumOne_of_positive_support_singleton
    (Hsupport_pos : SquarefreePositiveSquareDivisorSupportSingletonBridge) :
    ∀ n : ℕ,
      1 ≤ n →
      Squarefree n →
        moebiusSquareDivisorLocalFilteredSumInt n = 1 := by
  unfold SquarefreePositiveSquareDivisorSupportSingletonBridge at Hsupport_pos

  intro n hn1 hsf

  unfold moebiusSquareDivisorLocalFilteredSumInt

  rw [Hsupport_pos n hn1 hsf]

  simp

/-- Positivité des entiers squarefree.

    Ce bridge isole le cas `n = 0`, afin de consommer proprement
    le support singleton positif. -/
def SquarefreePositiveBridge : Prop :=
  ∀ n : ℕ,
    Squarefree n →
      1 ≤ n

/-- Forme non-nulle équivalente utile pour fermer ensuite
    `SquarefreePositiveBridge`. -/
def SquarefreeNeZeroBridge : Prop :=
  ∀ n : ℕ,
    Squarefree n →
      n ≠ 0

/-- La non-nullité des entiers squarefree implique leur positivité. -/
theorem squarefreePositiveBridge_of_neZero
    (Hnz : SquarefreeNeZeroBridge) :
    SquarefreePositiveBridge := by
  unfold SquarefreePositiveBridge
  unfold SquarefreeNeZeroBridge at Hnz

  intro n hsf
  exact Nat.one_le_iff_ne_zero.mpr (Hnz n hsf)

/-- Le support singleton positif ferme le cas squarefree global,
    dès que l'on sait qu'un entier squarefree est non nul. -/
theorem squarefreeMoebiusFilteredSumOne_of_positive_support_and_neZero
    (Hnz : SquarefreeNeZeroBridge)
    (Hsupport_pos : SquarefreePositiveSquareDivisorSupportSingletonBridge) :
    SquarefreeMoebiusFilteredSumOneBridge := by
  unfold SquarefreeMoebiusFilteredSumOneBridge

  intro n hsf

  exact
    squarefreeMoebiusFilteredSumOne_of_positive_support_singleton
      Hsupport_pos
      n
      ((squarefreePositiveBridge_of_neZero Hnz) n hsf)
      hsf

/-- Le lemme de diviseur carré trivial, avec la non-nullité squarefree,
    ferme entièrement le cas squarefree du verrou local. -/
theorem squarefreeMoebiusFilteredSumOne_of_eq_one_and_neZero
    (Hnz : SquarefreeNeZeroBridge)
    (Heq_one : SquarefreeSquareDivisorEqOneBridge) :
    SquarefreeMoebiusFilteredSumOneBridge :=
  squarefreeMoebiusFilteredSumOne_of_positive_support_and_neZero
    Hnz
    (squarefreePositiveSquareDivisorSupportSingleton_of_eq_one Heq_one)

/-- Version finale : C-04b est consommée avec :
    - la non-nullité des entiers squarefree ;
    - le lemme `d² ∣ n → d = 1` dans le cas squarefree ;
    - le cas non-squarefree. -/
theorem squarefree_asymptotic_density_of_neZero_eqOne_and_nonsquarefree
    (Hnz : SquarefreeNeZeroBridge)
    (Heq_one : SquarefreeSquareDivisorEqOneBridge)
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_moebius_local_cases
    (squarefreeMoebiusFilteredSumOne_of_eq_one_and_neZero Hnz Heq_one)
    Hnsf

/-- Fermeture de la non-nullité des entiers squarefree.

    Mathlib fournit `not_squarefree_zero`, utilisé ici par contradiction. -/
theorem squarefreeNeZeroBridge_proved :
    SquarefreeNeZeroBridge := by
  unfold SquarefreeNeZeroBridge

  intro n hsf hn0

  subst n

  exact not_squarefree_zero hsf

/-- Version finale : C-04b est consommée avec :
    - le lemme `d² ∣ n → d = 1` dans le cas squarefree ;
    - le cas non-squarefree.

    La non-nullité des entiers squarefree est maintenant fermée. -/
theorem squarefree_asymptotic_density_of_eqOne_and_nonsquarefree
    (Heq_one : SquarefreeSquareDivisorEqOneBridge)
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_neZero_eqOne_and_nonsquarefree
    squarefreeNeZeroBridge_proved
    Heq_one
    Hnsf

/-- Fermeture du lemme :
    dans un entier squarefree, tout diviseur carré positif est trivial.

    Pour `ℕ`, une unité est nécessairement `1`. -/
theorem squarefreeSquareDivisorEqOneBridge_proved :
    SquarefreeSquareDivisorEqOneBridge := by
  unfold SquarefreeSquareDivisorEqOneBridge

  intro n d hsf hd1 hdiv

  have hdiv' : d * d ∣ n := by
    simpa [pow_two] using hdiv

  have hd_unit : IsUnit d :=
    hsf d hdiv'

  exact Nat.isUnit_iff.mp hd_unit

/-- Version finale : C-04b est consommée avec le seul cas
    non-squarefree.

    Le cas squarefree est maintenant fermé localement. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_only
    (Hnsf : NonSquarefreeMoebiusFilteredSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_eqOne_and_nonsquarefree
    squarefreeSquareDivisorEqOneBridge_proved
    Hnsf

/-!
## Cas non-squarefree — réduction à une somme de Möbius nulle

Le dernier verrou est l'annulation :
  `∑_{d²∣n} μ(d) = 0`
lorsque `n` n'est pas squarefree.

On isole maintenant la forme standard attendue :
une somme de Möbius sur les diviseurs d'un entier non trivial.
-/

/-- Bridge standard de Möbius :
    si `m ≠ 1`, alors la somme de `μ(d)` sur les diviseurs positifs
    de `m` vaut `0`.

    C'est la forme classique :
      `∑_{d∣m} μ(d) = 0` pour `m ≠ 1`. -/
def MoebiusDivisorSumZeroBridge : Prop :=
  ∀ m : ℕ,
    m ≠ 1 →
      Finset.sum
        ((Finset.Icc 1 m).filter (fun d => d ∣ m))
        (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      0

/-- Bridge de paramétrisation du support des diviseurs carrés.

    Pour un `n` non-squarefree, on isole un entier `m ≠ 1`
    tel que la somme sur les `d` vérifiant `d² ∣ n` coïncide avec
    la somme classique de Möbius sur les diviseurs de `m`.

    Intuitivement, `m` est le produit des facteurs premiers dont
    l'exposant dans `n` est au moins `2`. -/
def NonSquarefreeSquareDivisorSupportAsDivisorsBridge : Prop :=
  ∀ n : ℕ,
    ¬ Squarefree n →
      ∃ m : ℕ,
        m ≠ 1 ∧
          moebiusSquareDivisorLocalFilteredSumInt n =
            Finset.sum
              ((Finset.Icc 1 m).filter (fun d => d ∣ m))
              (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- La paramétrisation du support des diviseurs carrés, combinée à
    l'identité standard `∑_{d∣m} μ(d)=0`, ferme le cas non-squarefree. -/
theorem nonSquarefreeMoebiusFilteredSumZero_of_divisor_sum
    (Hsupport : NonSquarefreeSquareDivisorSupportAsDivisorsBridge)
    (Hsum_zero : MoebiusDivisorSumZeroBridge) :
    NonSquarefreeMoebiusFilteredSumZeroBridge := by
  unfold NonSquarefreeMoebiusFilteredSumZeroBridge
  unfold NonSquarefreeSquareDivisorSupportAsDivisorsBridge at Hsupport
  unfold MoebiusDivisorSumZeroBridge at Hsum_zero

  intro n hnsf

  rcases Hsupport n hnsf with ⟨m, hm_ne_one, hsum_eq⟩

  calc
    moebiusSquareDivisorLocalFilteredSumInt n
        =
      Finset.sum
        ((Finset.Icc 1 m).filter (fun d => d ∣ m))
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := hsum_eq
    _ = 0 := Hsum_zero m hm_ne_one

/-- Version finale : C-04b est consommée avec les deux derniers bridges
    standardisés du cas non-squarefree.

    Le cas squarefree est fermé ; il reste :
    - la somme classique de Möbius sur les diviseurs ;
    - l'identification du support `d²∣n` avec les diviseurs d'un
      noyau carré non trivial. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_divisor_sum
    (Hsupport : NonSquarefreeSquareDivisorSupportAsDivisorsBridge)
    (Hsum_zero : MoebiusDivisorSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_only
    (nonSquarefreeMoebiusFilteredSumZero_of_divisor_sum
      Hsupport
      Hsum_zero)

/-!
## Somme classique de Möbius — réduction à `m.divisors`

Le bridge `MoebiusDivisorSumZeroBridge` utilise un filtre `Icc 1 m`.
Mathlib travaille plus naturellement avec `m.divisors`.
On réduit donc la forme filtrée à la forme `m.divisors`.
-/

/-- Forme Mathlib naturelle de l'annulation de la somme de Möbius :
    pour `m ≠ 0` et `m ≠ 1`, la somme sur `m.divisors` vaut `0`. -/
def MoebiusDivisorsSumZeroBridge : Prop :=
  ∀ m : ℕ,
    m ≠ 0 →
    m ≠ 1 →
      Finset.sum m.divisors
        (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      0

/-- Identification entre le filtre `1 ≤ d ≤ m, d ∣ m`
    et `m.divisors`.

    On l'isole car `m.divisors` demande naturellement `m ≠ 0`
    dans ses lemmes de correction. -/
def DivisorsAsIccFilterBridge : Prop :=
  ∀ m : ℕ,
    m ≠ 0 →
      ((Finset.Icc 1 m).filter (fun d => d ∣ m))
        =
      m.divisors

/-- Version renforcée du support non-squarefree :
    le noyau carré `m` produit est non nul et différent de `1`. -/
def NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge : Prop :=
  ∀ n : ℕ,
    ¬ Squarefree n →
      ∃ m : ℕ,
        m ≠ 0 ∧
        m ≠ 1 ∧
          moebiusSquareDivisorLocalFilteredSumInt n =
            Finset.sum
              ((Finset.Icc 1 m).filter (fun d => d ∣ m))
              (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- La version renforcée implique l'ancien bridge de support. -/
theorem nonSquarefreeSquareDivisorSupportAsDivisors_of_nonzero
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge) :
    NonSquarefreeSquareDivisorSupportAsDivisorsBridge := by
  unfold NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge at Hsupport
  unfold NonSquarefreeSquareDivisorSupportAsDivisorsBridge

  intro n hnsf

  rcases Hsupport n hnsf with ⟨m, hm_ne_zero, hm_ne_one, hsum⟩

  exact ⟨m, hm_ne_one, hsum⟩

/-- La paramétrisation renforcée, combinée à la forme `m.divisors`,
    ferme directement le cas non-squarefree. -/
theorem nonSquarefreeMoebiusFilteredSumZero_of_nonzero_divisors_sum
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge)
    (Hdivisors_eq : DivisorsAsIccFilterBridge)
    (Hsum : MoebiusDivisorsSumZeroBridge) :
    NonSquarefreeMoebiusFilteredSumZeroBridge := by
  unfold NonSquarefreeMoebiusFilteredSumZeroBridge
  unfold NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge at Hsupport
  unfold DivisorsAsIccFilterBridge at Hdivisors_eq
  unfold MoebiusDivisorsSumZeroBridge at Hsum

  intro n hnsf

  rcases Hsupport n hnsf with ⟨m, hm_ne_zero, hm_ne_one, hsum_eq⟩

  calc
    moebiusSquareDivisorLocalFilteredSumInt n
        =
      Finset.sum
        ((Finset.Icc 1 m).filter (fun d => d ∣ m))
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := hsum_eq
    _ =
      Finset.sum m.divisors
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := by
          rw [Hdivisors_eq m hm_ne_zero]
    _ = 0 := Hsum m hm_ne_zero hm_ne_one

/-- Version finale propre : C-04b est consommée avec les trois bridges
    naturels du cas non-squarefree. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_nonzero_divisors_sum
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge)
    (Hdivisors_eq : DivisorsAsIccFilterBridge)
    (Hsum : MoebiusDivisorsSumZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_only
    (nonSquarefreeMoebiusFilteredSumZero_of_nonzero_divisors_sum
      Hsupport
      Hdivisors_eq
      Hsum)

/-!
## Somme de Möbius sur les diviseurs — réduction à la convolution `μ * ζ = 1`

Mathlib fournit :
  `ArithmeticFunction.moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1`

On réduit donc `MoebiusDivisorsSumZeroBridge` à deux faits :
1. la somme `∑ d∣m μ(d)` est l'application de `(μ * ζ)` à `m` ;
2. la fonction arithmétique `1` vaut `0` hors de `m = 1`.
-/

/-- Bridge convolutionnel :
    la somme de Möbius sur les diviseurs de `m` est l'application
    de `(μ * ζ)` à `m`.

    C'est la forme exacte fournie par la convolution avec `ζ`. -/
def MoebiusDivisorsSumAsConvolutionBridge : Prop :=
  ∀ m : ℕ,
    m ≠ 0 →
      Finset.sum m.divisors
        (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) m)

/-- Bridge de la fonction arithmétique unité :
    hors de `1`, la fonction arithmétique `1` vaut `0`. -/
def ArithmeticFunctionOneApplyZeroBridge : Prop :=
  ∀ m : ℕ,
    m ≠ 1 →
      ((1 : ArithmeticFunction ℤ) m) = 0

/-- Les deux bridges convolutionnels ferment la somme classique
    de Möbius sur les diviseurs. -/
theorem moebiusDivisorsSumZeroBridge_of_convolution
    (Hconv : MoebiusDivisorsSumAsConvolutionBridge)
    (Hone_zero : ArithmeticFunctionOneApplyZeroBridge) :
    MoebiusDivisorsSumZeroBridge := by
  unfold MoebiusDivisorsSumZeroBridge
  unfold MoebiusDivisorsSumAsConvolutionBridge at Hconv
  unfold ArithmeticFunctionOneApplyZeroBridge at Hone_zero

  intro m hm_ne_zero hm_ne_one

  calc
    Finset.sum m.divisors
      (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) m) :=
        Hconv m hm_ne_zero
    _ = ((1 : ArithmeticFunction ℤ) m) := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = 0 := Hone_zero m hm_ne_one

/-- Version finale : C-04b est consommée avec :
    - le support non-squarefree renforcé ;
    - l'identification `Icc/filter = divisors` ;
    - la lecture convolutionnelle de la somme de Möbius ;
    - l'annulation de la fonction arithmétique `1` hors de `1`. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_convolution
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge)
    (Hdivisors_eq : DivisorsAsIccFilterBridge)
    (Hconv : MoebiusDivisorsSumAsConvolutionBridge)
    (Hone_zero : ArithmeticFunctionOneApplyZeroBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_nonzero_divisors_sum
    Hsupport
    Hdivisors_eq
    (moebiusDivisorsSumZeroBridge_of_convolution Hconv Hone_zero)

/-- Fermeture de l'annulation de la fonction arithmétique unité hors de `1`.

    Mathlib fournit directement `ArithmeticFunction.one_apply_ne`. -/
theorem arithmeticFunctionOneApplyZeroBridge_proved :
    ArithmeticFunctionOneApplyZeroBridge := by
  unfold ArithmeticFunctionOneApplyZeroBridge

  intro m hm_ne_one

  exact ArithmeticFunction.one_apply_ne hm_ne_one

/-- Fermeture de la lecture convolutionnelle de la somme de Möbius.

    Mathlib fournit directement :
      `ArithmeticFunction.coe_mul_zeta_apply`

    sous la forme :
      `(f * ζ) m = ∑ d ∈ m.divisors, f d`. -/
theorem moebiusDivisorsSumAsConvolutionBridge_proved :
    MoebiusDivisorsSumAsConvolutionBridge := by
  unfold MoebiusDivisorsSumAsConvolutionBridge

  intro m hm_ne_zero

  exact (ArithmeticFunction.coe_mul_zeta_apply
    (f := ArithmeticFunction.moebius)
    (x := m)).symm

/-- Fermeture de la somme classique de Möbius sur les diviseurs :
    pour `m ≠ 0`, `m ≠ 1`, on a `∑_{d∣m} μ(d)=0`.

    Elle combine :
    - la lecture convolutionnelle ;
    - l'identité `μ * ζ = 1` ;
    - l'annulation de `1` hors de `1`. -/
theorem moebiusDivisorsSumZeroBridge_proved :
    MoebiusDivisorsSumZeroBridge :=
  moebiusDivisorsSumZeroBridge_of_convolution
    moebiusDivisorsSumAsConvolutionBridge_proved
    arithmeticFunctionOneApplyZeroBridge_proved

/-- Version finale : C-04b est consommée avec :
    - le support non-squarefree renforcé ;
    - l'identification `Icc/filter = divisors`.

    La somme classique de Möbius est maintenant fermée par Mathlib. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_support_and_divisors
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge)
    (Hdivisors_eq : DivisorsAsIccFilterBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_nonzero_divisors_sum
    Hsupport
    Hdivisors_eq
    moebiusDivisorsSumZeroBridge_proved

/-- Fermeture de l'identification `Icc/filter = divisors`.

    Pour `m ≠ 0`, `m.divisors` est exactement l'ensemble des diviseurs
    positifs de `m`; le filtre `Icc 1 m` encode la même chose. -/
theorem divisorsAsIccFilterBridge_proved :
    DivisorsAsIccFilterBridge := by
  unfold DivisorsAsIccFilterBridge

  intro m hm_ne_zero

  ext d
  constructor

  · intro hd
    rw [Finset.mem_filter] at hd
    rcases hd with ⟨hdIcc, hdiv⟩
    exact Nat.mem_divisors.mpr ⟨hdiv, hm_ne_zero⟩

  · intro hd
    have hdiv : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne_zero) hdiv

    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_of_lt hdpos, hdle⟩
    · exact hdiv

/-- Version finale : C-04b est consommée avec le seul support
    non-squarefree renforcé.

    L'identification `Icc/filter = divisors` et la somme de Möbius
    sont maintenant fermées par Mathlib. -/
theorem squarefree_asymptotic_density_of_nonsquarefree_support_only
    (Hsupport : NonSquarefreeSquareDivisorSupportAsNonzeroDivisorsBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_nonzero_divisors_sum
    Hsupport
    divisorsAsIccFilterBridge_proved
    moebiusDivisorsSumZeroBridge_proved

/-!
## Cas non-squarefree — réduction à un facteur premier carré

Il reste à fermer le cœur local :
  `¬ Squarefree n → ∑_{d²∣n} μ(d)=0`.

La voie arithmétique naturelle est :
1. extraire un premier `p` tel que `p² ∣ n` ;
2. annuler la somme par appariement des termes contenant / ne contenant pas `p`.
-/

/-- Extraction arithmétique :
    tout entier non-squarefree possède un facteur premier carré. -/
def PrimeSquareDivisorOfNonSquarefreeBridge : Prop :=
  ∀ n : ℕ,
    ¬ Squarefree n →
      ∃ p : ℕ,
        p.Prime ∧
          p^2 ∣ n

/-- Annulation locale de Möbius en présence d'un facteur premier carré.

    Si `p² ∣ n`, alors la somme
      `∑_{d²∣n} μ(d)`
    s'annule par appariement des diviseurs selon la présence de `p`. -/
def MoebiusSquareDivisorCancellationAtPrimeBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      moebiusSquareDivisorLocalFilteredSumInt n = 0

/-- L'extraction d'un facteur premier carré et l'annulation locale
    ferment le cas non-squarefree. -/
theorem nonSquarefreeMoebiusFilteredSumZero_of_prime_square
    (Hprime_square : PrimeSquareDivisorOfNonSquarefreeBridge)
    (Hcancel : MoebiusSquareDivisorCancellationAtPrimeBridge) :
    NonSquarefreeMoebiusFilteredSumZeroBridge := by
  unfold NonSquarefreeMoebiusFilteredSumZeroBridge
  unfold PrimeSquareDivisorOfNonSquarefreeBridge at Hprime_square
  unfold MoebiusSquareDivisorCancellationAtPrimeBridge at Hcancel

  intro n hnsf

  rcases Hprime_square n hnsf with ⟨p, hp_prime, hp_square_dvd⟩

  exact Hcancel n p hp_prime hp_square_dvd

/-- Version finale alternative : C-04b est consommée avec deux bridges
    purement locaux :
    - extraction d'un facteur premier carré ;
    - annulation de la somme de Möbius en présence de ce facteur. -/
theorem squarefree_asymptotic_density_of_prime_square_cancellation
    (Hprime_square : PrimeSquareDivisorOfNonSquarefreeBridge)
    (Hcancel : MoebiusSquareDivisorCancellationAtPrimeBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_nonsquarefree_only
    (nonSquarefreeMoebiusFilteredSumZero_of_prime_square
      Hprime_square
      Hcancel)

/-- Fermeture de l'extraction d'un facteur premier carré.

    On utilise la caractérisation Mathlib :
      `Nat.squarefree_iff_prime_squarefree`

    qui dit qu'un entier est squarefree exactement lorsque
    aucun carré de premier ne le divise. -/
theorem primeSquareDivisorOfNonSquarefreeBridge_proved :
    PrimeSquareDivisorOfNonSquarefreeBridge := by
  unfold PrimeSquareDivisorOfNonSquarefreeBridge

  intro n hnsf

  by_contra hno_prime_square

  apply hnsf

  exact (Nat.squarefree_iff_prime_squarefree).2 (by
    intro p hp_prime hp_square_dvd

    have hp_square_dvd_pow : p^2 ∣ n := by
      simpa [pow_two] using hp_square_dvd

    exact hno_prime_square ⟨p, hp_prime, hp_square_dvd_pow⟩)

/-- Version finale : C-04b est consommée avec le seul bridge
    d'annulation locale au-dessus d'un facteur premier carré.

    L'extraction du facteur premier carré est maintenant fermée. -/
theorem squarefree_asymptotic_density_of_prime_square_cancellation_only
    (Hcancel : MoebiusSquareDivisorCancellationAtPrimeBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_cancellation
    primeSquareDivisorOfNonSquarefreeBridge_proved
    Hcancel

/-!
## Annulation locale — découpage du support selon un premier

On prépare l'annulation finale en séparant les diviseurs carrés `d`
selon deux cas :
- `p ∤ d` ;
- `p ∣ d`.

L'idée mathématique est ensuite de montrer que la partie `p ∣ d`
est l'image de la partie `p ∤ d` par `d ↦ p*d`, avec
`μ(p*d) = - μ(d)`.
-/

/-- Support local des diviseurs carrés de `n`. -/
noncomputable def squareDivisorLocalSupport (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d^2 ∣ n)

/-- Partie du support local où `p` ne divise pas `d`. -/
noncomputable def squareDivisorLocalSupportWithoutPrime (n p : ℕ) : Finset ℕ :=
  (squareDivisorLocalSupport n).filter (fun d => ¬ p ∣ d)

/-- Partie du support local où `p` divise `d`. -/
noncomputable def squareDivisorLocalSupportWithPrime (n p : ℕ) : Finset ℕ :=
  (squareDivisorLocalSupport n).filter (fun d => p ∣ d)

/-- Le support local redonne exactement la somme filtrée déjà utilisée. -/
theorem moebiusSquareDivisorLocalFilteredSumInt_eq_support
    (n : ℕ) :
    moebiusSquareDivisorLocalFilteredSumInt n =
      Finset.sum (squareDivisorLocalSupport n)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := by
  unfold moebiusSquareDivisorLocalFilteredSumInt
  unfold squareDivisorLocalSupport
  rfl

/-- Bridge de découpage du support selon `p ∣ d` ou non. -/
def MoebiusSquareDivisorPrimeSplitBridge : Prop :=
  ∀ n p : ℕ,
    moebiusSquareDivisorLocalFilteredSumInt n =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      +
      Finset.sum (squareDivisorLocalSupportWithPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Bridge d'annulation par appariement :
    la partie `p ∣ d` est l'opposée de la partie `p ∤ d`. -/
def MoebiusSquareDivisorPrimePairCancellationBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      Finset.sum (squareDivisorLocalSupportWithPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      =
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Le découpage du support et l'annulation par appariement ferment
    l'annulation locale au-dessus d'un facteur premier carré. -/
theorem moebiusSquareDivisorCancellationAtPrime_of_split_and_pair
    (Hsplit : MoebiusSquareDivisorPrimeSplitBridge)
    (Hpair : MoebiusSquareDivisorPrimePairCancellationBridge) :
    MoebiusSquareDivisorCancellationAtPrimeBridge := by
  unfold MoebiusSquareDivisorCancellationAtPrimeBridge
  unfold MoebiusSquareDivisorPrimeSplitBridge at Hsplit
  unfold MoebiusSquareDivisorPrimePairCancellationBridge at Hpair

  intro n p hp_prime hp_square_dvd

  calc
    moebiusSquareDivisorLocalFilteredSumInt n
        =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      +
      Finset.sum (squareDivisorLocalSupportWithPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) :=
        Hsplit n p
    _ =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      +
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := by
        rw [Hpair n p hp_prime hp_square_dvd]
    _ = 0 := by
        simp

/-- Version finale : C-04b est consommée avec :
    - le découpage du support ;
    - l'annulation par appariement. -/
theorem squarefree_asymptotic_density_of_prime_square_pair_cancellation
    (Hsplit : MoebiusSquareDivisorPrimeSplitBridge)
    (Hpair : MoebiusSquareDivisorPrimePairCancellationBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_cancellation_only
    (moebiusSquareDivisorCancellationAtPrime_of_split_and_pair
      Hsplit
      Hpair)

/-- Fermeture du découpage du support selon `p ∣ d` ou non.

    C'est l'identité standard :
      somme totale = somme sur `¬ p ∣ d` + somme sur `p ∣ d`. -/
theorem moebiusSquareDivisorPrimeSplitBridge_proved :
    MoebiusSquareDivisorPrimeSplitBridge := by
  unfold MoebiusSquareDivisorPrimeSplitBridge

  intro n p

  rw [moebiusSquareDivisorLocalFilteredSumInt_eq_support n]

  unfold squareDivisorLocalSupportWithoutPrime
  unfold squareDivisorLocalSupportWithPrime

  symm
  rw [add_comm]

  exact Finset.sum_filter_add_sum_filter_not
    (s := squareDivisorLocalSupport n)
    (p := fun d => p ∣ d)
    (f := fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Version finale : C-04b est consommée avec le seul bridge
    d'appariement des deux parties du support.

    Le découpage du support est maintenant fermé. -/
theorem squarefree_asymptotic_density_of_prime_square_pair_only
    (Hpair : MoebiusSquareDivisorPrimePairCancellationBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_pair_cancellation
    moebiusSquareDivisorPrimeSplitBridge_proved
    Hpair

/-!
## Annulation locale — séparation des termes `p² ∣ d`

La bijection naïve `d ↦ p*d` ne couvre proprement que les termes où
`p` apparaît exactement une fois.

Les termes où `p² ∣ d` sont traités séparément : leur contribution
Möbius est nulle.
-/

/-- Partie du support local où `p` divise `d`, mais `p²` ne divise pas `d`.

    C'est la partie où `p` apparaît exactement une fois dans `d`. -/
noncomputable def squareDivisorLocalSupportWithPrimeExactlyOnce
    (n p : ℕ) : Finset ℕ :=
  (squareDivisorLocalSupportWithPrime n p).filter (fun d => ¬ p^2 ∣ d)

/-- Partie du support local où `p²` divise déjà `d`.

    Ces termes auront une contribution de Möbius nulle. -/
noncomputable def squareDivisorLocalSupportWithPrimeSquare
    (n p : ℕ) : Finset ℕ :=
  (squareDivisorLocalSupportWithPrime n p).filter (fun d => p^2 ∣ d)

/-- Découpage de la partie `p ∣ d` selon `p² ∣ d` ou non. -/
def MoebiusSquareDivisorWithPrimeSplitBridge : Prop :=
  ∀ n p : ℕ,
    Finset.sum (squareDivisorLocalSupportWithPrime n p)
      (fun d => (ArithmeticFunction.moebius d : ℤ))
    =
    Finset.sum (squareDivisorLocalSupportWithPrimeExactlyOnce n p)
      (fun d => (ArithmeticFunction.moebius d : ℤ))
    +
    Finset.sum (squareDivisorLocalSupportWithPrimeSquare n p)
      (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Fermeture du découpage de la partie `p ∣ d`. -/
theorem moebiusSquareDivisorWithPrimeSplitBridge_proved :
    MoebiusSquareDivisorWithPrimeSplitBridge := by
  unfold MoebiusSquareDivisorWithPrimeSplitBridge

  intro n p

  unfold squareDivisorLocalSupportWithPrimeExactlyOnce
  unfold squareDivisorLocalSupportWithPrimeSquare

  symm
  rw [add_comm]

  exact Finset.sum_filter_add_sum_filter_not
    (s := squareDivisorLocalSupportWithPrime n p)
    (p := fun d => p^2 ∣ d)
    (f := fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Bridge : les termes où `p² ∣ d` ont contribution de Möbius nulle. -/
def MoebiusSquareDivisorPrimeSquareTermsZeroBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      Finset.sum (squareDivisorLocalSupportWithPrimeSquare n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      =
      0

/-- Bridge : appariement de la partie `p` exactement une fois
    avec la partie `p ∤ d`.

    C'est ici que vivra le vrai changement de variable `d ↦ p*d`
    et l'identité `μ(p*d) = - μ(d)`. -/
def MoebiusSquareDivisorPrimeExactPairCancellationBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      Finset.sum (squareDivisorLocalSupportWithPrimeExactlyOnce n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      =
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))

/-- Le découpage `p² ∣ d` / `¬ p² ∣ d`, le zéro des termes carrés,
    et l'appariement exact ferment le bridge d'annulation par paires. -/
theorem moebiusSquareDivisorPrimePairCancellation_of_exact_pair
    (Hsplit_with : MoebiusSquareDivisorWithPrimeSplitBridge)
    (Hzero_square : MoebiusSquareDivisorPrimeSquareTermsZeroBridge)
    (Hpair_exact : MoebiusSquareDivisorPrimeExactPairCancellationBridge) :
    MoebiusSquareDivisorPrimePairCancellationBridge := by
  unfold MoebiusSquareDivisorPrimePairCancellationBridge
  unfold MoebiusSquareDivisorWithPrimeSplitBridge at Hsplit_with
  unfold MoebiusSquareDivisorPrimeSquareTermsZeroBridge at Hzero_square
  unfold MoebiusSquareDivisorPrimeExactPairCancellationBridge at Hpair_exact

  intro n p hp_prime hp_square_dvd

  calc
    Finset.sum (squareDivisorLocalSupportWithPrime n p)
      (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      Finset.sum (squareDivisorLocalSupportWithPrimeExactlyOnce n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      +
      Finset.sum (squareDivisorLocalSupportWithPrimeSquare n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) :=
        Hsplit_with n p
    _ =
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      +
      0 := by
        rw [Hpair_exact n p hp_prime hp_square_dvd]
        rw [Hzero_square n p hp_prime hp_square_dvd]
    _ =
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := by
        simp

/-- Version finale : C-04b est consommée avec deux bridges restants :
    - zéro des termes où `p² ∣ d` ;
    - appariement exact de la partie où `p` apparaît une seule fois. -/
theorem squarefree_asymptotic_density_of_prime_square_exact_pair
    (Hzero_square : MoebiusSquareDivisorPrimeSquareTermsZeroBridge)
    (Hpair_exact : MoebiusSquareDivisorPrimeExactPairCancellationBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_pair_only
    (moebiusSquareDivisorPrimePairCancellation_of_exact_pair
      moebiusSquareDivisorWithPrimeSplitBridge_proved
      Hzero_square
      Hpair_exact)

/-- Fermeture du zéro des termes où `p² ∣ d`.

    Si `p² ∣ d` avec `p` premier, alors `d` n'est pas squarefree.
    Mathlib donne ensuite :
      `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`. -/
theorem moebiusSquareDivisorPrimeSquareTermsZeroBridge_proved :
    MoebiusSquareDivisorPrimeSquareTermsZeroBridge := by
  unfold MoebiusSquareDivisorPrimeSquareTermsZeroBridge

  intro n p hp_prime hp_square_dvd_n

  unfold squareDivisorLocalSupportWithPrimeSquare

  refine Finset.sum_eq_zero ?_

  intro d hd

  rw [Finset.mem_filter] at hd
  rcases hd with ⟨_hd_support, hp_square_dvd_d⟩

  have hp_mul_dvd_d : p * p ∣ d := by
    simpa [pow_two] using hp_square_dvd_d

  have hd_not_squarefree : ¬ Squarefree d := by
    intro hd_squarefree
    exact
      (Nat.squarefree_iff_prime_squarefree).1
        hd_squarefree
        p
        hp_prime
        hp_mul_dvd_d

  simpa using
    (ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      hd_not_squarefree)

/-- Version finale : C-04b est consommée avec le seul bridge
    d'appariement exact.

    Les termes où `p² ∣ d` sont maintenant fermés par non-squarefreeness
    et annulation de Möbius. -/
theorem squarefree_asymptotic_density_of_prime_square_exact_pair_only
    (Hpair_exact : MoebiusSquareDivisorPrimeExactPairCancellationBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_exact_pair
    moebiusSquareDivisorPrimeSquareTermsZeroBridge_proved
    Hpair_exact

/-!
## Annulation locale — réduction au changement de variable `d ↦ p*d`

Le dernier bridge d'appariement exact est séparé en deux pièces :
1. une égalité de sommes entre la partie `p` exactement une fois
   et l'image de la partie `p ∤ d` par `d ↦ p*d` ;
2. l'identité locale de Möbius `μ(p*d) = - μ(d)`.
-/

/-- Bridge de changement de variable :
    la somme sur les termes où `p` apparaît exactement une fois
    est la somme sur les termes sans `p`, après application de `d ↦ p*d`. -/
def MoebiusPrimeExactOnceSumAsImageBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      Finset.sum (squareDivisorLocalSupportWithPrimeExactlyOnce n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ))
      =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius (p * d) : ℤ))

/-- Bridge du signe de Möbius sous multiplication par un premier absent.

    Si `p ∤ d`, alors `p` ajoute exactement un facteur premier :
      `μ(p*d) = - μ(d)`. -/
def MoebiusMulPrimeNotDvdBridge : Prop :=
  ∀ p d : ℕ,
    p.Prime →
    ¬ p ∣ d →
      (ArithmeticFunction.moebius (p * d) : ℤ)
        =
      - (ArithmeticFunction.moebius d : ℤ)

/-- Le changement de variable et le signe de Möbius ferment
    l'appariement exact. -/
theorem moebiusSquareDivisorPrimeExactPairCancellation_of_image_and_sign
    (Himage : MoebiusPrimeExactOnceSumAsImageBridge)
    (Hsign : MoebiusMulPrimeNotDvdBridge) :
    MoebiusSquareDivisorPrimeExactPairCancellationBridge := by
  unfold MoebiusSquareDivisorPrimeExactPairCancellationBridge
  unfold MoebiusPrimeExactOnceSumAsImageBridge at Himage
  unfold MoebiusMulPrimeNotDvdBridge at Hsign

  intro n p hp_prime hp_square_dvd

  calc
    Finset.sum (squareDivisorLocalSupportWithPrimeExactlyOnce n p)
      (fun d => (ArithmeticFunction.moebius d : ℤ))
        =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius (p * d) : ℤ)) :=
        Himage n p hp_prime hp_square_dvd
    _ =
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => - (ArithmeticFunction.moebius d : ℤ)) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hnot_dvd : ¬ p ∣ d := by
          unfold squareDivisorLocalSupportWithoutPrime at hd
          rw [Finset.mem_filter] at hd
          exact hd.2
        exact Hsign p d hp_prime hnot_dvd
    _ =
      -
      Finset.sum (squareDivisorLocalSupportWithoutPrime n p)
        (fun d => (ArithmeticFunction.moebius d : ℤ)) := by
        rw [Finset.sum_neg_distrib]

/-- Version finale : C-04b est consommée avec :
    - le changement de variable `d ↦ p*d` ;
    - le signe local de Möbius. -/
theorem squarefree_asymptotic_density_of_prime_square_image_and_sign
    (Himage : MoebiusPrimeExactOnceSumAsImageBridge)
    (Hsign : MoebiusMulPrimeNotDvdBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_exact_pair_only
    (moebiusSquareDivisorPrimeExactPairCancellation_of_image_and_sign
      Himage
      Hsign)

/-- Fermeture du signe de Möbius sous multiplication par un premier absent.

    On utilise :
    - `ArithmeticFunction.isMultiplicative_moebius`;
    - `IsMultiplicative.map_mul_of_coprime`;
    - `ArithmeticFunction.moebius_apply_prime`;
    - la caractérisation `hp_prime.coprime_iff_not_dvd`. -/
theorem moebiusMulPrimeNotDvdBridge_proved :
    MoebiusMulPrimeNotDvdBridge := by
  unfold MoebiusMulPrimeNotDvdBridge

  intro p d hp_prime hp_not_dvd

  have hcop : p.Coprime d :=
    (hp_prime.coprime_iff_not_dvd).2 hp_not_dvd

  calc
    (ArithmeticFunction.moebius (p * d) : ℤ)
        =
      (ArithmeticFunction.moebius p : ℤ) *
        (ArithmeticFunction.moebius d : ℤ) := by
        exact
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            hcop
    _ =
      (-1 : ℤ) * (ArithmeticFunction.moebius d : ℤ) := by
        rw [ArithmeticFunction.moebius_apply_prime hp_prime]
    _ =
      - (ArithmeticFunction.moebius d : ℤ) := by
        ring

/-- Version finale : C-04b est consommée avec le seul bridge
    de changement de variable `d ↦ p*d`.

    Le signe de Möbius est maintenant fermé par multiplicativité. -/
theorem squarefree_asymptotic_density_of_prime_square_image_only
    (Himage : MoebiusPrimeExactOnceSumAsImageBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_image_and_sign
    Himage
    moebiusMulPrimeNotDvdBridge_proved

/-!
## Changement de variable `d ↦ p*d` — données de bijection

On réduit le dernier bridge `MoebiusPrimeExactOnceSumAsImageBridge`
aux trois propriétés finies usuelles :
- bonne définition de l'image ;
- injectivité ;
- surjectivité.
-/

/-- Données de bijection pour le changement de variable `d ↦ p*d`.

    Source :
      `d ∈ squareDivisorLocalSupportWithoutPrime n p`

    Cible :
      `e ∈ squareDivisorLocalSupportWithPrimeExactlyOnce n p`

    Le changement de variable est `e = p*d`. -/
def MoebiusPrimeExactOnceImageDataBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      (∀ d : ℕ,
        d ∈ squareDivisorLocalSupportWithoutPrime n p →
          p * d ∈ squareDivisorLocalSupportWithPrimeExactlyOnce n p)
      ∧
      (∀ d₁ : ℕ,
        d₁ ∈ squareDivisorLocalSupportWithoutPrime n p →
        ∀ d₂ : ℕ,
        d₂ ∈ squareDivisorLocalSupportWithoutPrime n p →
          p * d₁ = p * d₂ →
            d₁ = d₂)
      ∧
      (∀ e : ℕ,
        e ∈ squareDivisorLocalSupportWithPrimeExactlyOnce n p →
          ∃ d : ℕ,
            d ∈ squareDivisorLocalSupportWithoutPrime n p
              ∧ p * d = e)

/-- Les données de bijection ferment l'égalité de sommes par changement
    de variable `d ↦ p*d`. -/
theorem moebiusPrimeExactOnceSumAsImageBridge_of_data
    (Hdata : MoebiusPrimeExactOnceImageDataBridge) :
    MoebiusPrimeExactOnceSumAsImageBridge := by
  unfold MoebiusPrimeExactOnceSumAsImageBridge
  unfold MoebiusPrimeExactOnceImageDataBridge at Hdata

  intro n p hp_prime hp_square_dvd

  rcases Hdata n p hp_prime hp_square_dvd with ⟨hmap, hinj, hsurj⟩

  symm

  exact Finset.sum_bij
    (fun d _ => p * d)
    (fun d hd => hmap d hd)
    (fun d₁ hd₁ d₂ hd₂ h => hinj d₁ hd₁ d₂ hd₂ h)
    (fun e he => by
      rcases hsurj e he with ⟨d, hd, hde⟩
      exact ⟨d, hd, hde⟩)
    (fun d hd => rfl)

/-- Version finale : C-04b est consommée avec les seules données
    de bijection du changement de variable `d ↦ p*d`.

    Le signe de Möbius est fermé ; il reste seulement l'arithmétique
    finie du support. -/
theorem squarefree_asymptotic_density_of_prime_square_image_data
    (Hdata : MoebiusPrimeExactOnceImageDataBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_image_only
    (moebiusPrimeExactOnceSumAsImageBridge_of_data Hdata)

/-!
## Données de bijection — séparation en image / injectivité / surjectivité
-/

/-- Bonne définition de l'image `d ↦ p*d`. -/
def MoebiusPrimeExactOnceImageMapBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      ∀ d : ℕ,
        d ∈ squareDivisorLocalSupportWithoutPrime n p →
          p * d ∈ squareDivisorLocalSupportWithPrimeExactlyOnce n p

/-- Injectivité de l'image `d ↦ p*d` sur le support source. -/
def MoebiusPrimeExactOnceImageInjectiveBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      ∀ d₁ : ℕ,
        d₁ ∈ squareDivisorLocalSupportWithoutPrime n p →
        ∀ d₂ : ℕ,
          d₂ ∈ squareDivisorLocalSupportWithoutPrime n p →
            p * d₁ = p * d₂ →
              d₁ = d₂

/-- Surjectivité de l'image `d ↦ p*d` vers la partie où `p`
    apparaît exactement une fois. -/
def MoebiusPrimeExactOnceImageSurjectiveBridge : Prop :=
  ∀ n p : ℕ,
    p.Prime →
    p^2 ∣ n →
      ∀ e : ℕ,
        e ∈ squareDivisorLocalSupportWithPrimeExactlyOnce n p →
          ∃ d : ℕ,
            d ∈ squareDivisorLocalSupportWithoutPrime n p
              ∧ p * d = e

/-- Les trois composantes image / injectivité / surjectivité reconstruisent
    les données de bijection. -/
theorem moebiusPrimeExactOnceImageDataBridge_of_parts
    (Hmap : MoebiusPrimeExactOnceImageMapBridge)
    (Hinj : MoebiusPrimeExactOnceImageInjectiveBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    MoebiusPrimeExactOnceImageDataBridge := by
  unfold MoebiusPrimeExactOnceImageDataBridge
  unfold MoebiusPrimeExactOnceImageMapBridge at Hmap
  unfold MoebiusPrimeExactOnceImageInjectiveBridge at Hinj
  unfold MoebiusPrimeExactOnceImageSurjectiveBridge at Hsurj

  intro n p hp_prime hp_square_dvd

  exact
    ⟨Hmap n p hp_prime hp_square_dvd,
     Hinj n p hp_prime hp_square_dvd,
     Hsurj n p hp_prime hp_square_dvd⟩

/-- Version finale : C-04b est consommée avec les trois composantes
    de la bijection `d ↦ p*d`. -/
theorem squarefree_asymptotic_density_of_prime_square_image_parts
    (Hmap : MoebiusPrimeExactOnceImageMapBridge)
    (Hinj : MoebiusPrimeExactOnceImageInjectiveBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_image_data
    (moebiusPrimeExactOnceImageDataBridge_of_parts
      Hmap
      Hinj
      Hsurj)

/-- Fermeture de l'injectivité de `d ↦ p*d`.

    Comme `p` est premier, `p > 0`, donc la multiplication à gauche
    par `p` est cancellable dans `ℕ`. -/
theorem moebiusPrimeExactOnceImageInjectiveBridge_proved :
    MoebiusPrimeExactOnceImageInjectiveBridge := by
  unfold MoebiusPrimeExactOnceImageInjectiveBridge

  intro n p hp_prime hp_square_dvd d₁ hd₁ d₂ hd₂ hmul

  exact Nat.mul_left_cancel hp_prime.pos hmul

/-- Version finale : C-04b est consommée avec :
    - la bonne définition de l'image ;
    - la surjectivité.

    L'injectivité est maintenant fermée. -/
theorem squarefree_asymptotic_density_of_prime_square_image_map_surj
    (Hmap : MoebiusPrimeExactOnceImageMapBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_image_parts
    Hmap
    moebiusPrimeExactOnceImageInjectiveBridge_proved
    Hsurj

/-!
## Bonne définition de l'image — réduction arithmétique

Pour montrer que `d ↦ p*d` envoie bien le support sans `p`
vers le support où `p` apparaît exactement une fois, il reste deux
faits arithmétiques :
- produit de diviseurs carrés copremiers ;
- impossibilité de `p² ∣ p*d` si `p ∤ d`.
-/

/-- Produit de diviseurs carrés copremiers.

    Si `p² ∣ n`, `d² ∣ n`, et `p ∤ d`, alors
    `(p*d)² ∣ n`. -/
def PrimeSquareMulSquareDvdBridge : Prop :=
  ∀ n p d : ℕ,
    p.Prime →
    p^2 ∣ n →
    d^2 ∣ n →
    ¬ p ∣ d →
      (p * d)^2 ∣ n

/-- Exactitude de la présence de `p`.

    Si `p ∤ d`, alors `p²` ne divise pas `p*d`. -/
def PrimeSquareNotDvdPrimeMulBridge : Prop :=
  ∀ p d : ℕ,
    p.Prime →
    ¬ p ∣ d →
      ¬ p^2 ∣ p * d

/-- Les deux faits arithmétiques ferment la bonne définition
    de l'image `d ↦ p*d`. -/
theorem moebiusPrimeExactOnceImageMapBridge_of_arith
    (Hprod : PrimeSquareMulSquareDvdBridge)
    (Hexact : PrimeSquareNotDvdPrimeMulBridge) :
    MoebiusPrimeExactOnceImageMapBridge := by
  unfold MoebiusPrimeExactOnceImageMapBridge
  unfold PrimeSquareMulSquareDvdBridge at Hprod
  unfold PrimeSquareNotDvdPrimeMulBridge at Hexact

  intro n p hp_prime hp_square_dvd d hd

  unfold squareDivisorLocalSupportWithoutPrime at hd
  rw [Finset.mem_filter] at hd
  rcases hd with ⟨hd_support, hp_not_dvd⟩

  unfold squareDivisorLocalSupport at hd_support
  rw [Finset.mem_filter] at hd_support
  rcases hd_support with ⟨hd_Icc, hd_square_dvd⟩
  rcases Finset.mem_Icc.mp hd_Icc with ⟨hd_one, hd_sqrt⟩

  have hpd_square_dvd : (p * d)^2 ∣ n :=
    Hprod n p d hp_prime hp_square_dvd hd_square_dvd hp_not_dvd

  have hpd_one : 1 ≤ p * d := by
    have hp_one : 1 ≤ p := Nat.succ_le_of_lt hp_prime.pos
    have hmul : 1 * 1 ≤ p * d := Nat.mul_le_mul hp_one hd_one
    simpa using hmul

  have hn_pos : 0 < n := by
    have hd_square_le_n : d^2 ≤ n := Nat.le_sqrt'.1 hd_sqrt
    have hone_le_d_square : 1 ≤ d^2 := by
      have hmul : 1 * 1 ≤ d * d := Nat.mul_le_mul hd_one hd_one
      simpa [pow_two] using hmul
    exact lt_of_lt_of_le Nat.zero_lt_one
      (le_trans hone_le_d_square hd_square_le_n)

  have hpd_square_le_n : (p * d)^2 ≤ n :=
    Nat.le_of_dvd hn_pos hpd_square_dvd

  unfold squareDivisorLocalSupportWithPrimeExactlyOnce
  rw [Finset.mem_filter]
  constructor
  · unfold squareDivisorLocalSupportWithPrime
    rw [Finset.mem_filter]
    constructor
    · unfold squareDivisorLocalSupport
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        exact ⟨hpd_one, Nat.le_sqrt'.2 hpd_square_le_n⟩
      · exact hpd_square_dvd
    · exact ⟨d, rfl⟩
  · exact Hexact p d hp_prime hp_not_dvd

/-- Version finale : C-04b est consommée avec :
    - le produit de diviseurs carrés ;
    - l'exactitude `p² ∤ p*d` ;
    - la surjectivité.

    La bonne définition de l'image est maintenant réduite à deux
    faits arithmétiques locaux. -/
theorem squarefree_asymptotic_density_of_prime_square_arith_surj
    (Hprod : PrimeSquareMulSquareDvdBridge)
    (Hexact : PrimeSquareNotDvdPrimeMulBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_image_map_surj
    (moebiusPrimeExactOnceImageMapBridge_of_arith Hprod Hexact)
    Hsurj

/-- Fermeture de l'exactitude `p² ∤ p*d` si `p ∤ d`.

    Si `p² ∣ p*d`, alors `p*d = p²*k`.
    En réécrivant `p²*k = p*(p*k)` puis en simplifiant par `p > 0`,
    on obtient `d = p*k`, contradiction avec `p ∤ d`. -/
theorem primeSquareNotDvdPrimeMulBridge_proved :
    PrimeSquareNotDvdPrimeMulBridge := by
  unfold PrimeSquareNotDvdPrimeMulBridge

  intro p d hp_prime hp_not_dvd hp_square_dvd

  rcases hp_square_dvd with ⟨k, hk⟩

  have hd_eq : d = p * k := by
    exact Nat.mul_left_cancel hp_prime.pos (by
      simpa [pow_two, Nat.mul_assoc] using hk)

  exact hp_not_dvd ⟨k, hd_eq⟩

/-- Version finale : C-04b est consommée avec :
    - le produit de diviseurs carrés copremiers ;
    - la surjectivité de l'image.

    L'exactitude `p² ∤ p*d` est maintenant fermée. -/
theorem squarefree_asymptotic_density_of_prime_square_prod_surj
    (Hprod : PrimeSquareMulSquareDvdBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_arith_surj
    Hprod
    primeSquareNotDvdPrimeMulBridge_proved
    Hsurj

/-!
## Produit de diviseurs carrés — réduction à la coprimalité

Il reste à fermer :
  `p² ∣ n`, `d² ∣ n`, `p ∤ d` ⟹ `(p*d)² ∣ n`.

On le réduit à deux faits standards :
- `(p²).Coprime (d²)` ;
- si `a ∣ n`, `b ∣ n`, et `a.Coprime b`, alors `a*b ∣ n`.
-/

/-- Coprimalité des carrés.

    Si `p` est premier et `p ∤ d`, alors `p²` est premier à `d²`. -/
def PrimeSquareCoprimeSquareBridge : Prop :=
  ∀ p d : ℕ,
    p.Prime →
    ¬ p ∣ d →
      (p^2).Coprime (d^2)

/-- Produit de deux diviseurs copremiers d'un même entier. -/
def CoprimeMulDvdOfDvdDvdBridge : Prop :=
  ∀ a b n : ℕ,
    a.Coprime b →
    a ∣ n →
    b ∣ n →
      a * b ∣ n

/-- Les deux faits standards ferment le produit de diviseurs carrés. -/
theorem primeSquareMulSquareDvdBridge_of_coprime_product
    (Hcop : PrimeSquareCoprimeSquareBridge)
    (Hmul : CoprimeMulDvdOfDvdDvdBridge) :
    PrimeSquareMulSquareDvdBridge := by
  unfold PrimeSquareMulSquareDvdBridge
  unfold PrimeSquareCoprimeSquareBridge at Hcop
  unfold CoprimeMulDvdOfDvdDvdBridge at Hmul

  intro n p d hp_prime hp_square_dvd hd_square_dvd hp_not_dvd

  have hcop : (p^2).Coprime (d^2) :=
    Hcop p d hp_prime hp_not_dvd

  have hprod : p^2 * d^2 ∣ n :=
    Hmul (p^2) (d^2) n hcop hp_square_dvd hd_square_dvd

  have hrewrite : p^2 * d^2 = (p * d)^2 := by
    ring

  rw [← hrewrite]

  exact hprod

/-- Version finale : C-04b est consommée avec :
    - la coprimalité des carrés ;
    - le produit de diviseurs copremiers ;
    - la surjectivité de l'image. -/
theorem squarefree_asymptotic_density_of_prime_square_coprime_surj
    (Hcop : PrimeSquareCoprimeSquareBridge)
    (Hmul : CoprimeMulDvdOfDvdDvdBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_prod_surj
    (primeSquareMulSquareDvdBridge_of_coprime_product Hcop Hmul)
    Hsurj

/-- Fermeture du produit de deux diviseurs copremiers d'un même entier.

    Mathlib fournit ce fait comme méthode de `Nat.Coprime` :
      `hcop.mul_dvd_of_dvd_of_dvd`. -/
theorem coprimeMulDvdOfDvdDvdBridge_proved :
    CoprimeMulDvdOfDvdDvdBridge := by
  unfold CoprimeMulDvdOfDvdDvdBridge

  intro a b n hcop ha hb

  exact hcop.mul_dvd_of_dvd_of_dvd ha hb

/-- Version finale : C-04b est consommée avec :
    - la coprimalité des carrés ;
    - la surjectivité de l'image.

    Le produit de diviseurs copremiers est maintenant fermé. -/
theorem squarefree_asymptotic_density_of_prime_square_coprime_only
    (Hcop : PrimeSquareCoprimeSquareBridge)
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_coprime_surj
    Hcop
    coprimeMulDvdOfDvdDvdBridge_proved
    Hsurj

/-- Fermeture de la coprimalité des carrés.

    De `p ∤ d` et `p` premier, on obtient `p.Coprime d`.
    La coprimalité est ensuite stable par puissances. -/
theorem primeSquareCoprimeSquareBridge_proved :
    PrimeSquareCoprimeSquareBridge := by
  unfold PrimeSquareCoprimeSquareBridge

  intro p d hp_prime hp_not_dvd

  have hcop : p.Coprime d :=
    (hp_prime.coprime_iff_not_dvd).2 hp_not_dvd

  have hcop_left : (p^2).Coprime d := by
    exact hcop.pow_left 2

  exact hcop_left.pow_right 2

/-- Version finale : C-04b est consommée avec le seul bridge
    de surjectivité de l'image.

    La coprimalité des carrés et le produit de diviseurs copremiers
    sont maintenant fermés. -/
theorem squarefree_asymptotic_density_of_prime_square_surj_only
    (Hsurj : MoebiusPrimeExactOnceImageSurjectiveBridge) :
    Tendsto (fun N : ℕ => (squarefreeCount N : ℝ) / N) atTop
      (nhds (6 / (Real.pi^2))) :=
  squarefree_asymptotic_density_of_prime_square_coprime_only
    primeSquareCoprimeSquareBridge_proved
    Hsurj

end CouretUnification.Logic.H3
